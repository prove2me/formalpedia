-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1825
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:48:35.893926+00:00
-- url     : https://prove2.me/submissions/58a20148-19fe-43f1-b31c-b49e6b38aa76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 328057553 ≤ n < 328237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 328058803 1250 328057553 328057567
    0x305042d02130e280219030219031703100510020d030c14071e050a0804080d1b03030f0e030a0c0b0a0c090e04020d081b010c080c04050108040c081f11 66
    0x46042c410003440100c03013a0001030b042034513400300c403244140250311040341018010a995142014401d4a0080d1040c0140040c60301112000b040d03103000140c10362040300c0342440c5500a150003198130410545480102d19510700201d0500550100700801603008880350111803949440395010f50b914521784000310036100c0700030055511620001400e00c4058150300444c40065000c044041e543c000111600407000c0d00b4150025041030007410034600504d400000e10354824039141107044507011400c1c5009a0b6640e007500100020440b903114252107132800156140140301402212500d41c40b03030620200c880c505180c50900080050008274600200030000c5075000460030240c6001c189407045c40d4865000103110f08c080d13283e00505445000a04031a4011400e640c01c40d9946894002c0c041c01499103016140200112113040005030240310800c81c1d0740c4101340b0150040e00a0201d035183c20340341c1d03050383d00b481740305400e02803a5510513400500380701480c410780ca0246da60350452414181 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 328060053 1250 328058803 328058831
    0x20030d030b150c070e010b0409061a0418060e01080c0306090a0f030c05010e010504030903110109051309020a08060403030219020a020d0605070e0a08070504060905160305042d0213 79
    0x1102c1c01e00521200c4000c101540140c40412040014045c01d2004000303941e51443c5000c0350768401c1c0543e0508904040000480c5080405100c5410b0a061002402c1c541866108094201e10380e50950340c960316500002041607592140314041d010702c1c0040c0c281001004241482e0200250242415601620488001c038400c82e4136100107550500e007911640c1d1640c00c185000d4a40107140d91215482c110600013050f810150341800c49100b985003101030001c0c00019940b2503001c2c07240940017042400c00c500008102c0c1d00540d01e951000303140d02a100d40b54500d0901c0c00da01210300710082a4002000160110a4000740715200c00c10310050022043d15400b080d0146000c4a0060049403903501240b641d41c02520240030124010300707108202903803200a240d03220748a01c55a4082c42c5044c001051701c0c0e240d40581c1303200b03035520440c180c4441100c01c4102c004040041090b00d40c281d4980301c002d07855403460b411540984044400f100d40800900400c5800313081d00b02c020904030716240b61610111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 328061303 1250 328060053 328060069
    0x50a060503130b130201030e1501031b0305030d0f321005030303040308011401020c01170417040e012103081b040b1c0c05070201080f070c20030d030b 66
    0x8480345881038a03034031002958007aa95003558000c240c05503802c10002032654018103030002074001d030f034140b10000c0c18510b80c2d51074071072151808450607c3d000050020907120380c0316090301c001d941c286c44003c50340c2e52141411504100c0711000c400d600d40c0c1400d0091810b60080c2c9013035034103440e80405c81d001408600907510481a03544020041380e0300000780b00301c0d0b07044880b800070007010381030300d03503074035003450002d0881000340614840c203035411204403001e51000555610080041c1c5520900b1340c650004002c249500400444194452511100080403640e002d0001444090b001c5041c55040c0f2200081c0d80e5501041212401c07240e000003404284e10402c03003504440d031480c0c0c1c9480c149030062200b0380351007a5007042c1d24520001504000194100c51010104035465504105900e12000c3c115458422954064006110040804d4450500040342a04036605080c5000154203940e1441c00c400c1c65407070340c943c10104101a4511a003400e1081004103000782c03404100002070f030f1001652807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 328062553 1250 328061303 328061309
    0xf0114071202040b0a110d020d1407080910050c06061509042c0a050105100302090c0a0909060e2d0a091b0306090c15020606040b040f050406060519050a 67
    0x2603407140070140340d02a0341143d01500401e44095074440070400090444c01c50980c900c02c01d0310030904940410751000c0760100e911800d030f80d280000d600c2e50b0b0219080315042520103031802c2008010b4000300703a4803052041d1618100c1e40783d440e02c1c3c0c58003002960030305400818260280c09500d144900d800072b00c0048414000003182c0c0014040681e400c40c0100903d03006083c0d40b00551801090200980000c0c1005440d11440007482581c3d10300e070b03003082065094071009400102020201e10402c0311100600741c04521440d02d0281c503550352800c141a100d0680c8000d50880d1b054082c403c0400c1c9140340760400030510b80c241e00c8640c4d15003400714040940100b0503688669a070394072404214110807000707140307980c906442407501d03101e0800c50300408100350211015034898000048820b05503040c81c1543d880ea8003d4106550f0322018040034040c985042c660143d903c0a10880c010780c1c0780b16180c040c9008200000303a050034403003401703158142000d49201c0303c2c114030800c0090341d03506039084081e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 328063803 1250 328062553 328062557
    0x181314010e0d030e150a0516090317070f05070b0711040216030e06121503060112030c021c0204090b220203032205090f150a080c01140d0e0303090f011407 68
    0x14120080b0b1180d170601c0c00c1e030400c01d401002244240b01440c12950400c0e40101d4148035001c0b1a03180d0000c003079484e02d039107201c02403000464203481c050b6200918081c140481c068805c100c5095010b94800e41040701c40d4110f1403071a10b005c11584180710b51010091017100064404505d00070055000400c0c4e100440341c001d04004080d40160041d40341d80080d5a00c50030719404030500c6040600e20320b20035000d110030450080c49502d00000300a62071030086608282c140e1144408140c2a400b81305a4071010403d240000100ca00c1190040e01d0701d10688031101d00900e034960490501162604200c1e080700260301140c07104008500c090303030b0302008998416602c1841c000e605507942c03150b400d1030007440d0b01450b44400d800f402c03c040f00b052006801d2041141c0280984090b01a000f0016505010b00543d080c0340d1050403410000d50107002c2501c0140c114130308950a24a000c070507402954444d14514035507820100601c000c0c207100f0040c2131400711580f4024040094040341800002500910404c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 328065053 1250 328063803 328063811
    0xb030421080613020903010e010e0f06060a0b030703090210110606010e010512100815010311060403080f0703120e0a0c0504050705090d0305090406271b030b181314010e0d03 76
    0x5908960b04175503c5900180091045d2080e0b850654000c040c145940d01a5014001c402034121601003945482000300824141c1c0060500e20041c07510713000105000c05065a40301c1369005070303961000200c00030829680e181000d40c3d002251500304840a0100e40c1401861a80e070b9040b0380c2c01205680781d6011946016480760f958000740700c1004055840302000b4041d080c100003103108140c102078103813401000720803c400c00070b0082c809241718903c00905030b01401d12a41c610002544002c20b80d0301d001e86043da1390511045803400c1290142c642246803130340b100c082802000203580c4090001e0404940c2040b461410740e1024091340301740e0300d00c24458281c612003201014050b000361040044c010f132080100310340703c02c0d40c0060a110038820418500c095802e40000c4c910728020012800185080100b900540d082d040c0e018051841c85141d000130480301c81c5204050103860382d8403441c01410f0310b840002d035a08001c03941031050b280310305069042807524040b20710700050083c10b9207154a0700013 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 328066303 1250 328065053 328065079
    0x902040e0603600f010b03010302060a11101e0c05030907210f03030c1b050c0f0418080901030c110706120603080a0819140c0c030c06010b0304210806 66
    0x10400c80f070348a50202404402c0034100003078a8203034800d03100703900345403030100c1691700c4130483c44460100b48030082d40a10108010b9680c14402c0000e425203481460403240c2800c0d240c0d4010040d202007900b08500c108007101c0800301600035026203003295040f03080c1240b4500300418860b40311001e502840d40340c0b041030003110700c00d4a0380c005a120131541048610049058500e8024064440000543d00294440007502c0100c2004000114800c0c0d000d0004c222411804040c44070f402107025005d64416600d8445a2261200c2240b80038004d10a4071038940d00c00e80c000c005011aa00c01a0040411111640340c00c0680000981941036400c3ea04100d01411303406212400600542c1d00000c0841d400803451803009500f0180141c058051074048224076a1158840400c07901151981c100765078401000c07940a199500080070f0401100041d2031038009000216494034400b03034050b0341d50090000c00c00c0b083c448050100e00104a841f00d615039918070010b001400401c0c007414540c481c4141c4a144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 328067553 1250 328066303 328066423
    0x412020d081b030331060b03190c081b0a060806031207030f090602120d021e0a12060503030f030f190507110f0d020a08070305040902040e0603 63
    0xd100c1c1c081241c040d012a400209038560f45a400903129540c1c00318048034a82c1d488004049914291a40035900740c10200701034a0304000341944c0d040080e0503000d50015264111100c009035100703107000354041407401e4506141c1901c6c003401008010583c4046d041041081c2e6078001c14107003100c5461900d8420f980364240081d0400e0103250804254042c00252542007540101030506009099240c04000c04d40d1404140d031100800d80d0000c0c03020740c04000440442ca001d50140c001d6081c0055248991200007201640c2c5900c0041040d011070040c010100102020b4041c50014282c00e070055814401c02c5211411103002c043c05880001151a001038210862280365080408074124140860700f480b03400508410113940006251b405034200c4592100e000007070496440300d103030b4000c4c0010700f00c0c2d44940d20240c002c09011420480c08100004e0074692034000f50014202000c03143e07009003002000c151a084e40e441d40d44900318074100c0d0a00e0090b1096441300603901c0c2070011041700c0c4100c600d074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 328068803 1250 328067553 328067557
    0xd03020111040f03060b010c020a09110903010203040813090204050a05010f031404080a0e120606090709091a0a080a0512030c0d1109090106110c190e090a12050412020d08 75
    0x1429015001c04100000c80b00d035540030b941c044030b0158a040092034626070044801c04035003907004e50800c40c42042048041030940c05103070428020f001890074070007000002401d9038800d40f8256884400451552401c100c4421600c0040000801c1140b82528003404514011440d07c900c80c140041c0107404900b040c06600075407040e50080140c41840d281500e84006c0700c3c3c1003500007500040c030006008020713081c1850700c1d002c24510b03072009100c55582d880c00c0080218008200c6003c0203a91000002c00442c0390041100c50344481c1d03408021803100d14140800141c941c0d0141c48130f0b40c021404600800c60124000780e030f9000e18281c00b41d407591407030b610b82928803c41c503200003ca840d000440341105480406071030010000c4031301e000c01e40d9a840045801051019141c990360f00f0007060f0481d18a8110341c40c58603c0c003014880f0f96002c0d81d070440170000a42c216151040b40e000107841d08200011350314121850303801802c0036410107003010000c0d02d6a0b0076071b000c0280140181600142070105e5001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 328070053 1250 328068803 328068821
    0x7090507050904020c0a060c0e0f06090409050d09080c0d0b0a0c1103070b0402150a0801090203060a0e090f011b0c020411070b0c0d06050102030a1413030804090c0206090115050d030201 81
    0x4810340d1742d42d49030000295940202e4a054504038036290000741541d01c9440c0160070135000030945154421044100041640030307980484c0e000e50381d070030060005203081c89204949517031a02c03650f01b031030316000c4410309041c20054228401d1b041d4140800000c1c490081150308900402d04c000303841075400c9000d440c0000c80301c2c41081240f1010620380f0410417000f0b8440d20440c400d4506c891210700c110f40042507802041440c4003c601010300604c06040315030302031948518000c0c103c010180d5950462200000d0680b82a4425080001030b107800b160f090095048517040c80320003880704401414024040c1d401d90400910880e1942c0d0b40744c2c659580324055500c0207400003140303c0c071410011040d29241d881200e0848281d82090000183c6600101c10f41e803000500361100181c0c40100360a00c0710720340c812205144200d0381000c020010440250250019181540300012000c9002c0d1000c0e19040c0b00801c808100c0c0e041c20440c41c80030306940d4a01c81252004da6407034074400d80d180b806a002d458480c4c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 328071303 1250 328070053 328070059
    0xb12010f020406031a0a0312050f0409021902060601020706180305030a0c02011206080d0c060e1015050306060303070f1a0907050901050607030e09060f15030108190302070905070509 80
    0x51000d40590515074000c0c070886609840400c001c0c0590380500900c083c0e02100c6681c449444182000407452200083c01c5e00e40d040c1c9012490110703140042c80c40750700650020b21910798081100c01c401c181130f1605004e800540e00040c0000d01c0d001000030755030101c034000c08080005c01e95a0490b031600d000104c502440e4004180c07511407034501c2c001072841c074030758005a000845800d060111220a446413a043d00c0281010b0071031900d5510b01501d8540c8140c0741240c1c0307207558005caa5804a0280071311070b503018203484c010070080030340c088589456121307400c6240300e50089014005140c2d400801c5030b240650054090b1821801170816605044c00c1007d030045942c528000c1110070300c4080f4a2805031841180c1c54040c0b41d0701e92080c4803d81c000d58000034041114956038141c50303d00604c90951050b00180b044080c00840302c003041868030302500301d1074100c00100060001007414002640d9680c0f140030042e41e86071064500941c1c03180c170703482150030041c0c2d504041140e8922440440350341444c05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 328072553 1250 328071303 328071311
    0x90c020a08040311010e2425030905091b030a0b040b0306091f02040b07020f030106050a0b0d0f0b061603030b09010303050310050103051501180e1f0803090d060b1201 73
    0x341071144240013811041c034001020803010310514602640030101d5044460640601058100203c0e02c2c43d0740f14584400f0b422944000c4560600140c9018403074540c030a54441000a140c08280300ca44040904045d500320448401e06418158803001d0741d51110300c42001080f41c80802020a005007214512181c25004050400c1041310f400a2010b440034158100020104520011041280601c0c012282542401c1110101500e000c20100d10056002070000600c10340d114002a008941b030780c002400326901140c030600480f02c40c407500c1d03041d0750140e401b401860b000400080c6207200302074141501601401c4400f040c90300c20b9000c8481d0074005070100300956141d05018150790011a0104040019a10081095407080c01024040c400e65055805031803000c3c1c0040d9000300c280c1e200b028107002800e50002d0303140c80c10751065001e141341c0c80c007982c00390070400115000e16003140c10126a940c0100000d100548038003090008964200b440090007910b504000b407075505202c1c03280d103115824 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 328073803 1250 328072553 328072559
    0xa141b07030b091b01300606020109110f01020a032a0b150f01050d09140d090303090b13090b0f0301090b0108011505090c1e04030c0302090109020c0601090c020a0804 73
    0x346685000b070590034201d680316130703503000200309000380441440e000031144007541042c88448202421401e0b403a80c00d5010140307032803407408101d800590000380180e4480041c50240b00f0013230201c0c980743c0c00584070080c0030f011160000c0d560b0071203400000c0801803024402c41140461000e458a140070160704280000301506008900200c00d60320020b14030107003889000c5600d440c0c0c0041e69a140d040c0c6501e07003490041c4410700014946c0c0f00040e038030382034200c541c09082041408141c05800311078a420304424250b00300244030005a4003c5100304804001c0e40d0b1071141003c140400321600711002048040081d004210551a07010101e50150308046107031042140d142c1200741600c0070070001708040030580c0c403110008031061148a422402000103e07002400c034100038001c1081c03240e849504665200302550321030f84039500c19500036203910010301c211720300b44104600405061405509114018000e107480304011320a0040f000c1d610341d14403210500a1042d0b14105402407089034865603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 328075053 1250 328073803 328073813
    0x180309141203191209051e01090b1603180c0e09030f0904023412090b070b060301060509040308070207560903060108030a05041509051e04110a141b0703 67
    0x1078000130824181e209003c7d40d0041c200c1c14840e001100790010141d0915407a9010381c07481c401130801341c1078101034444210810142d02209110f01d034512940d0088841c038130f405140c2c000580050201d500239001044480c582c118400142c4280c45412100140da0305403981c10019826032412003c005055040448200d603100364140a4640380941c0300310092600003402125100d146000b203001c210030602114000c2040d104075158859005400000c400b81c0700c01c0082c8800700c0454044000a00342004c1042190741440184011b0807280300310b0740003541840ca1046c0c201002140c46500141c5100c03460304000600701010303810103407000c81c1a281c1c01a42e0000c000d551180040e64081c0c03083d00000551503030300000305c50758600c4550701c50b802c103414030307071600c42c20305a030488842044103901c0301042c20f603241018015070314059914000c1c040c0d003075401c0c00300f519440c280fa4031030f40030280a811386181c3c005241c000e100d103030601c00136a142e99565084074888140394000d01c05104003400801080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 328076303 1250 328075053 328075063
    0xd0e060d1e0c050a02031218120c1506090601030507301802010503060d03050403150221070503160903120f1b0512090418030914120319120905 63
    0x3154008040c000380b90b014030103954500c41d03203a541c0010f134004c01c071040c0000125000190410040311082820301c45c2018110f1400001c1800c542c1345c1a03001599a1400c2810880b140356440e07540d0055101c0e00e000d00003c1e0000c0001050203051640f11000258014031602003011241d04100c81d20f8185d52030742051204200d8030041d4103074001d02d460310030318284500d14100446030740c0c1655000d185540d40c02c288610343c52000c1003103086c4481444080300144400140c240000701c0b110740140c40b840e074800c44245005c40c06000d100c25019075800c0c00003060f8000c04807544103001d5504640c1000a03030000721808249a030002c0d1040101d030105409180d4003c1450031603841c2c555401c000105402020410700d881090002c12a0740000c180d0003c03001d40b02d01034040300100400006614103c103800f0b08494070039003400c0300000e01101041c0401c440020011000d09000d81c0c460300808400c0e02690750b01d21407000503401d0b02c014503058200e140d00c15411021107003008035080c8088401403410542d24 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 328077553 1250 328076303 328076351
    0x3120f070906030908072a0603020909010b34061b0c0b100f0308030108010e030a09120201120905010b0108090309011205100f0303030b0913050a110111010e0a0b06120d0e060d 77
    0x47d070780504001403840c0c800e00a540c41d00c1c400802d0301c580c036443d00c81c0c01c1000780d0000c003540d84031655403030000e0140d0032140008441041e000a41c40a01040d0f403410310100d0b600c1000c454111407890301090201750303000030703a41040c03540001e20002c2c9444868025a00c00c5090307000402000c4800c0c804410464060007450403610800002d111400a112f109511390082518001c002281008200b0107401e5170200144064010b0504001140207540c14074162244000c00b03031800c0e0b450b40c601c0120303542e1080d6441c0d40003811170059401d2520308000200a5051001a9444035444801041c020a1308038003150041805105044800d90780e0324001e400341604140d11031240c200c100001e005464030340c1e41d90307100e00c0d44940500080811950340300b0341c00303401c2089e550400c000c110b29090108070034410304d07941804070001002120003525041000313038402407a450086030100c0c0c86114a020000c4e100241d90100e0070612510b0700380c2c1c8007086040c0a807030021b41082d0300788100d0740c0a03c540c41c1001001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 328078803 1250 328077553 328077623
    0x30302334609060b0319050c030616030911060a0c0b01320a091803140f04060f020c060f070b010906051008090102071e030806090411010f0905040603030203120f07090603090807 78
    0x2401058004041d03c0e03000450380500c41102c2f88002041441c840d80c00b084a047c442c4000402c3c0001d4580410415040161032101051b14036003002d050188139000c042c01002103190000c01d18204241403c7c40c13680c41c2040c0c41c1d528402c1140382000d0341c2d44134a03442c040c1130180b204004000c224030790340d144080440c809802095528244590005651049403901c00016000c0707031074503150180468018000002c08421405924808019944c070200140361f40000100c0341c5444d0813103420070311000720040e80800340281c507001080003643c0b0340c0c000d50700d003040035403c1582095450b03624980c00ba10a42c2c4005110031220508020162000074460440c1e900a58031b1402c2350383c0d14414404400d00580d0060081081c1c8100c01405610a0b08008180343c100e1905d0040c0554440105068036000d400481c0583c0012074a1036084241c44082c1f43d01002c3c81102500604014501802c0c05065004036000c00d034803013000c003080c42522011592040e40c4400040400e0700c0d011103101c14502042081c0351 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 328080053 1250 328078803 328078813
    0x3020901050c012a2a06180c060905012609070e0a020a110118120509040501030b01081c140d060302060a090e090304030302334609060b031905 63
    0x4015403080a2440882040e100d45040d05d0b9402c07900c00301d020b105c07240b0840d8801e46a0000050700d82801500c41c401381e228200c0711043c0c5040ca0805482d150850300712504024048074032041c14208403110126190310545a0030346910780c03205150410082d81c10031f0103001103460920480340c13030b02ea0080049011a07928100d6410011849500fa501104072545082c40800d040c2004200b030710300d42c03140d25101410700350700d458a0325000c107040d074000340c3c02234940310128001040520002d00140f480c0d60500da20710701c01503540e0000030744409400c00300045c4030417001c5600501ca015640c01a8041c640051010751100150030000308261414000c50100022130300101d80592800815242603a6040e000303002041c1c45842043d2241030702c0d0702000c40412010780364904a4a0003a001c40c0121840051a4030225079400814451096040f061003001c441000c0c0c0e020342000c0604000241c02c0044d0045080c81c10350402c0750180010310b5100754140a803d145903050710904c090266210b200c0c4d03081c7d90b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 328081303 1250 328080053 328080131
    0x303070c03050d1715062104060c0203070c210215091315051315060804050c0108010f06050702010e0301050703090c0803090105070807050304090c080a0f150603020901050c01 77
    0x191100680d00d0140c03424084840800e010100040c100c403817100010300700c1410503208185103103924140c0038070701e401019240148000c0c840e207405494211105800254035080300c3d0b41e13a041c006c20481c86010602c00c42410b03c8200c0000b40700015607150380040209841500052211503580c0c0049520703882801251031064202d84140250352160324808064a41c0c0d52405080c05140c2d911007208c4944190f0b00d40394820120b482a102e400600742a076600700d01071a29181062411050f0000d0a0505c145c0c207004021009165802c0001d039502403900c0d43d21113107e44016908407032022885a03043d4203100810100070782c59400300c14280d000d00e00c1c0d112026074034020945c40f889101000f60004004103e0640427804038001084000d1013403040302e18241e40c1d017401e42d084408c80c0c82c50702c00090ac1d0909000507241030340a1141c982001040420807078a18024204100300320f4800e40080c550042070902140e80103500392101c1450081c0244002c52040d0700c030001101181c500b0b03100700990400300c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 328082553 1250 328081303 328081307
    0xf210212100621060e09010c0f0809060621121305010306150e06040e090601090b01020606030c1c060204121e031b020a0b0703120b120c0603070e0303070c03050d 71
    0x100846840e030701d4420100d1280d000f07255038040c0080400d40b44076103429001031201e40d2184010b11805150300002005811a480205000315001100040084110510881100108106400050403034640c01003c1c88240c070b0940d05515190100721502910702d00c0000c104410300140701545035550604a1952107800550884515000300c40e07100302148940c0c6521070069a8040380702100038061400c10390746a5a44030f8000040795540a5078229a004000201960146101000003400a46210703d8030401180d52030b161250800e120714000c00107200881155810030b412203406c00803e540e141d455210700300c000c02100804a80c112000807060003810306144c202411b2952683d0743e4501d03400d40a10042d1405194802a43d00007141c04000801d070070208020b1030464400d850301c40003e003641400c4411642510351040c00323500c0f80007500c3d42e01c010200f404c98050808480760790316038490200c1144c42c01109020300b40c040c07100260a105110541c2e203a641282d00c12012103041060703280e81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 328083803 1250 328082553 328082581
    0xe09030a0215091911010206061f0c06242405030c0306040204170d080a060f030213150f290702060711030303012d150f210212 56
    0x280c8001030300072045580751125002c0040e60804841c100303d40c076031072486080b0310844200b20030131200748038621902c1116580522029500800844003035608980090925402c1101c8403000003c2250105080c020840d40d503101c0b00701c6020301001d032540c0c00d48621710002c03078600b20b008805540d1200700010404000300c000b00301f080e41d40b580d503080c150340f1001802141500050084c507401602480007003a0089510320000620105000a0880444002015080c0080a4141001142814818800c02c0900303050038045a034140e8500440000d58200580180021800421515480e05c4000b60701102c0c0d841038011f41d51440f03508417036040c48200090400040c0c07502e1007052481070103a0340c05850241d002d40041c3d030045590900003400b090001c0c0c21071380240c2111049200360766103d180600355a045103040484000009081070400d86400c6156000714a00030800c00e2407401c24000500c50800c4580026a41e68044182400b003410b5901071741201d00002600300d4030000151030580b036100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 328085053 1250 328083803 328083817
    0x10e0604080405310b1f020d0c02180a230403020a08030903070501050106050408100e03070206091201050901020a0e09060a0501030c050f0c15010b0a0e09040606080102070c0e0903 79
    0x22003071802c0c0c80d10701840010590015070129480e588a60b200805203501340c0f000c509045241e00140201c0e2040c200500c0800251000701514a5910500032080d00001c03903514400c50350822500140c0b06100140345010006008098100c4150510500c1d10340c44e004100240c1541803110105080442204c0e40307a4001c41340078006a11148194012030b80302401140c000211606984c90425591615400e40303c080c2d200c440040e200040070401040280040c42a06203485418000132020031840342e600c0c010500e0180c4960030000c5e84d45159500d90700d000d10b130560510006e0025140021014bc003d40203180d0b044081040c100e510707816803030200c0516209071402425061118201001100184800d100500c00d03c08200220181a44d8cd000a00b00703a000c048000e01020480e00d1080344c4019041c1d1007040c59101c28466001e60355000350b000da0160400f541e0349040d9036550306103a4040e089c0c541c031282c1103510001b8018188000103811f4015120b5031111b0813140e031501c400090752442484 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 328086303 1250 328085053 328085063
    0x70b0f1312050a0f030c08180a05030f03040e06041b03051504020405030303070f05090d0b16050901120c0905060d091101020c060904020903011d15070306180b0a0e100503010e0604 79
    0x240c101e0f000142142c040c20758090003807500c04543c100564480140d030384082e69100c3c90440c200e114807018505024100090300c2c0550140448032181080c3c41c1c0e50317029a000d440c24584d00100091f06540325a4016407038603030505000440030442080260047c44256516010b22070b5120065616042a0080f2001c64030050000c61550b912000101da401285d0321200c010070000700310800d40d9507241c0c3d01010206014180c030051a061651640c052040507483d88801e200050100b05960703a0005181c0c00c013084100000324400400d40d00c00c80d09148140c000540c0183c011400c08484000c5a0024000318031405052039a8110300c001641d84125000003147c0c020b108201d038401e0b604183c1c015000c44540600003040460301c1501e1007500c02c8400d0100e600f55400240039030038400c684880e164022410307060030040503003000c10126a1540100415801c01e4480d040301c4c0090b00c43c984504e0013046110386403800703402d0095186050000310710859200c0d6082000d00c4262600119a05004075400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 328087553 1250 328086303 328086313
    0x703050301180608120405031c0207060503041a07030903030e010608030a0e0d0b010b030f011a1207051b0708070603050f01090b010203070b07050d1a03100e070b0f131205 75
    0x80b801955070718000245004815441c0c642c0002c2603007040048a00200904002ca6200c90400b0f06062402c0078034070710140044800380361102041d03000715610007512135034a00030743ea075616401e01001c038842075840e5045100d0786404010308281c3c1580b000d18620302c659801c2c040b01804569071820b0328018052135030070742c000708120340046009401907030050303901800d080c100307455130f44a031181c3e914268001261440000700b0044000000c28069024100e0400c06514503002c0c0d8141503400d0240b40d0941d000da140c03003c04105d07060300900680d0303107940b002c0055200820501803603070346904084c4120000d901c11860080341a6000e400740341d2040c501c0104100d69070b860003442e0b0001e0084004440e042d404104075000200319502d98491140c08503807982d5a44079030000340e1502712041c01000040400da16034407071041c0e0340c01044d000000c140505000c1100c034607402d03000b810004954084100300300009500040604d528001d00441d420407200d9000d00f40da510405100c4049c0400d00414075042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 328088803 1250 328087553 328087559
    0x108040c1701060801020d0b120304030c0605070c0305060907050103050a0b09151f09080601050f0d0b10080a140105092808040b030103230c130b03100c0f02010608030703050301 78
    0x219081504100307410000200f85140d07540724150032a0b1241900d050016142e00740304000c1d080c50702c5817214025502004624003844c54885031082210350140c04104000003800c03d003070150710304154000c1c54001043c0da0050030200840c42c6c0d91101441036901007414100020507404c2e1602c40c903444418042c01c6c00c40c4a54840f92070400340d42850005650143c00020303c44550390740c5c00c15004040d200c90700e9010b205400c0c011a245042c505034481d900c03e001351421140b141d16650300c01c504443d801100d207070154480300010001400140c101030030510891245034140049a455031041224010003042640c9506000c80e885051000406180e0f07144504400c0d00011107074401d909090142c0c2207141001d44500010b0b08681c002ea10981da075a01050030400c2030031f200303101d44104662070001403190780c0112001c5650304039680c1e00441c04560303481c22400e25071070600007000d441c008000f041050b070303115480251121202c0210b090056107441008101848000110361020340c0545440b030071a86 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 328090053 1250 328088803 328088819
    0x2060a1a031506040912080910060f05011805040e03271f11060c040512010501210507090509060108150402030a060209030f070e060f0108041e0215041d060108040c 72
    0x180140c4600c4d0095603902c0704502195400c0600003425810741c0d2642e1207814184605441d2805160345010039030b18104003041400c19017012070080354000e0030140551100b4403115880324030190301140d00b050414000440303242000c00103015120a01c40230408000d103120016088907801d0201d150404060129001200c1200c1406d81e51081030f440d0100740210741500043c01c003d000e0740d004100310008941480640380c20800d000144e00c4030002002990300d0841c01c80500c0605030380210b00d9210384d850210500005014840c06090300880501141c20495052542d0311000d00c10000d10740030b85408803a807804413a150314000c0e0740083c010000c000c19511008006e44c0710740b807288d501d0701c03400301001003501d0284074a0008005100d5803503c207180c02000c0c4150701c4c500074000742c1000b80c3ea40030030000481d1054a00046503051020540b6004180b010603060342c2904407102540d040401c0000e40940b0896070008030601e107004118564888400649001200390340090007440c41000c1804100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 328091303 1250 328090053 328090093
    0x31b12010e0405030c0703030e04050109140601030c030902041118010f0503040204150302120a060509070f170a0b1003050c010c030c02044a0a0b0103030e060f040602060a1a03 77
    0x80c0181c09980c94072440040c2c0c0351914200d039200b08e022031041c05840b0820710b0b1900c06c0c00e00400c01d08006000010040d0800b0900f01d4004285505140daa6280d084809100b58030600015a000e030080040c0c5102d030322070f447c05400c9285015003065083e42c82041e15403142c14a158088515204c0301c0c03c544481d802c00002c1d1540150741184080f00040000269036407004a60304008500058605444c0c40e0515000b5541c0007800b0280c60b901c0010b0404c20700d520151048110ba40d48280f80b40c800141013035040c00c121100c1c1c0d02400c48980c1800b400050074005071034104a070f100d94115142d1120200042d6142c081c120310103004122015417a601505064020004212884a02002260307042d0550011101c3c4038805c1c428101d00030402d64030301030008112451041c51000204800c20065440d90305144c4140002400c00c05080d5804681d62204815a10016113004c2d20545032a102d2200075a100c004844089000f411301c005540900c2078840020442100074000c0d00840845017027a035220707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 328092553 1250 328091303 328091311
    0x304060209030a02041407030e060c0915090603070f0905010c020d080904090506070903031107290403020303070b090c041109010c02030f010603030e0a0e0106051804150b031b12010e 80
    0xb6009210f11000165158401c0c0290002840250081800e07c000c00800300c44c10040319100941c4040c4c188880e10101e24195910040d04644040d200e003401c1560b8070312400380c500c2d11a04001e011082c0301c011a0401440c8040c03200c0740e40c804610955460044850280382c11000c2e410004e46121440400d400390010000702d00d01800106101e0f402d65038a92900d030041303c05100182d1200f00c00d2040580c84405580080d000c4402001002d09103205400402121812000a404840a01d268010520055400441d00142640c3e110446410318040c072400494070b00c520741c040e10400d048185458412a4289400c1260b0b0071304103642040150b45110700c0e502e003641e040c8903c1007600242d501c01d000b0480a0b520030703a1501842040c0d0428010600c025403ca00091145040113002240c3d102099031505d9012048030003511021b9004640200351404807400482d0400c1c10100d204c0d20484002d5005150305007403001d90380c265044070550381c01b80355800c00300644d0040c0100a4151442400303600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 328093803 1250 328092553 328092559
    0x40b0f0f0118200c010606050306060a08040309170303160f210b120a020f100c1101050412051b03010b0303030606030430020d0309020306040f0606091107060c050406050304060209 79
    0x2445894900c0030b1008115024090855000241e04040613400e0191000030321311030800038150b060010004000307000702d00190041000d035200107418140705000e203000801d07500c02800c25103d03419004a07260362045030f408029a0032201f19802442c440c07100910390049c1542c54007020300d143e02c0c00c1c00040481e02c004040c260b4450b1405801b03540e5140305495554814002803400002d05d10500420359400d941720761082c0171900001440d0383d0811840c4d0002548400040d03440e000590041e100c2e40280e400001082d200c0b52500000c00200103002c04810f0040c2661030500d00ca41300c20903098034161010139070182c00500215201c0e082c2100959041442000c1051001051540740340d0603580541c40c140d480e8030382c90217650002e0303018404494104103d15050041c100c2d80d802181d0707999009080100b050002c8400381003444015802007004d4600b152061101c02545003400d80d06070400441501e00303502d0030808046442c0683d0072501101c207161902c908640d178603140c032002504074548481d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 328095053 1250 328093803 328093811
    0x60607060c110f070e0106090e0f090a120203220f0e0c0903030a080106090e0c03280e07180527010f090f0b13020102031801180608040b0f0f0118 64
    0x80205081c46443d108142c0280104610b82c42c01c04d0789407801e001a8007450900c80440d0b01070040d9031040903d20b5014550b00c0c2c0320710351611210310b4140392498110000d094000e100402404d02540480140200386c820340088503003650402542181a031a0300c200e0b0b00c8800e0800007041904110810940c2c4030400c00d501c14280342411001c641564811647c0304001107000700107001c42a00103c215028000910b240903140c5402ea80c3c140c09444090188181c11030b50b444100c1061041c40e00c100c2e050364810b20300340603c85000103c070b5510700050180c42c210b40346840c040748003108a1300c50544900d0003507400304641401c0300540c0d041c5058a640c203101c25500c460740341001c0d180f80c2c0603042095103d8030041801090505000516000c01750a280c10f01d0b00e8900f0074000750f80c0c00419650b6440d05420b28901c618203a400690300b40d81d14280c0501d00104114000446540014100744200e000f0340441450303030364119080c07000480c1143c4105016200c840103000ea8070b60341405140d14116098001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 328096303 1250 328095053 328095077
    0x206070e19090204150806010c06320714090603060409050a05060f060a0816090f06051e090c0a0c03050306060c031219090203101512060b01020114060607060c 70
    0x41c480d007482e08080b1a0a0f00003030104200c0300340b003800c003034810502e20380360459040200008088072500c9402800603a102c01c59005480c448015000003c00c5c0c0441109205d1003454000110f2102282c208003ca801c0380c00400001c240c800c1166040c0000411051840da07454080100810704504165428444d000d0040c0009200700001c81c007680c03849400c07070326a1602c2030810506000d05c0d0011078103604000c002d4030843c542c0c981800700740c540c07880011071001c06008565000381460b1780050b6201025000540e4403024840d0700950140e015901d8580c0c5070790704403005806100f02101400021884100b10000c00c6c4a51302a6400c508001c00081c60000071032005440e641042c020009100c00e2038042c440f448009401460503136811440034030a414540d00025110100740e208400500c2e100d40303071080c900414002d00304c041c04a00380d0b030447c0d001c1d050401c0d0000b840b0305200580503600e040b400d218202d0200c04514481d8800a00462400c00e055a6080192031200d6448080c440094440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 328097553 1250 328096303 328096339
    0x60a090305030705070f05010e0919230105040b0a03080a11120304110a0e0903160c030507030302060f2206091104050705210c0a110a05030a05040e06040605010206070e 74
    0x5001c811301a4008004040c1840c2c240006500b040d4000f5042c0802e050700b00040d03440b42051030380e100d103018117501da112200c0100c0d50080c1104080311107000f00c80b0017000c00c0d001010040305068550a0700c0820a10000c0c07000e000c101100c901000e040300b00d041c0400380307807940b00304000722004070204191502e0060a5a0141c4560000d440854082c4540240e004960406401d02c0000307180d0f00030441298201030801030388a200b081c809058020f80401c03800c0610815051030001154000c04841d01a956410002d4981d081580c41124660345140840d1003444040c40c0034100d000c540900d218240015a510801090400000ca41500c0000c180340c900c5d90302c0303103d02e03440707844141c54055680c100e00c11861ba07030103c51400d0304c03840300d503407801d1245103860340c010b441c8007010138140020382850101c0c07114500342110302c1c020824403001600300a03039075111010308100d4800004d05031080d12044204419121103008460050380144006058a4880c40304907c210001607d141c0c0000e0741d0200b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 328098803 1250 328097553 328097557
    0x3040b030a020316020a020f0103090c0512030306100906082404050403030c0323011a13060201150503030c0c011404030c120302061803090d08040b13080f070311060a09030503 77
    0x407450045502004001e034250b008450025906071034406041c081c02580d0018200742110302d0140e04050307441d50580100002c8400000c050503004100401c0f204915215a990b50b0040710a24050085142c1c1481c0c00c034010680b13a01604c2258880350000d6a91002c03c20141080c072040725840c07145941d234030030581c03602c0c8502409603000c0d5402081d0034100d807201500361b0b0304a60548014040f0a042180c15141040e406815180d070704201c204c84400c1013800c50300a028801c0110541052414001400c0c2d805610102d009004041c091160030303034075000c154503401040c03c0039685401c008212103240d0301c40d5100607030600410000d181400c0e04c0f616034241607003150b00b1010303400140101c01c400745a01040340d40c0e40181444802c20381260010040c0313840740201c03800180640c940302810310405c21984c0949000d01455241191260074a50544400c40038901ca6410710740a042c2110200d9500450300d00e041e2500018030b4881d201441041c4000e6030320400c0e52504203c00110301100040003800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 328100053 1250 328098803 328098811
    0x30c10150308120108070b07020607080d110301150905060403120315350109080409050703095c03030f070c1a041d1f09061406070203071703040b03 65
    0x2e91007981440d03071041c1b1b4081d60380c1140512540c00c1c4013110043e0764480c1100c00c0998445c102030b4031070000300e0b11131024003046a546060400044000b05284e076a1101c00410041a580d403000019511014411288110700010344088030384141d5074140b0b8000d4024502050052410ba00556510007444408071142507503401580c0c0800440484807410400326090008503c0c0200705800b5680c0d6240402c0c451445009441611303800019001c901070741c040010150410541c0310301d07607280c21100311540709611100303962507182c42c0900d050794201100c60880e0109240c41c0e41c14040d400c079620307070107070400041d19074184001c024210440c100a0b0141020034801c490074400c2c103040c040341c842c64884080800c486510300303010801030710700041001c2d880c605034107608078a19102e40030401802c8951031070040e5540c41d0f07021300084d0202c440d40010200c031440b1003030311004051001044560310505070301a5055220843c18455207144030034295a00340d02c0c03012645420f0f680c4854550030f410480e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 328101303 1250 328100053 328100077
    0x1305040507150f02010f15060819140402030609070501020601120203010905030c06090d05130506070614010e061816050a18080d1b0b0c18040f020304030201060602030c10150308 78
    0x140c01e80c3c000e80c090051050341580706400b8000a40301250000940301a84180410044030801103010340028144c8002c285041590030b00038049013801c1e03140c08030402d0320100d020744204000126101800b0601d4003e84005074041d007080d0340307050210f0100300820141a07a15542e00c564420004000b08000c011910b090800b038195843c00145880c14211401c52400601c0401c025079440d44400c03442103019100e00325005510740d26641403420081000003080e1071490780302000070400f403070041c280074030800c0d08440b1405001e0140d20325080c110015120740800c04521060b0600d0103010b04050882d603913084c9807140c2c28808500c2d028414141c40c0d0b01541f030907080f4a0810085503401a0401822005032200c5800d8101d0380d500d00c00780700f4000b40b0007941c4403008906420101d40c3c0302611401d5500090062240ca001403030f00100075481590224055841e140c000640e80380040166400804898054180b2045101c0450301501a41c101c481780b0400c0fa02000c0300096410000d041500d107c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 328102553 1250 328101303 328101317
    0x80307020c0a090c0801060f0807031505090703050414030f1911151f050d02040c03182307240e060d09050f12040329010b07060b0f130504050715 64
    0x301902a045c6801030704601c041002400b079912803507401c0914190040e926240020ba4007002118004d114445a040a94403000100905c41c04a61581086008034051515041c4100000f008150340b0321610500c203403516010b00245407070390160207201108583c00e013030940d502103c80c088241000004100d070010100032005000e100008141c0314010500401b0381180d17618104030003d2003049284200030f1085444131240003c2e6803184c4c2081e103030000b105070000740c445811700d40148440c0351702444010740c1d4101108200d042c280086d014044456a1078000c1c00c283d42441d02c0b1041040543c081000d00c180c8903604032450b103589005012074048900c000603c2900f40c500507050074511406604558050010406445c0003642210204c0380d01100369401481c002030b00008840c09220602d0040880800020f142c2c4035a00092032594070842c000c228001840c1c08020500c00e10040003a0010030181803880324ad101a401b040d0010f000d9000c40301c08681d5904131000d01c228520540f0005065 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 328103803 1250 328102553 328102571
    0x90608060106270b030403030e060705071a0610050d1413020f04060605092428050304110f01020f0607030f060608010806070f050c0a05030403020901140d080307020c0a09 75
    0x8007840d40705100d0078240140071043d04040e01e03d40b60711114040d44c00c082400101150415029a0100c0c210304100e206481c000d2610f00401351154105070f4040e00c0340e0b404010904264030400b10450300c114002000e200c1040510881250141c00000026100c1035035030b00200c003a4101e00400034810b10400c4801203c092482c03040c4600c003c84480c00500a03410400700740101303500a020b45902c4282a40c4d881d0740e90000440c01d080e02c200220144003240310004a41d0031221404590540b8550044400100070070040000c80b0303640701c12075010385034100d07414843e012450034006200141c941441242c3d41e42c0c10320003065060860964404000c04c0c0d40301e4050b00e80f81840d0190100034001824030440c070f0b40c5091507041c1c655030010140c2c0704024070b140302c90403020b0007030341903525407400f120448442a0341c3d498140d0342c1e68400c2c00b00b64464610701d00002030118119000304400d8002501400403111030b41da8510294001401d410b095014000564410b6181c0d280790700f0080c60710a1001c961490 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 328105053 1250 328103803 328103807
    0x13030c0b010e06040b1c060213170d02070b0a0e040b0a0e0703060f0503010612080309150a020c010f09030e10121103190209030303130f061a1011070b03060604090608060106 76
    0x100c5c940c0c2890041e200340f001c3e11001701004582e200d071035400c1000980d8880d02180003a50030201904540c0c40b24400c102d032114407840001e080001e9403120b0702141c000c10f0f242c140c1714005020703221801c0001060029010010704082c0c01840c84c0010240c0001e1250b0348031131111a0070b0304200d400000088e42c5190801c00d440140a5100040a09400801400e410500f004211040b00e840281450000101050a0450400c05a081da485074408c409244c02c086074000080e5010000c80d03c4250309001c95100040c81601c1460025641a16000d014030f0301a002d2000350200d86411609102500100820001890103000300004200100903520310f0030309150440c2d4040343c031a15441c0c03031042c081e01e030f25504c0000450b0340040448100000304402c0d490080b06132020400d00400d0b850500500c880000442c0c514502d40310300c12208a1420303051610300310791280b09103800d80300c140c4c00040100440d1201c0030046401101c0600003918180c0c0701c0080e8070541d9001d52101c0d234940c0c01000100440d035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 328106303 1250 328105053 328105061
    0x1f02010906060509011a090f060304140106080118150b03030301090b0117010303050f03450c09070f0309060e061902133b060a0b040e13030c0b010e0604 67
    0x1002c2262400810350600b50f40c1c10106c9031707000020300d0580c5c1c006041d00c400c0d50382007038010300208024001c40c0c0e03a03d81440d095100000c18000040150300b460300105142006000348008a22001c10a8002c00030b59166041004070f1811039006203917130354003401e4458805200450181151031400f14042d00b070000010300d41d8003030161282410240e18010320010b588401115a9014010710550300c80c0c5401004c4040315842d0800c0408040c048a814203182c51520b20708042d0802d90401e443c107941504020b143c4a003015031101d81d10840d4500098007160049041980c422003510b4005491200e0ba641c00c400c42c0c83c19100c80c0d07042d9000708100800d80c1954401000648041c240950400718242c0c42020005003078001c50741400c0c142a002e84150b121811407401842d040900e1516824000c81c2080c030351070040d600d8034040c0d07400392004034922039608101c03402c587c03122404491581e6944144d550900d40000300301c1c1044050680c0c00003183e10307100c0e824007910075041c450002c1d0074800c04000441d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 328107553 1250 328106303 328106309
    0x3180305090310140c070201050d09210203070b0606030a06030203071701050117031e0909040f02040c180302101103040b03190603020d03030b01140d090203160819021f0201090606 79
    0xd10308141c1c402c01c40960510b05190041401725005442d44200d10041c0c6613802120302c680c04140c9401d2501060081c0a909202c04507c044640030300c0d10541c540482e1039100300c07075020702402411004a4041e0400d500256402a01618000b404580301d40c0001c0c100200c503840b15000c3d2142c6607020184401c03c2c410580100a00c03031911b071502106540042e117034002c0c101c03c288070185015411a494404208031442100020303d0041c40d807805241c0f0944120f6420000e902640c0780400803510217000d4502e8038041d0303c405652168080c03440d03082044001ea10f88091082040d40103e0b2118031200b00f019001a084027608a0785901d045180010403242030f040e0f560703543d420b1200820150b00c888035003900e43e43e050720b00816100382100040c3d0703a201264144003812900010392600400c45a805512800c0c8203c0a60325842e02d10881c10600c200c40740980c08107900326050340500000c0d03205540e0920740c03018040b1850045003c0700e071008240e00410860250351280c50000070003a96119000103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 328108803 1250 328107553 328107583
    0x20c0f0d0809060c0c0712081c0606230d020c0f06130305070318080f07180509030a270f080d0f14090102070506070c0612020a020319031803050903 65
    0xe5490000041c1c1c2c2d666002130940d100f01030300012117203c84030091000302c0c0684145030700c0521184280c6404c0d00d46900c81c0c1d40c1002801584514410b0000050044000b210410b5840e01040740e403022911450308029102d04120040c20000d0b281446094000392030030052400c003504038050428141401c09400a04031601c1d48440c006820029030060140e64009405103000072601e407016242c1a95249140c100d5809480313207244100000c480010b4031320542d00b4102c0c0f1403c049001c1100001030724016601c100e030030b400501c66255024802c0366031050410b030321310075025001c03465440306603841400d030000010007078a0361080c80b0b008800c0048034402402403805050a00e030f400e00c0244600c0064090301081d010024002100e80e2007001340c0c501510340100215900c8030342d0b1178641d0010b42c051060130042034004a0641c1c0600c1c85100b0f0b100840100e801962408645607910031242008100d20030516a5440e100d200d204100c00013120030920a0700d8569540c1d4400d0200340c03900341900d0071111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 328110053 1250 328108803 328108817
    0x302040e0907050d030f0c050601350307060b0604030f0510050f0402030717030906030a200a02030d1e020d0f1d1b010201020c030a0e1c0b0f0a060504020c0f0d 70
    0x100c540c07075032a00100d1017505803600c400d44003070413001219819042400030780141b00d1500045469900d80075200c4000c4051358000c120100000600c3c40c085a12545240c0079403c00e2042f4030208506402c04d00c03c821008010710f00d455104e0b035a0b0305048442907401e0328150b1104440240c20405403041681045580e14803240c0d5140036400683d03940007a005a90099030401034000e41d0210810075209012001001c0c0d1781c80c4c2c5044410725004007540c0c0c154414240061640311030b507026400441d48403010030f5000c3c51030212600d881300090005031a03420b1980e101f4101e01c1301810750703d1000e0314607090403010204804036601c88420a85143c40c8086c400b01400199421012030b00180c031001249084685200d88240800140d0081c080e66021007944c0c00002190154940d2240d440200018129592050780d10903621800500c20100401030282d0885804079001118585000d98000e400300404900aa01e0300c010905030303000624009107a6002a650010918090041001da10803600c0d00d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 328111303 1250 328110053 328110059
    0x15060903020d2010050909010e07050304060b21030304170c031c020c060709030302240604021b01110a090e0f04080a0203040f1706090105101401020712030302040e0907 74
    0x205454440360000b8071201104108409440300c84040162844000b4084d004124900f04003800903405840101e200e0074a80c000401c0c403505120000740943c200b80c0c1c64904507599503540741c00030b044422260b03900500c0d1114114030802210304036090614110090f50316810503180012140040444403600a1001d2154200c000e0b4000103485c1e64503000306045415441c1c4d080340100034410704041e10042c0c094101004041c82c1c200e144401100d110b5801c4603413104d10f09921014001601200d94140800d002c007043e03207841e040c0c0103060312007003101015014041c0200c4403401c482e50225507051445002c2018821a600004010000c240c80224070105183c184001450716000a100800741000441d01c024024803c006490141c40100c0400d44c0068880541004c2c4218942e2000305901c01d43d00013941046042c0101c500601e02540425555800d081001c0205068040701504600c1160710008400c00c10006c0211000d000c1d0300d00603a11410b2005a00807014010301c02d0000c4d41c0020410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 328112553 1250 328111303 328111309
    0x30a081c0b060a03020906250302070b0a0806010309080d050906090f0313120c030602070308010e1f06080a110d06050102071a180a080d120b15071403040b0d1506090302 74
    0x5842c3c541542c900183e03900c4a4200203901c3d03024545800d00002c52101c1300c04006030700e100d607500c0098029002c5810003907607045e02208507c40c290700940000e1035200806c010354001e03001402c0d8188580301c440e0034848036000711400c581040310042840e0703103c081440801e09082c82450000c0d0902401703103290071050088a441c400507446414038808808881505203c403006030300d0050f40d0f1100081d96100314038200200014002e001d401c3c140707190748020480390b06000c82c03e00080c5180c0903611700003a01d000004c2e00c1100004018040f5280c8461046c40da0100380c0c4010501c0c600b04010010340282454002898040c07240c01c22080300b1501c43c8407103918401034080d640f0721810560030310b010a002e10045055655554080720080c80344442200101e9000b20130f2804150140d03404200c4038100ca802c00440318a4042c01d030694000401141d804985002c01c07a000c0050590100c03403910b552511b0403051680012002d030342c040c0e1781e000347e50b90341c208550401d03005180074a0144800d900b16000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 328113803 1250 328112553 328112557
    0x10903031107051b150703181706041515060918050919060612030e011d0105090409050102070512030906070f050d0e0708010c091410080c0711030a081c0b06 69
    0x142c030081184409548130382d036807001c03119485d100080c4002600e4030710516001d072801100d1002c00d0035034543d500020400003031596500301e000446c04000c1989072a5034031580c10107113a0a0303050700019200c000c40301010484502030b400a01c0555200803215241c0506c0491420082035007100341d0b0305020600900030000104011a001c0d1100035620391802d0713150800040c0410b40c410b040380c0c0310f40c0d2135072002d168011000801e0f01c0310a8a81101d10390301000700c4e0641001c407545981c0031500a1100c104603003055070103000418400d0000602d0200d1507101d041c90464100c603500790020f0000304004120f00240101c0d5004010f90402e0407425640301d0001c3c03c14002c01403a6299280d44600b445e400030300411044006103101d00c0200005541c0600c01402003c16001e00010603010840782c4c0e201d030a04140b05041000240d4400c511a100d0320180d2589130300c031040a50315814082101301d101e59040c0085001903106022a0b80c1e5564444100041480740c24440318004e0b160450141c0309407a1401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 328115053 1250 328113803 328113823
    0x913020111030702040603080405010f030e03220f03080c0f010509060115031d0601050f0f03100203131707020a090c02061810050c090a0b030c300901090303110705 72
    0x1c190188030039056600d8514081c05030043c2d841030410400000b0701000d400200169034007a61071098240d40d400064041e1441c003112820b283e44100000c8282040501c0b490000b0f000c0c010700c1d0501030303548400c248140e0055400a44aa07a80084d0840950104010f61244064640000d10544c5005200b560301e0300700501c42d6141a5245800340c1070454420780c07211402012448803421101c83c40d012581e90f0710024041d00c0e014042c0511801010720707200707a0710120710600a0080a1009080240801a4101a151040181c42c1d080040e0014002610707001203941391104440c3c40350098010001c080d1000d03800500203e140030901c005032a070100e4516440380c0e400c51a5802d0708902001e10b4074000c62000702d81170240c03a11092090b41751a0000415420108917103c1c5680c1f0344a40c0042c900d448103403110711201748100148005c1e00b801244c0d4030307060182e2881503c0c0580b080d03107442088040440e68410103954034194901015018814429020301e01052541800c0c200e6640030b0ba103010300c1d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 328116303 1250 328115053 328115057
    0x103020d080c010e0703020102120f040b0a110a030203030a1b020c01030b03192109050a1202040204050405010303031b031e0b0a0b0a020d0e030a12050d110c07090b09130201 76
    0x4100d52040c01041d00803250442901e00082001913410b14a032619100301d0700049005008081105130810404010344481c1c12806400c2c51415207407990742c1c0b46a40c010343d04041800504072408648040034003e40d000507020f50051652840d101600c04103c1e8102130302c550030340300002660b03200c86074006075200c0c40d140c003800d0009005401d180001d01d0800034401003616034031902140130030003c0608040002c031400c0c14001e400b0a180c12403d4a81340a80e00400f40c02c000c03900c0c0d040298401020740410202d001410052405071140081015104240c206902098607010903c07451075101d070702440310713000340d150401001880d9041025105100d8021000e050b444500003030680d40e03840580ca00903c40d40b21483d41d15000408040d440d0701c2140303031000c00710700d0042d035884650030007141c06540d55610240410507529001c109030b980b0380000448000903175841c0c180d06c02c0c0d421008001e1180303844840080141c146810108829600e0090519010307081ca074003405142c00c1c0c01c071600f6451076824 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 328117553 1250 328116303 328116319
    0x61b030c0206090d060501171204080a0308070c15020a020d080603060118110a0c02010206070e060f030901020c07080705040e030913090f06020304080d05010b0a090306020307091a040504051e010302 87
    0x7000010741020b0790b4950240c17105160100000340040550020000b1a081400b6560300c112010300d10102c43c0074a1103281055009088088001b0340710303401c042da02501c00d04028069414984400c050750700201c1c1d4100600342d000840c80d0f54142c0411281c10b152540f40f50544107881c1c5080400d0311000103114400e50003154914001c214141900224061050240034503106c00c981c8100809450780c80c401640035005400c0441c040c14401d640039115820060034441c905003141d407010041e0b030310040030045a0b5600380a140070000080c800b00e0300900e101c000801c4600d090404000481d811005075000701e603c208988212138680710741007006e0b03400d02c46000482031179070b0030b1540c150101c580004100f103200104001c00c00c001403016200d5015260010010740c0e8a418405e50302d40f0a5021450100d034554004200141540c0c0045501c00c2552401d52038172560b030b04101c50340407107071901c02d81d07208004a400d01883c2400d100e500c1d480700c04182e8840c0e000440a040c03185d01113040c00081c2c099400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 328118803 1250 328117553 328117567
    0x7022404140135090a0f0501020702150c120d0204051f03050108010e06060d0303060e0a02130911030f060a08070927030f2f1c021b0103240e01061b030c0206 69
    0x30a22010306041d0304004c1b100c00c0b4842a1401078002d5001002c1240710395140c019551401303400c9002d80b4000120540207120543c007400c0a512660000c9440a10b043d40800c03000c6259102d103142c00048000c94044c5c549595803c610250907104140c000c060242c1c500082c06c10f40c440300007222500014240c0d24880e41608a04085001d003031241c00c10202d01110300e05000d00c8488541c01070000310022542a8100b54480c507400d4140e41081e403030100302e10000d10108101001c040845500650020101d5107850b0359a0f551905100c050b90042c09060b503034000007646c038800e0f141d81000120500c2c561426600d01960050403180300d601e03003002040316503424002d45181c01d007140d2100341c0d52001844003180048490301e40d91810702c01190f00303011802d0540b00a260001510140c0b0b0b04640300240142900080110010006c0c0d01102c3c606d074100b80b804c03428550980f4040c801070611841b607449198149800074040803100c080c001000e000c521520030109a0180f45503001541c1101d0a03551904 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 328120053 1250 328118803 328118821
    0x1d040c0e0330032706091903080a05090f0712020909010606050307140904060b0705010b09040309090c090e070225060f0305090a02150405031006080307022404140135 73
    0x70440110002c06441302c0e0030503290000d0320301c0c421030481003101c03a5103d20450070306d0050f0032044014007062050010950361080da270013a036413019061080f80d00211510503404e00d03164941c0e0041c07106030a0040103802b50300b000302c074059000041400902844e440c1c100c2c01003041c40010f10b5901000100c050280b00c00900d03104031180d0010040082c0009078840108a400c0d074029a01100ca039803078900c04030080d041203940288516019100c03084e80300c3c40c002c58900680508200c1104004100038041516000c0341072403405070304582d00420042051040103007031109d810403041ca400354446810010907903c0381c1c035101048114500030a00d170700c1752403245d850b000d09204001d500100e5850003015114400020700300312142102140c40c008840e4011800b100c445006031801500200f00390805820018a605120300c00041000ca020800100400494002e504200b0303d0700c103810265640c66078410f0740241e041d00c0d205140f141080c1c41c07461307051804c142040035402d904040b10025110300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 328121303 1250 328120053 328120081
    0x30102090d060e0a1407050414061f020a0503120f07051c0c0e060d1407030e070e1f12050606010305060303030a15050a06031d0c09071d040c0e033003 66
    0xb580c03000d4014280310170000607a440c0d03c1e541c003945010700d1800340707a2000724184185443c040c0201824403420380c1c070383d00070b41304203041c1025248041d4803840e0300400020340200b0040ca0b41ca026840700e074500d4101110780072700299029040d40104141800740e00c09203200050f0440c072000c1c03040c000040c04000d4410560761340c81c1080d415640100003050304110139502c1e80109014140b560000d2101d0350340c03918180c1c101c0d06280300c8051079034000300c41030102c582c441010039005603011007848021144002103588014445c2c2204010944000b65041084810081c0f250010307001d0805120314074160000c030703649000042400d504262200c5091040d0000202443c02070000988814501919030380041c000e40b02c040b040c5c01000c05113540000c103480001c2107801126400400c08401902c6070081143c0314a0601c5080300c61640032084203645684511132126110741c9601c42403900300c2403004160801a55400f0100ea035414a0b070118080307002481c60b54098010007a8a640f00c2d2a041c0074100d0075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 328122553 1250 328121303 328121323
    0xa0501020c1503090a0c060c03080109061d0c0f0307090e0a020a0516030c14070e010f05211606030504060c140301120807081b300a020f06010e0601030b030102090d060e 74
    0xc86c666240410003c1d403041121912502a0719400090b980c1d580144080b00e41910842a020307840c4c039181c00300354080c111031a8000b0130025130142052030300304580f8455401600d2103400f04031700b04800c2002c0914910301c164000381031201141828969600a0903e101710b090b1400f0b03800e0510050010180101100308055030064030703600d000c6514035481f642d02c81c0103009100c40101d81d80c0001a80d40c800ea501c1d0f20035504090813a007910918420b911201c244042107a019501500c0c0c008950516042c0c06500148441d5030302040504280c02d00d90211100d02c0c400c0001c01405003056009000070ae41140c0c1120480280c400d0a01002e08140c040c0d0301422900501200700060300704c2c441c0c94080c00aa070840644020b03624140644020112811301d00000e03419410101c40c0c02c01008281000a04421940d500540c3c4000104180d103c2c00c1403c260031000d4050800006d11682d5645403181c480f00e500260b000314a030512070302c00100082d01442e4001c00d041d031205035009034600c00744004010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 328123803 1250 328122553 328122563
    0x4020f0303120a0605031207021e0307170102070c0b072103020f03040b180303040f0b04020d05032101050406080304050f0609030f070312030516080405070b13050a0501020c1503090a 80
    0x340e00380790f508074016103014450315109206d508600c1400c9203c4204a0303004940c000c020001040000c01c1030110b0080c1320007000d50500440760001003450810b0b00c0100d194155100059643c005443c3c03240344104c181d005001126024005040001d903100d0400d010701500b030006e01004400800201e01038411059001002031007c400d12081141c1050300e5405503502d2001c418a08003c000025602e00044602600141c40004400003007103425070f1041c0c01a0024110080751100d0f500d039240380d0b42c4990141c1c0c4a516030540d0350540001c01d01184c5001d00b07030807141480250716100320241d40b40154041c09121b0f100703c503040c05080d0b0398442160f01c095000f5040d0341c54003452084058a23403200d84020785d0000c07402140c85c581c0d41d10030b10410384240716106451010a103400422143c20f0b074002c1c412159441018404502c0c4280700300076000c9045c0741809400100d0610041c4910a855030f0701450565204000e2160a035440c03410101e48000c248000e107032a41c1e83c040e041441c204004001403e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 328125053 1250 328123803 328123837
    0x7021905100e030d0e060712050606090619090f0f140d1a01060305060604050d030e2d01021009120c05030904091a2503020f0403051b031e030304020f0303 68
    0x2850b070001001400e4640000b070400c00507070108000494031a1811a0800000313101c5240301d0100002c0c951003281c0124000e402641410500780206840d5031010029240d440c12a8601d0400c09512529040c081c114190318940268034102a8012407130607400b40c3d00304862111104d04041d240c00444002c141d030008006012504080300c0c140105d80c0030f01820700041d091000040150804c10202c0302212400f8083c180303030880f60340b804c440301102c5520b4968405442980b8000010708200d90303410b810481c18016075200e03032100001e45450b0803221210fa00c1070901c0801004581085945004403280d410701d90100304052a216086100e28a02c20b40d1143c81c1600800a1002c0054034605054071101c8003c17294480e030450110400c40040304255a101c00e0705403501e00e6100f600901b80712403088880600b030a80726a60396040c00c0ec864081504080600400200383c601000000504061070141d610003400311455151240b000401c068000c40c603040b40d01400c1e171410000c9406048002b92014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 328126303 1250 328125053 328125071
    0x3090409051f090302060a0218150d050a020c0d020a0c0311030f0f0c040c0302070f02060901122a081003080702150d090203010c2c0a0b03070206040c0e0702190510 72
    0x42e00605030201c040d80144078840c001894042a8800c4801e00f1040640012412282c001042904441c11071500300b101c00c2802880b0750b0b00000d024140c01784640d0440540c4448025202c40d141113203041e440000c550042002d9408907042140755401ea03500582d106000329191000b003407a21110001c03140c030318880c0d00c0108c0c445010102c1c01c0c5035003441c11a0207020b011100ea204501342e019003800584212640c1100c03400601d000c00003441c003204181000400c40c240c0140f07690885075410640031901006500c144c2e280400e078102c10101100d9410810418240500f0501c0c0c4010703580001820f0030b0700003c0000070742d9110304a04040324902c0c50141d0707503588920403d901a00909a00b24003942c01c10075080507603030045042c1c2030f01c43c42220b9400002000c0a000c4049520190202c9800c034010203008151022000000c503c210f85503001001103007801e20b021501000c583d030141040b140a030003030143e0305030702242028400035100303512086a11142007050800e0000705a12071941d140070118 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 328127553 1250 328126303 328126363
    0x312040b0f1c0c020c0d0b070e0301200c070501051603080a0b060301060c020a05101205040f05030c03070c0503030403020d06020c07080d0905120f03191713020415080309040905 78
    0x24980050355003034464082c100024006c010442035002000802100002032045100d61040b900b0700074000d0010540343d4000340b005003482042c481140b00a0703400202400004010801c2c0390082c1001c1c6032642c5003040d01319503a00546082600202000804000304082548035002001c0e031280c020041d43d60303543c2d203c00240103400c40160890150701c109000040f149026031456298042c00e131140c08038000c03014004801410000c104880100b4900520b002190003000034151410002d001140e86403118180059400b45a51041c2d20a80c410401440140c0700c00d02c40d04802c40e0b01030800760b04d800c03050a00d070b801d024003904680040d2196040c41c2243c9a40049c07044101d0354140d445054030b10080c025142c4541941001c43c48607841082200b101c0410300450729183c0440b40350515503100f03a0540e0350554035064420440b107890500c0c43c0d001703501d03041c81801c03821841c21200c03c003441d2401a8141c1c890244003071003480f0316503d04500080c070006000590036001c0d001912003000c910810a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 328128803 1250 328127553 328127561
    0xf0f0f0405030d020d0905210a0803010f0f0602030f0a0c050f0601180501150c03090f0902030114040506010e0103050c0c0a06050f01060206010b0306151213020f0312040b0f1c 77
    0x41c0d64480c0c450541c840b2900340c0007017544090311440d5038641c4000d46c01d1505100c100d51f092860900386c01c50002d20201443d505005120109200e1261113a60b9490107040403821030f03844e080340100e0291943c04000c107540001c101d070302d801d01c0f4100302611100c084000361441100030350b010b02a4010070911a290b5080810342c2070584000c904206504070525003420b007107034808d0041c2c1d82c5a4502031002034811340101c4419540ba4480d24102417a01d840b00c48401e42e00202d54070400805401000502c11800440c8858020880a0307500708460710380b10300000e090b8505020040c0c140740d039401c08181d0b40303500740e01281c03a2418039400b220490005460a4401131001b01c920500d0a00c4a000100d100c92000c5000d50481d400a101d030f40c1581c036160b0802505070780d050001e00c80894100300c500f80d0740c0b00303510f5194400e8001440ea04410015030043c010300b01c031500c1c2d0310751003a0400021410300e403c0c60700c15178095502259100b504c5000c0c3d0500d02c0040d220358a6411b41421070320300240c107240f4140d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 328130053 1250 328128803 328128809
    0x3080c04230301200904020f0912070e0c0f0306090603010f0c020a111f03050a060e040f060606050c0a0f060f05042604060c080a031d0a050606030601030c03080f0f0f04 74
    0x2c00038240306595000d2035049592a070101d8a5003040b418801b40b4150b00904001c1c900c01c129180703000740010008202540f100d482c0300060f00845010098117004191055000d10741a0040340f0340300588900000034803006007054425a400c00104030f06440c250300603c000002020200706044032102c01960714090b000c01217801210380c00c0a150241410041c84200309001260b400016050700c00030b50140030300510f8500d126a44000001d42e488815059034001c50080004295010403030404c48103407001d40d084481840007c01800412100001d104010180c1009141c43c11500514007a0007400350300101500d000e040c08180018030050415413041290401c1c01d044244a540354004000d0050b803249001081070348d4182c40c08115000003c00c08031a20380781c00140c030140c410f07980c000d1401e05800b12459038021030400c0708201d400c00c40c0c150031800c103d0081c001985103035240e5100c24600d000052080d50040350b8070048440280c19694841e0340c1c4040d0b2a1281c3e442108500a500244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 328131303 1250 328130053 328130059
    0xa05011107091d06091908070f0c060c05010506090403081801091205040f06020a05030405130e07060513050a0f0623040603090309090b211002070804061103130303080c0423 76
    0x9004180700c1e01000072801b03e030f0561400712804003421038072000215000601e003582c0c980000c20407403001480c80a003520250030300d5192a0f564402c9403c200f03003102c10051645000c1c1720964207200200c3d8100d06565481300014504010388805108124094000220004e00d455000c0d01d030151b10b103802030050010b40c0c0f10b0f403c4240360f2503610b00d030880e07490b02c20b03d20140903078000300b00902190502a04101c5a021880fa0215003130001020840c50904035030b0000d00080d10108210601c105400b05510040a0403078070a0011820204450341905030b920814050102e114510100418184518080010b100000d203403140d5403000050040c000c040f004a00040c88042c0c0465820107901c0f820080d2030001e06440036034481c180d0700100040807424a50060710441940d40a00141c03400107084561250300380729281c614107072014110713030700381624000d00d50014001001145c8950b0700d04d6080b26010b140602564807000d6074009144217680000c564214030b0306150640036080e62806c00309070016 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 328132553 1250 328131303 328131313
    0x50a140f0f1b04050303070f0201090902040b19090e01031104050711030316090504020706090c0605030403021c090f0e07080108010c020d0c0c0e0405150f04020a05011107091d 77
    0x5009262884100c1d07030100681d5840010400444481c0b001c2c1a10280c10440349162684520010740395812180085a007048071458400455a102041c00d00034009403c1c1541420706100c0071401a0249010b9841e600010120051280d407140711008003e005080d46603c0315612400c2460f03285c1104001e182c051818840890750705031003803404000c003031040d502450858680071400820200c5400d03a420803c81060004620fa44e550f100400c51588508000544461030340380c0030310f040406604c4901403003410f004207c0847d402241c0c404034120800205c106107a05c0d00b4007500c040c00c00e600481c0c1200004c00c008100c5000d220402c60040c07541741c54a5080340ea9410141d03003600c9642e80c851005810800c103400d10240200e00b0440c444d8455441000341c0f645441d01900c42540c00c8509882079880801404802003401003103542007503003110a8030031454150049004000c0a1103034038104803030082d512001c96001d002c2d0700b002c1e0403060f4041c010000c1c407821400210001c43c5d400704140c050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 328133803 1250 328132553 328132561
    0xc0e0603071a09010c050d030c110d02070b070804090903050a031a10051c020708040608010f0b120a0f0507080108150f04060c050d0609050f010b090d1401090501050a14 74
    0x44520444020b14145603800500a0b00b201081d0040b59071641072000300038140c4000740c821b10590700c601c5a995000104811444402880c1c1c4440100c254241e4212110070b005043c1d02040240079078101e0000307555115494940664130307118541c810500c5614040a01c000c0561044c001c1003000c07680c0c1e9062028041038041c001d61030702001d1711298040400b00da4042031900450107041603040d58a62403800072400c42190f016680003440444141c1000a001d103c43ea07004190a4003528040000d84881e03820001003060502c0b84450f1448041040c80018940c1c150541124650502c0c00800780903d050442c0094a0fa0b202030103280d00c1d600440501c417640680070349089204a00a04c402883c6803a2902c40e9002001d00300040c104100341009041b106943d1402168001e14001100098074034242a2102d20b40f031042e001a00401e40422501d03009585070140520707800e23001618451007150f1a23210394010064407034010495400c01003046001400303076000d0040030210a00210355996 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 328135053 1250 328133803 328133809
    0x1710020c0106050114190305180115030201090b2d0c0318031e06040f1106030c03070f030515010f0e0d08030405010b010810030f03051605010b2803020906040f0204030c0e06 76
    0xd0b03d88402000c0b00d04141d05240d561083d0006a0841c102627a800d001500c2152102d094890360068030241d080210000c008550344007181c94014002528403c1c204403058000c520003070072008100c904a569500442a080c80c603408440303415001c2c4007220380d12a1a6807010750800f000d029403a21a015512410078441c41000f9032107c2c00c01040003606203030350381c0c0e500c0d40440500d624003030306c4648807101142c00b1501c3c2e050041d4000c051a4071244e840f4a400038004080c450341d1100c1e14101420141404407005000c0d01054441009007800300d007121604004071b600441090b82243d220100c034032400180041c1070011801540203200030b114246406006450310601502d18038007990303140c402000810b6003055409042c03486440c10b10b1402613400c50300d54694241d40b2064132603955540228260b442c190a665100d005071038405010300803d645150403038021440060b00810301080014011740d100d074840319025911210841d110340e142d0070105410300301381c0550395800a4601c00f2448501d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 328136303 1250 328135053 328135057
    0x232a0109090b01050405210604140c01020c0105032a041e080a08091002070b0f0a0810080d0f030b1309021005030105060301090f0905100c02190c1710020c0106050114 73
    0x8041a102c0350301d0a868241400b001d026400c0e0b0410740e406503440d1f1456440002c2c0100d901641c05008940c4200507c071040e14149160714540c030b410340d4001c400305840e90340c1000a40303500107503039842c3c00060080006d00b81c0081c000e42e01603500f2a680001c0100d080000120525011000040c1d0b8403031850b101e00d8480d95401e2064800f400709042400540090300e000e40c0c041c480900c0a1068800c2a541c0e1059511907803c080e5162034400d5000c06e007514200d51041c8126030080c04079003d45000d500d80038085031907052301d12201041081d5100301c07050982c0213030040000b0841c00752a10b04400741030001500100345981040744901c0700800d0010001c0c0c802d0040e6410707901300501d990300c0c6d0f929100700c00c2c00405480d512020b01c3c40d294103200020817814440d02560800c00900841c4981480380000e0501880940b45841118109202130101e0300403140d560a03505c008140507001c640d4103075128a8509030014101c0b00e01d000248003103070b0420641140307084a40a0701d0b00c0c01080d246e00403565042c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 328137553 1250 328136303 328136321
    0x70603150e04110303040801020a1e02011a040c170f1501050c0706210504050d09050103090c0311061605070f05011d01120204080a031713232a010909 66
    0x394028000c5070102c2c140030103020b09400c004080300e00d001da0f07c48010342a03820620103540400d5041000c0341c2c400c10103680341e0038945a031344000c0020300d212072000310320340010b50110703400756a40311350350000607005840c03803182180c5c44916403000785400826999181d00c01caa8500c402c4000c0c05d0200d0340755010b0001e41c2d83d250b00840143c001c075401c01c6021100f8140d205000031814508010113015880f03c0c0c4038082c0a81c4c0511702800c03a01d004030201508860490b881241003500e010034038000305099081c0c2a083d242e00115000300708800e000000d003180982006c0c0c0c031441d0681032a440801000248403c01c40c1c00340c0110160041c1e66200640701a00c0d10420314104000e0042e81150541c4610424442181001d600504080d10b82c020585400300c10300044010403028004030f90004481d030999a030220080030100c41b00a81680c46d10000b0801d50001e201d0a081811070318001281030000702414502034030368a40310702da51310360303964200380340c0340c0a60116840032400b00c0c0d00b4116004100403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 328138803 1250 328137553 328137569
    0x2180d080a080903120901020703030c09050d0b09010b0301020309070f0e0f0403030e0a08160203060c03090c12100213030213060f150e0a120218060904030f12090507060315 76
    0x18241d080c0d409840c1540010406501408100051500e0300d085410080c007030f0f00d1507400181c0f5214586005401c59040d46003140030311507101d4081100f076880c407058400c10f070b6000002c00c040d0b0720703442c00715409000416041c81d4107500200812080702000148282228807455480c02e03602d64800c980020001c060b03c25032029140d038000200824043e03040401c404c10108125002950140c49030319103a085100302040c100d40c04500e800661138100006030708503030070005140ca1410003980e2580d41e808030031105405141c02c00e01810f58400305001010307074070080391000d41d030342c0c0c120102124458101b80001c078400c0b440d42c090000c0e001541e1181c24240d8110b5080c40c103d00303003040440e81000003614444010001001c0f100384140c0c407000c00d407100415030001c0f4180c2c0c2032030720310421510b58909401c5840203a007400800c20f00356500c4800580158050030000c00c03036603038404100c070304a0481360400c0803030381001d440c00e08005000510200312011b683d010003604041003208003c01600d80700f801c01c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 328140053 1250 328138803 328138807
    0x100804050c010c020d05061611060903040e19020f03040c140a05281509051e010f09030f03080f0c070230060a0f0c0504030302100b03030d02040902180d08 68
    0x960355004031903000d445130004150203246880c070b55546180a1086812860180010f20900b52a50b0014280d10f19401c1c2000030307003039500d03289441507035038025407140301403904041d03000c40c008503007604c983c2e500c140181c201599500071000d103907640e0b030b4002d032001c40300b040c82e41701c001501d40c101c44500b00907081e0060811400c0e81ca07100410506100ac0d04007820103d00c07051451001d600d20030580fa0040881d80c40710317000d43ca110480a03000070300b0382d0b10407070281074080c00c00240da00c959800428000400d007005949184024001c5810b0103503900000c00341c41c00300190300f06044e002881b607441804064600c940641d2192602000f60240c03040082d000807032400b00c0200c80009101000c240c6041000d00011151070181c6a031401e00162030711200c6a9854150400003500d6000b0050500d80300d0034041d00d8140b550341c000359100c48000100c40d00d2503480005003146c0d581072045030110031a000003551140d44819100c80203600c40300d8500300d0400084020405424072030300e030304941500840401c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 328141303 1250 328140053 328140073
    0x30711030705180a050402131806050f0606071403070606030305030604060b0f0904020708160b16030c0f0c05160f050906040603020307171005011424030601110708120910080405 78
    0x1201a040161003280d016200b00140b000c2e00e68207100341c0382074a807240704005c9c0b1400d090030a0000c50780040e00c15140c42c9840d40c00c11125807100e108031103080f40c0c4101c103209171510040d42d00b0700754010000c004044a04103900007061503440005180908400c58040008507915010034002e407007400407254500701d081c000e1840074546540078110042c05000102d19000c050300d4020300100e01350340121201200002440051003181858120300e090300d06081040191a4201401ca040011424810040410840810444188007000304004140200ca44940d1a06081c20140065010b114041c80d0340d40c0006802e480d081c011070003265009000b808455040c21400020954941e9003881d480c49250440e0320780c1803440c843e550007407000c0401c99a20101d9002049201031318003128804045540301018480031078101202c0d000b02090914101490410708164109111948009114041e11102e4100380f180c0c00010000002c003107510407070010064109491504040c5e44c060200d40c0144900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 328142553 1250 328141303 328141321
    0x70b0a1a030d0c02040f02030f18060613050601022103010612020403080906030c0c07060306050f100207210b01090f0c0203250809042a0905032104050303071103070518 74
    0x21801060004c3c3c00460b1204111480209030383c000d03600d60300c20b8002e010411800c4009880c0a180104c4c2b01c00107020541400b000046008456030380c11800a6602d4001c195240e008101340c2001c2045400110a409044a15415507030000d00c02c5502207600415080c03980303201842240d09496003c0046418102c1c408280131140d040240b03030040007401082510007041e800c11140c0d00a10140d039001c10154141000e0006001c03a800d02030340180100c0302078102c12600400d42e00c003a41c0c14212486c442491040c103400350748088410180031a41c0442c00410400d015030040e40e858000440113010f40048507100309c0e940e100324140402000d846d00c1d2031030010f0150034110b1240e640036003030b01401c08135001c002404841c150003034000909141c9142014400c1c04906400042d07600e424004840303480c00c40460b032074211240c81d150395205c0141300d804807176a801068a01814020b42140d031101101e28010f0189070f866115244270340b085000018052502c28407842c014543c2c004040e080c1d89800707840d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 328143803 1250 328142553 328142567
    0x110a0803010b0d060b0c01020c0d0c2006090409050f06010605031e040501090c060509130209030c061b1c090b2a0c041104180204030803070c17070b0a1a030d 69
    0x264040050304c503c40090300c21508005484907410140005a541c900032506501c0e00007241e0316181807044c42001c50000c246460b880d240030090105001c0712920040001030424070501010070360007464003810300700b805000100302c40105402c108481042e621603105807000d01045807103c0700642c1503a40b403c1d0402e0b01d0341016820078841c030300118000e02c09030f5400e9800051134014800203103010030700802c2440d004041c0303142c0c40138000b8114900b0310010007282d22200b01c0d548150080d6000102c00840010112003507c241c80d010702907504102e03400b41409248400c415105000407184400400c6611041e4100c41e01d01100c030005000b0311080390300d41031071500300303c05811140c020441c40d040c66458501496a038408040101ca40c5d43c0d041c0601c5041040c51684114856403050006000040825049a07003109072401e054120605500d050003010303c00f07290580180700045050b02c100b040180c155030046007400000c0c0314140c00798100c4520500298141a89031784807580e0035070340f1802859 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 328145053 1250 328143803 328143817
    0x319050a1b1809050c03070e0f1f120606030c120b010918090507060e0a09060f0b0c0a0f082a06070513051c05010b030a0c03061e0e0d110a0803010b 65
    0x14002c003081d50390710403074084039011900414800343c00400c001405a00030070301c5d06040700c12202e12502c1c520800119424045403666104894158002c44200794061190005440d01c125001e0150b00c1c1c8802000f4081c0880021400c04540c0c1400c448060304401d0107a428500e5069589000780c52a00d1440d0302d01407107034401070a80703903595401701010540030300404c1e01400c9180c45012080c505002400b0956130190701084c3d03420b103808402d01c540040040d40c50115100414030549400310b0002c064280740d1040f40080056120210140800c08500c01801e0402401c06141c2c1c3e4510180b2241c141d001008000d41c4840d4101800003183c89005102400e41e018120310f000c51050380359404503c070032401c0d001c0414100707104007041d4100301c024001d500c5448801e42c003501c61804a81e40b02401e020f070078000108500d49a609000c5950028503c5c204101800101070020140340a0305907203403140d404070200000da0203a01c0c25003115002540b400b4042c0d0203241c42c1e241d40c4ca040306200e03158004003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 328146303 1250 328145053 328145087
    0x6090c0901030c05090d0b0412021b0d020604080d081504060803090103050a020c2d21070305090a2d080d0806030703050d110706030b0a03080304170319050a1b 70
    0x8064410355072686c3c41a0903050384524070308a01070400d030501d049000b40000071081194418947c86039550440c42000039590800d41d410440c890b102d00c005411401241c11185e03031441100742c543d940903404102c40b801100d086003482000003002d0b06000680741c2e1406030801d141e000700480342c140d520076405189d028001d8100107050103051810b0506202507151004841c0084a503d504800c0ca40c04e181003140317800c18001c6c400041c030340d1824003580d800400b03501109407011070a0018580614202c440c004001403c903002151030365840d80440460602900403c4040c01070b507100301410142c42800d0f5081c0b60300609960b0702031300e8100d036040c40007000d40d40c06026189002000607410044400c10542c43d448585018175940d800c00c3c90094194030000c10507080039408001c40d02e41c0d848107420381e40c104c04940e82d29600c5007000c0d240d61403034042900e045000041000711440308070303107051003041200d44140a95141e460040050390300103d103510f2038100c0888411032060050202d65038200002d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 328147553 1250 328146303 328146307
    0xf060301180e010606020102091e0a030b100305100219090e060f0a05150c0609010921021905011508160b0310120f121806030e01021e0703030506090c0901030c05 71
    0xb0340310a0030344402d5403103400581c0d0042455040340c0307401c02c42c01c29100b03810020700d0090380c0f1102c0006c0610404c1e02c005420508800c001c20b00e0302e64000400005950000110703005002301040000080d44508003006131404c0304180403c159100304056802c680075040b0259840d00d1340340030808482c00c1e02c1002c541c000310441001500351a1490408000c7d4030500340251900d0380031440905045004102c0101c0c0c1e4904400a00064a00c61200b170200d0034900409480010000090345085070320318441501004444899040200540040c01c8409100e012003038155592404a80e540c510147c80510145c0f085078144044402940079542c88500b1300c1d0041900c2e60398090141e40480c010605030381e0114070002c04014802c2041e600051030700c0ca860100000880300ba100400700410b03004ea90f0801d0780f074220038030890301d00f501aa200c080c04001c800e007081c1c00c440e207480242c0d400580100c01203810400080c2081c54a140a10f204590b0071411510300b00c040001140101945030440091002c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 328148803 1250 328147553 328147571
    0x20c09070828020d140717041a040204290118060903060c14030403090302041107080715061e0e010905040804060e0109090501080a0303050906060a03200d120305060f06030118 77
    0x1050051712035080c041d55000c0000c0c03e100100070011001c0c45049079800645809120000c0c0d0315010102e80500c01101c110640d03100d80c03001074007070010200d41a55940900004c501c44410615074540d0b0007409803981e01400011040b40e510310f5480780318040208440100400104003a50060b0006204600c4c00d400f1403c211541c04000380c005031400c0c2c00258290f201401181030502c14012000039600d0130343e04110f042ea907005018401c21000802114a58070440c0e100c40003904010b0203010302001c0c19049050703494100051200754845c0b0801c016108000103907045862050f503001e20303048a02145400e040c5181504d00c982e240d411241045000d003c0091150458440c06d8081c04c800c03000740c4506865410020161030002e0900c3e0b489801000501030140d8513404107008a99025110040791200189468510b00032011081d0300044c01104e040100a240707078000d1000070440c0c03020080b544803130703040c0a41020b40051044d0483e42c100014080202003501116035807007000404900a04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 328150053 1250 328148803 328148827
    0x13062709080a05180405011a0c1f0911090403021c050903030313050d081005120715020705034c090309090b01081306020a170403020c0907082802 64
    0xc4095038400000d03c020a21103048121100000084407003190148103135414401c95070915a0b00e001d03001b4a01c10000303803400701200180030707050000f004ca4111514542d045d444540c003600c103007401260781001c64140105a841d29600300307030269815034003c11001e901092002c00030341601144a05011080c40b03034480d40d07582003006512a0b1106c44402000748003e0fe065490304084200540901c0b1b0303078100f045490300c0d6800c1044211001203c00003a81021941c41c282859602e4100d208100c01e50303007201540d0354000400504071001030f411501e805144240000f261450382d00383c0041642c108417809001c604440103650003070035668408136040341241da1841110300452040700800c075003110030044c0e40032600c652040c0400a003004102490b1104500420f0764503c0c40003041240d01151008107a8441c3c00d0301d030862403062410320100d06203810302a550300503030000740d440f45003400d0021703a04602c03442507030b8018004400c42013409074042284c81c420245002405c0c0040d5030a00c112901c0031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 328151303 1250 328150053 328150057
    0x20061902030a120e0d03230c1b0f060a090321060f050402070206070605070e0910050a060e09181f050f0106020c0303031603060f0608061306270908 65
    0x4080d80003196540da4108003d028071441c2540445114a00a00310300d0300748002c20401401c18030340c500020b2582e41c05410f8401d850322100b601d40001c510404000d42c00080e14010180c1e01810101101c8509681e03401c0d980e00c0c0d12401100c00550011408554200000d41010f1000f601c030341003209540340001031100841d1441c01c5110b48076510707041d0800859000080d1500600029641981341203120b4001c80c440344604040206074035552400103a8051103042d00e89801c2d140149110310720f0402c20100701699000e402000d11440080c040000c540f401091020600100a445540180e44803c0c1d411044418008100441d0040c9890283d00b070306c4078003111101c1c13190440001000e05006045c421030f640705801150965200d0318004e80207a4000041d2a80282030f000c035140420340b40141180601301d1340c0d000002c015010040843c0c02500500207a118050981d200c01100d15907417030440130b44280c4d100c0c280300380c4070081903012040c41a0401c0d242c1e80d908800b005c10120030f1a52071141e0b503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 328152553 1250 328151303 328151347
    0x905070e0a0c0e0906010f0c050f1903030b040603030e19170f011b090b18060d06030203010f0510050d030509060706060509091501090203041a070f0e0d2006 69
    0x1c075514861000b4003900300302c0203c901281900c1e070014074035280700007070700c0d401070300b85200709000c60100e5220810134204007001c0d50080c120107840b000540c00310f241e49489904142103003ca41030591107042c6041030311451301200d17015070b51084400621028000300c4034510700300380140460101c000c40e564140200600000d106c1c0001030062140ca09882402c54140084804d5480d113100b04011040d588844404142c46a42ca00c1da40e4a024002c090040194048070306904080042070445071035040760311990841c1e00a030f0027440f6a07118144103000700e600c11a40320003680c000c58000d118905261230100a01846405c01619088501c0d002520380c1c0c0140b0701c11203030251240424030060410007995074210803000002c1c28861030142003044400c10501480f044503901000140502c4500307150312020040e02ea448142e503051100008200030f150140100200310422406041420100380c00c24510313400042c6803c030440982c20300d05031300992410541d446a02400490b07400076000040385a2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 328153803 1250 328152553 328152571
    0x20c03091e0d11040e01090503030f071704200609150906070605160915020615010e061b0706051c09020a170708010f0e060412110304061d03030a0903060905070e 71
    0xc1901203c00c2205550211880280c41e906040d003c0002800000c2540c1d0000c1c41e26030710603002e507689041100d210400050500380700307551780e080c441403080400310b560f05031542c00924903503200160301f03007d683e104906446400074180e4600118215188001e401107a40c01803070750b1700c0c00c806a242d41d0203440e030544011082e003e00d03d13a14640c098000b258440140a5405901100c05401c040651210340007012100c610820481c1118968031909c440615424010005915080c03200d0b851800301c1d8508a003030b001072190180c040ba10302d0081081d40d4503102e0380442038280002c166124000340104000c202c0c0c00400240b80030441004d440e40c07402140d000030005068191400c041d0342d0079a021a00d81c800e956117014104000c01402044880d032158001032840441d1380d42810807200e201041c40b640416010100c0c0200d0100d03031040c000700b14501200c0094179020364000c00c01d500e80c8210909036011a5607010b007040000c0d11034000c0503880740100e080d105003039070b111510381c1c00d82021140030007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 328155053 1250 328153803 328153823
    0x1506030311010513020a0e0a09020913021e03030403080d06240f1701060f020c030303181023070c0f03091d04120c11041d070801020c03091e0d 63
    0x1182100f480b540e41c2c041000c0c84070380c0303040352181c01060229a42c0e0088107000200b9000107a0440d00e00d07008441e10b658068001c0f0a28a40780120501c0f01e18a0441288103485441c640034002c540d1100d00f0b0503401c5c000380954070b041d14590720719003e680116504d8158545400c0c0004e410042841b02c5405030109007440500f010b1041c0009040341d0900480078280450164024496419064030505440d250704002118480310b9206030729040d02044629810b21000040000c1f240c11110703ca040119910b04540e400000141040c00755450740200c1c00082c003440b0800d80c94a050403d200e600042d05003003408440010740c550140b880580001075010a01021b030400c4240c10805c65003004041d00f00303026203203003000c0e56804c9a4410445043d410083d039503507101d080c000740c03490896918600400801603a0003030111981c00c00d125000ca4801802101c0c40000d9085060080b02c140900b020301551802d000003003004044052032548007041e03140f054030360f1440c0e220074228003103c5006100b0f142c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 328156303 1250 328155053 328155077
    0x801081218030319300e0c0d050f070803190e010c050102030a020301052b02041e051305010b01050a0e103015050a05090a090807030e030c1e0d15060303 67
    0x1400750540950208440c0410303040005000c0c02c1d011707080304541301c401c0d00031600d034010201c21480c040100c00d500d540400d4020b1000100700c00040d050040810758010340d0030342035581f4078440d140d018140c50400c1c1e11003000f840c540c6040c461100d0210400701410200a062007a80701c003030880e04102d401c0801503600000501c503074500b558080200062016240494020103009018040c0420700024011a200c5105072000388201c2c00400040300d440100304018a4001c1e6040000b9041500c10340c1c107540381c0010702a065220f10100e4030103403d9521000740104150080c004c5200e00c6110b103a040001e0503010200b18050030f06202850014200484584907124402c0c40803210300180c102d01c8a903404104000d1501d62000b0001100c00032130303041c0d10581d606000400600121b44005004410001e4210201a00104c0c0226000030980440f041c00783e0b00814058003101c545520494100c0c5503090710b100e03281035400742680920514001109080c5c680c4460180d07011508110080391000c0901 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 328157553 1250 328156303 328156307
    0x90a05061306182402041203180611030a05162306010f0810020d060b0309030403060f020301060c02040911041506120c0917010e19050d0801081218030319 68
    0x780000608550030a5210800340e691440d100500c002c1d8400401e030742c411144140c030030759040e42c1c007c054000d10882c5003045450300508005460480051300c04070f0340e10101e40300b4030549001117504e5001005501d0001c500350265450b8000035203111903c2e40b01000000000d514a0a400d001030100090128071100d11041d1410010144c11a2080c3ca0006c3c41c108020703040050142ca800d0705056005a450240c03c80140140003541c020720302084001007848024440000200202c0b8040c5408020401c04030240c0310a9101c01e214075000106203440c4e40f4050b140c964400c0074198400c1800c0d0202c46214404a02a590300001d88444000e441d00204079440d0050145271040d20002d8040040c0a2165000b802c0d6860b41d0207240f51000d49041f0546040c88254081c0300c40d450344034201d030402c83c1110103224083d030281c01c00300d0f1280691827540302ea032405040450306a0301e40704054440a9581d090021003604580c00d0842070b40708030248003005490900042060300303403038264402500b800b8140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 328158803 1250 328157553 328157561
    0x6021c050411010f0e030d05031807080601210c0b0d180f03051309060f0302010f02160b0309030906040b030a06440f010f0507020d17090a05061306 65
    0x411525a8205410000000c1d205002000c400c44242011000c80d050404100c6003200400d0519404d40f1580c02142c01158101e0040c40c0b0805400711850f500168090501e0703203411051140050a03030003080140020302d55264503510322410b4011400302c0701d00c02d45480101c16096440501306582c0004c40412815060040b090494081c007650300120000d559100003c661700c4201a081110200e14918000b00c40c4410340010900304109000d5107880344964018003243d84001c0340411a016940041c440c0041400c00e40403081800d04075006140035800e4038240d00080000003540010015248a9941c100140014143c0958002d48038900b00b0360010440b141c54101e843d0510402c40e0301c03441c80d0800402c0500111107100350502d8004078410b00140c04005801c0c6060f94001c0708450001840c0543c00610121440c41d81480140c880c02c074240d85820b0036010240000e02d490b2141b103240c4403c204400d420840e032604076010300e1529200e650402e101901c540700d200307080e00300340c50030b1000c0c0d806 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 328160053 1250 328158803 328158847
    0x8072006070303050103060f090f06091a10061214070f140414040b04020c03040b0d090f150c031a121011182205130b010602030705060a05060604030f0503090a030602 73
    0x250030807901402d0345031010b2b1109605001000740c0d031119650b40070042110b00825020408400c5504a802e01450907401d440b071500030140081c901800c0304008191a02600f8844491113400d1401c9807141c0c0300c2210318980d20010300c814011007000c00c0215030000c0c070041000748284e100510009102e6010402903c1d400d0510724420340c01031041c880c00d038801008641c203e4481500c503c1d951400300010f00c02503c80e00c80064061004180c0d4032092002e121400010120b050f00d00f0031203401100c00c158116680d1500c84490901c11051b01c071402c1c1060600c00302681d040404481009000703000c03110644090040215941401051920703080310b80b07280605202c3d104a41000c01c02c0c0341500c007a80f000c1420301c881c0d450744d902c13080880c075543c0810030040d16280e0000c2c2c21000568440002a5036544010790865007842010300003000b10b411072203014003a40004002e030389414519110340d404440751807819101800304100c20b8030390743e0704c5180e070500440c400d410158448069135582d81e40040126 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 328161303 1250 328160053 328160081
    0x3010e01020a05030609102403051f15090801050106090812070209190f0c1d010305152b060609060b0307090306020a0e121501120807200607030305010306 68
    0x3100040c1615000004eaa50014068500300c0741e81e44c0e40c2c070b482149a010307030f4004000c6420002e12814840b918101e030030410041903e007440036890760000007220789041c590100680b8083c160a00000042814a281003466403401c400c00d151120115400c449081e406003002c1115840104034407442070001145000c2d1000712a801c002c07071900130820011005103000074480e4036103503881132103003030790301c030341460448042d00f00180c0309000e001800704076084101c000110034040c018101c0358821b0281510820b065144903624101003400e02c800d0460b0302d4411a403000741c0d0401540341d90230400309008018041c9001151980c80e1444c3c1e18103d95840c1c01c0084110000c00030005c0b0548c000c20a402125403021005075100c400d81c00840307161015400d11507111ba840c100f1148000710004084040e048c544045440170390b40d41ca18403041c0781001e100103100e084140107503c0840c122010070107140c0c0900d030080012104150000e17100b0313803180c44210003180d96800180144940f602c00c5c03030381c824651 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 328162553 1250 328161303 328161307
    0x601090606110604080306090c0409020a09050420180d17030f0703021801230403110f010c0f060c03061d16020d09030f0203010b04111801140405100c0206041403010e0102 75
    0x95105d01003584801429240612020004a4201503070f6034115002880f450a08646070111418005c0c0b441c4400e01c541c6108034108901030221071013034a01a00f844d1456806d80746027424840d0011040224074824035804600807001c08041003003428148041790b501145e0a90341d02d40414402c03a030070301c098080020148140702100007002e4540c0c0146105100b400c0c03410b08500700b101141d0405000d5169620b4129021500100300300a10700c040c1020f4400320740001c12401100c00440e60640d030184003500b011982c07003021000c19417030b0380069054400341c0340208046494034464640107030008445003440c500c03042001015090410050090031041c0302514291380302c1306c1c0042500706640005000a10f0482c1c0b50030847d50b00750701950b51714101420900041503895045c03011a001a0100c42d80c1c0d41440814201e00c1d846803621040921608440600385810725042c4030342c02d20300c18106000d0000017200c1002603514a00504003c050100f083c520116180c0c060600f5100d80c0e244400043c0c4c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 328163803 1250 328162553 328162561
    0x603021008160504030f0b0a0f15031106070206041e080a0f0b06010e0603160e09010602010b03070b0a050d02030c07021e03120708071425050108070804122006010906061106 76
    0x4410820681d003900547c00341c1458072120700e100000c1c0b42503880c0b002c05070303e0b040d41001e50440c540500c2d030481e4021400603070741c400384c0028441e06201c0e80310001c2d4859020081031241c8401043c80000824001c20410035540d1105000c83ca003480301ca2040c1d62003414a0100c104109035480002d40c0300740286468000c146442c408207000c0c0c000a40701c000001d155403032081c3c0840c400c41c008618200001c00107001d6503034800c4007a00800c3c8001109000f80a60900480c103881b0a00c00c45600030019135400c1d103402d000300280b01c029007014048111482c020404000543d03240504009055001046046504013500c1010300d0002116444401d000d0f080c04408042503000055a4010360411106100d00c0040c42001d41802013030304580c05109000c071400702c0504180c00d140c4c1d00f03551003a01c8040480d1507285042e10103500850b0000c0c8804002103601560714070402000000b0080058000e506240c880b541d80d0806200740c0040300900e6690008001044d80300080741480814031002d4111810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 328165053 1250 328163803 328163813
    0xb15010804060b04020d09080405032104150c0602070b060301151208030709050a0603020304120c0224090a290f221a1b0d0903030c06060302100816050403 68
    0x180140702a10342e41e0b480d0100c089584698040b100d44201a03001080000441d103044c0314145c01c07500406000b845488070381c2c0451590784540c41003006d5880d010314242454446031908180f105803d0804200411082d00300281a13800035180d61442841040c3c910301d00007040c582110141d024070541d154016000300540b03c903072002444001d0300700e00c0c021b6695540138815540c000d81984542e8214100f20703070000d6002e90540c003075030180c3d00c00c000309014444841e008407084602e454000c1c0d0300c0504400b4101e4010460a48410681d1250300702a00700031098001400b91846544801404c00c4240c004800441c10040b0151848415101140c201103115400c100b20b800341903007582445c042000da903884105a0415a00107054034070080642c03080140081c00b8540040c0c001c1420074079441c103003034814080030866407200c100556030109040d00c0e5850440f0840c0202d5001e41e0041e6440d4000b0000d0380703c0f00403c03040744d101c0d91180f14640c10700d441c0200c1500040707028881000402d10052001503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 328166303 1250 328165053 328165067
    0x5010e07060c141c0203070b0907030c170f0f100b0a120b090304050d120206070e01050a03020f0d060305010542030f0a20120c0d050a05060c03040b1501 67
    0xa410003c103500c401405034411389807814a603401075030161003602d450080383c1e000004016991181c1d00d1130300d654981e10903ca0780d4135418003004000342c18070b034400d2140319506000c05009000d55411928990b4144001c0307420014504000701458000503201d00b1301c880140610885030780140c800294040c907282c40400d401b01e482e41e00030b222003000300c086610742c0d80400917100138002c02004c3c4ac0310030031189030402d03050210750100343c0540509000504164018a4603034120001078545514044906400310300a52005800041030725051052070051281784c4181c601861042c00001014107004825401c0115050b0003440420b0314007443d04404507040d400100c180101d80248003c8900d0b000c00a4280105400340342d95501c520b03101c000500400c038032030381542c41a03a6013a980c00b46091042c88107440020001d8107042d8003200442003b410050454800d480c0035805a41d10f41040b40d031140e042400c00d41c0c04075484080882800188550302400310342220011455a551660810019182d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 328167553 1250 328166303 328166327
    0x21216080c06030109180c1d01050603130201030e010e0f030304031419081009020712030b030d091505070c0e06010f110619111209010b03010203041e151805010e0706 73
    0x19192210002042080814045100d900031a8100c81d00c3c0c88006119802221400c014a110b070000000202410a034040ba805237507000c0411010500c141c0040d030203030030018a5450151740c1d440c0c50a4941a0601014840c800b0300301c003446d96820617041c0201140c1f4588403100d5098070401c12000f05403a0582d0009400c54036080c44011a662407610001500c0290300c4110034500008910007009103850003010b90134560b85080203c0214841803540c2c82c0b1209100d42c0203c4c40c0d040060100c116545c1c0101c2e031400c6903203886490100c0c1540c5124107070001e41d00c0022940c0341e59042c4200da68100781102900201e9207080141c0303e00140d00719980306806040000440b61103042000000e4445d0056071a1144440703032150713208105990200841400c88880c85c21b035107840d605a00500d01802103e010f250000303140c01c401140f44140300400c0308031903800c88822a0030308280c0c010510f18081c0c60091101c1ba40322480561041c00c245080d911040444551500002814820f1940050220910f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 328168803 1250 328167553 328167569
    0x306050702031b0c03010507030b1c020f041506020d05280c2109140307051011010f0c110607090b0a0908030c06040c090c0c02060c0a021216080c060301 67
    0x28035199400141c0c2540b08200d4070b40c50721200110212400070300090820440301040d00200040d0352000300440446030b0a1035140c0e40301c00c107140103404a203a5030102c11200ea000070704019410091100240c205c40d1092544408845802800c00405405000000c031140301410294641243c00824030341e00c070400b219050f5640303050329050300c03080e100f00c4413000010f511480d2030303a010b0000910a008400601010800140c601502040701540e000380e0398071461000d401420244d0070481084015070700180218100603c1e04c0ea51040503d090055819410090784001484140c2070700007006001c14480c03080b41e99101805012180790f01070709800c1101d200000c980c0d10b9012030700e8101d03081e8200343e001814611000c554044400c01c0450802e00407881091402440c65903186041c0c1960502c80c1800041003482140201606001000701505000350b010784412055560004240405104040b0001d900c40c2c000710034038141c850f4800700903214001c010000b030381c184400180e4a1105003c1c000d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 328170053 1250 328168803 328168811
    0x8030a0f050c1507120605010e030715050d020310030308060402031e060a030c08010c020105010f0303020c091306090c05030d2c041b030902041a18060604080a08090306070306050a0306 81
    0xc80c56010f203c00b5a00952000d000d4a803030400d10f40c0103082000014648011901c2d01c2000200c2d0740c0210070107a180900500a07101c114a400000c0c0140c681521601003446410031500c01c0052a51000718824600341d40507003140307419801d0007090428000c05050041e071040091011703203100e510303441004100d54110301c02255114800724680000c01d5000500180c031842d0081000181034021402496096000b0001070303980e0342d00450380b02d525220250141c2c0041e12440c0c41e43c00c001c82855032290844903108101e4003145e64000c21036512060a5400258004052015103800e00803208001d003640b0b01050128464500500000e0f50460890080c180c0c0c1c05c00c40c1110340300c94010700c5000c0d0004c1c2d01b0042e03c02040e403000c4c004d0420300300b04900c120325001388448914a07030b904403c031035607014242002c0c0c201030322150301030356101408103a0301c0002400006654442085072181d4a0b00c07819005407180307d060281490010042c00784010b0500306130090100b9105d040c2d010701101e411550101d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 328171303 1250 328170053 328170067
    0x41a13320307090908070b09060c0f0d090804180b0a1d040609052e05010e1f080d020a030305010506091c060902100903020306180c060d0b1c02090108030a0f05 70
    0x2a00d480401e40c00408014140014201402400740c00b0b000c2e0180607103200f0f45180c8e1401e038000d0300c1300c2040795100c00102c414001d500a40000c040034040e61044c1d4a03000401503141c1d11080065049130b88035030700c69003042c1401c00075948103005000c0111010303203248032810f0910281104003034180c0808018520a10001403e211854104c50410760700070060780e441c40d20b032200c07100c1081001c0321090381d01e0100415201842c00304d4401c00c1c2c1259081300100300729072a40303500c086208201c2c564210f040703c45d091011641039801c1c010108412a50303001400820118070340176041d12416404a4840e10041c842c00c0955110420700040024504001819801716454820010704106e038000e90040440f5403142d0140d82c20041139000e0300d000314202d450b582d8a9a030151031190902d50004404d8102400700704460400c6005015070807018100401d0003904400418401603901394040c4000595101240542c03c00c0704449014200d200f010b1450044107030340142407014551460420070400040c22 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 328172553 1250 328171303 328171309
    0x15050a0b0d1103010e090f0c06070f02061e09040b0d08070602250605060909030703020703030e1203030a0506010f090b041202040906021206041b120e03041a1332 71
    0x2503200d107840b40828a8895031904400c1c0003078001214414480c5c441c0481140c450300c13000401e018030307090083c096407501c1705903981c20700300400f10781040784c0110b000d004419910401c0060034101600605c800c80d20b40c603080d0100009e07039050004050060303034045075584c0810782c10303000c45000b950031440142c2e5480300e100d4031466031a01011118900840c0b0031107101000100d4010500034001103800c25001c3d25074a842e036480344507002008000d81d015500820000b4028017100d00f40000083c061000e061008503a00d01f142d1003140c81c035100c41c0d551410041d8940c1c00492010010010345883c04103d0f0524500303070207503c128091141802e00d1f403503000c1c08554031900b20084047e4007100654483e03412602c10480c0e520290f84030303440341e810801803001d00e005d2008003d42d00e16040e641c00e4400070a180035403004046800c0044010f00040201045030070144540b030302c00221032015240e940400340b000c3c084024098000201c914502c0001d050007070040241c01c88140800c1800ca524130b6142000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 328173803 1250 328172553 328172561
    0xc0c1a0426070e070e040b06070201030b0303090a060306150206100b0304060207060905030904140c0a032a1112042303070f0b090301050c0406050f0309010605150307020115050a0b0d 80
    0x81071895201d000004103c014070440800e0080040b07480b018141e81c0d08104001c181d5842000c4135410090078050300e0f000d984240c009001145000d81601d284c5024500419440c01143c0c001c203001c07a0304d541c010807101f04601c150545aa240380f020b05a01d003403456900084002034843c6407140c8101101003410700000c4c0c8c0c100c17580c840d07000a04104a51041c50590344a40020515500c15498006040040808060000d21071040c4040382c42c500121002e00f900104040000a501501c0301401c2c036240d00c42512141502102d0750b11000d41440c8203180319464800360301c5180310301034400d000820840c601002c4201c09442e0038002d41c40410318110100f0710f009096884035618000c103500000360b0a201c400248240c19042e0001c0c4615500c0b488903020314401d9100340000544100106803410b51010059508400d11340008243c165641001032142e262011440b08100000800d10039001e8092042920a4030a040c42025051511000615162032841042c2d00250700083e0715000140940c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 328175053 1250 328173803 328173869
    0x708040c08030301060e100306240c020a0305060f0c040819051c030507020f06040503040e060a03060e010b01030c0e1513090204030606060e15040b0d09050604030c0c1a04 75
    0x41169204e680d580401080704546508550041c010340c08a64400c610070f0040304141c4041d0b540d004440b00e5121902d04c9202c0c0041640c0081014a0040b200142c2e604e9410400441c000e000904040c20580b0109980800c0a00701c8041014200020442404007080340d0380c200c0d5215003640400b0205040560800b0001001c0c01c442418060078098200d4050b03008600428146d42103984900a44080070b549440c1914081c0c0352b0b85c020700c420004d4600e03a000542c0d00c0744001e0300c507246007030b645e0707552809032000440c419140b65103400000c07180e540c1c184982440290360340b40030583c100c5600e000c51f0a441d42042ca890b610400041d42c2c8548200075840600201040c4200310350700c0e60b03281822001010140660800a16500c22003240762500d800950032a000f9614035600e040c0c548008400c4c20343c05141098401c5844c4d084a034003080050114611581c000c0d19900c1e811801440c03e006405600d410403140003002a044070b06540c0d440d403d0754103032044290120848100303c028940c0a0a40003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 328176303 1250 328175053 328175069
    0x3809011d120315060a0f021908030109111c02030105011209020904020d08040f03080d1a0102120c010908030a020d1127030a240b01020c0f0609130204090204030203070803030705030708040c 83
    0x1401500d15541311b00c050070410640c5d400d940142c460300241d0740107a50611400340070b03000e00740018800d99580f13601071030b02c550940344020320380307440118030b072a5002c49030104607a6698084010011541c21140080c81011303081e40820445180d81d00103400240701500190294518030803010820080b40d007101d01030221007041c07414155513480c180b05541e122030301c1c5030f10060030090f81e2030007110320442c04503c881c0140c002e40003000b400304c0e01c40003503042041860881d6488294010100f8140d000443c069040d0520150f07a64108103900e13801d5800781500801d41c1e00d41089442d502c9894600c00d0b0941100540c1f900000559180001c2d18100f00000c020b030944015040403101003a507441c121400c42607403030044c0000110741006a8a414160408a070084044070403514a0f1a080d030050070045801031140c2140ea400c003900004a801c1078001c03211140d40000c0074130039483c0030092a80184410b01c0118510314000c2c1000300710380006403941c1c0621100c0000300b001c100d0f458481c500130749520 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 328177553 1250 328176303 328176307
    0x1815140d0e0f0c0904020d03030f060b040305010b0a1505130801020f0901080f06010210050a0f050106020d020c1c020910080d0807080106110601033809011d12031506 73
    0xd001000d00030204840030408902c260084000d0410380801c84070840800103005804a55039a002d12081e45180f56040f003c00d0355805114000584078444c11028040301044513480d0383c00c40ca0800d08440e00c40c0702043c42208a000304102a407038610340c0030f40da01e0917841c0082e200c144180442c0c0d0004c12039004140c80d03500100c0c1019024030303100054100d81c20700340d80304031207134494600c015000e44042d5406801a041245601071031689904010740090306550001400604150340c901101c2e0280c02200041e00480300d034030380d015410480755107625012030b441c4e00c60704203812200d0045458034800034050b020039000a001c0b0040c00d1462002080042d0965180c010040302c01040d2002c01c540220109942e2000415483d1084264640110404000b04020303400e503110f0010f42a040200080c00c222000302c0c1e141c3c1e02c2d40c01804041d18541c01a1008030505010000c42d09540e0000c540c4400c04420b803c842c0f40c07891000a68014001190b5103031079507070f00d50305080d605601c0f204856030f07001000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 328178803 1250 328177553 328177567
    0x41b03120e06121b0d090f0303060509010e010902030c070b041b0803090d0210020a150b0a0603090b0601181d1008060408041403100908070605060619030b360601181514 74
    0x510317040e01c1859480327680d00304441501d5008106003542d081c080c0c000d81080701401130044503e554001e5400915402e407240c00d01603a5a1780c0c0042074070865045500340d10002000c140e5580380825600500407440295052080301d80204001d84056400030384500c02410000c410503000388100c11505400414140d1401c403206a01d0014009e0103100c140149510700c4000b841600c60b01c40d0004059102007000180d071a5000116001400726a084600d40d0b0b8a0100052200300b8419050711003800004552742890000001c10109245a010003010341080c0200700009a01d041140c1c00e54604110b00c20720280120301091410081c682000300c1d4034074120304242800f21103c00b400d000b034822031050007546d650704240411401243c034040c001454180342d80300c0c1140a03400140400e0780240c00c1c48041c04801a000d00303000c0c450b4440d5800721005903919800e501c0004182e581c00242824445100e018a81120003080c2c914811000310036415059140900c0c402e810b03210590800a10355a16144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 328180053 1250 328178803 328178813
    0x112081b1618020f03010306050415020d27030f05031807170c010230190e0306070c080307080601120f020a090906030515041b03120e06121b0d09 64
    0x1069000300100039624801030030196007140216201e481040413160700b503074070350b6417107070301900014008071079905070f0040e6803207110300c10300c0030300042c0503481004100c00e07140194840141052211542e1400480050301001c6600304105000034105440c01e50b50701d17503854032290a100707902d890650441c0113146000484180b0b40c0c0c0400700d40c000341c0c4255372003034580c0401640e4564812500d61034520303003000c08182d02c10500d914424401c1030036a03058035090400c41403401580e1a1441d00c00818400408449203003020400d00e0b500c500c6504145842d5001034548018030b00005101004100312840060074503481107400b902e00422080052040b54401c0c44043c1c00394000d01481d0700060100d034000110401280101d80c01ca030b80043c05004103442e60310502d03c500100030402c4e19886100e2840200c5c009400e003010300154010081d00741c80c4601001cbc000d000d003050341200743c4205014445070a503855096100c80c2c000340c4262100450f0495990080d0b49c2d8040c000300c03840f5042c0381c0851041800f07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 328181303 1250 328180053 328180093
    0x10050f03190323090a080606301516170a0f06030f2f0a090b0102011509050115050307020607030504140102040608090709060b04140d0204020414090f0112081b 70
    0xa40d003190141e80070746e211000f9540e1a00c2c129082a801113a14100380c00000d04c0039490700310a50110740c07009200c007000040d03910348a5604a000500304840007000302c0c03c0801030713010802d4442850910b8003210074442488240070060070950081d6902d106191015207264002c600450303100c04403a607506544d06200c807509000342d440843c00da26100c0c48405c0c8045442903200b21110040c1a1101c0e00d050070950401000d40c050450b040d5903032511583c10460201c0c05602c02004006004242581440c04031075281480701a00000c0c00f9007402480702c00e907004608564454038910300003c5c940c1d25411b2443c144980641c9002c4503500c000743c085415503000620f513204241a80c00c481042e544d07040c1c03503c03c58801e849075810105051009100c26007501112855101c80182075400107a001c4e0005402c9074880c1e8480602215514240d80c690300f041c1d00050b030300000d400c40360a840d43c034085c500e02c06800f104200600fa204000340030004c0704005203100c591900789100f202c40b0034142d100c0b460400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 328182553 1250 328181303 328181317
    0xc1c0503090d03060b040b0304230d0f080601050d0c020a120c020f0907020a03080c130e0a14090c01031805070e0108060a020721030b09040b10050f03190323 69
    0x6402003040c5028060701134007503070701200c90704400da500c1c2034600f03141e0000c00d810282080f202e84aa4000201074840411030764028401c034507000d89001140d540b80a401403911248840521001c1e030200500d07a13810500741d0b03008000d20100418015202a800c900300041c10000900302c03851841011076241d400105060a40d10070303039082d5110945c9100304140004212007038001603200001c40340001e031248004982224500c03004505200c80032910801c44001a00036521039000f8804001d00344449005460300c004144100390801d05107210043c0d29000700c0c40b5654103068903aa07107034040580e1905040c0c034254000c0e06070b50145440c0c110b40507114000b071103095414401c1380040b03000c0400610031941c038240d002110590b4148404010700340c21030400180414144e480241e008142c5079504002c0c8141e2144141d0351140c03030001c03c107400700384d415000107005600c00b10344d035481c649001500c00040481d01381c5248880340249402c86801c0d401141c9042140300c0003402c0c20b10005410094001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 328183803 1250 328182553 328182571
    0xc0908010c0503010e1503150c0a031d1e0a140a26040e10080d02011b03090206040306110c030c03090f1c1203021b03040504110a02070b0c1c0503 64
    0x8581d00707100700322242d000a0040d00c52141c0c9010100b03003100000100c00300781c50700242c1034a91000500080415504048600000b000000a180c6100c140d040c8240112185801a4150f04200d4201c41031346d100202d00c0c00303441d0600c0c540c0c0c5002c44500c0802240d940503503c1407421001310840128640c80d030101c0f8008542517560005017a00802a01008070304c84482c414001303003440d06d0920340302c8080d075010384142010990504007103847c10b0240b01d5200100115000407415910100e600c03081c2e81d071100d0f50002018904440c910069441c081100c0850b608400003140700c405136034420fa4a071045180f030f01e0301484001040c401703901e07000c03000d00207103070045441e2010070345110148a51114000c0e0081d0800309451048400544621190f0003002da03e481d005040818041c3c804011410040b917104850380301190400c01403030303d4040c08080d80e00b9920040e05001200b00e0107565412540181d000143c404990b8480e074910411a41126a02500e05a2614007454002034100c0e0f009440f9221 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 328185053 1250 328183803 328183811
    0xc02072106050411040e16091e05061305040f0c06021f0506030c060a12050a0209090112031404061116030c1203051204030e01110705010f030b030c100f09091e0207030e040c090801 79
    0x51580d450303215840781480e08275242180e0141c030780d1884004180007072100394421000700401542054900c01d0a2145101380e000341401d041d40d003404102102da6501c0301045621201802c4200c4d1030441d0b4640320303c001188080365545940e4000307800c142001c103100b034010f040401c4141c0d10aa200301701c1d0042a04660040060381c56403411503050303106100c90f00f030304254090010000c440c0014940903195010f07242c001020550103444004e1548141e0151000035040c030303400b443d1aa001c0c44459103010f81d00d1107008034545184c3c2c1e1006103642620503d002075424072001c100b070502900848000703400340c0c0c00c00c105525051a0280c03d40da0500d0419002607001000c8004403c000a250015078005846164410a040600b180030b8101c020005802d80a82c01c164a119220541001700041c1380d61070784001d04159000050046603036034805a03103541088010102c011000c0d01004001c4404400580d440c1c045040c1901c00d0085401801c0d0040e00d404108506a40d0101002c819205498001d01c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 328186303 1250 328185053 328185059
    0x150e0f011508131e0f060203061003050405060f06060c0105010605041401020a03140a03090b0103050c030c0108070e010f05221401110c0402070212100c02072106050411040e16 77
    0x69403160b080780d2040c42d8034002125400458a0007001003121524030300100074200203580c407604294102c10013118080c0c0c0105c01d1050070300d040c80002c00e4504807440d0403c92031070141c641958a0501505c885416800706005c190541c45030412169584541c10090000b940d49a07070081c8194460310408240015004c10510190320100d11701e1980c6805603280c21f900d160140401c1e01544c444a0318106245d6034501e060b00159054194034002c43c068005442c840c0c03449018181400c4401071039a04108060007006a03c2e0b07000020004540800c0c41c04404a240d6010282c80e20712607564001100341d00540c014070604804582c640580d04412800d068080164005680c61190454110121340181100510900303090740605071391030006210880074101d45074010b00700000d81600000d601d44806e20310024030740400c1803a00421740140245101c90100402140070b0680e440014002134440ac00b140c1400394000030228199001003040082ea541c6070036139a920f0101131110408034100b02000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 328187553 1250 328186303 328186307
    0x32a09010801150527120a15090b040b0717010e061003060f05040506060403020402040f0f0b0a0818010e0f07030b09060702060106140f0403080306030c0405010302030c0103150e0f0115 81
    0xf030041c1401d60f141d0b90305140408030764050f03016a0b9000e10354483d20a0240c0c081a640e0900f038840070300c000c10064074501c1000d007040c1040c45004051989145e003050305407000514603072031260380950408018901c40c0c991329070403160a14920009000791600e800080ba1445a40c1021401802c003210b4191468200000980948d616803181c0051001d6018081103581041c0d0032095000c48000c1c115890302c2d4495000074200d802580010f40c0001d811841400302c001d03400302180280c00904e01541c1070900f241001002500d00404c9143c92100c111503041d401e8409421036003e202c0c0316016a6441c40074650403a540f45e00c6840145e03040c0300d46501054648030013007411070180806038050103990782050390503901043c9421001035844000c20a071b00c4d1007155007000d80301440c4240356003503903410110b00f0549081e89000307629100e6840c0c0801040103983c001200e401e41c09003801d020a48418460310f0059003070441d80100c42e0460808200404091b0b550507032410703103400c010b1100101100100c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 328188803 1250 328187553 328187579
    0x270309362d0e0f030d1d030a0f0207060c05060a020901030e0607051c0b09010b09060c060a06090f0e0c0f060c1c03050708040503090118090e0a0302071415032a09010801 74
    0x2c2c500d4681081102c0c8003035000c90f0700550f41006e6a02040c00e1031182e00120765196a0007c40440b0010b0052440030005990521068005100b5407410041500e296121141c4071a0b0141500071a0303680003c480c1c0490340207400c40070441245000307890582c5013055010b044d42d0703c5000500b0350b101c1504c0900d52550413030701c2030800000010707101c469075a0814000c911282c0c80b04480d9a8099014050f48084c45e200704507840c406c140300c10021420350310740f02420301500d501403902d224403130500030b075541c28950000d107c200183e0101c0d40c0c0c60030840c450010902c0c078030a804942580703000d45050010020504001008482e070582e5007000b16a40d50001254200c1080d90010300c0d1307030020480b10340690300c5821502100783c0c44003400c10885599000400480d032111000b200550025008201810b03010f2000348010125054500d02c5a448080020040c09480050001e10400800483c80206000140c00820702564802e48501c003030781c0083c14003030b0300300300041d900203074040d00003007052821540d1f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 328190053 1250 328188803 328188823
    0xa0815070c2f1516050a080301090b090c0403030203092209061406030106030201020a0807060f0e0a0614010501020c0111010f05070c12030204062001270309362d0e 72
    0x8101420513200482408002040d500180e860f03110361b03080e01e000f29a10600460081c0445140001c1c50340109090000c440f40007403e0040c0c0300e509100c10408a074002c002c8030303140081200e0300018002006040d4916090706c0103810002858051208100070751a40b02d038400865603054110300d551403500305400c0c1e07a01400000d00681003510761400068040018011062085c03401007084070140300200d00301ca41c0e0301100640c03540580c80000600c0313114070681c01d0000341034445003031560400d000030750b540024002250402c480406851810102036100b40101c455119040c001c60a10080040641c1c810603030603074043c61281903118140c0e001e40b088804540303450315a0140c40412003280c40d04111403151650f90355489541c048a403e10b030303074141144840c601580c00342910702824020020030b00c4d42c204480c049100031046200c581a1a10464070401e103800040012807401c5090000d4005a6204503200c040441000212803d100d03640c541040c103003070200300c00001e0680c000d0b90f49403814 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 328191303 1250 328190053 328190089
    0x1110106150e060421031e0e0108060a050913022407030f02031303020d02030a21030b0f03030412051501030f06270204230a020a08060a0815070c2f 65
    0x207081c03482d00e4000401744404580a0308005a0400c680c40b6600d01807070347d90a0103000140c4000c0c0000007589c0000110740c002c04290380e0705050f2424840810742c8410f016100800b07845500351030781d003155140342000c800d0054400d030668070110061550b0351590803005048000c00c0c0e541245007a40707840001918610b030070f45017240580034915001c2c172070049501401a40c06001e00c508100c08501c01c90200c11403c210300d0740c0e4081d500c00e5100f0090442d01e001e601684103824009000056541c000f05507000e030740718003040d4a004160b9140c460718003c0041480003d41c50080d0001090041b640703a18944035020381d406010000c1c2200030030038040c0d50101d4107803200a000c0d01c5803015040551090503c00140c10080c3e505030440d4030050305c1075804442a055070354001441034000c641c8018011b4000c0d2043e05c9880c03020303007442e440a8803002c3e0403a944034800d01c4c040020702901d100d500c02c11100c1c1d800a002c032035610381d04030b40d40c3d54903441d118125000001814071180d481c1841c600350000b4062003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 328192553 1250 328191303 328191329
    0x1b06072c0609130212070318020315090a0512040305071a031303030209060f0d0c03140a051302090a0e0706020f0703020108060307031b06031113050405040201110106150e0604 77
    0x1841080615005000442d070400c5850f810000b1441c0e50348002c08400002c112202c11500e0300765402003c4e158a40c61082c0c0300080e50210310300613100096010090003e160b038a41c0241d03650f001040c9045a144800780023445034440c410800394a00c0d00030800c0c0c0b07000f1000d580350240c80e0385614103000c88540b032031200300f5010800500406c2200c41020141c40c82480c1c0940380004510006410340c1201442e030482860014900901072114403441e184209641014041c9281c07e0303006031440b0794005e03c0c940800d9180d0001596600440e00224a240d50040c0389058509008091070000e0803200300e0410144241a030204038140005044000010010003c25210b4250307801190109405018560513120f030407001b00000c0c1004012042146458545504d0f180c50044002c0a80741c0b070180d10032102c18100080980145401d01c200d080c2e440a403000b240607189c2d4070040f04c4698904180d00c0113546440008149401440f90f8410300414598403800180c84a0b41000034510692003000b20326241c2d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 328193803 1250 328192553 328192637
    0x120717070f17060d0b0901061809030203030615090307150f0206010302091602010e0106090e15060603150117041115030609073903090929061b0607 65
    0x4210b1500da000001038440c0c2058507082d80c80240c0e05e40107a03000c0a00365181c000c00d010401c070540040c00c100c03840110521030701c84035031000ba45038400506104d0207940800c001c0c10303c049981e400c64034024806030441d43e03001d9840212289e002c45228103140010391040181c4012440004c0c0c96041c1c9800411055040e100d407000b82000440f005020410b40d501c5420641e03040000b0320507200141103406001c150300c80080758050800b1480c60150300d9038104142170114540302da400341d035440518034203952041c1002d0070040c1c803000c281d0786012154211810804c800c00c001d86044454049042d41d80b490800d0780c1c1c07098007503540000c80714030390024004400105a42d00c54016940c0741c1a1101510010201c540d03107211501341901000c2000c4171200c03c00300c04051340440f400c00205145402042a100c01100200502d0306803c444c800408644c4129207281d516041207a48031030024041041c4070101d100000c2d19440110740c10004205d1504042c1c00c40c0e50340a2a0000380b8042d802d5000c00108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 328195053 1250 328193803 328193837
    0x9060f130213051f080f10090b0d0b0a1d0321040303090503120f0105040203160e010905180609070c020d0b09120a0e0a060518060906120717070f 64
    0x40030300d102060451400005068441311032001c09160382090b22032030003100100c081c04d01c440c050400c1c14025400c604000d0752130b8034100100c094450080d0082015079a203400213080d180b10000c080e180c48640030030b02100001540c03110a051049410740715081e110742d0080d540b02e000700c0000b65103040c4050a01014040b08200c482d50040c422300b00010301445a454143ca50b41000c1041d5482001c88418800d5000340200e8050043c101241d05600e10300d00034125500842c280c084030024000d11409034296070303000340103600c050030740503120408a0708004000000000151065801421110007240c2d01c684250060300455030098440c42440b900743e0380c2d61400c0ac0000382202c190340550a20709000d481007100a01b620907481d52041540c440d0001002842c4101e40d00440600008008550998142c0c0240710f400520850b00d40d511030f884a80400e8282c4160b40c1040d40c1031002104000c05103401c0a8007082c07180031001c000002d07545400003030307030b1001c00b510140c00070511001110010701 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 328196303 1250 328195053 328195057
    0x1020c0a08070c08010e030a0914060405010c14030f0a0320070b1e0a0b040e0a1713081002041a0f0f03071106150f01030510120f05030a090509060f1302 67
    0x251207101c4000149030707a0030703001e4211b8112880300040e0342c06c00034840e4151a403142100d00a000000046100d511621000600c50301c1180f0595040c03003400d400000070b00220845081c00c070350090082da81e9038040f4a034a40325513801104074201207071a11708015901c0e580241c02079146043e40d0b08803481d004c03031611803101c40b02000f000311034071004014030102ea100d0241245401043e41210202d001000807003004113072503080041100755400003900700b0204907030707049445015a680a1581e40c0302c00000121000200036000303450303036100b41415860303103081580c000d20032505140368100100d1481026640d06106a005403a0a09018480308000101400045400120b0741c24040320030300e5000f28460401c40b0031a001441070b119101044a03604090448242003202481e08211900e883c0c2414644070300203002d0705401d62403421f41c180810810015040300c0c50307002011240c450455010003441048980105405101d00c000890001d05001150240314000141914403803204042840029 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 328197553 1250 328196303 328196317
    0x911090d26210f04030f08070e06040b13060f05070b0604060e0906010510030c08220507030b0907090c05190504050d030302031e0105031507030207060203130507060201020c0a08 78
    0x1040c80d810303040740701d1565000800240391034048105800c41d44600001030a507004000508880c0c92808000029500565640045105040240c07080d15414000c40d821200c82e0062500500c00003404640c0310303040405030058ac0c0c2280005103840d43c90f00b50840307903078004030303162004114144003c0d00040d0804080c3e6621040117000000c1d01d44e03850b50401d0100500365044040d40d048600140410f0400440c020f0001d4440c0c1001d2181003000800140301100003060b21038250031704101d1241ca02d0f0010368100340c02e60468119607000b510f9042c025200c0201340c8440710b07148543d0f03100180000b214010b0b2050300c641919200e040000c00c1c0744200030507070052040001c00c002080041210380d00c0e60a0000e84a009540c016100d01d01400e0300c41c01c036a81080340d2180c1d600000e004000c0717994002041e10180754040305807400c680b42c0c0c1d44107070044e000ea008005d060038004810840c51510550842ca001406501265a4255075003c20383c200c0c450400e21801300d40021b0b40003c082100f110060900d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 328198803 1250 328197553 328197593
    0x406030c02030d021c050603010203010609180605120303010819120f021f0b03010b0a2124141b09010f05070c030303140c0301050102030405040e010b04060f0911090d 73
    0x54116400340c180201d0f4416111080c0718601c2c10811458242180305447d0302c1b00058000f10710b1941411000380c95003140303106041240707503481400d0400e048641c0095000f0140502b0444010b201d400500d516030b0424010b0418034443c2c0c3c00040c10824101e2050079900b604608038070010000d0b008211407049004400c40705502c00c0907507012010000a440342030380f00c5040800030710f51ba81d50040500b507946403058580315800c2d0100c24080082c030480d00c3c41200890b00c42187c82c0c40b680746015844c0c0e140080b400002d0034984101e440c84415144c00140780c04003c1002000380713a60340168208440041c070014002c218043c454189154003070fa0545882d5041810107900f4695140c1e510000d48032650021000651190703400c00c2042580c986403500300e03045003005421903040c000001c0d41c9000d24420380384141e84a490003000f0640070b61050a80d20805402448001c3c0c4565108107400c21500c02c1c0341100d858400c6058070312440d0030544403d03100c001c00c0099000340b251200b10f1307925144448215 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 328200053 1250 328198803 328198807
    0x11a07350327151006020c0f33070606090507023007080301090f060f0e0a0c0c0203010504200301061a09040212011202150903060403080c0f0c010f0b03010b060406030c0203 76
    0x6404280c801d103584942841071000c02c0c01390030024000c4c14000300b4255980100d0681da400b09166603108241c2030420300200f4240322440c41c001828518100e112a44010144000f40400c20700000fa0490015a440c105041c4006c2d00c03545001c983d2002c005142c031680001480700302c100348010051848644100c9a1898201074050f00e4a0800350700c203038413280081c0e99440010041c5000c60113214001c0640c140d50180c21031800351804071140340202074214103a5590041745800b4020400e521010390058000c00c403624203850100401c004911a10218690003504a15a450140100400e0324441c8828040c014910341d518096500608140c40c0d000e90280001d410700050006694028406006101c24022181c0140030f040204c60381c41c051004010003108002e41c5002a1158103c0d51614100c49690341b000d100852078080c0c0c4880100401e0006000740c40c0c10415000110094a0303a03200300440328280c010142281d15030340384160841824001081054040d512601e801c1c241401568 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 328201303 1250 328200053 328200073
    0x150f06090c020c0f0307050307091503081908010905090d08180303041b06080c12130804080102040e1e1f0504050403050a031b08011a07350327 63
    0x3059030180c0366118010ba00803c000546842c02641340307814a0400d03005081281d003130078086502c0300c0325402284030075030719080d000c00002e0402c1e030414015034001e00790715210445156003040f030908101c5c424001a0b80d9000210f858001e0b07204440c01503240000030210565131010680c1d103e03200500c50700d1002da84142008280c1410b00c007d506c1a44182c882e100700b0a078102403201080741c941c1044003002155030810111541c460201e40e04c2881d100c42c0305007140d40340f2801801c0c00c0c0340c4150052903040b0215000491400c150060410341d007102c0c00216041e51050b058803c484003030417205100382e12020102d00b10740000142e0703a043c8100b00c12000703203044d158004036064031019203044000400000703209a6242e45803043c68450003e668240340031030b00e038000040200e041801020640c40114880f184480b0f103140407249801d03888040c140001c8041004803610011900ea026034103c04a00d04040c000810b41c03c4900c2869110241800c95100100d06002d803000016038103c3d6100711040c075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 328202553 1250 328201303 328201319
    0x6140702060c0604050f010504050a060e160b030610020a1509021305070c0b0f04030905011103120a0204050301062c0c0c0f0c1003140105040203090c090a020408060c07150f06 77
    0xc00d0400b0032400180040d04152428516105030003070b040d08103914210911001400c04254602c60726002640810752800c9902481d040c0203480f55400c0346c04445080c00600801400055485102d0464000343d02000301c81099841e14081500209149668140070601d4034007540032120751400605002080c410140c0580d089400558200010030001c14101c41000141140142d2126010002c00d0060900c1d940180040c1348038000c00d030601c251a43c2e19201e03035504006072801108142d0400841d41041d200d104000d50041c050180254284100411000c12006e2402d038000c0044100c42e03600c4110343c05a1040c0c00d4047c002d1402500c2c2006001c10407801007000084045100d0083c181580329001000030325031000304501d0a241c104150180c482d0b1000c3c0c0064110303001642e006d6900d6039448615400e000005c440c2681c803402503c01d00c01301c04c041d9130240c0f040c2c80f28101205c1d0343e612110400d403140d0050060040c00300c200065110070b030640d907800c600a80851180302098943d101c09131 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 328203803 1250 328202553 328202557
    0x90f0718060201060503010c0c0503030f150406030b0907080102190302031003020d0b180610050105090d05010c02030304141204050d111c1a0c0304030f142704060803040614070206 79
    0x7107500180e45605090006207801e1040d02041840c03801e026400c1e00b00c41d0754040d00c9004c0101000f221082c42400610400c080c48243c0c40c0440c00180200600c03a1a45001511414241c0300501e95108070700000c0342081052084070400d080140400488200d02c090440181d0300c000c103c44141024100000b00580300d055060555511511541e110351402d80342c5902e035400c1d004e01203c5160300050505c034420740e16031982c0003039490a10340a5034401100c80481d006209402d4014410b601c0d000c1c4030622075a0210184d805203101380d0002038100d10b8010400c0d582d0502401d0140a142c08200c10030861500301288200c0c03d02c0340f14903104d010420400260720140f0301d403010b075100c485800c0d0079082000c44010040c9030490040154082e06150700b0513051030000510080502ca090500600002e00a0b42070028a0400b4180940c3d520000490b00700804003100d40d05400801403485042c09250038052001559800001142014a4510201e64031050002202c0c0b00000401004004d40c8034080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 328205053 1250 328203803 328203809
    0x3010510021f0f15050922080a0c0201111b0906030f1209010207170a03050306030304030605150a05040e1005100e011e080d05041202011205040f03031a090f0718 71
    0x310000300f021600346440161100120705030b18050207100141718581d98000d100b07801180c0440c802822502102c1d46002d10a2020070181681c900031504a00456004a00c0b0120a100b0390b40c4826184801c3c408950b03400d1000c54098010f101c48041c040303a82840210654010401421500e00200791500035007861024040c0211040002894400950301000000c00808444601d010b2001c108a81542c8500300c005004041160010204045a4080040d10059034010341c08022905182d2103401c840c8915540c078074020b007181000082d1614092190401070602407025040c078021030601a00189401840301007182524000480d0320132031307181703900e018200c0c0c01c0da900300d05107075206454000c181c6075000075401d52081c900d01c0001c079444011340f41100c4000f41d81d00343c0040c4600c0162903100f030100300700780e034145800b0401c010700c0551404000362500a0b201046290724481034003443c1140303a00360716085510301c808110489500002560b00c4042441c1003e113140c2403e11b01401c50010b0f038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 328206303 1250 328205053 328205113
    0x904020c0a050c0a0810050406060509090d030506120c19120809091005130f060b07030e120309030c0d11062a0304060e04090609060f0603030201061a0301051002 71
    0x900e0002002002c2103000f036818030844003c07050b1807a1503a003594514107521104540c3d0b807180007003010000c9503004400581401440031905180c05d50645070355413006024480080d0414004c14002d0800100e042000902d460240005d8502c2d81d0510440d0311000604490380443c001001800a4100c4400368030284070b500016954a0341100700206104050400741410401940c00c0003582e07141d034214034400304e00400101e801010303949070500074881c075400b206070400300155800806611030b1703120504d040c049070019043c480c41e4601c0350b0750b406000c0c0c4241d01584035120660b19031030107178210520184078411410050101b10041020307900320302c4061410740100b032849019105120000c01d402d58901c40150700301450702c0c400600d865000c1c510070340540c0d541c22280042c40100d0f0032004026401072401d01c50448044c00400003400d440c8800c0e4019440d00c000400d54904440c1d14440000c19101081c0c15039090000301300b0169a5248018194452085001c904443c10b01500081035125 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 328207553 1250 328206303 328206313
    0x105040e04021305090a0303110a0e2205010905180105040c05040906020906120709060e10051803010603230a0b0115170705070c05010f020703031b0203030c071d01030506010501050a03020904020c 86
    0xd8031f0042c007681c680e00404100188140108860540d00850840769260100c84207000e6402d42c0e010241042485600f02c0341c01800c141c008101c00b00c06800a6002d51000443c100a0001c03011001e03080350743c02da50040c4925800602000300b441c05401203424036000d0304005191000c0f100014030268028401e14a1510302e20080044154020281e07000421507820b0011801c100140021404202041c2a40034080c001c035a6611443c0c00f620010440d80c006002000060340b40d081c01e6080414100340385080100b403200410800c0800304055282e680e002181c10510b9083c00e0043c40c820724010300d2001040b03920340740c807001040c00c0c84419004800a46900356100b0481c02e01400003081600404e050090303140d030b260205a80010044100c030b0f05840c10514188010044d8030104240300c00296051001003209103140302d01103040002c44074005103003540110305403c9603040c02d0382480050410740010004001650240000f440c04013028a401803404841138000b42c126004420120313903a6100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 328208803 1250 328207553 328207573
    0xe0411120f1305030919090e0c19050f061806040605130f03211b06020408100504030906030207030909050f0f0a050c041a0708030106020f070b090105040e0402130509 73
    0x2903280c02a00220380340c40c6004200081c0d10740a0b030301d00c20146480d006d40141d141c40040c00c940c0020040c00707004c2e4244140144107c07220403540c2d99104201003413181486034440c81402703044080c200215540a8038040c48a01058104075240e0064540814090151000610240e40e10002000030f400e80d51137860325020b00318040e1000c00350503004105410307000041072010031101600415110040d10704594000070008089820486141e003a024001f00540500200107943c0c020b0415641d0355400c40b8100c110b19290582600c40c240c1d000344c0414200341d428485070b84a900241041402400c02c49101c940e91038150046440c100d070381a01001d0b0701c4040c000440350810101e03800c880031040501642c10042c44e10320241c41303540300740d400d130b405018001602280108241c0304c02c55005070000380c6075a51004041c0d100c40502c20900080c1c007074844040b03032403c4128152036406c1d01c1030791194207243c1400043c001a410150003039a0240c01000f402c14241c3e0700d80141803148607620040c01078a05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 328210053 1250 328208803 328208821
    0xd0518070902160f0f060c0302071a060d080d020c03030106030b030f010903140a090b030a0203010e01080607020304030b0a0e0109030203091503010e040f0f0609050d091e060e041112 80
    0x8a4100080c0301e0300400240b0440800070324100815600f02140400150391841d01200e451824080180017a0030000102015030305907000c0e151041c0030340c00348a03008030b60b600d940e140008215003450b48495121803402c0410f00c0c141c0501180100c0b0303080103181003031030611301d490364009a004000280e280c4612420700c2c1030078000b03139500f501300d4802800301c07007826074001e0000b400c1c500140f8210b610103da0900d0040c81482e4500040c015004200d46e81e00b032020a400c0654801d00078055001c0d00c040001403100c100184070b5100d011594003443c00c003429a41d441c1450140500302074a00c60301c900c1355045c046001e00c01e110f4031500c02e400a660b24a41030341801038402c01c40b200c520280406000400041c00d02c2c0350201c1e8026801203050450780803a02d40f00008000c20040500503a25049600e402c00400180a050200c841d0710b031502c82650f41d200c1070940070020503001035402c00f120400c202e214041c00440000c101700400108032030040f60540301c5103420200005101107103400c24840c01c00c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 328211303 1250 328210053 328210063
    0x140601030614280e0a09020f010c080f070f140f160f090e120f0a0318080a0f090503030f0414010c0b24061b0c0306090d0804080d0518 59
    0x705002003a01807800b0910001105484004000403202034900088900d00144140503006425500d51200181c2082e24004005010796001203008a180404144040d03000e03d40c4242107560183c11240740c81402038245610390800c0c1c1088412421001341e031000103a108588405442021008110190960030014074110803101c0e00700411805000a2110150109a1005864030404042003203910015242d2a160040304404581c52000c56010501003000d030040c420940c0355582031200d1050920f482018002d00400205004c0040000e902c0c20b50150130200d0745911282401e5102d240d4800200741150b2094060048801001405100300071110b5051000389400f840c000351006896a070340702e41c0c8040503101012030311b445403810003c00b650f001c80b501c01c0d040c09013116458030300300380401c40203003a42440d81c2c40c280101254a55107040005540c0d20940040c002000d42803a508416074418038040c200380d0304075100b00040102d02c0041e000f494003039004c40725086154141070b1131035070500d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 328212553 1250 328211303 328211309
    0x3060105040621050f0304030c030b010504060e0411030f060901060e100608180c060403060605031e031903091b080d08010e1b0702040504241b0e010908011406010306 73
    0x40c03880c06005000f110360a00c8000c50324080030300203052408803410300b14601441100d03041d1030341c40002000f2081000044224041700e2069601c800e65988a004010544841d03019071300c1c0311605440040c02280050001124007140034003511412000c6080c1c15050140454100b40c05a444140c10021118004c0045500003030804c00d140d400c50918a006080c4038000e441c4581208400016811551003070091800c031240050100e50380725520700e07024000d041d8520a081c4a4011514100d108600c0f0404120020070000050751518905103400030340042c4101400040587d180c00440014a140581d074422032050310a03441090f1030561003914010030030740d411041210490040142441447d112a08802c60021440d498130032603403c4c024a01035420007039841400d24007030005000e4207244050b904251130240805038440d00c10100e00b95078038005540c400350850440840c80358820508550074040501d0110b0504cad6490701003900b540c00c1030040d5102e04174600c0610285603050720a00e001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 328213803 1250 328212553 328212559
    0x30510060203031311150703030614030303090a0605090102040308070602070b0117100903261501030c0e04021e0d051909030e0d0804080f0307020f181306090606060201050603060105 80
    0x81c0d4a46000700102c124081c0d040101000b5489040d0745c2250381e0f210130318190900b020a0076031a8061402e00801510651045400b0a00803e0b81d0b01c000341408030480703114000c0c5c000145481070246d0341e070500502c002461540c15541c02e00000c000107030800002e11a00e8050000580ca441b02410b0074a0040d9040e40a400d10343d100303040a120910001c0740031404000e4180300003440c0700c1d05045c29500a800c0303508607251404a201c08280c81c011108620b03001e103c50040350790400e21140c00550032202c490b8001008a5081c5507034540e1440c0030f030024012a854803150780c1d0500304441382209580c1141d040b04600545410401140400a17a02d030070b20084905400d0221a000d80c5000c0d1440035600c402c41d002c3c40508180c0d0f01489160b0084074010140c130070031075030700351000002c081c1c81e07420141040f4410354024500391030b1b501d030281d00310100211a411600c156190040c10300042c12000d002110020f445814903000328082c1d1003000b0003810301c2c0d000458945401da04060500b0390503080188 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 328215053 1250 328213803 328213807
    0x501050a09120501060b070303020a021209030a1410020f070308060904021c030309080c01150b0705031218010213030b060a0b0307031503020d0c0e0702070e16030e0607030510060203 80
    0x40c105070712080001c21240580201101a8007904000d03024201c1c9800040e6a01000075400d0308040d819401003100010550032384005400c01441100944504540c0580c1540309840e550003185050022883e4030001d00c040b04c05020810154000f40c7e0030524a80910640202c1c04805041d00000340783d5000c4400c4a00d000c841c9070503800104001141411748840518085009080600a6001000442e04010140d86441d0900c5065000e81900c0384010101e00b1800c00015081602c8016034640aa22001460400030020070010f50130300014410031003e140c032621020b00e1b000c28401400d280d0207071560401c1403400c5040070110010040c20f480e0140e00084820841030b0b45000a0381d0304040503240200380d400d441000c0051100198001960201c0c5440140c0c0800c484400d81508450f10009640c1d550f5440c0e501c1a41c0300c40349072044c83c00c243d07036140c000782044000304021001c1403264140007482d00c0d01020682c0c502101101e207540801e6071401440f02c000c10021100307004000600c0114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 328216303 1250 328215053 328215067
    0x6111203090a030302030c09041d0111090901141f030b0f0303120a0b0f030f060108061e13150e06060103060504060501051803031903020a18060507020904080d0204080106030507050105 81
    0x3591070b041c0a00180806502102003034038100e03003008403204400000e109020f8001c0003100302084104040501941d5840c01c00d40c2913130070700200107441d49104001d20704142c03a80780078071030b10306860020915503024428241d1807540002444030070103807483c075680c000f035034000031021700204515400d100c0d40710760f10901440c8900c0704103000380c0350701610040700420160440c0001c143c040010b01c03030a0b40d06003e25030404801c11300008029048406003011a009070f254170610380001c8201c2034810480354200780000d008200303181d005d01c034401c2c407858200030f001c0c07540c00d040b030121241041d1100311038016405012040d0f0741070051030007510088800304001840c2c140040c1407072040e089941100c0300da010342002c0c1d81d0b0701481900d4001c0146907440c0300c00080c1d00d03001002540013050140203c0d404860034403508c0107580300041030341e0807034581350320740b80c019020000c190742d0040080341c008004100c400d4030b811ba540043d1005100050010801e40c0c190314081e070800405030852410032a081c4566 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 328217553 1250 328216303 328216321
    0x8060d02060316090503030f19090302030307030c02130e0604020109090e07060c020307030519150605010f030213150903021e0a050d03050c01020708030a0c111b030c0a06111203 78
    0x583e000b211074100d0790b4120940b40d10548031503070036900159060001051540d00c01890314003c0c9800b58a041590500350a4030310140c99001c110b00000c0c1d09030303005006900010f80600700e4841c4150000b0a01c80d01130b171120104600381e986a070001c044a0304400e0a200865800400280c00761120900a21001040300b1400da1307104820b1241c03008100f640b10300d08042d500e080c40568091b41d0081c040d01d030f82d410728109110001d03101910485135250300304120100f0481c0b500c694400d88405a441c0b1020041c4400200c010f50003003041c422034643e4514000916590098412881101d251201c8207214034500401444e6070a6118448402da407503080d5040c48c5c1c2d01c014049090318030071114800c07442150b0408403950b0250700303014503240d031001030b074070051180301c074060f520400404c1c00a001c1e0300b9161404480c0c40b04a100030030326642c04403000508088844401054a40c8085c0840d4034055281d00011200c1540e580020b007c01c4c9000c0113510a44000d0282d0303101c0100030189186107080100b00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 328218803 1250 328217553 328217557
    0x301030623070e21030706020405090115091a0c0a0302061909020312070c030606081b010e01080f060f040501090c181a0a3005130312050601050702030a0b04020108060d0206 76
    0x5052083c0f15002d18084800c513060009180c400f5120101e9456001724a400002948107002d014460030705000002188078080ca5a03003980c40e0169250b01d440b61078010340240382080341c205c00022080a100c1120703400360402c1940030a502a034000c1910381807200d058081d1070501110b1040503424003010700e000d0703200012007100421010030101c3d500c0380e0604018803241d081d03420003041c642c140000054092130019010b04a00041c420300c5a8248140d0010344032001c4c1c02000a01155504001420340003a42d4202540060041c1040c5002c100e0100007408032103003600444030306603840072003180042d23014100149031191032035298038081c1071001c00c04020002c3c1030040c41c0c4983c00115800c08610407808202d291641854641d80040820722025250b40b000c900e4082982c40c20000502808007a10707940000740c0c05d9102c0c918451406010703030024000080205062090403c00000140c404020751003159024070410021402c0520004000c100301070f0001d4480d680c0070103a1405a5070b2002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 328220053 1250 328218803 328218827
    0x20f190314060a1214030f04030b0f010611100f0f090303020319060b0409050402062502040c030c050d09050c03121206010c02010807051e030901020a14040605120903070602030103062307 82
    0x840c4d1744420a03601c005502d940b00b4950402031500340414000104030341602201d000c0c001c21140707040180c0e02c501b0308a50320780c1c3c03030454298280d02c1001c1b9205c0034610f5a01281c0c0040b407240003c221a20000e801c04c8c00d84800c4802203002980c00800c01c820030603032485d62a0540c15038101071014500c0d0a003100290302503402510000e5980e076000c40c0455840200b102d03040ca00860160000944080510710f140803c480c05900660400071000003480c401e114070b0520109645070b040c142035200d0b54100c001c00c0e42c40c408968921171500c0c201c00c1c1e40d03801c12264048103001c450032030313071001c419140ca0301c459000340142c0d050000c401c00740c10043c3c1c0c22242c06640802280f400c2515940200700e40754840300c00c1c40d040780449900006000c040c40e01900209802d081da030300c510326416254940c0d8140e500c2944100300000c1d000784822800462a0300440e50442c5c803a0048038184003003030300c41b001240d20a07402100c1c1d4541e22014000701000360907008052440e4000b41010f07510381840c1c05450b0540c580 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 328221303 1250 328220053 328220063
    0xb071110030905060411010e010305091207020102070b1b100608030318010207120503060316050307050d030504080d0f120b090f0c0c150a0608160603020f190314060a12 74
    0x11008580032407007540001007854001d0700b02c2c2c1503401e0074108855407000a0014900040b94041842032035400b9005181c05030001e90001e01503500c0c10520803206030003405049045010f541800203920001d580038205901f0f401602d420007400a5403554038210b5290010f40c1060305003c0100244400401038941c4040e5883ca410046a07480e02610b00900c64601e004102d5031080800c1d034061a4808060343c822074040c1c044074411441038030b040c00e044c54284603140d85030b03100c40001e0003281441d80906041c6d40c460309100c0d04082d200ca01d6603080500001d1940c002030480c1c3e00016155a201600e09140289284108903445048003c42c0408030010905408080c000e40421040850441140e041c0d99940e0165000d002e050741c1d50746011042541c00c0000740d8281701700426010800300e50782c0c00741202e54119403034a51810300241e010f50484074049120007030500103000c0d040e00441035100703e0000303a640050580c0000f0844a2203490180115005445880b42445001e641c2d400b07244807581c0007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 328222553 1250 328221303 328221319
    0x909150c0a0512160e0312040308180307060e130b01020303071d0d0b010e010e091b04060b070f0c08030a09031704090204030b010602010b04020306010512100503010c02160b0711 78
    0xc1105840d14443c1c071210084a1294404004440041ca0140d40d00c41a1a6135000003000e004c204255981d0700441ca40031152030100300030000214070000801c2d882081002101c2d40d000d0b0b80300024107102e000d078400008a820300303109200d1441d00c1c00441c585110480d104000080c3c0440c0003e603a404024201c0041c800f840c2081602c0a980d21503132180000010104140e082540c540f4091034030b000c0c41510485011080082103214912858070701c2890703600010130407801001a040590410019941c2d00255170348804a44441c03801e00034851070b405000025040034440c9094446116142d0240c8600d0300103110382c1c2002540010040700301c2e501300d121050924096030044201d80304960254041e9480064004200158201414106c030880e0300200309100680042c00306902c02190710701e000030002c00410900c10048401260000820140d607003049440e1800b107403c40d50404042405a80583c103a022a8a48ac0e490100030300b07085036100d42460400d6480c28100135864958a202d9404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 328223803 1250 328222553 328222567
    0xc0302010c0611030a2405011413050904080a020d0c170703020c03010603060b0102060a0b09040602030403020a020409080c0c03190803090f0d03020414330706090b060909150c 77
    0x201e030300004000002014015503e082c5081c0d2a4014411481c1d483d46c02c8980c288030b1031141c4c515489020450320306840e00d4200075103508100304160301489000044810010021807541c0b142503076a486140f0034903046179589100300d000703894410500002010000d0410290340020702082071605960054001c0684800310b81c6401d0342000400c559840d015803a0200000a100300c0790030250124000381c083d10b910f070315a0604d00b410b6070885a8101d404c00410400300300000c115600441d8824000d10540f9000344680c0d00040c182e80c007016040e2081e030408500c04985070740911a94070059011401172143c003102c0f02200300c288420001c050701a10b004130010350328580c140f1400c0340403904030381903689120740700c40082e0080d0050f0141c800c10345843c0500110300e08248040b00e6142c032603850f01032207190240c2c0003481c1c01101a5603190301140248100380018091340101407020707204010700b540c54601081400398101009000001c00d07480042150180d4040300c0f80e0ba5001800031112558502c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 328225053 1250 328223803 328223813
    0xa05040c0c0618020406060f0807050913050f04060605030c030c06180604170d0503040f0f02060d0906050426030a05070e09160e040e1f060b07140105130c0302010c 72
    0x851110160041d4108511449120300100d010340026100f00c0c0c00300704203611440203c0c2c40d50241380001002c41c000c27001085d1080d0140001e070203442c0004240c4a0321b2100b6055210503160144c070284c0301000144240300400848e8020300000d0031041d00104075022035000080d0740c1e40d24044800d03001c1d000000d4800034400000142a00301c150103000543d4031a81e54006142d40030103031240210364000c10401c80e0000f07100320222400745400072500300c811165074a400920b115074240c03caa01c04010485110720450750b0240041c0a4015600080e0714a0603040c0715068642d1101000042212000d01c10488014081074a40200c00e81e000003c055880d071805a500d400e6141000f5441003664007040404c1c0c00401040320541c00b10741c0c40d00074120b0700c2d00610040e01c40c01d008852031500801c1c040003070b9900184c0b00a0071100d04a03c007280c03040c2e482e00300392a2580310b644191103140c900c0c004d40e01510002d0092903000045081c0340842900c664072900102401400001e042001082d41c2c0010300c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 328226303 1250 328225053 328225067
    0x1d060f09060706050f070801050a0b121f060215090d09180225021804020102030a2d020607080708040f020108130b0f070f080c0f0304020613090902041a0a05040c 71
    0x2039118900b0001350a010825515031101203a0400001711482e00105250030000070030004c480c44120f200e07080000c0c500020036848401443c0e41d05a0b001107449a42001d1541c40c21070060481360003608860401c0070007402c10750002000754078330750301648450309551791101c480c0341218000282c2440f030300e59100c44100030380f00341c0e966070210744a0035112000c1c0985000c0c524890324821240b030070301c1107202038003d58040011640a409600140f00600c41103002d0b0500600184499a505100c001c1c4d00304141860a0030710780c0e440060784a002006000341c2c00030080c0d60054000e047c503031510324099961540d00c00035158000e041164a2000c2103c1140e20807464045a40c1300f0141c440514101088804181742101c100c1c0010b104808190040da00680782a401030001000d082d2a021803440c09615903031020788100d812a10400040c42443e0340303450b4a00c050011900c000c259402103004010035903100c0d031540314400c4102d8504a059a030b4070110f0104407034003a81c0c04a002c004107807050301c0c0d0b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 328227553 1250 328226303 328226317
    0x40303020708270f1e10110601030b0a060e01290912061005010c0b0406110f0318010f110a0c1506080a0605070201140103031116090b011d060f0906 65
    0x109880c4100c50340c1903079480c3d0f200d290984165000c1c442010f008003003090310798550300104029003a2103c8040282000c488403513181800b418444640e651015500303140c40d01c04d034426140700c102102482407605142c06000000c2c10b140c071400c102941003c031100f440c01d030004010612108107101e0340c00c0d5110f200c41a03d00d5503000600e609480140300d150346403035180c225541e5150703444d00400440d0755801800ca114060344c002007282c92582e5140c1c3c80c0e10041c0901a1214020f00040c040c0e40281c00c1e0500003184100b00103030614405041105000d030035110301c0050820514104004894003821180650300320249134600221441001d00300003200c110403040c5030400c10700b0f0400108154034001140c4c1d00c0c062040d1070800c1140c0d00c8074412400ca480f2103203401d4800f0010340040001c6072162103000340440311072082ea42110704c50a818226042a984015021615440384050030743e00042001c2079200f042480307261260a505c009000e40c0304448050084e01e00104410001b80ca03080181ea400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 328228803 1250 328227553 328227577
    0x10905011b21020a02120102030c0d0e0a020301020a0908060c16150b03010609021c0905060c0708090a0f0315060b1e0d0e0a1e020604060309110a060909061d040303020708 75
    0x2d00d011045000f520f031104244180d008130301194403004440c07014400c80e48503070442c1200d1820035007140c0d0480064480a011135509104292006000d41e4003880200180d030015140c0c00c0e07803285000d25850510344018003850581c6800e0000351489a4000d0301a0102580161410541e2a0126003500105214551160150303e00707080811079040320303401002c00b0a440410803c04ca0301450802040e21a13440c4003c007544c100310040750240c03001c80068a8040e1042c41801d0401c2140c1000c0b84e2805610380c001d00700d4441c2248200148850740741c221102801c0400c1c140080d6060604812491040918045003014205009102c0d010541c0c2030f16508011403000384104041c45808603a1072580120984a03018026100d1400d00343c40e806030219180e001e0007190401c1d24101c1c0540c020f147c80c2d41c0c203a5500108501d3300383d483d0349100000340030304507a0b110b03150070500b001e8004048a4054010b0500d1012100c6c07009070b011414003407144e101e5410f10b005a46d40310140b40140c502c1c02580e0a41d02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 328230053 1250 328228803 328228853
    0x40314091807031e1b0c05190506180c300a111c0f0b0c0c0d091406040503060606030901061707091406091906051507020a05010905011b 60
    0x80541c1c10313088000c980c4c0c203030f2500a0891904004107011600032070b07560310b01035400c10300c007604c518050348807075440030f01071801c1e81c0f01d00700c14102e002041300004004850640000080100410349040c0c00d500000782c40d0700404141c81d108d004159611454080621501c4480c507071b8150070400d81012041130307500002030b20034101c171030b2900400042010510a11a160300c80129202448028060261030780204101048002944811c55900e0001d8044a04584100404a0800010895160403d05540e9205c4506240a07102c586da8504000300b41c0c41020200020016541c00003078854000008903081d659a85900001500620300c5038044020525440c0c0c00d10300950000c2008821122082d01c28030040c05608015180c0d440110382d250f5000c0f500350003003002200e007042d411801500000c00000d2664407200040c45c240281007210b0710300c190028082007182007100c0f00400520080c24512351507800d08001034030800e10340020720444064261410103000d00110b09080b50310000400300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 328231303 1250 328230053 328230061
    0xa0b040b120f0705090705030f07021c021c1805040b12160f0501020d091205012004140a080c0904030507020a0b0a020f061504020c0c060406030203010312080403140918 74
    0x5803a0003480074040c0d124003c074072002402e403c00b606050701c180040d65480f465035071900d002c42e900003005060a01107104d0810007030200c2d843c20700c4001200b405500109030119440395204a1243d5443c000d0b0204804400b40c0780380003a00c01085402d49004480208a000d103c8001c0350900c0f8001038400c0c084c0c890002d8600500104264001c281c800f104003c100c5c5039110001681e442000d541780e8400100010401c100ba0201c40a081145d14820400850708032420210740c0c40f00c03404518038400d66a000601040342c07001b00360307403a00e81020540b80700790407616140c403058441810300d45041c0100400c1000508042c0306800302c4010ba5402031030086255140c000710146900190202c5001d0b01c030302c2e05c003406011000980940308501080c00c0c000e25400060038030000c1e401412402c1d80030311a0030490320095031540007600290071195070050b120341c0755040ca00500c0d00c3c1d450403441405100020710012940c40540100d10704c40001c01169036900e1180401d5200441c061951800400c401c144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 328232553 1250 328231303 328231339
    0x10e0a03060b0a0902030403020a060504020d0c060e0f030718050c0d14190b03061f0801021606180804030314040509090d11150103200306040c0504050a0b090a0b040b 73
    0x4070b42c505800380c803501c42c01038482440710100e00c400e44018001d80d202c1341e0410b0004040b9006940e20510140c10b803114542030f03070b5070312032149030a8116001162040d566040c0c2400c0042c2492528501140284900392400382e20451800c075680d5030031140c41d00c41e80041c0d0b07001001006c81d01c2011080e40104480d08080c01e84010f046c00c152041100c0440ba6601668502410b000d4030b034132100001c01920090701c1300c541781d0b14142081416090300000c400d9001231040820701c003400c4010320f0303c0c3c0003015a41300751410204480005104a520821055a45001c02d40c004191019a541400d15944400c024120841d06014607840b0390790002c2c814041000810010031070303a04544c6c46031101349500e080403074082d8031500b07004144100700b403d060040012800c000032422105030542c0510b141402e24401103800c00e5001c48080d1140b003c50113003000142402e00c501c90340035070b0100c1d04001a10601002505101028101e41c40c01d5803540002d490750b50311a40581c24000009262a10440094180b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 328233803 1250 328232553 328232561
    0x1306030b03010c0809100b0f190311010306030302070e0c09060319052a0913140412080c031602070801050709030203070f030f0f0f0f08120a06060504050609010e0a0306 74
    0x2059001e542040c0004071240c0c01201d90b14000c03c4880d0140503422541804203000341590000c4940c050203424047c0150703142c0b29003154144240c400c90142144c19400c2040c003048014540310304141c0b5100081020a50128110341592105905200d003526103050318503043c0208150503902141c00410b0280361440d6800c0e01483c2c032440c2c0420720203603a07103030750400c5480030520b1000601c681c881e14040c00c0031300c04c60091690100007000f044000065880210494803040c440c03d458403c0b190610040c00b070410a95100192146001e08161034004a00002c1c0d00014102c0783c8180603011034414040d0092101d00040c2c1084e400810140ca080880149101f402e48410fa0080c042c0450110b054030407410780d842541d0300b000c0c0381010b0f1103842c0e84911030400416400d4600c902d40d8440500011190b10040b0880c900410009844888100c011440c00c04054014000146056020428903030000c06442c11a00d00f01c8140d600c07400d00000607a8680d030000c046070752003140c0c01004001c200442d48 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 328235053 1250 328233803 328233821
    0x30a06060f09050f190b0c070305060a0501060f0809010e0d02010b0114070c05060f0f070f0201111b010f0509120a0b0601480501050402030c0a0b030f06030102130603 73
    0x10303031252100280101902d09480601a854100c19015104d1035142007081c40080000e45401d203440c0565a1184900d05a41080208035070305d0300000307000c101b0b100c401c01c03950742c000603014420000c95141000107000784442050030b2050203141070008010320400e50040f19000c1050703003541c241c0a40074400038020050600300a0115082450b001030441b050020b4032005a841070468030f0407802c080800426030002624030b070742e0001c03c204594103544e051020b00380c1940b003103800d07181c000321920002d001c020301c1401c5155641c2c011045140030507a40c11010345a01c1080c03c002c0004d03414018112998070980d58099041409042c840460150001307031031360315038000d04111b0f10603100c400044170315504215161712a41d0301c01d1030143e0451283c44808400803010040201400c85050a8ac898652142c40c2034400740d644808120650274184150110304108072009250300381407014000c0e05010150070301420420700e000003140d54a003503040301c072108101c144074050280d4500c0c0080c050500a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 328236303 1250 328235053 328235057
    0x120d08070206010906061413030f050102070303110c0a020409020103061e0f080c100f0302070c14090a0209060d0f1d060414071401120605040f021810091e0902030a0606 74
    0x2d0000600c1c40c618807a540c01d9038480d5a1301540350142419241d090382040406081c0c1c240301c0c40d00040001e9400d040742c1d1042d8071a500260b1154041d0030060b04662609a13465801d02e402c0015003500c0b1004944160110b9040701c0000305031403a400120000c001580240b1400415060040c060045000050049818003048400500d880300301142c4c51700e9185210346d8011212001e00d50040707019510001c003004035403400508002603a00c4401c4508050b5125000c4926031841c10074060910388415a840b40d803c0c1342c1513142c0804c00c00880d407540b00f100b0078160441e0f6202c0b482410030740613800920012030403070010a043c0400c962000e45070329040d9401c071120300707280096000820300810904202c4512440441c18508103c00540360750016850401481e03541d1200440c45036507a103c2e170010ba4a000d0b40042c0c507031a22040e04c6454081c908a05031142c100703440c1c0800c0181d4400503800560f135110703000c01030001541c11203581142c0c80c1c1d040700c0403850000c4200141e000090340140e08a40090f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 328237410 1107 328236303 328236313
    0x92a060c050f100222030c0909050709060602011d01140112060b090403021b0409020f040c091a0a0e0904020109090c050706020403150c051303030e120d080702 70
    0x20034214480c580e02145800d00041c01c400117102d04088032490319441e03825501d820601c0d0000d44514400551610080420420180500001007841c10750600241380c0b6414040e0107803014102505046200308040011030390140240004048490080140c50342081e46a0000d80c5d00c05005840c00c44e01d56542400030381b50340e4089031045010364045c044450140425a242002a015641c031690600c0840300150703a8101c49200d10704070860700060001a0401c050b145e07610b60380c0c421800580b840c41d010115102e490300400007110541d840b008901003690800404480c00d4402030700181104406002c0312495502456544100f41040703810400d20340d48013002c1c1d9000d500110354150740100140e030004694011103000700990f0501c282801c03070700c1510314020441884054104442e009958056031651801064150402c0068907c40b110550025181e541d080d60030100610413 = true := by decide +kernel

theorem cover : BRFrame.Cov 328057553 328237410 := by
  have h0 := BRFrame.cov_init 328057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 328057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 328057553 ≤ n) (h2 : n < 328237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
