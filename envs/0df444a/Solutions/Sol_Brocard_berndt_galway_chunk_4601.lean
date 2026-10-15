-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4601
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:08:53.465802+00:00
-- url     : https://prove2.me/submissions/891d5b6c-7522-4711-80b9-0ec77f7d491b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 827338129 ≤ n < 827517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 827339379 1250 827338129 827338151
    0x305030f032e0302010801090504030516033506060c0a0b0c091e03010f05090703031b080c0f011104060c030503041a01060c050f06090607080c1323010e1e010201 71
    0x82460202e000702980d00021042082d50b8000c0d02060060018001c1807006160590b40101203200d0120080c40c2d110804011005061085500152500c010000e80329629010714134ac1c0c51001440030314060526002c000a62070b41800b10a90b540c00c0710800091403500c2159480e44440c12001301f072507401901c1030000d4480c9580d503002003602da01141c03804803100107012007454213540044200044850030311b070a000c1003400c000351120031240c152900c0c81490703d90314100049041000ca003c1c1c000f5a01244281c46040045030398024106c490000700003440342c1d0743c030340341d89405280310700004541c0307580c913a0300806e018100a5030f010b4490400f40d254040310076103145c441103003a00940e0014406416074000c01c5010001c411615412000800043c90f10007145a07030740700001c010b0001c001c0342c44045500400141c040d00c10710f000042180107290f07222460b41d07040c07140c0000c0303028100d03012030782c00002940248060361004c00003408641d0a1f800c0020400ca10000d85511241150b43c0c0d80080c1c44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 827340629 1250 827339379 827339431
    0x3090f01020f030411040915020a110703030e1008010e010501030902060712081f030804060e18070f0818061b13090614010815010c06230109150305030f03 68
    0xa03082c04040c2e002626410300b4144017682c481d984148902851501981101080303511124950807000e6120141c0e0b00d42008108440c10184007404600071b2003603150100816030842c4150741030b00400e8032031200800d200c51045032055000c5c03003024220144500184155407291300710050242c006000146060015507900c010034501840803800240040f05010200403405051040700300b0307450300301a015045498017074040c0b1403880345c5e00a1244500242c0019100e0ba020748801e00b80711200e000c4d4601d4144400b905400910300d4400010f60408005540c0c01d06003565110b5964241c80140f0441d41d55007034078841c0300110480c3c40c0426100740105500d00c1c00002176078015054031103003c951503240400d0907941403a04100503050020080400c4052142588401c3c0030207400d10702044010110b0a14000403c0c02c603203602d0300c0382e03d80e0300c4455000c0408000c190480b01c10340e1041003112001745100300411840c0c000101a0781042050180ba40c8100700910b8100f0314689041800c3d420b212144c007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 827341879 1250 827340629 827340637
    0x504021807090501111f0510051503060102161d1b040b0403020a090203010506030a0504021309051b1c060905072402010c080601050304150603140312010f0605030c03090f0102 77
    0x2a0000316000818089942d005e060380d041404050002d2000090f41299204440c10704081c0040340f80d964000a142820303402c0350300b40200005060780a441582d0005403401d98000c9846901500c508414166040f0001081004680c4018160020100404401c0d10118406016402400403000d404101d01d90010010401404d100071026030740c0346184140007205110f54070040245205100400054440720201c030307400075004c200054a9035842c800540503450b02064044106d15103000c1d40300b0460f0000d1000b0540c1c0c59010031002018092003084071002c0c1d42503000000f801d80c1002200018229000750f20001d00c62019204a961242107032004a4083c108640089003d0f02d0090480b54082c49a00071881c002e10381060545040e0001816921001d080281024541102c9031092041c84d4080c1000d16800200102c4003410307401403c4e81c2e504840300000740c00c02d0380000050316a10880900d401c90b54540c45490031503560429800341d030f17000100150300500581d502c4c03001d4040c085c4010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 827343129 1250 827341879 827341891
    0x3061e040e0a030905030a0b06060a0201090506190b1009060f0302040302100c030f0302030105060403110d06050c0d0c051603030203061c121403091b01020106030206070b15010503160305040218 85
    0xc000402d40b03030038004d0010b10a6805180a50004010100841c800070300301c0754484400c3d104c4554401c1d41c5801203004000c6480050f14a018580501965550003a69901080d08002040c4040b0b4501010402c403400202e50710130102c0c40d420740070440d5070b000741200c0070b0a0001d8107005003440c0d501e8011400c0320a00059040024900600c0c000415030002c1c3c48050b00300d90741c603007181150f0406001c102c40c0d2240d400081c19441d52a81ca000315541d601d00380c07035a8186e10510038042800d02c41c200030b0f200d4220040f00442c841c01c0100c82d9440d684580107503181d540c00c0703e005451031546914150020340c00a4901a045010117101d41c503800500c113a50044d09100cde008182542d440d401d001003110340d9908855240102c00c00900040000c0020301c251403c4600002180c4095171000507801090150b200940201d030100c0c1c280284006111481d214a00742c4002082d94542c0100441351880304a42c0848000840d415061005100b5408150301a2000c0d082407240308200812944010003283d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 827344379 1250 827343129 827343133
    0x50606040f0b0703083702190807090510080a0203060301150602150610020a2010020102130e130b09010b1503041a01121b170f0c1503061e040e 63
    0x80f00b01016404608640e106221440c080c1188104e00f000303640a0b103000c0651402c400c4c54283c01c90b00980030b54105c0c1e1400002e120304181d100f8011102610706c11045a014000c80e0178410300040a0400d604074280c161000c0d03071070f42c245550700c14940000b0340000e04004d401d50750716032048401050610080001e8080c5030002c02440340d42c3c000710035a0020040041d801004140307485030315540c00043d000c00e0f840e8004150350200076040072920641c00001d200c01c3e80444400b041c0300b515a01980240b41001d11501074444541e160034081144400584054024a5840c5240740101c1e0500c090350350041d05223400400c802c3e5038400000d005110040400e443c0071000001d0200304003c10003d40e4494040d0a00140780b9850082e0f502c1c082c1501c2c00d40603003076481520210300c0c0044800c14042c0940308001d01da821104408038003580d102c071401c0c0b89403c2449080300c10314a5281810303071f0742c064800346441e640c60359561344140403101410f94040c504541c1c242100040f2540c4a0160051907950000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 827345629 1250 827344379 827344387
    0x1020c070b0f0f22081c030518160e0109060602031e0d090804080f0604020f040e0c030a0c1d060a05010e0607060614100c050a060c021906021207020c090a050606040f0b 74
    0x110482d05054a17070000000b944a145550f44543c82d03040b05000e41c0030581400169999419444100d5900003a01500b50707006e9480c10b0a26103e0542610080d20540503140a041e170300c0706205812207060b03024140c0540e00074400c0d51445010364076180b40300c0d000400514100b10f031140544007a24600700040324000c0c804034060003107040400c070022030508084020051400d1a0b0003089081601c02071450003103481c0c10075502100e1041042c44a0808040d0858102c0ca16504109100381c000d4010b048541004000400743c07001446003490050300010f00e900c06075403a080054512900c1180d00c980c1000e070511036a0081091b83c49590010035030f2464401c00d82c0280010400003040c0030a07803006101c1060b250b50b000c208002442c018080d8030823030020304007050907401d074601006401c41d003004102c902001c03000c20035203402500d02c000b1140d08014451303c40b10320690715001090071898000800c000003070241000f60300840d8001c20003410841c034041d11400004172a50050b0010f800700c000c006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 827346879 1250 827345629 827345677
    0x504150c02150712110a1e0b060d08030f190219031113150306030b0702160e090d0e0420180901030503030406050405191101090801020c070b0f0f 64
    0xd411a0408248010035500c0d080383c40d0784403009124065202c500b00b056210482500000404c900910380750450384045000e880346003d40428141d80c5411501e10b17907018081034241c02c1900003400440e50250075181144d03078102c01d0010388407008107a030203200245aa0341039010759910007404849400c10070800b8502460342c024040d0703030b00d2a550620380d1204100c440160140c11315424155941e001c2000882201114100c01410380c1d0380003d02504402030a00c4045500010b0f0400f00c000e41d0300c801c58a0705d43d60b030103a85440b18120388180064000b46607104101d8030810b041c0115800040000500415031181105c50441004480f200d003100055050001c1300c406105105070f0004645100a41d030555039070646030700002d08010a1951202d020500f003040900070342102c2c200e050250b00d043c1d901030421141c00c1c4031115600380494518000825105018001c071011310380382e0402080d50a2a040c8242d88070382c4503241200c45604240940c484559180d001403e01c49840081880317806014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 827348129 1250 827346879 827346889
    0xa02010f0206060105090409050c3705060d0509010905030d14010f030305070308040321020306044a030a0906080702070e070507030309140303090d09140904030504150c02 75
    0xd4403000350341c0a4010010182ea001c0200c50404a00390f4000c45c0c4880c10f447e1491815501c10700250740a0360b1480031414044030041800c8020950154805010400d9000d44a09806a000b4130b5001842004120403401803500720307030b800a4201d4000103003407440e48c44440c02c542250303820000664440d902003001d000c00614040c0509159452040d8007459941c02170058403174a203004041c840500d0008042c1400340e500b1410204450301900d00c88812049a4402580200c075010b128915051981c40c601c422149150585603107503c40240181d65100b10703008041d4490b991000700b1115143c55085001d040c009031418a259454420a40c0d04001c00504103a000a000b07104560201d0003c111000228050315040308550030300c566610303141e04003100500a4004050b21084210090a83c010000401140b20300108400d40d280c018001038100c590042501c02c45845002074031000318a07152001020360014401d003011840c0554441e1614202442c1185041c04604440010400d5040c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 827349379 1250 827348129 827348147
    0x15020c0c0121090c080607200c0112020d20030a0b010c051b150705060907140307032307120c38090d050c13050f04060b01200a0201 58
    0x24200110100c00d00e0b0406100080e64025044849884050903004c0c400b040e03048001504889081e50410720f042c03100a0304021020903c0b030800104c04101c8403130354002194103042200142e48201c49107800060b0740004e5000b84000790304455942d0030a210140b20301d03d941c9620700c0712000301c80c0c59207400f012100488034915000307030610030400c0c554000100c01007080c1038402d130030302c0c0408014a04400418000c1010000044640d02c0000d501c50602800055551144031f641c411103403d1303601d813a0000b005030640d80d2aa50103612040c8240000b4032003050b028111401c0340e00300803280140c1e1401a01d00880783e40070f991428081c0c900242481076141280028001e51002101c07002a00f03c0c0400c45800c504440c2d030005a8802c100d98980190401160b003560001440c0081d40d034118100b9985440041207454483c62403030601074075010340303400381603c540d5107449141c4c9030759036a0701c44030050120840814108035100401c000b10b170311858510184e058005004040300c200e548005020707090707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 827350629 1250 827349379 827349403
    0x2031c1b0e120309012a0206040e090d050436022a010b010813020111010e010605011b050c0d0602040b1201030b0f150f030f0d030c09060503090a02090402030a15020c 73
    0x7080032001c4c90b608014000c002c099403401014000c00414000083c8840408000754861400034000a4010700e10300c840703020b10010030035100c0c0742e80309400940e001d00c654410b000400103281200a03288404090090000409004018411f0031502c10f150481c5d000d020503818200c0e01c03110f221141400a0490000004004002c0156000c0c120000c0d281110080c0010040d0403114032030411644910701461052406100a01c4600619100c10b806050b072402180e000070314072803030110100c541140c000002c9070048054200d1110b040d0910031800049841138903603680130040007400f028180002d201000500c3c0c941c0c03182d5415440c20402e9004090318106501c0b8014060001c800f482c18561060101c085030180c0000504201281c10068180401c15440c0035420008c074074650181c02044001e081030341c078210b42c00d1301c480094440f40030544000070300fa40601c0c1d401d40141400100303a40c01038001411109501e0042d542c03c41d0104407407405d03406c2d01c0d0b000303d0100f1340c0302010006611210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 827351879 1250 827350629 827350633
    0x807090501031e0201020c03010f050114010e090c0c070f0608070323060906030a1509020f0a150c0602070206030a0f0f0608031606020408070305030c1c02031c1b0e12 73
    0x75155807501c0348103442d042280035030400070340c03180000c681c020000c242000c40c000e4024813a0000001c25400100000d114415515265501c01c000030340c03084c54620030010005080b41c0da10f4a0750300c079003541c981201013400740030310440c0404500c1d03400324404840103240c15580c440e5145821540207054034080489103500385410f480c1600c0d208000c068040d404501560079403003030758400780020b15294080d080505401c0019056041c40030182d0004903c41b4001d0700e100b030302504000d017403001c419240e1003804282d6140805d8181560b125003540042c0c1d6000e102c015080c80e0031500099065403050b03460f503a0040e95014100c003a07201c2e500039040050f49020040220520340244640c481c403a0941420400c1d03500c00b42c40e01002116070503075000e07006c01e004581100e9168a00583d40703600541d98450f8a1148141d80c030100c0140e540d2880758503507281d01460400141001c4036882d400c1c09102d02c4840c6482d6150070b00d1900c54103003110711002159850044c5490f144003131142d00880740e2048076540d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 827353129 1250 827351879 827351881
    0x6010c020312031f03050a0609020a21060507051908040c0512060f01230120240c0712080414060a0c0e0a060c030813020405040305180d0b0c070804050a06050408070905 74
    0x443c0d1b000c15240d60a0340c202c1e0011038031407680e10015060b0013140d04600404080e48210a00f6540c0d4010341e903520038829042001292180b441c1641c81740550f00c40100300e02c02404095420754806c10805401910902204540036240c1001510103d1181d04094523a4410f50410142001c0031901c50700511031680303644101c1c0860041a601d0720650165181405001010200612064038200600401c80f9007034406074144105200103d05450703864a0004070b804c3c000c2014080003030201d5005a03409242c0b95003401d424801a0b614410050081d9009020825080c0016006205041c8180c01d10440094074040c0442c000c1c00e2070480320310188c01840554000d011042d00062036800e050b415060882903540e039003420780840c60301100001d42250a0900340410150440c2c0030f0488000551200480503000c8030a000518203c60707000b804c0398082c038020a19a01101d0b0040403034500506190303191644030404140001c915610800020700c00050401c4881428803020018100c49002400a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 827354379 1250 827353129 827353133
    0xa0c090503031b0a0606030b040c0e090303040b0601030b030a050106150c0b0f102403110901020c060a0207081f110316053411060412060506010c020312031f03 70
    0x5a0301070341a64405909608064501c3c18404000480746964004000c2c442c030781d101d190480b0400c00c142ca049905036403105010540c25185101d580c895503405006506560725074541e4181100082c20f2181410390703480c11594039860501c10121018000c1d000816124074000541c46482000e603610420000e80070392010000b10b007e50059004085620400744680716201e001002101903801000341401c098038805034802941041c401000c00c544042002100d001500f0f251803140c107010030b005070002c41e192411403411101030f021513401c5104591080e912128201c1ca8400700e5014281441540c1202905400c2d00340296201807005045403421424090320391800b440c6054441010701801041d002807031445840f11680f01c0ba660340d00b03000c8d50101911000d81a220000d800d0350081d400300e9111006003080380031602160b2609603400c55449460700c85100500e4058200c0d070400803040182000350758204481034001d8407290480d1b0707407400e00c074208010100042d80ea50341c03416200c18007000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 827355629 1250 827354379 827354383
    0x20108090a020f09180307150b0d05060f0c1b06040b0703090f0312110f070309051c032a030206090607030b0609010f030b1c0b0c0304080415050705060f0a0c090503 72
    0x41c0e0103c1910056480d85812803808101c0d5508200d800b45480007140440620148000c032666114044804102d0300c40001d0030300c2a644a081006091a0302c9203010407203030b4030013510f143e501001d904211800c015004206035484d0040d0042214290f100c0800d0000740075400074400e811000a090030840b403801c03595040c02d14110200d010b41031082d001d10490700d000164000c0408142a010025130758181c0c1c042c240c0603900705140c1600020341e11b41c00403c940c245925500d0280d11800d40f064190710340d0b40da0841e241c042424180300020342c034042d000c0385c080c20301a01400e003610940141003a840c01c5002c0b14940b0754010215070800d4201487c0c002036484100031101c090710280381115000c9101e40e010782c0640b8114504035004411001400f4200300c07402184000288240c40100f030726140c07c61102030070f0100341c8024182c2001000200500d04900030712110111050070041c5c10900f40d501e80c1c81c182001210441002505030080044282c418440c100a0100d9820b00600035400e1070046a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 827356879 1250 827355629 827355649
    0x3080117072c180c130b030d03060335070305090d080a11010c1d0d0b0103051609051017072c0f041104020c0c0303030a060305010e1f0b0402160f020108090a02 70
    0x1e001e907400040803498016030350011061b01001408460f0380c001401c00080080c41c0324030050780c007503103402144d043d0faa00c61202d6240c0402d024000d1750045000d0b04241c003a03030f4000381c401c4050100800c960316072a20340f2540b100c18140101d00c820346a0f000480c000e002c101c20243c0c2e580459241c607454000c84e81e082140900e06a4612903215580169440031131900d190031940907140e500030b40000020400000350701000c00642c801c02051490780d828041d425a0703401c0d03330402150074040300140034000700c10407030181303031004001101c051541ea40c2180819400c13124030443d820124000e00c602c4000110300e0250442003030780e1608094a801d03143c1100c46094402403500c030b10f400003040c6e40444000c01c040408910010156175403414086480070040c02e0a200c1101c0550030810022041a40030030b18040200d01660103800001d21614040000d0008882d4203a00c558207004030a000344010408406140c81940205c50800d09400007528a06008120721207a030f001003000401610760740400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 827358129 1250 827356879 827356903
    0x31b050a061407031b050706020d030c0806060c120c0c0301060f080619020c03040602010e0d02010507082a031e06061c02160204050f180a03080117072c18 68
    0xb181c0c8902d000d280813102031500301d105011301015502e400c418441c0100711101283d49075001c5a046204c00c100503400e65900c03c804402052a0a0000301903080c01002826154000c50544401400b1030070640c0468014000d481c41a610510307c44055080c248554000750241e0b0502010351850008515920031004003540c500e400c010742103549690440d0182c4440b0107101d001e880d102c0b500c4410080c000d194088242c9045d01c45c0300714120015006218190103648190f45070191582c50484865030320081c40002ca548401c403015807030b00000c4c900042d41c007802d0b062541d1104a0394880d410300a0440203840d5901c00c407401c01c9455406581080d5880c0e880701502c1d030168540c0441c481800c0743d0000c02901a410a0405c0104812040d016010701d00c28080700303181002c40c408510310180d07036000d042c4004020480b000010f12210780d603288081035444c8800c0441c1c15884d02c60440e841006a15022a81d14600403040400e80101e0b44840342e41c003044d45c0c840da8034940c04000000f65951055140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 827359379 1250 827358129 827358167
    0x4030b060d02121c0305130803070503040312090c0302100207081b0f090c030921070b090c0d140d020f0c19030624060f0804060b010507020a031b050a06 67
    0x621401c545a10341c40110710705548007134442600c003c140e0100030b0203058442100080ca400000b40004044003000d0080701d8004030114195982c801040e42d9607400503005500f0301101ea845240c1244c8940140b0810314230460301c0c900030914500c18000342451540f403150641d0045a000d0044240000b8504207242d621a0080d8601d450140800c440d0841c16480c03d40003400c080c100020014000f0066004d00700e03c0c0c04842c08003850340d00e41e10300011841c4984c3d030700100410403d00403908204241c1e40020005084e2088100090300040e038400a44c41c003140c0d103503000d54018141031070501c41225505280c0c0080c10b0700800c100074090b143e2074068075007482000f54450981440050040380c6000e1070780142c0420000608094985003800f100821654410000c2408901c05102e803416803100382903a1906e0040792034540e1000d0244c01c82c03050140c10030009000315405a43c0c2c030150311004600544840b900d003100c01d1006600703174103a6000240185428041001056802a1100361424403200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 827360629 1250 827359379 827359399
    0xc072603122208040b0a0e030706020606010e0609040518010605010e0d0b070311041d0726060312130302040606022a030309060f0307081807030206030c090307030b0103120504030b06 80
    0x556000721801d0204043d1502c0c001090100c0e21401010040c4800c10031511b0740c1d6001580d00c003c0555400707882c0240d6006800841c0800c0c013550140d50240200c48008100070304089210009c90b04070f80c0c00f00c40c010207424201d900c95445150a1041e50060002807030000e540c250201d000c61122403505d1001410743d807160001420307041c400c1c0d01480c91400100c2c04250f855541c0c03803024489013101c84841a81e043d4070408100c20500070203a000c21480c00c10000c801e482c003425501c007a000001004241c140c02030b079406501180c84d90004240c0301c50b0306a034020310f00b81140140804c60740150840000e642c0b180d104240480d07010b6854107592a140c0c03806082901d440800300e81540258003040ea044030300800d03515460071994000c1c0d40314280ca50b503500d06c01da4800d800d00e90a84080400c10110b034005110a0015041000c02541d201034000c90344e6207409501c8003c24030f413140c1d80d8010b84100a05400500030011154001c1500369460b2030403500b000c1c1503403600f01c0400f1000d4600d500ca80d8840c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 827361879 1250 827360629 827360671
    0x7080304060204030b2e14040f0603083601021e150a09050c220209061605030a09080a320d0203130603110f07080c07260312 55
    0x14040301c1c00386038010300328211410251a1b8404c00710202e48560501a018005500c3d0f90400c090700e182151500803075078440070412014440201862800428500e80b5540701001040660008083e0b51030703a01a602c11119012040181955a0300c618801018201d090007120303a038002021900903240c10558050f0090041c0c25520300140c00c0b4000d141e003281c036400c00004600b02e51160b00a90f0141065940d2030100707a082000c0342c1c89188004400300b003101074100d100c050982c0039207802c03400600700a140180941d02c100402d0507050044074507074400610301c407801d03074040705210081404000408440726155920810380c07001090200010b00700408104181005001d60100d03440d1071801e5540b17401d580940251240e2150400381c0141700000360014003240303c0d206144215044900c21814001440405903950340141c1e02a10021f20600030480c0280c0300f801407000400808d140000d40d581e181251540d0980c10000c40c505582061160031305003001401c203142d020342c05125011011a003c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 827363129 1250 827361879 827361881
    0x102071a0a060806010803070624060c020f030a0b010e0a0b0603131b030c0302060a050d02120403020d0c030815120d02031e030c030a0506040f020d0e0c0a08030a0e0406030803070203030f010e0603030708030406 92
    0x2054ad00340a1007888040001e050b500901c101481e18000e0f19003a80300c002c000285940c0703400a0038020040d50300ca10040110750200d9a4458101314450b1012032101000800240990001c1e1020341200c66810200c1c17040080c070b4416000c144400403000b102961564550700342c100521712000e07000b03020000e01d0024103846002110795640c0c115204645845d41240343d11207040c0c084130120050702c940002d21444500459075880665415030b40c001e803e0f561160030072010080f42e1a195080850010842200c000c14881c03c488031005500071030f03c58000514801d03011010351038491112108005110441d0410000c40c1c1e841a8036200200702038440101040003411116184102a88003150490341811070f0340040704028542400c8ad0320341c1d840d030360070802ca51342280b2410f0358986c0200450384000d4010b00d036590b0101e800a1000880c80c1d0b4a4440850b00c2d40700b00d4401c00182c00000411101c034840c0b020060140ca520b481904003803406002180d0f0760700c19404013030540c0c0c101000040821001e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 827364379 1250 827363129 827363171
    0x2030319061206020304060f0501150e03120a1106011401121806110a020106090e030a0804152c0c01050f18060d0b091f0302060c0102071a0a0608060108030706 70
    0x4007105846030114140f140003174000780c0c0e04444440c2050106904d141c82d601505050f100b0170740d14040c9100f0b5222040d04c600c1c2c14074504d95090300400c01d01142b5910501c0140000740020b440b54002c419103540b2050038560143c03c00c40481c80c84000c85400c82c0d91103819844c940c1507143d400520b030703102c0c1a00111840030201c40204a10b08185644101c1400c10300136001910082e00280103080c0c41d1103108090300c110000d0220740303a10901c09042010311410b012504030f4012070702518140f85214170b034402d99456222010381e99148101c1008100c06003400c0c82110000740700075046070002c501c002403180c46100e444124090300070a00c006178120b01d0003052640c0000910341c03903032901d00d420705802070728000b041c5c0d41c42580002e0000301081c000d1740c4004204003018540c9a0b2550642e801c006545c0c1202d4241c00c410342d800d00c040c00004407103080c030040c501c400040704146c626205001d00300381c4006030000d034060340004004215070030780001564038950b4040004580e908080c031101008980b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 827365629 1250 827364379 827364389
    0x50114040b0708180631080a02070503060105090f130b0f060a0b09030d0f090506211b03040f1401020c1b0301090510050c070209100306110405090609180106030b01051009060203031906 81
    0xa91401c0c010b0400124800400c005222274090300c80300341c0d45808260f245c14091103000e421080150000c2c0301c0000916a40340d00c00312034440c0002c05500c60304e403004005400c03a044525440329109101492038180524001044045203182c604a00790010079107034000901750b1024041004060441c4502034410070000d05000b4044985030755800c001203c00404121403504858841d6020949a042c44001c2035140c03010145a28550f0301d880c3d1754030001c001c80002c192058249403801e10819034080c00103142211405004007a0b08c405411600215408031040a110340c1c0b4240f5641c0c0080c101003000c50040600c9074001a81d81e6662154000340d20550800035486081501048982c220078150b1005036030082200f00500d081c60120348419100e00d01441307a00c400c6440000e600c43c40c000058030f900840284d601d820b00c02c2c02000581c2075a1541c1c1084465248000050103d07082c0300e000c600d20401c031450000c000c980f41c01d002039280d100207001802414400301d80c40780c00e0361981d00420000c01c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 827366879 1250 827365629 827365711
    0x20a0503030a0302040e060409020a15030b0d050a020117070e210703050609060603030423040f020c0304180c1e02073b01031707050114040b07081806 66
    0x30b00703480028001d6115004103242e508200001c11a181481c1c820200341030b602030701c3e00e08003a040400c00503034400e044c1500010951649146181030726900c5a45c08050700c01c40c01001c3c1d4a50620014020000c0b580d001a19090100d00b0440d00325485411002c04070025036110308081d001c041103601008007280050b0880c40742c214000200140020854030494004040e0b0303600303446402c03c25480344250700c02d00d4500740c1861006240f2940403150903105440007400012101c0c031000c2d01c02c003644c00191b802011a040414100403602c00d000741d6840312304410500f000140ca1540001d07010354908031640341e01003d00107518007514001c10650004d401d4004c0f4043d02d4210a01d16118548090407502c154500341d0100c03c0e013209201c0550b90f058a610440d140790012280b82e403609a50000d210a030f4003507485540311010100000c1400317014a0290b42800e40c1c914001101420108014110808400012600040c0307142c000c40c607244c02c1044034245400400c81d100c503a9040d00c4902ca0811078003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 827368129 1250 827366879 827366887
    0x30908030f060306150d03120207050703081c02040f03230303090607110307050c13020403150501050909060f07030f0b030f0a150b2b08070b0a05060409050c010c020a050303 76
    0x1004080420600c0b03598118211012581e075500c20300b100e01c1c14140038030382041c0848000303000280142201c1c2c039450800c40006042181c5921803d241c82e41c140d00c1a03a24820001e04203840d8036483c2e074020030080d00d8480940c80d25191018284141c074891001422099600343d0b420030b06420f24100300c41807040b10080f07a03124200010010307120301c415030754a0040303a140440b010004d000802500c480941007005005024495010302242c0030b0031503c01820254204004000a46401c0560302880003030000042e0070360421301402241c3d01c000d00035041c95800807003002a050502150350341d01c0b442505d004038910b10b00309150b038060441c042341035034980079038503601c00d0070bd00004803014001d02541104180b004840d070081e0442c0c03003841483c0d0f040f1407907140b1903c4c000f0303000d0104ac00c0d0b000180306c1d880c005180c3e40c54030090b0743c1000404581c60003d160603c40c000005028603078002600301c03810000c0d140f41e13031345182d628100e00d11386506105d4641e1900c0290b64406030140000c150150a417551 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 827369379 1250 827368129 827368141
    0x207050c0d0c1e050420120709080703062903030406030f0b090103080909071b0f0c0306110c0d0212042601020f070203010e07140d060b1c020f04151503090803 70
    0x2030b242150003124026443c0c802c0100c1076420380f682042602c180007441b50701d80303009804a0b01600303400130320180501c406960300103103c6c641004454001c5000d09400a0b604000306503090308000301e0315412180703170301c0070b28641b0055401000f12001c0320307081e0a00040150315100c028015180406440c0ea0041d001c00000007888580c80041003000001c0b21030100c0c40c1e6414a007a101c412100b05201e4014a6004102000406100c2d1410314580145082484c9564a0b50b51500b40da40d10345a060744444007140c68207040f003041049807070070503060000d0240c40d5800703054102203010310700c61b116107a81804100c1e40341994011800c0144c10f08400250f50f6003104204595460313200318022030080d0700e044880030390010b006c9030220940d01240b1031100300b1046c1d5010400101808030060351284d40d900c06617043c81c4d46004c5001c3c0c1c0f11915090001c94036170f0031300400500c01e0802441da03001d9418440c001108040da000e09005507544ac03502c405003039001d000d040740140699000101130210000500c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 827370629 1250 827369379 827369429
    0x20a090b03060f0f070507140d0906171e070e090a020306010e03061e09280606090b01120c0203040305011e0501120503030f43030207050c0d0c 63
    0x1111005800b00d070000e80703411220400d51401210f142c213960083c1e5000c1022544140c0060145a014a98140c2aa00d0900046040161104002020555520381045544e80005002d0400c1110464201d5549001420f003003914006125200180d81d1035000038040030301918100c9048640a0001e040d01d01d04003250b20000c1d03205840b0180412003031001d0003002c2c0b50002c3c0d141c0c0f29400b805408a0b14410405921142c02d101501101481c001c1d0031407181c04081003c0b00d2420748550317032141c2030400c642d4200f070407c0b9502500602a4a800d09000c0c44042e45c1000102c4d009100310100001d100102c110100c0c1540110f400c014940e500b0704262001101e80d00701c2c0800c1080e140c0104003c580d0fa40c114040c500f18a114005019400c00d000250307580342d070b50401c15442401a500c0303c8030302c072000c09500021215045110130103002c10301446c00303900070580d00741e4400c1c03a01d09045280002c543c980d140d881c140da0704000d00c1450100f030281c081041201c0c2c250018581040c03032070700e02810240014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 827371879 1250 827370629 827370641
    0x1508010516030605030f030405151902030307080c0c0c1009170a02180f01090207020607150926160c0e0c07030e04060f0b0c1f0b03010b060301060f110109020a09 71
    0x800283c01c102d808030b12032030082184603c40d141c0030700079483c0919040510494030395204005507420420700c0b00c0c00c0341c440b41040302203d1180740d5010310b65234544440068402e400141c00f11184403002d0241c0b9428020000301068807500441d400760340c1c1d14148c0c0007220f281c506030300011410800e01c815840c07a060005980e1142900c2168064981c2c00b803950400c1030701c00102d034500c1119078100010007030015a0740c02030030103d0021b05010301d440096180e4030716010711032001081a5076030302000c0d4107000c1e0800c01281644822045c0c0c64a12500c042a801039003d02c1035902805400b0003803607002c01000c000200010070034000c0c0902d0a280c031100c003001035004040c00780c020603800006490b16140c14810682690305c6078008100c454200700c600d4200340c2022141807000e00c5490340e844003000110041c0202403c0c00c0e41d01080808440c1c0600d82514681d14070f9078004c807000d0006110385504a04e05200001061410182d50102944414094008110b019420021043c001304000c0f00c550025 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 827373129 1250 827371879 827371921
    0x80a02090c030c030c0c070e04032d020c04021605070e04030f090b030403030903030e10020409150e0a0905071a0a1b11060c0109020a09090506010618030615080105 72
    0xc0e600c00d98401204410900c011100003911038010400524140729010240110355550b03070803141c11381d0300d8617020b40c45441c00b95005c1c0e01060b41441d40340035100d2001a00b9800c900449000184000700d0340000e55030b03600382d000561040782c010607000d10182416404242c100e8100c1e088800d17040d9941002c6103280f00030703182540001c210300342410406008071000f0040340c03010021680303560b4881d18118003e140d450000c5081540364507190483c51b00c1005402c1c040e82c403c04c40182e0301c41c80c1008810464a80180c00103401c550301c03104000c0c1444181c2d80660141c01c2d0800440c00c4070080c640700e400c2c0f0400d904500d0341c0d45468280881e1903044a409020f804446031503020005a48042c1c02d100001d41d114014138582d100306804245003040b1024000740302c8003c0020035041121360000e408162150841d60f142981c81c00c00c2000d101c0100840307030040c02c6030b0400d81c40074505013400c1c0042e20702c18003002c2e101989900c07203401280d035040880002050351701c000700b15a060410303241000302d0303860303040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 827374379 1250 827373129 827373139
    0x10f0e06030f0a03080a020705030309011b020d0516051f1a0a12060f060b070f020307050d0215070f1203021b06060d140c03030f0409051e010603021b07080a02 70
    0x1030311420001100000c0400311001010054180e607002c990580303004090780006a000e00c204400600100095401402d0120010032056a0310f0190740300f86422501303070021580040f00096043c0e8011040300d00000c441c4407220041407190030b00e00d1506108503480000b090962140550400c05640442d104004030071840416010110405c04004200d00900e80c414140d081c040c0c0009503d44d01181860881201c04601c00760340d0105020350782c00c00d040a40700da400e030280900440c602403004a01911003107402200401442e00072036221105900d0541f85140d00051203014480410041000c1d00e82c031402d40e070301b072940c003c100501039000a00e180d0490081ca22001c1300c100c0001c607045210307560241c1417100700030b21b035292141e0304660400c000040b40160841c000040d24180014040d1600c81081b50340c1c0c89207080c00310402c8034001000348801da45200c034140c0f0a07071000310740681100c030503281c050f8031013426658604041608668020f403d100f20307503001031745040c080741c0001d10320b000301e030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 827375629 1250 827374379 827374381
    0x30f0a050604021206040504210f140310050d030203070203030406050c1009020f1014070f14031303080a170f0a0c1407060c0203070605090705091f0506090117010f0e 73
    0x20702c8260f0042030200ca0300c211000c00011a18101680103d5000c5c1c0603200c1c1030800e200d0800340c5040a034800303840c2400586c01c182c480942503003040c80400b50403c580c412504d18540075403240c02040345400f45510072048003480005142c820408c3e217001c150000d050740d80c1c03540d6808001d0b00d558030810200c034050050402d0020090814455482c00540207020034800c01c0340c982c2042001600f613160f03078040c88182040508030072036503005446018802d0a801e05041c00500b021904402002d0481c1025882045543d000202451420341120b9000071150b41710998184141e8224081a0780e03c69440c011404000710030010810142c045c0c0900d80041002c650f41010440718050b009900c100034890400c106400922541d00050002c04184103690810b24141d4950301916000d0b10346918540c09206c040c0460701d0840c1c2c0340351308421070480c074844036074140281c2c1030213140c60702ca00f5102c0e08005c2004021a4060803440300035584482c0c0b405819a129a0124a80c0c105070090804e000a910 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 827376879 1250 827375629 827375641
    0x60905130504030e09103b09070e040606120c09110a210905060708150f1008072003040305071a0f0304020607020904050d1814130b06030f0a05 63
    0x221806010341e400d55206900c0ca038958052111019000c1e01c000c400d001003075000911001b890803d0710344c00c804410b000d41c10900503641e4494403c1d5451f4540040301907030302409a142c900040e000d00700c1e14900421242680c1d80d06044000b82140d500c00d52110711035640c1d00d0b003002220441d00c1c054940c589000c00035040ea00074aa081390098500d01408644164401c5031015058410824251030f03480002c141d41c162651810b09107003042e96804c000c1150b40d014002023054240e081d0680080a5444094030010342b40040c14494a035a151400d100564002c51000f52258992101c002505107021504a141800703503903603580301e0311003601c1500840e00301240846202c407110320401d1490f0f016a00344044200207484030b07403000d00200e034005c01c100a000700680315018654840c600030b0001e130055100d000406080300100c00c3d0b0024100c03c0001c02444001002d000c03410824500342d40500c2d26550450003d8010031501c2e5036940e011901204200089400d007003403a115111070401408161980 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 827378129 1250 827376879 827376881
    0x12130c08011a040f0e01110c0d14070303020901020f0313030b061c0803190603060b091609060c03090f030b2502100b1f11011a0915031606090513 64
    0x40c050030b140100032202c00b5190640081d080645842000202e001c6940d01c10350840780603050002000401281305480440706100c0c1a04070207850404102590643c01c891546d441500d50040c10716a0101e44145142d00c00c0100180001c640c504907a6034860170034024080303440078402100d143c030142000518509100c00014207904002184a40b0100140d84032942c1350002001c0f030450001c040100c0e2041507403030045500a500407800043c440102d0030074801151300042489036003540c0c616402040700d50044014040710b00f03502d4040c0d610061441c045912542d06d921003039851001020110034441541403c6005050012003004d5420780c1c41c041d294440c120f080403001507040765030001705a982c590800c1b00000c04c01010140305080392400001420825a0031100003031001902c0300c1030600034800e4a8820500002164034030b116040041d0744e03000c004108041d100f1035580c5403c42030302c00700245400c609802000195090b02c03210000c10407074251050912038041105002080403031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 827379379 1250 827378129 827378141
    0x60e0d0308040312241409040825060c181508130821010b0403080720090114150a02100c0531050f0604090902010512130c0801 56
    0x40608a251050000e0300c0035901040000c00980070b11111015980c1440004e00c1024600c55041d1480c050b030f003000c40003640495000e5017020600440c110143c070003543c1c541450307990259104a0459583c2c082c0e030200760300f2101c402074080c082204800420700300565904080d0b00b42c00c0a503a031100f420b0002d403644444260030702c41c0b61140942104003409441c800c0c58a16881440003240744400c42c950341d6805010b81c0a01000140c41e820001006030182100040c00c3c0140407003556942424112303200d0382d80d684540d00e8000c100300d03161031240c0d8a1140c101d9510280fa6001401c80c0c44030340c0d45008005a40c40d59086840c407031040680c4c007001c07008501c41541e40389030240c1d0003446503804400111006190110004042c000244000448001600000303e80103d0041034070041e40c80c00e030f5002044c160280c02151050340ba0840c00f40207516401e00380d800701c5280e41c4002c512522240016989840754118044800070603104010105946004a0940a110f00c58000341c581c2e8550106080f104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 827380629 1250 827379379 827379407
    0x3010f05010b0d090c051201020a08070203040609060c0c0f030f03080a050f0f060d14011d010c02030f0d0e06041101080907060e0d060e0115030c0e16050f070215090a06 74
    0x30003072091030709041003580000c150034805c00b499490795403a800058907075116001001032582d00040c885da02c032a030168680b03801c0003003400198201030a0010103020710344240030f110100f100361440c090510143d4801304000b06080d0f0001643c2039201e00b4019201d080440d402d0b004140220041a450406407150038890915069400e215403500f001c02e0b8405c03c4c001e403a003a404028100314101140d1000f5040c440103890500010f40001c240004190300c080c90030b140c4103264500070400d8400d5070048101d950001c142001079550b0045101c40c0f2008202000c031010b054170940040008120020b28401050781c4c0988586041c0d40c0c80c200d6480c9e44034803902442c400110002e0021038107040c01c403c8105001d208590209500c0340d000707441030859425030100c28100000c52010414420b09035000005001c0055981d12503107088a01e07200800f0762000c200003000400901404071a12070b20544032415402055050701140c401b48846c1d01e600020308551150750303200d0001825034000d103600c0000803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 827381879 1250 827380629 827380649
    0xb040c11250312120c080a0b0105030402060304060e19051605040b030a060c14031614071a06010c080a0903020111010209030a1709100c20131e0204030b010503010f0501 74
    0x1d09550394441d0388946000f0000601141032411200b0b18424002c004c0ca0001c26564041c50f89481c0c00b48a003503502000c0480d052150410911016882d0b08040700e03032054000502042122854a1003480c00403417202022001101c40d41490400070045146500ca00c960b8904004007515101080226034840d0171140d807652203003a6401c0003d8490304440000c200700c0c02d002d1045010b408100380f1a5000b110340490700c02c00315040511468000b0320b0703070946001c0c0707881c1c550828002d0b41d1030120b8046454030400c0c002c1c070790307000041e4168851548030184a03403008031a500c84900c04c0026103a0b5115001c103c0c00f1981d100716240304c4100c140309452503107070020024144c1d400191200c01030005000f1100d821508100080c1c44561125406c0c2c504610301c560b200b45000d45a03003400094081d0365240608280355403e480103c5580c3d280f410320900700e03606000280002080508100c040680c1500e1a00c68004a000018002c500300d40307604a400550080c42810841e03007110003150000d0207165010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 827383129 1250 827381879 827381953
    0x4121407060f1104081005010b0313110f1003020318030c030708090f060a020601060e0405040c0e0a06080105090d021c140d060302060d0b01120b010e01050703030b040c11 75
    0x820303959000880010011500001c8003250031443c02c001c0e0348150403801065120510503c1d1541051140c540184440a509411403d003595180d07800315031148064000c4101152078019981c07440a10b00300d050f0300030100000b41c5240c0c1c80142c00303034104449080808001c044401d1380c40c030f0080221021003140001461403d40c1560b2448856004511003a4200d5144402c40312a601c813403004084189090300240070540c98100010504400c45880380d0040f42003038207100004000d0000d1509886c034080c00d101240d92480c0007540240580e5216000540c203020903c040454040f60034147c070083c55081c2c0d02c9900714074060b24691ba000352983c90005015107154422107982c0d102425000208140c0800c00c0e903584d4001800c25042000111001d0f81c0c2e0710313030200c120f60f00b044001c045001c454034144460b22200740003800c011303035202c91076040c4000090082c0c105032082e031013071401c000c00030420030000c2100d01c001030403000040d01c0c28402d0300c50314641c11880d00c4002c04911510303007284025804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 827384379 1250 827383129 827383133
    0xb030f15010b0c0102090301060806101217030601050904090b10050315061219050c01120b01080f0a0906090506040308011d010501141c0b09010906080a08070203070b0a050304121407 80
    0x2e00e41c04031001100956003488090050b41d0b080c0900d0004005c081c009202e1780c14052085943c42c030300b5502c0000301114489140001894003012078050001c0000340548940c0c4003001078503244a56250700303a21030718000c151000c00c58102200ca004180c130030445200729440740d0500d9543c0141c8001102c8000070000000c03100e00d01450704420a00407a0103031400000350000c08a044501c2c114101c420741c0190070420120f5a00494085030416001c4040c4207250403580040c0c94600c002c1c01d00035540390b01c0030000c0e240701e000b41c004a00c1e01d6808901003103002d42c1c50800c940c0716082a641140060107403000010292065440f038150100740780e003100ba19034a007400564085103132441c0c1003580c5100b4818850518940340300358003001e95110002c2120100c0c0d504100707086d42c05030405503146280c0b030400c2c04400000182010443c0d03010a8840d550201d07030000078600000d0b030f4007901d20840000780701c03040c49a104000e94011886014401084464a102511240490b840711001100c040c005d03030700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 827385629 1250 827384379 827384399
    0xa0b010504121113020408060c0901170a0e030a050301081501051e0102070906091d0d140d0204080616020f0d1e17130212062511060a0b030f1501 64
    0x1006034401d20003400e8440d0703031a0100d002e01013012a0000129400b040c1080007070000e2204651048541d03105910300020f00001a001403801e0301d100080300c46160000f5440d001c95403019a5215a1404032611190030f0500148203500034000c646840c01019509448507118a1409040c0e03040100f0301501c041d1907000c40000c0719900c131407d904501c244140000d542c122032203120041c00405d800801c035290f01904508115240d014a5910b980c001102d40642551021960b40c039140803000d000d07034840125001e18041e010b40c0e0007101c00d074080c01e401d12490410890000c2030070f00300b50702030b01c0c0404132801416450310402e400c4040815039913500c81d810641c20620800d980c102a0400d800c10760300b0410a514008002c071123000d00c41c455410700c00e0940c5401c140c0070001d444400300902040c80c080f02500310246c003881c0c401e408400d40402400b2564040c01a5040c036240c04412030301c1c646001d044003005000b00100c04c9000c0c0c002c1400fa4084200c0218050302e40541c02d20409040c0d0b440c00b04182 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 827386879 1250 827385629 827385659
    0x1303021c0b0c1606020304060902030607080c0406050a030b03070806011e06170604090f0302030a020f060c0d111213110f0f010810080307080a032a08062707080a0b010504 75
    0x8044096086a0f100019841d4405940200c0c0241d00008051040f0310600d450854060282010700c00700c2c00c01c104442580008803015142c540c81c1088c3c86178004103050b0b014018501c00540c1c9401016400309001c0000240e0718101c038892070708200921940790120034210080d005d02000a03024010403840c5220200e4865017003000540f0000c0d01c0582a00c407002c00603404501140103801c0040d0001c092581041024084011100909494140f03c00d21030068400c2c010752500070b80c0c40c0c001c04003e034007208003543c1d06d06072151490261031034004a040102c01d0014001c8440308080e1141804c0c40c108030228101408000d0822503500710000015950301c01d0091803c0c0448820f0765002c00c0b84801840581030f2a03205000040d10b90748040d8024091324400640e03050725000d08024030282542081190f40140c50360706000142e42c58840120f49181040c0b001d49003102d181d4002d9803031401040c46203510580c2c0b2581d91034019201c00c1e00000a0701c11090302c0704d0005e401840103024002a00b0840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 827388129 1250 827386879 827386897
    0x1b2703020d080412200102371b0305070902070f0b0c0904060905040c061b08070809100c03111f021c110c0d140318121303021c0b0c 58
    0x85003480e0380d81138039070618541d15008440e820100c2c0204e03260a41d20030282d14042000f40054085482d110040144030030603005181d440c103292188005480e14802c0c40c1c004082e0b0840c480307982d40c8e54642d214010f0310445100c11500703441100c1000aa180f250700c00e80e405903900802201e016000c82c0c175131044000c000341c004011b07054100424000d036541c80c0701c6e0700001d03d411070010500340741c80e0030201d0b100c0205a00006c24020305035422010014440408000c0591200c44140c550b01036003020394490190b0395015421a00889000b460f2581081c100b95500d4400e503107020243c0c0e0843c8019403a100341040141d102d03400313401000282082c80e0050200b50096581300c1201c1841c100c00807055564405000e03104000c0003d94503041907080c0006518040a81054408410031411002c8280b10051104110890348442003032105801e00603a03601030306040c13070381e52070382c0b40c14104080b000c1c0c0a01c0203d02c110301c1c0c0400022089500c0300240c3c03d09400400d01d803150b80c0c0c2c2c080030001ca40c1c03148240c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 827389379 1250 827388129 827388143
    0x31406010f12290603010b0a050705100c050c011d031c0f090303062105030a0e040b0a0b0a09170a08090105040e04051005012321011b2703020d 63
    0x2440049141d03485480c107180c90481c0e0f0034850212881c12020b03403c8041081d240154010001400b0700c0722150110351884000d407822a030341d085542000c0b814100440c40e020085810034040040c4076074808c01408030140b041008000791000804440c0119401120303d5045030810320004240e0307000f62030600903584500c4400314950720146800002c0b00d11006003103000c60b80c1d4507402d00c2480c98021a15458500c3c0c114842d203401c5280d02c0703983d42c034040d0000440070845021411945521650040400c501000d0078808609031a1051145150010a2a180060b064610000b401c03a900418000c1d40c0709140054084006242c40b140c038070b41d100320841030500008100004040b80c1c01d0b11000c0c4a10b0085018000300e90009240d04181c650680c80510300000c3c240c03901c030840c1c03541404003c4c149005c48480d00c06210120500780c0c034048142c64041c0c61b51800300070461401003800300c40c02c0c0015035a036030034241e0700c401404001b10812114101805000c01c100380014104803441d0f00b26207014200c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 827390629 1250 827389379 827389397
    0xc011a0303090d380403110d05040b030a0b0d05101a061204080c030c0c03070b0a05160203240603070e0415270503190e1305040f12110d031406010f 65
    0x11100204d003060130321a4a4a096401000b090650024042003801c40380300c050b207100c0340701800c01046070246001d40c04190360008007080500b4240d0b440401a20300140121a40c54a1800d1051700c030084909072060341c5042143d552a5400f00940040114030020b0090b030424021401e050f4030080c0041c001c580c1010304004001402501708090702a00c3e50a42c01030a5103100c1c0b1003450306000c8035611001d94a0313814010103024a03048000d4031004000510200c543c0a0b0900000e45840303581610000b114810342c84d075289480503000c00c948900d800f83c1c200d071141c50b0380c1d215504078a4000ca030042c1c41d800e400414282003240a40020701849000345003503541902c0000060100b0041000444842d840004c4403100181c000000754042c2c0c0d06c42c100803001038003c2003c00c2da10000070211414403640d0310002410062001c1841141542180a10b4034811951001410341d01003544483c1c0d551050f00b2401d5800c40c0b003801021282c1c0c1960080340d400c0c0d1500d1005645500b19020000e040c004451 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 827391879 1250 827390629 827390693
    0x50c030c0109080705010f051627120605010b1207120b21060a09120e0301021b0102070c1208252021030f07020a09020c011a0303090d 59
    0x10042d082d60500502a050761941c0501e4007608403602c2122901c1c1803800c02081150166140055000ba41c8090a1075540d4404101c070036241c0020740d08a921084000f0100400c412000c0b0038140011440303080104466621200754200c10f000d4120521005101c1c0c0c40000c4104d84920000f01c810b00c076440c00414034419500002d02e00750849151912100145003002a0080d020007000b81c115940c40e0f800c02c92240c035600d44c040988040d00401044c4070310540c0d4050191001d504680c40c0c854001440003840c00c080c40e034503009c0d5000c00ca0568503040520004106121054080078090b0352000d446450054a48450328200024410030990400c100c2010300103e84250141040d0350031400311041d03204c6038881000b03480c10050b007021480760300d414050307041d000c000001c40c0c02030881e213140e403911102e0601c000f5140c03044076000340c95458000704040c024074005420031025441407824184040303c0d200145680c90050403c503560100082c3d10140c007003441050351304012400c00350a02007a20ba41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 827393129 1250 827391879 827391881
    0x609060a05300402130c350108070906081216030c051f0e0703020307030b06032508012d0c0315120b0108070e0a05090102040e0a0c0801080d0f050c030c01 68
    0x540506402c0070140000c20045282c081500c050100d04404100200c00f00e0040c018011410341e1802c03a00e402c400142e1400b0100881101110396078440b102e200d1568403041800d0b02d445151040341d124074200000814402c401040c82c0d0074078005000942d0030700312449003100e244003800b402076060042c19411080403071011301540c851140542407410715604031810110456107848402c00c041e03000340c0d03010310041e0340104501c0112500f041d004178094592400081c1003100f040b42c402070300039000e40c50426460106289004607000b22001700065000c81041c032038a914004032480010420500c03c6030102860703400b004100000340740010b07540c4031440c000c4156044035082001e1000e58860f0450412040362030160151130444050010309186c982c0c1442c1208000d05031280f000c3d200c0d030001c0c0c4041c0007541540c0081c0200b2038091030900b00341e80d5000c000c1031400540380c0003d03c001e0011944105c00500200ea10300e00e0355031a01303840314079801180c0c541c1048081210078001089020920320003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 827394379 1250 827393129 827393197
    0xc0e151c0623100803161514070801080c0f0604060f0e061b070b090904030f0210050f0f090109110f12010606021f090f1713090b0f0609060a05 63
    0x451420182d0b0506642d481c032520396540c040b400310f034020800300700c1c001c05c14860740414550100a012061400500074400740000b80d2600348a2401c000400c4140c943c0103540c5c604075070800003642d644040038028040304139000d030701e00d0f50000e00400041200520900041031284103030328115064000000005407568080300101865400015038000001030900030b14004240b0741000781e252551003c085001c00c0301c02480a811b00441e251041000d900034000b007078040f0a4008108524500403c00c02141881a201c0c24901200070001a140c440d051150303001d02a0001c0a0031309108a0ba42044044c00d4600502e54024880c2901090154002d004a0703020b00f400381c010341048090f4045042107110492191442181031804901c08900c404008158964102d07600e40345c440000ba8400c1070368880c0e184a24005000705100148520710b603130041031594000c0f280c40000d917035480d0030044540241240a076100800b040070040a0340908018040d001004041070382c5082120008680a15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 827395629 1250 827394379 827394431
    0x5030d080718091b021906020304081c020a1403040c0b0d020d061508071b0b061c110307081b0913020307030516091b08180a0c0e151c06 60
    0x14513071a841c00c0081d048036000001e258948000d00070040444035008000d4510403011740620f600001141c2804510300480d02209022540001c0035102c8d0814100254040b0200c0700014510ba003850900440e000c080b40e0103140c0090f08101e03058100800e0083c1c0b540034540000c41c01e90b007000400250030303050069030020b184000c45114140302c840005481d01c40010070a0013001030043e030800810001682d0204402d400000030466a030312140402d4152110a035070b105c00b900740124900800c00640c5441800020980565000a82d12021f141ea160354404240024084441e9a1021030401c6046194000a481007502c08402c06401103401d008041d0070580c0da40d0441c0c403c2d22035030070094111900408820f4001c0000300721040108030901d906140301e03000c1100f03940200d81c5000c00e10180d868107420f05019078601ca6a246020502c4003010302c1144071051a160004003810b01030200a9032481c4050410b04621003810140c8001003c9400101e1340360707544805d01039184070b4460508046034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 827396879 1250 827395629 827395631
    0x5010e1003200301090b151608070f112407020405131b290a0e041d1b09072a15060303021605031209030a1203022205030d08071809 58
    0x9418460524183c850840e809805401140c0c0094420043c1c60700300d0350869012a00c00150702c8441c81e00c200b270703403142040150032a261043c210050121551000134840700450b5403100190003891600907840300200d04452801051242a001d81015080315034080c8201206043c0c50070b02d80d5032400d425000e007601400301d030f407507401c02d01c841100020020b41c401c40d076510300c50381d1410801e4564102c5c450007410320304210884c440b14089440703030b810002032400c41c02440c813201c0d000c51000e646c2c2c9000b14406210a443c0886034004182405200340d800344403e41c0d50700b4242054035041066006080041450001d044000180420700c240307290312007004182400310b041869070400900d8080c40c040350403221030017003008220941c0d002408104491a4264007030f00d6400d03c10000b41842d0030464064460385040041594031a40b40c1e000f0124035241140d54520420301f9018080075070717081d000e0140c1641c0a643c812038100d001d0f001c3c1d5607201c03a0926013101282803400c40041640d14642c0000406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 827398129 1250 827396879 827396881
    0xb070809031b010f05041827030e04110c030a0e030f06090d09060f02060610020a0204021c061502060106030207062c010609020a05190c0b150f040605010e10032003 72
    0x99a480381c1c13803621903100d62034664186824040418262030f2400100e14480e5603030b421700d24907030f0007420702d844504503018601d06e6114610308002c0c14955440d001070b44614541910189489050400d50305200d680f8001036003020401d44040d0351b4206500c82c1c455043c0f0480780b40d20400d440801c031861040a00390b010386a4222620005841d41c5510b40001e02400422180c40c04a20790029860354049000c5669000c18074110405a0410010382d50294016000040709012011541c50300c1c5003460700e0880070001d440d5211155801100704460074001070f0040d0004000603403183d006492642c5c0035000001d192178200842c40d000c1c2d906440f40940a1020320484030000b1001e00c41c02000f0481c2000942c90103080440003001442110b0420405500c56500f14514600c0361001252181d402141002242450307205c050145400c0324401303201da002c1046d072640c28240f5006840c1111810307100c0c44179000c0c0f0082080b400d10b00380000307042010b50f60600803c000c880d240001c0048000310544c180d607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 827399379 1250 827398129 827398183
    0x506030a11030c13050603090d0c03050906120603070504090305160614041203112104140304061e0912240513061506080105062b020a031401030c0b07080903 69
    0x4004d842e5070081c3d114a0040c4104402c0031008600210414200d1400d04000109403406071482d002c0c19540c190011000b24004880000748280c11f80a14812401c440d901e582d1241000b060310895640140014014021039015040d281d140480ba03500c202d20104407100300c01800160303417400f16070942d040f50700303042c0e0032121503054850481c484907883d12a0b45040c040c001030310402980540301070490020b00000074140000c904000002203103103030940340da503a03076224000c10f62400a4a507003141280d81d084100094051405041103541c039142c046502001c9032915504c070341c03480500c06c807411410704807099450020321915100d10080a21ba00e00768610b030806204890b400c0e895030319006a07088007840029049148141120702c111482903441c201d104103132017960800c7d1103003102c10182e81490140c26510740c015141182890b0b03070070004030040990b5000c12610a1101501102c40f00f2024808070070118018010180241400e80c5000000b0002ca40350800c11081034840c901020701c007482c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 827400629 1250 827399379 827399407
    0x26150f0a0b0a0b0703050702040e01050402031e0d030c0201020c071806080c09180313080705010f0e09010911071e0c08030301080303070305070e1c060b03160506030a11030c 76
    0xa0001010303101000011115004940700309210b006002c04180c0120700c58003014400d034211002268050000e100c1840030b40b032541d02800054800f00d01c80d014440e1001d89491803400c400c003104003070700c000706410b50107420309034002c2000d070940b103046540801270310b04078440c2080b0440043c031305000407640510b0541d683d50704560080e003150803280c2080c00d1008440d0f45602d2400e800604200b450f10380c2d4511011968914030403500800c0c20302c0901200000c44607004179609040b200280c0f42c0c04100d02c02d030389007100e02805600403194080800d200620822074140d2008403401d0000c2010351408520b80c503024000706110030b0102c0b202034240c02407801c11506000a00050406070000c60655041280ca69180d02004011104040c3d96034001101d482c420800d2080d032540242000c41c0d8107000c00c03505c6032030b004d100c10140c078001d05050340c200b000c3c1400200702c01d480e03d410301c00b91000342c109010001150f00142051442c580c4450500c00c60008150085000d81030100507140d81d0408006108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 827401879 1250 827400629 827400631
    0xa0c0905010f060206041b030c0b0d0f051e06060f0c03180303090d240c050c06071b0b18010c0504090513020105031f080d2c0a26150f 59
    0x18400c580341580403c060b6030006086500301d5440003484038031700c22220007918144910392005c2e005083c410000650014080002c105d1808618420300c41100c030b141c210340540b201640d42081583c00070b00c0084690740c0038070125030000c0006292520700000c0700100076154000c104521619000025080708100704044055103514081d1701640c20002c2e808005030114803280405014900750b9448140038002e910008a2861224a01006024280e050040490b0040e14100203a0302c600b10100e51014001c041d103c1d400481c10b40081c41d1313140c880e59040102c400260200355070b12400380c400c618400003800740915400c0203a07103154540e031808030100103441e4040c1c08142407601c54006000542d920200f102e500c5802c960b480d642496141034400d08011055100f40308a01400c0b000e21102d9a0000039482001c0c1e0001401842c601c200380702059208050700120ba02900005080008a000309000000c00c4400c001c000a4442281c40c4141032103084071009915031205420007143c1100e000b07240f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 827403129 1250 827401879 827401889
    0x280f02180901081507050d060f060e01081e1b090904030c05120a050a050a020c0a030b011d060d0201032a0512010602030304020d030e0609040f02030604110a09091802030a0c090501 79
    0x400d05101940211402040090900c0c2c0c100600041c80c0742801c40e1542108c17000b803034601c0b8120015a551a0020141048a0802d600103441d4002180203815040200340780302032865400c1ca59901c892400e00c0290380c4403003a034540603100340449207955941d050010b1245001381c4401c81d90800500c2c140381026180440d9030300701a428401c00b04090f601000341d803001e61141c10816580c00c1007400c141c0c038108159900c0c540c46000c110011003003005640400b4100c500c00c0100040901855003d44400b0b00f0031070b0075681003401d45000c1d10156200350401140785101c8540c06920700c441c4c0c0301a04120061b13600c400040b940028a100021001089090040c5040c0c4090350460805a00081c40c200320340c3c1d4042c0400030350046e013480d10343d01c0704100ca410b081c006104124081c03013800b5103000b0790001c5a400340f096280c9054504021455000c4840c64007440c1e58a412441c20061224018071800b111000c104c0050b00c50704005850403c40c07600264002c03550008074600e4002c600043c0d8405804c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 827404379 1250 827403129 827403133
    0x150906091d0d050313050f0f0106060c11061303050d080403200d031a06070507050406050301020412060e0a0609050c0405100b070303020f0f0f03040c060305280f0218090108 76
    0x510070910100e01048110304a00d4525503076100c1c20001514a001800c019005000725134014034504000544070f0900309801e0003d020140d0383c0c00007620441d20004014005a80c1c0c110011000c1c50b0220060800f110f42444903140140c036074031114070380600540b030030780895001c4052005164104240b405146841da84917000b0b0500d59810740d403261810118039080c9a1101030602d003600f0941d00e145a1040e0151000e52501d5843c100710ba501c400e1341c410b9500030703450f100c000b09445c1018001c070b601361031500c807030003000b00070710b0391040010a450301c0b0703501e00c50181e00100f01c005a42e81c02038092060080004140c11000342c001c101c21100d015085107103140f2603010800c003290800c004c0da81610b41508005880d40590000c1c5445031043c52040380c404480002c64407104e00045000d1401030740034034155030622361111800d8044420a4030000c00001210f00103d600007030301604040038540c1c0000103d03610000400b020141c0e08403072440c40811082030500001820403942540c01060310b600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 827405629 1250 827404379 827404421
    0x4060506070204020d2918011a0703090f09060905310c0b040608010e0c0a30090b09280f080f040b04090c0c03120209010315090609 58
    0xd1450700c00c00a0007030040b9004108045c4020b415400504072200081060158004100fa034502c3c8130003401015104404083d84070b04540c15080006059881d4520110300c03154015259011a401544e001c134100440c501c000314460402600c44002820ba136a00807600904008101094603001084500032240d410452a040c1c041113140c40364624100b643d440305100181481481900f254210298030000090001922940015558100d91707140f00143c00a4403101c508001034802d402803640018501c8240004500e600c141590b0303000801000c514150f5415044070080d01d02090301901e02070070b0312003041107041e0140980c030142c00300694404400801003840700c41002204d440038000c04030030420882000b0081003141d0362203502c2c0d120503850300d5580c8004007482d4401e0199000c3c40741481101c2c0e4469000310052000700c0d604d81c035810415689011014001c2d0403181d42d8504064031409495044607490300900d0242c80c0303140d80232a4a82c200072407202503400c85107034031403104180e50b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 827406879 1250 827405629 827405639
    0xf02030712020a170604060308120f070207080a080f0408060405010b040e12031302012109030f0e031c0201060f06080402041a1c052a0102060105010810050126240406 73
    0x1c01d130715009480f01060003151186400b1400902d004d400082881c440041c4028003101b54481300c501c2000925983e07029030761420707001c17600c802c0c50388510301155003d01d0303940c000110b0715005030580000003d03100b81041e40d2a8006880c082d010748080e11141d6440c044420141010f020b00102070b00d00000900201860402103134061100401000c019420306243e0030441e88902d161407104041c2c0c01810b4050304045901c5002130800d803408401140304000398807541c1c0e0140d00700c641c0c0e4072001009404c1c10b40103500f1245415014455502c1195603525010a07545540414070700540043c1d520083d1906d802d04c1030000300c861803841546081a0342440c102e46076101800d000a2041c041645c202006c0c1d545001854003101000c0e071031902c005562003059405142c14400641c404c240d0854130741380d983e100159410b100584040e00c1d03218901c2818082c03035000c1c0c0311440f040c5102c600e8042440c00112001d40c2090380a5481c0c40d04c6030047c1400c0c1c1103550491800c00d44082007203804000c298a0f00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 827408129 1250 827406879 827406887
    0x1e07050a030f0e01051e010e0c09010503060a0b0406050c0f031602270a02190c0b0703110c0307080c16080d030f020c2b0207050d0f0807060f02030712020a 68
    0xc0c190a0070941c8485042034400c80c940c00c0a40000b00074070003800141050690003100030414170b403011021038031100000780701c41114092401456981051881d2400000c011103590340002c00b03454100b00b082c0c2000941a40d402c005200a0106503142600c42030321506d4603060200c0380070205081da106220311404000344244040f0503660440c3e0b5110305001d07201c042040720312104203007070544c01d408007005031031032250300200422352041c030000e03400d10030303006042c0c8481000641c092300400550380000e00c0b1600a0b03101c80042e600c024089428148030380300030f502e10343c0024801c895800e0007144403d984041001558280b901400d1410041400d04514503aa021160403074400c040d213031550940400090b904480700c0341d04940503581e041c1a101440d2112403910180812090110b812140229202180c1113007074a0000f400030484c100c65403103040700d020003050300b515506400c12001c40000c000b0b00c10341800210341e07000540c903445d02420142c24501c0e5604555000307401003050b41d01c4d00c0c3d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 827409379 1250 827408129 827408137
    0x100f03020a0501030e150403090614280e120c0301060503120d1e090c140103020915031b12060108010603020703080f0901021309050f0a0902100c0302010b0d0b1e0705 73
    0xa284c00244841c612002c907140000c0031413106003545240041c0410b05503c0004001614015107880c0e081d11441100020a8410001c64130980c00001c1483d1240319074005219803c00c1f0b0919280700c0030b1039100001000c503007070a0440c00050b0700c8a40c07500410308003805800003c1c03c045000d0100d08482d10000c007081d100e500c4c42c0307450059448070418410100841303200980761192400b040107011f035141814850165000e2596110400702280070b440d8464000c94400e041d000c0c02d0003c201c0c1100710410038940000e803400e1000c06500c08901d840541e210082c200ba0f40c41002404202d040c203600240003000c06801840c1011300410004000c690000a038581280b01c1c0301c3c0b160020399038809903900901401e400071a103465032082c001003e5286c0d401842c0958041022050b45807500440c1a080394031501000350041d0811030721880c036074000c49865090b00d0084c0008030703000f0002d0002031058185501e0445140d03105600340702000403000100c5102c411805810310b030b1424036030005030503809 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 827410629 1250 827409379 827409389
    0x2d0b0d020d110a0324050606040b0d0b030705150301030303290d051203100503010f0c020a03050714030d0903030b010c02031207020604091103010623090f0f1008100f03020a 76
    0x6032038500702e00c15120054620015500300403c4841009481d480305540203030400c0c0d1452460500e004a2105d141040441d0100c6540700c0a261810f4080060900030b40068160540d060280300310003e402e440b41b0f8051201461160f4540e40e80c1c0d070540c0760150171526618a024007007894100f81d20303142402c0c16028100c94804865100491b0b2540c642310b0b24008100c8003050813181c010061000750408107561034182d40e400ca0080c0725a12926001070200c4040d45036640c01030703016020102c0801d01600041c1007050050b0005c200c1882d44001d214a958003840a404150b551149840c0c01c1c584d0622030000300d1a000d2a04000680c85600041d6541701082c081110480300065000115600c1c4d00c1110014482c03480d085c03140d24074000f020180d0b41c0091060101003803070071107000700710403240c80080c40079203800b0615410f100d001c07028000c2c1d0044401c0103a801030780390700ca8850076960350350a0020b403081c0f544d42d5146501d00000e655096041a134083c0000904400c0240016070f60408880c0580d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 827411879 1250 827410629 827410643
    0xc030b09010b03010c1805060c03120c0d090503030a06090510210b0f1503030c031c020403320708060c07030306050a12120503071b020102012d0b0d020d 67
    0x144505004500400400c10410f03810361030320041d460020f40014041c40c040400c044004041c40d951010300c074a0348503000104982c1e400420030101c0c650407460410390130942c0260301500340380c845590345048800c07502c0f05640c10350011082125600c014021480580341c030340020303c15410480740c0d03402c40c217500740192041d410181c0c41030341c0c045e4202651190070310f800214684541c20f00342914608203105680000322810340503524410750800000719201110190000c52400d20003107070103007078a1050000780b924107400700000404a6060b1400a4242c030001c1819000b804a00b9800150195012521032090300085001c021200d40403807400ea20003041c0f458255511490f00e42200100181d4114a91003080003d0100c0c00e07005402540803560710584e441c1c1038247c6401000d80d51404126400800603400e00942000c080700c8144180c185071040c000840d40680c010488020500350000171248980300801c820107404040c06140c2108009541d8241500c180c1e4020030721040410304045c0800b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 827413129 1250 827411879 827411881
    0x307060908090d0c0e010803120a0b130c020c01020105060411040603020f09040c0c031b0b01050609010c0606171905060615160b060108090c090a0c050c0a08190206040c030b 76
    0x4080520221000510300820481000f0300d246061040c1520601502040b103141c20004214040c0c000b0884007080071061101c5015600d20010f00d000e04021031055800c21000210200082606d004600c918000c90b00940420700c01c4500090845100074180d600c00ea0a02e45800145110403007114213641e010f180c0540d861502400c00d0040d40308c0c2302d0b81640c20a103082d6170000420b5201101c2d1148520036030f61241403602d10800300409410068002e40b0403008040100201d00d0060000c0220b1081070506000e400350301c0c1c940b941250b15551003c0d510f20840000004802024403107141c00f0240c1d950050401c4030705855065407a40f000344510b00400c890842032480c00291802c2c0d586081003040c041446501030700d44541004c078180c40d100e0200e21030a0118107114000310703245200352005000580c00756242440c90004e8028000e000b0288003040100e101500c1e010300c801c0c2c1081d8082d003c42c5603920703905403100b0614200c0c4207208085400c880c06000000c2d0b0050300403000c44e03810100355001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 827414379 1250 827413129 827413133
    0x5070c0206182e090b0f0f2809081e15100803070507050a09091a06010302040305160302030f0607120b0127180b01121508070306060f120503070609 65
    0x2c10411501d50490141c0c0c07500307908000d40c0c109000c580f0040070956441e5400d0780c2c1c0751102d05050050080c03c0d180c054043c80001b001011400107008003003800f90040c98582d482c0b5a01c0700b10050740c0d0488000180c030404050210020400400d040c407042c444030029490350944409031200c000144c0c3d10031581d090008211419411540328001d441c4004c00d503580c03440c15140403991441c0078400c2a0013000003410006a5800522600042a40140d2060710107901000c0501403c0c100800c0141415401d00004c804200f003044030700101c1e0b11001d011f401c41402c600406241c80201040031034254452010002c6440d8495240310f410080d035040032520880010058420b5002045101d9894800c3d400c40d401e4040040f00c02c208442140b805185145680d0050800307640800200750301081684070580d68000c0c941c1c0c4601c40c203030005145094041e40b50400c460600c0700035031082e100c03a62100000c0c0f2400c1c0808190800070320884c1103015501403299281030716401403041c082c0c450745d51402c01d041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 827415629 1250 827414379 827414389
    0x90b030a050304090c090603110d0c140c0304260a110315070503160801060f0c02040605060307170105101b03032d0f02030105010512090118120305070c020618 70
    0x501c0c1d1110030341c0d8070786403101040e1000740351010b401400a030107405c000403070a00a10540c403c8603007250f900c0346080c26001c6031101401d00010440c0410183c180061b5182d290034000e051078188000180d541c40b403810701d910785198404142c0c0c108242d520028040b001000154580c1c0e95a0b0203001c0a80061920000900301241c10110380c041d40c42440402560035070003001544603800340c00946040c02210b100407200078000b4021500030617041000e00b0710984c006c84c61070500c24801000030038465240c4010854a1f0010340d50385001c50b07c045002d07200f01c50300c40411405001c0546403207a0400022a00502d42501da289910180c6061b480081c2032521a800545078a14103881031402c22031224090300c86000351440151000386028110740d5804007600132a4101c520507500c3c242424040503081d40c107400c0141280d4070a40d07a81214007140c1c0c0e0050362103500c442c0035140c0350500342807061024064a4006010300100111441d80b1001a82c80c4403c0d0f40540200c4429842020741c1200814 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 827416879 1250 827415629 827415643
    0x1032403230a060905060703050411210a06060512190809060c060f19061401050c03070510020702040f05130809010219050601080c0a0f0902070f061505010f110304090b03 75
    0x41c0250140c0c180d14810702010380c0082c554280b0600440f480f80d078030020110200e07581560018240d190306180340140b841c0015088006412861490020744042c001141c035008555000303c801c81d0311000104103600d4030840200c8060304c061301808014142c00b407401d40c0d0030360200004011040101301c00541c1e44a14068a40a0364400100c615074145003010306464030044a503951040c0c45440f0340e8402d403040340150402c9403200c041004100d0703c80c400540c1c8039004018000b002d84014001e41010075010401080a0f1900440040c0d56000f140140f100f030710380713611400464604008c14402c0154040034115040c0741c12066a42d02d943c0d481e0300407030510808400030344800c1054416407082c0000851030a04847e42c0e0350440701841c50340801d100a101c0d45204000c07040d016100300f0131500005400420f1810711690076901d100000390382c2d00b4102c5016541e01441c03c6034841080c441540c1004c40c0503049101c40c140f0364001c40c0003028503640c901c0341c0d028030f401407034a50380c180080380c504010321 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 827418129 1250 827416879 827416943
    0x408040905070e030c06041a030417160615080d1815080a2004090c0905041d0c010504051e0d0822050108060d0605150303130501032403 60
    0x41c0a54281203500030007051440007071912038024408240d01900c2d21100300c8080312580c1c0078040720503681c2611030300c10703400041c0150307408814025a6102041c00800622144000c3c01c4049080080d90a100084554a00181da011004d000042c802d03000d00254440f002c60007441c01ea40074056a0919400490165010b90754402c9148440d110454020b0440b5120f0840c1000070050f40801c65192400e001d4100e440600c8004200300030300003110141c1003124116094240200ba9a030303034002040c110785140b4009500f40d40800c13901004200207001c404104103003440c027542030a040000107100703c1569280741051f40d05802407204181c44640c1c41c41c1500d60480308140e00c400c020040540003500c00c1c59200c00644041038046050760044400501402008d81425011041e994404004000242c098241480d400c80c00c01000e9500f00018451303008442003034403400385072200242c140c8030005c0e08980036241c24800d084151807c06200801c03a500040c4082841e1580c00442507201022120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 827419379 1250 827418129 827418131
    0x50705030a24090915150e07030207051605130506060d091b090b0a0e0405030304080307031d03210903122706070e1c0b1005060304050f1e0304050904080409 69
    0x8001483c1206600000d0f1150062005803415012060500211211942d04103554099203606100c0340d40000c2c0710a51259007420014605000d41d1102844d1004400c141004e80100c1e41b414484c50601452221074144008400d011600b00b9800080d014056210045031941e600e225400a22968096801c590a501b110481c50940c5070714a201c040c1080a102a0250761a44000134004500d1134030350380318580100285096840d103545000c02948090316800415444140800c0c080e24544003008001e403640000f16078803d44140f61149a00c00c151125080301c40c141e082012002c070200c121030140d03240e5040b080c103690310b030381c0c200d8008111f54a41180c040c1d03540012031040240014424010400c1d625251904801c2c5030030090032801442103d120f03c1e1005094800007190303485da140e0410040c0c42d441c80d000d031f08e071004980c60b600300f11426103e83d44102d00d4603200c05020309c1580303544403112280340d034908039074030100b03a403072281e441003e0084a981c1d0004060100a0f0180c5000d00718a0350 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 827420629 1250 827419379 827419451
    0x12010e1f1508210a020c01031e1a0109150e10021c0201020703030b0a05010c0f1106071a0105180c030603031e0903101a04050c13120312050705030a 65
    0x89981c0f1000d001141203024607412002003001600002d4400e0b44920b03600401c1d541360000d00440281c02d140b600c1c81c507404900180886642d0507806007039010014907083e52100100d25000402d00d80c81036000c00010000001c402d11240e0b44403114541a1109540c001c2d0b1440c22044128988130410000c14950703618403005c80360310796040d0010203500380a9230301800841e200034100608040b1030b2244502141e02c414038180069810300c0000d01040c0111171903801030700041d01207000d40d807210800320b581602d90b8501407003c02c010400c2c1c43c00351600340c645980b40b9410039501c2c0c01d0502c0181103861245004000940c684e50f003001100d080b98040c80d040b200092a0215141d81c5800c05514944280194600700d40e0382513161103110011a003081e41d401d080607007030041c0402000050201480342c3c00800441200d000c80395808001011595941e0340c20b8081420020036100303a4039401900c507804c0005010700c80d5882020b4a0b04003003007110000350120007550711022414005049040031507840d07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 827421879 1250 827420629 827420639
    0x10807031e020d080a0207060503190e0715170901020a0806090a06051924140c03040b1b060c0a0815030a0b040c1701090f0314040b04030501020912010e1f15 69
    0x60301904105c440f940031112200c0e200d21040e0741e14041200c0b0f01819940c120184407040b061a0490412429114140c403a115143c90811114401801c0408003003224203880f901c4503003007c03107070710340c0045440000c50038148038841c0104100e001070080d0b03104080c6c0501060011a8070b60014008140c0204941d5510807548981d92a00c80e0342e03c00c0e617460390004420b0451100c1c8510200c40003260319038592000c3d0702d8030030400426800101103c041c501c0140808118418203000814044541b60444c14007440e200d20000c0c504000100030260700542804100305440c1c1041407203070803c40072068070245080c4000030a02d0b0084103000a02240f003083e0500c01409a4100010140c070100160242c010b6940d5001a003600d4035681c0080200c02d20304500d101180c424044454805043c8400510341a81d8100c5140c0581064000340d071141d50000b80700c845c0c1d280c111204c2c1449540c01c4028000d204103600b00a031a1401d009841040070b16070911100318490f41c0d444026240420002e80c02e01903111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 827423129 1250 827421879 827421893
    0x13060201090b070e0102120f09040f061410050306090703141f0510050417070f030b0604050f01030203030d32010f06111e0c0406092003010807031e020d 67
    0x550019910b910310400850102032051401365980007068004289140c100608814035511512080e004000103016284090b03403280540c40b9003403841c0101150751414000c1d04180d161405043c0c034800e900c1c44684520080e000415654000d000315279070a1070365142c24054001e40820304005458103c2c40301000401c4014801400c91412005a1a41629154824040345076882c0825401140c0107000c1000815444100407203141d801905403490b26035511038510f80301c0c0a54004031031456080082000604091007807076408410b950700d003080c80d403550700807079200d00c2640c88445615403036246c03000700e43c040c56072007402c03440c4491021128000d584540800d03c480c01e00030041d59880020001a106100d0200e012041808002601231480d504c015a9091f0040032400030742401140c00d000790a035107c0c42120028008100701040716507400218002c444230401045110b07440510042c0710006000405134181d82d84812000c40510301200508003101d201040250f1014603410008100102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 827424379 1250 827423129 827423141
    0x8070b090a032a2c04050f060124020d0e010c051609090b0a020c19110a060e030f0714010c0f05190b0f060d1218080717061e040813060201 61
    0x144850b0421201d03103555011142c0d52404130720301032a04401e44114040340c000c0d50102d4110303228404440141c2d003242c204509100c2c0036881000821100701c4085059144006068400c070090b201a1010980280000e040340c0c90708904141004412026902086400c01c12101900540218642d00c5503549100001424180d14202c071504041c10105051030141d0007929500e4004101902615110fa02c9441d240301c49040c0503a814034201a03074501076200c50099401610041d6180b5500c00c603000b050600d0704842050001c1c5503031281070208200c0a0080b1030119000c401d280c6135001c045142040310000f480940060b120303000d0f140301e9020804100c0c41001800303200d202b03c1104c5640704802150394003000c84140c0d410101100c0d01e20b0004d54201c1c0c80c52102185c42c204540100d131103200012500709070781c04c52001540901410f000000100b0005040ca6a003200100800d14143c40301413041c05080102d01c00c1540302d540824204901002680e544101c8480840b030419a156402800703800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 827425629 1250 827424379 827424443
    0x705010f09080d0b0904020f060f0d0f05160e0102072105070b03100f080d0e010c080c011e021c0b0103110a0206010317070305031f091a0405010b0408070b090a03 71
    0x4c9031101076807803400c102194a10482c0c00420180d501c0b8010301c107000240d44201c0001c044107c00300801e00d0700c50024807880020343d042d007400142d60710f404045001d038165156411000d10100340104640c907070f800035504040e07401c060010000e011290110b28140643d0030801892030140d00c2c03000c215964440040c610070310505200004056aa42687c041c500280c010741c2c90175000040c14583c0a800742d400d030300181e0f0040c54400400d64141d2229011500541d440c1c4510341d455008038000f030350110760720080e06061203008520b45001c4024049511840d18145000251034000e86401a0701961280b201c80c05941041c540d500001180252180401d000848180c1c00550301d500340320600300c091356211030341600c0300c0380f4645031130318400001721030034a044810350b6403800c5c040f03841050703406043d5141030200c4854044800640c100310603950140c0014410b40c40c00c1c003007001185400070341081154543c444c1c01da42c1c0e005e1540412104452030700043d000290a403000d6100c500304501c10f10180c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 827426879 1250 827425629 827425631
    0x1b030f0b0a051608040201020304181a01021b120307080406080115050a120b040906020406020f060906040b0105330403020f010f0203180d061406030607080105150705010f09080d 78
    0x55980340007981120029545424101c0e5411880d01d0114041c60040d50414014011203080903520098019442d141d204401d900350b407a250381e0704404038214005185c00e4401d0001d050418500d105580d00005100e050034840c490010030307600a070f0028011a860150407802e0f6031760700c039210240540800d41c01c0c070404c01d010030020b80c4039500c02d02c10f5054647ca5006991000211024040c3e4034002d040300070780c420b902c9952106d41d0000581240700a000a098680180481c001011009420800e00130030000b10380c2c20800411000412100b607007410b66000b1101580344010120f000c814480031800e00c0903002584880020380104150058001c59108807034954801d0b151100440d20001802c0200c0c015a00600400c2c2031050756021100842902030600b540d8031800b510703004c06446400f05c0c0d10a084039448180089401c061200c07a900503901c0c108603440303516003c0415120003030076048402c3ca61000c5000c40400c0801c0d0402100da41c2c86190500901e0f43c1070418a409601041c5120806 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 827428129 1250 827426879 827426881
    0x10209121504061a1905010e04050603030a2a0f0b061009050907140d090c05031b04090309170c2805040c11030d050916050d06091b030f0b 61
    0x2484001000440945407040c40081c1e0345a6960b000d010308144031402001810007100588203032942043c4400c442c285030a0310504615100000d4000d030740c80c1407018010344c10001004202d4800200f03c07451814140303001005c0807051400340e00d140004030150450f910711550060b0a01441c0014580854000c1640144a483e01c8003002031500b00c45025801088000100300954a081400355500491604003107058008600880e070360b680c840900b020045581c1c2a9000c103104c2c0d0b01c5460005010f055009050b1009180d4002c6003001c2c42481a0b03225503100c1100c00e00f018481c1c4110310041c111a03c0700203498011258494407500401c28480c005c000106c4203820070b0901840c0368104414500c5000702c0603082c00300b80800f03810081003d500703100c030f0305540264031081040203100307547c0607242c0054141014045141800712240020620744c0c04c3c258144020340e900a0201d00c0254040400200d2540383d1529410400b0034441524102907207900002c140104106030300c4c443d51040d1646a16 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 827429379 1250 827428129 827428159
    0x305070f060806011706031c0809011a0a03080a12050c0a030b04200f040b040e0114040506060307052109030904061e0b0a0e031f18020619051209010209 67
    0x242e214200c030709900086400c0f000000c509a0f0400045d081280034003520422070711041c0c058544011004d050b000a840381040150700d05081c4501c4c040a0f007401105040c0080040002d0100b01b440e000c050100d280c0050307000c803180d004624003030341e50383d0329076042c01281380a0350000410307000740c1c0001012904003c40d1001c2e52900d80301d0520b10540b80c0c0d03075010b038041121460080d250030584072440c0c45a010070000c144841e010700504003c00c1d0060700c0702c1e00e035810030b5429a00401143e200e1130141d410101030202c1f41d0343c0c400176a584141d13107207031150304c844403070111031081c250804c0390340750000207041404141840070004004241040d039092001d03603030303904c900a130741c4010400914400455000c20320001500200414043c0030034903041c0e22044403040001e040010010708000503d1120303041d20290310060080300841503550200c50700046131500400d003548a04d03013000172118881d05100705050700480a41d4030f24416003240c150186401e00740b0354000e6108404191080c6030a0a008007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 827430629 1250 827429379 827429387
    0xc0303030609140c040b16020a170f01020f0a0507050c100527030604030e0d0b01120c06050a200a0506040803010e1b09060915070c090c090609120302160305070f06 72
    0x3004d032041000c10f0f4649403030035407182c0c0c0d103030440d491224100c4001030025015a5440d41e0b560040c00d4001c0f0700c2c4486042a41c20a860480c4420103110182d005011803811910030718155030342150300d42040e680d01d005070b1400504002094030010340c44a05001000c007119031220161010161000b01c007190a040c0b00099044038054190541d0b0552000300000d0000e849114240340b0184e002c0c00d0600112656550301401d004240c0001421000c828410390500c40304000300001484141449031030510044030090882078034410700a8040c0d44054140c864600c20005121141d03044000e03100b5a0a0625003003150b07a0080c8141c004c444001c03408100c0440c40100c0d4503a00b004002d00d81031030b1a4100d0280055608091038696202203c0c40740a851400c3c1d074001010f03410f22035220001200c0c10031850701e0496900c6101c903020041a944140091500030100f24140d881e007540059455240d40b5040f440e0203100540030f1021101a9030000800c0310014594066440c0d60f0042401151202003c079 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 827431879 1250 827430629 827430631
    0x23070f0c0812090f0a0807021e090a0207020f06090d030c03050c07090b0f091006081e01090e012a03150503070f0602060a091505060a0b0f0c120325020102070c030303060914 76
    0x303010518108030803401481c0102c0c0c03c1d40601009039942405801140000c0c2b06004100c940050342d603000102202145400081e2501403c0c04817022802d181003880800c3c119607190030000c050103a1130960100f498018000d0b82c99654981080f91079864070348880c2000b40a018032400d00030101ca11020400c3d10b00440c0f054462000301c2c0b005417140740381c10700032289a0030251001d06041455000300841032320408074140a442c49010208020103c444101c0c2103c840e81d0079545080108000b50303a070407441400c58028000c4515010841301c0c00c00c071017040500c0c07265102c1540f41c440c0b9180010081c5680000710112181030b000d40e4840c1c0c0e04d50b03001c80161103d0500050030034180041440002025a1000e40c0104001d00111541c40d100c0c80c1c1b010665200400000e990389000c180c1030f4501c2010804407100d000b20004050850400018104548040d288009240070002d0441514107200f541640c07078058000d05500c1901e50b8a04000e001440e960083c040810705140718410140d542c44e480e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 827433129 1250 827431879 827431883
    0x2150a0512180102040b21061f0215160f030c020601051c1703061002120d020a180e0a06080a120305060a1a090423070f0c0812090f0a 59
    0xa52a00c048500712001a07440207010094800e080c18007540196800d20280c005003c40340c0c1c41741e9940c50000304141c038000ca4580b403408055228400c0001d25110030f0a844099a400c41d000002c00080c5101a42440901001d54002c0c00189040209080b103a42c825040703040f040d02d41640500920401f1001d40d03080f1041100580c1c0494010066820840000110301044c030120382c020404513a1040c1140288074840040800040184543d514004d40445c060040c42e000500402c0c003014000402070040e1600c0341542030313010820088070360041010224401c551503c14060544900b1110300d203d0003034460842c2103243c40c1010403510700000e031100300a82c0000380400404400130045015281c01040381d0f800c0702d804000002d20051a80030b40c008164034203012a1946104418042100e140c24225440d581c0641780b441080000c6000340c5400500e2841d2080c0d6035403c600050700c440c90b80e6080140400400180350140c9203600b98298020b4210710181d80100703400a000c0340d40d0f03126100340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 827434379 1250 827433129 827433137
    0x91b03110a081314060703061a04050108010506070c0b0c1b0108090a02190801110c060a0b0a03080c0307080307080906060609060d02091f0216120f060b0d06050a060302150a 76
    0x420700c12030700400401c20f210300c50903a600f20003140040c003904121007070740c3e203d001c03980318a824410f0b44801803404810000c60490700d420300c0e04c0d110000305000700c18411039004a000040e0b4005000b414030040c40584544000d80365906416440075a4a00b580c150142c030803100d0000340c030a19807064034071500071355204000300349101454082010a651041d03844440c041200c40000d02c402007801141151641c08c4809500c07807810290b180e0401c1002040c5805081c03a005460342191745a941220517641c202c0c1130039442e1500c20010b24518401c401000d0000200407040013240c50f400f0095038410400c80c800e4a0703480d01c0300d07014895180210040c3d1580030384203000c0f00c03044100c20382c003501e0410310041120312040c030040c800c00c4c880d0070040385003801a002200c50041c0354034500c058200a080805804c50707001200e4448841c00d500b008030041c10741d42c6030201c00c0c035150b58100707800703100e00d1300040b041083e42040a64030000340214842240100c3d641044d016040300c0c1d400039203080c0d01007030711 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 827435629 1250 827434379 827434381
    0x8060405010f1403100e070906090209030316080f0304061a01030e2505060c1e060c0d0207230715020303040b01140303040f0b09131a19091b03110a08 66
    0x41090604000022a0107100c1d008410444031014040c10b884101c504000e4500347d81020300310070544450780c0044821a00401040d1240c1e14008200d5001e041d1900486105036140e15041c0000d00c15640a41c2d43c103140841480140715556020554103050300001030320b8200e00314010340c10384180000107981c40d0003555424044403c2c026900250904401c0000495034030b6100090040d00940e078030030b04030790240400e107644142d04040f4107019a030f1440104030034034044101e018036121300020000c686401040c40400c10020104a080348914210990044e88001e078102d651600c092040d03543d00c11501c071102d44610f00110840f2701454011a89101c1d9a00f00340c100786607005402c00311703a050310007088001210902e40c0d5101001d421004916580c1d08626030400c002d40328030004200b07800c1e1403c5c860502111411900c1071070b105040d00c8108074240c04240645940c107056004144e0241031031402c2103107200c81450043e502c034460714104103054840000f40001d0150741e5002c004034256030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 827436879 1250 827435629 827435639
    0x120902030c0f030c0409060e01050f042414180d050702210c1c02040c0528110706030209030d03060b0d0e0a0f050a0c061d0105030c040302091608060405010f 69
    0xb00300d650302010042c044800c000036903c04030f021507a04c2c8606440056072100d03000380c03000c1d0038000c3c9a048803c1041c210000d0403d5110301c07514103c10807042990180700012500002c5e001d8005000200c0c1d0712550700103500d00703400d281b4003401e00c110030005180600c20006080e01d00035000c1d5031060350050802190115064151003c01800103850350311481121984521a51030206d2280c020400111041884405105110a44007090282d00c103000d0305000e00450b40c0482c4d6001c1c144040f242840d039000c0341c3c20000c2942c0700307648208844a180180309000c40c0580d0550014166410305500300c8034005c940000890858009000d806600d81040007202c1d444503807500702c09400d00046d41a2106030b6070a03074035602c8001810300300f158607400c5003003280c0c1481150416030000b032200c0e04260f080c5001c0e01c821f41c10700400c8829064148403000c400318844040d0081500d014590241c0524003a08100004a00c40d0f0849034003400019121400500d4a040901503a4100d5002c1c0083c0b0440078200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 827438129 1250 827436879 827436889
    0x90905191427030903030301170705010503070c030305040303090b07032a05092206120515091009030e1009170a02031902190303200705150a05041e06120902030c 71
    0x500c100940c0e030b103c00d00030100b40d5517060005500a110080c0c0501450786a49401400d2a0135948600e0511a05004229642d9000302032510071991500d00041c4c40e69640c038050b40209880d0002410360840d4404019002d50160300c001c024056841d50350700801003282c01e000c5c000c0700324580c0c02c00007042842070102d50704040171901c034280e150350442c0740d50940b03646a00d001c45103941c2c03001400018421400003883f2f0140300070b02c1c18a5410311006458504001584c0e680c80d00e6038205c4102e00e541d508203d003818840d1841410b40c900c010001003008940032030050a140c2d0b1401803a401d60000160301040c40c100081c4040a0341e8080d015014031194514a801720309204031050741c01c203243c41c0140d840c018600303480344050342c801c0e207801d408001d003c0303641692420785009070b00166200e9103050000e6501c01d807052259070b200b2484a42e441a0b4408200c1d41c0303000c3d550003803440b060902440c0c12818401010002520102c0d91a085203000485541c010703107a1030360002c0d4240e00032502d4040c81e0300345 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 827439379 1250 827438129 827438191
    0x1e010e0d180e040c06090803030f19060e0a02030403110604030815010905040c0306140d11060306030313121101360b0a032901050412030909051914 65
    0x103107122500c079540c030007071414403100c1180c0031140360031080d60034071075136030042c642c070002d000f000c002103003185040389070700c030b1416409061000c0d8a0030302d20000d40d480c2115040300003c0d040b910201c1105007481d1112901030f40059034218081149881405840707a000600148a00c1e0950744080311500e1b0000d50514098103000141d040290f90840400d864446000c1d074610b80c2030035a000104549087d41a200c00d0507440011031084884c1d000d140040f0f00681c03420380400c00c04403292907a907224040020324500ca004a06841810040350003d03507c000c039102500680d015880044802c58200d0044070041f207003001029070500e036844c42ca064183d001150b48030050114070f54240c49a1180b60100b0326401c03032440703200081d842e0880e40c242e0154881c84814125401c03121101003059400010f4500d0140340036002c15150707212106400d040c8a10600c0c2d00502d144003040200342000d42c41b011120000c0c1d0001320040341415403880c00724140c144510b00c10144803024011109120000c0a0b500e20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 827440629 1250 827439379 827439407
    0xe13091a160230031602060702011503110301140f010801050a0c0912020a030c08160906060c20060a0507120f0914041d01020702100e13110c0f1e010e0d 67
    0x4180180d83e1840c0910000c501038030f40c100400001d0f00f41084000c0c644640200400110b90604501100c07440100c034071038041c0c075805041d81c6d210319030750703c0407900504429a200450800f02002e00007421204c2c51440d0580d00044000c0c00169114226070707003030f42d0101d00c42d840002c0103840100f000600c88908080d0461009003840c0c00983e6948071010741c82000d40050341c481c1c00111500174075044400c14180148030604080c801513180103006000003501c601d001c1c000e04002ca41580b604044020000c154600007800c49440b02c41c4094010721541001c0000c580c2500c40910b210382280c0202e1048100d19080d503213201e01030b41000d03540076150810314151030b04a034840c1c221000482c0205c05030b8200c81640b200050320f540190040107100700c0d10b00e2100b0184080c44424601ca40c03102c03042400c440d01d8140e030100b0b5800780600e0409043c45200240846c50207040340d0400d10700700119071008038076048012080000c08200c0d000e0708985441c03565021640c4000341c0851802d024196885401c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 827441879 1250 827440629 827440693
    0x4030f11123408091804020307090b0310060e06090c16170708070633050402031b0d050612070803071407030f05060109110406020d0e13091a1602 64
    0x32a0804440841400310388048074050f801243e080c5040c00c1c8288007408002c01090048210b040c25004a0f840d0015030044400860325100c820103039032000c000181003019030382c608001c02655400c81050030103040e900148221311b0b801c081000b090016081e0350341c0541498100762103c605a5654220100599246030100780174005040801d07e248054403890740078420100c0c000c2c2a1011400c01c9107540c02500401c441065644040382c00f1028600c0240c4030140c400584d29103401c030852040000ca140d503400c030100c0014160381002455046180903c50556465044a050700d14142c0ca80c1050301907034059038810b001d000b0100f01150f0742c2c549106140e5040c0c80495440703480348468040040f030161800d5200394010404103a007440758a607847c0c50010050b04090070100001d496401050307240702000000070700b1041945d00c815081c1c80000c0030a904004501c15807a042d010046070203c80b0304001e50410004405d044504000d00c001403040e0301a111004006820fa041c03414022104100700e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 827443129 1250 827441879 827441947
    0x9070201060b0c0705030c090405061519141005180616020907021f0b0f10090b0d0b010e09040809010809010905030d090501150e0a020d1404030f1112 66
    0x74120100052810f41d0080d8050620641850b0500d031800c00a001058000c0300c25404200c00b00d240859165002015140300590b41c0c090500020100300c819100c1c5003c804160070300003403009030b0340030400714031500383c410603c9181024001d0b100c034000c2070401350301001a03144c00c031004e10308480207007003040506261585aa00319000300d2010b1800720781c0100982d0200c40240d607a401c25844031000d41c01c5004d810b011a4444402062504a1001d041c60044c40070b0442e1049941c01080b42f0320282522400850700e5000100d4200094480420440c3c041000c01400c100582031036003a951240343c102c210300d03251030810720045680c040000d0804600f5540d501c041000540144010811403100318408141100181041421501290a00c41100302808000c1102c40a0700e0840d42e40f12800030300043e1a0540340000d41c005c0d000381d811800380081030400304002c02d500704007000400c00180c4d440c44421103901c0000c0d40e441c1d24400c500002c07014140719048840080780c8554000c6020700b1402c07021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 827444379 1250 827443129 827443139
    0x18060921150e1002070c15022a010f031506110a080a0216090e0c061602090117070617010312030b0913020f04020909130c121202070504020c0c0907020106 68
    0x15400c0680781129400741c842032034200210b41000403a01039800c54804524104855484500400342c500c25204c40d03000d5a000004420300904c6000b540021200d149010703969082525070b1003041308076101e40443c0e03001243e4006c0b14424490980c6903000b94014196960420009482414045041c01d08a102c0c034900100085d80318005000c60b9030f20f98000f040b82116000c854550001c49070000e118841c9040130307c4a010000280140007000240d42c0d4a40e188080b0700c0301c0b500c552081c41c1c0a034101086100000c1c0303819101c2848034a82c20f44400f5200900d4481004490100141451030407001c8400c0050011507244c98a101c41401103007800a04543c0b10f0000c03907144042259a8803048560704903d01c01c1d8204120b01060401040750110302c0c11034540d0005104460140000711802420880d5001304248600c240c00581250200c0d03a490061038580203503407000101440c030060003404000182401c1ca8000d0b12424a500c50150121141c0314040c8046968020b000ca42199250180052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 827445629 1250 827444379 827444393
    0x609170703180b0c0a020d020a080a0308010e06010504060f080a060f0b2109100b0f12100b0a060806010324080d030e120415110d0c020118060921 64
    0x260140c42510b40700502e8452440041c000445903020904205003008094045100440e01e14030180d4100c81046a44a450011508071601504140c0051103124116014141c104038001d040310b040d06d150344115980c0360011a8236004500c14000851090448444801d004490442d8401c1da5040d001820356a50100780b1804151540b0850600e80300080003054000b00c140d48400360b2214440c0d41c11241000307080ca5540d402508801c08015542c0c10010a09540b400780b60144c2600081002140003203480c011780c0c58000d403000d6680300324a000d41d20841c5081031458a03003180c080e9281c005040e80c40c50010f4011f8203000070300010718040445a0712030140c94410500c082c000d058020896018036100180447d0544189540d86500940b0704152030400003040314250b03a06030441e45030300c0300082401da5181040c44030300000c0b80545c2c0040d40e5000d500c003600000040c001d0ba01d60408081c042d030000c0900c203443c000d407400200900800c1c0003610f408103a40740c400c030514122402c20b02c11030322840 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 827446879 1250 827445629 827445637
    0x2407020a0e0105010f0206040b011203140a02070f14130209040902120d1713110316060c0b010605030402010f030513080f040f050307080c010e040902040e0c01120b0d060917 76
    0x69a074103468401880907513404188403000c4082400181510f040c01d40750080034400c144100480020b03c181d54804141c40351444d200654440403c8584541c6801c2020b501c61425005504109010b5079002034400300e4140000381d801805801d07074284200400392080698040c0700d84075002500c0e40084401a2240541c08540518980c054944541d02c000e004022520040d141c074903800385903050140e403c0d141c1c580034094a5016040c00280c210910109051405819207000ca0407064030000641c0d0360804110340c44280b003a0100c1c01c0c61f81c1c881005407072900050310043c0c0043c4100c10703030042d0b9034029403001c0e030000c41d140004019407903140e64440c140d6000711031071aa0880042400c21850782e41101040181501300d000d88403183c10045010303510510603003018100040d000004040c3c0d101c5910031902541c01600c20b2000c00c88403000781b41e40c0c49442400e1800181d0300041415030404c0f901c2500a9200c0c010f1009945007001e45034070001d00310701001035441005141000910b091032000070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 827448129 1250 827446879 827446889
    0x10e061e16050a260405011b020a0308030a020901020d050720060d061202090f0c0a03111b0c1306060c0213022a062a0a02070f1d01142407020a 63
    0x10100140f092202048207075055444e00c48028140700c01c1c03107a41c2e04640012604085140900740c42c040600002d80306405651001e0811f110000078440c08656580007054110070a80031942c4001d05c0d03a00c1107582c0d1182c00c2026080401c424492040717100721307210048021800800103810003180f10b110108075581540b0500c80000000030031800c6060804000f5401000b11082a00a18001c48010400d00c10800d81208040d5504850381c401c480745000d5a0b03510080700348032000c0703e05800c01296908002c424807845000200340d010340006050080901707403030031940d424441c80c0a65090181021155800d00626a000c0c4015080003209200c41400d03003848007012070081d2030b4558101c0c108480505403447c1604000fa0341800b502003451560500b0165288180e0380d5074440c84120306002154000b0440f01015400003c0d002d00703643e00b41400c0c002ca17031042030490303640d4444500080b000c80400a401c26030401c0c6010040329607102d07400c501489a045189050240d03400100e03026084e0b000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 827449379 1250 827448129 827448143
    0xd0501021812160e0c0712080106022b050a0e0d0615090603080f0a17090d2010051e040f060e010c120b0a03060204090b010e061e16050a 60
    0x1404025141000d40b0b0441c2c01035940c00707044049140000303180d6030b07111405482c1405000e10045003003500f040080320241a00b010784a9969030040000138040c1a0030b11034170006208400450015001d22010301100010541100307444401144003030380c05070000414041031045044c81c4215984845030040070591207402c1c005848003100c00c0c800a07904598200e1840285400000e200040340b4000300d1b14070408111001e5115003603c9021140044d044007510140d42901c400c0c0b02c00248000340d000a80442c644410740c990490003040b00306000114840c0f51550300091452040c0b181e50340c42903030030903e030400580100d02090441b00640d2030913141200d0702d40e080e40d5402c1c24001d03544280500020007070028022540072880080c0b10314a03e402c080b0000d56075004000407951000200001540d11030030079501c4641d22894074004080041120f80442d00c207150440d21460303c8811075540f05a8a03a54400f0041012018605600028240000440c2d480708001c00300d9010080c56000398400c82e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 827450629 1250 827449379 827449417
    0x7110708072d0602070902030c2b0e010e060a110903120403030e0f01050d0b030f1213050105040b070602090109053705060405090a0f2309070e150d050102 68
    0x400d824008240c0d011995542e1802010300059501040ca80211005010003580b0303515000c03c80b0300c2d140315100802c40818600c1c00310181c0d1803481d11503508a84086001080074031030a0082500b039800d00400d40c03503250030402c0010820b0420707602c070540e03907800001c1c80d13810840a0720200385840c2c00c00454480415000c81c08004045d407000110395144030a98844040703607800c0b40064114028034414503403140c1c46803d008001d440c200b1048103039030503030012501d0700f103c00300d4411a954032078800107543c101e181c1d0307001c10554040e1080b14201c0350303a02215441d10413940c0380e000c025084859401d04126041ca000a4642e5800d102008081c0c40c019103d202107804c0b5618241c2280030300c0c079002c882d50041d4400c010566034803003a0b8080b42c0090350401e805559440c0141b00510501d154000c1440c0382c081046044911600c3d240340c2c0b0783c90f000c0714074200d882d4410455502e192070300c01c1c60904031000c0700080c041c4a03c45448481000c0180c500c0ca83c1004541e15142a41c0010308500d241d0b000303501c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 827451879 1250 827450629 827450669
    0x30b010f0602011a061810050d050907210f0c09020414041a010f0512091515090106030c05091008090705040902030a061107080706050a0f140711070807 67
    0x2802410041005000030044e01054880401c0d501818410745813207208007007000f0b04614541c0e1141010100024000c9160000061000d01250022072071035003210b1419001840342000010b00100384c50004110213001004050704e900c0114500f202110044103c06512001822400701440500181c40c000341e140c50038100d0000c2c10071420344a0078466402c1c103140702082c0780f03c89c850b030060502c20318103c07844104485041c1e483c0d01c283e150345980145103d04100f00319002003650001901d94607038010a035116001540401462608403d510007900001007000c280a613002c0080001d440c24554200700700e040014529541d01c0f4088000714211030108410000140b154038042c0c24115410099414a80c01280d0b9035142108000c0203036030340b42000960340f4209415919a680c1c0400d449980d11030ba0304e81302002c0d12050311244500b6003030102d01414009640203407903481038170030030b1079016a465220495100c0310413840004075009058004c01e41c1c82c8240090b4014000f64400300203894110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 827453129 1250 827451879 827451899
    0x1012030c06180c03030323090a050124090902180a0b01090b131505090d150c0801080a0213020d02130e0106090806130312050405060a0b0f0a050603090106050406030b01 74
    0x506000710403640c0c2c60403228005810b0200c42d07401e5981502e00000d10408011064880d150780c183c82c2030130105213030300700026031400190020186106400034464014203101c54a0784404651a8003d4a0701c40c0034107100da00301581c00400d031580020b05540400c0c07510250003481c03100c25240c1e92061a159440c60501c5d580044941c8c009102d1000100e140005041d010038507200d40b030050350740001d48a443c02e040248160140c5100700c800900d00e064154603131401d1251461002070303a028203410013400200ea140207858240c102d800b00c80c0074103001c2034117500b00444100260300302c50050307a0a000c40002a00c0502c0901000100c1c0250070946605000b031100961105910000400c079030101c3c20310824a0100740c4030340141248000aa020a0b940b40030741d04079103085155a2158a00b17403c100a104002513094041c100c1080c0401a0031162001d011036503051b04c04031600688100c000700024180040250b0340711540b10700005440740c440c40000c0a88140760720540d40321800f00300600024101c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 827454379 1250 827453129 827453141
    0x150e03090f090a060b0a120e060c0d090c0911130b28140a09050915010203220305030403080403120302181c05070f06020f070302030c04051012030c06 66
    0x5000460800010a0018256080a15000d80070b003038080041100280c0942200c0054580040f4054850038003481c010040d001c000c2c0310403c0c0a05003501d95910308800300d00d45008007801d501170380c0703485050413509004d090a04800c8400d856100000504003215125411030a80c003000c0f403030f540f01100c8034050345031300c0700e6040900b58003000c0140e4020300e4000b000082022200d48202c6c00e40344c04410090702c00d01a0f40080751210b2400144d02100181d101c00320300184c1d0400c45c4e1007245500e501a42c000480700380104207000d070b8005c000403407034080e61011034a40741a05410b0404c1d11610303542c036642503030400d41c0215003032a40824140200403104606100d0181540340450411850746030b18121110b084400c05d02405e08a200f00d0280c11040f00c14030b0700c6035003000454020300d654a692000d6400e43c0d21074000140184410900c07081d0010a411007102d800400808a1320f002c001040300500c8060412098008604e50009a0b909000554210207009850743d400da10302d5804c1010584070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 827455629 1250 827454379 827454401
    0x130303030b040f05130f170a2d020a1e0f0602030403032003070e040f0c0914150f03092a271f1a09030d0e0307170309090415 55
    0x10508080017800c01d0101103000d010b94104002d4014000c05041108608900207481800180300080a481a580080102001d520f03448501114040e2405c0c058440c40540e0310248011f070441016680480e00d900944094034900f5248620358070460354824480c0b60b0144401c50310360350088200414560144911034074425001c81da44801c960303a085140c000c6c0300041ca09403e10003810f00f0741c2800e443c0c80d40400c03600d01c400c640800190500d00ea000d080d01d04148502d100039420f2a05424907810545007003084c042298035494203011510414140c2904000c00c3c0f001144200d807402d00c041c40a2082e445c401c08400060140700814081c00d11110356510000742228003903080c5610b80c04c00402c40341b103a010039039081309006d01c403022a0000d2080c800f9440781c1c0300307901d080e01a600422400d07401072a0f03d0100f103044403a072240b0000c0c140c1c0c051501000199154101140c00c01c400361003801d544024211075400d681c41c010514000a141c0401600c090710b1413240c1e20005010142d25110742c000c280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 827456879 1250 827455629 827455631
    0x30c0114010509010312030c030b04090b06030601061e0e18190e01060605030708040c0e0a1416020c01140d0f1b020c102a29060d03080408130303030b040f 68
    0x1342c199114111a440d01c2a030740000c0584d0343c400c00c070606200383c0c0040d04020004006214960042c2400c110080d800e50300030b4807900540c2d00000d40203005040c0084117400308007101c2501315151000b03072154003c80007010f800580c40c0c199540c640d0240940d6520031616a0707562084080321022020882e400c0900b0b0740100d0f0324090040c405150090162548104a072810040d15502d6260050108981d544800100108442131008484503500126100102220141c582d50b8541c600b041d01090796128600258005402c07a00d9203511410303c1d0801e1034000d803004c41c40d100b10a41e00004981020041a01c00342d9900082000c0c14042c03c40c1d00f1a40350144000d003201c5142d580082c0e414000e005080d824450403410702c0750002e6111000082000201b2104006221982003506008108540121f40c100c10400d40311080e059620415000303080103803c141c80c01990f0742c1d0560716240080c105440806050000d1020404115040000781d44030355800700300031550005010641d804844118102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 827458129 1250 827456879 827456881
    0x24080d05070209040605090102071205030615090d031b0510050403090504020a020606190f0803090a0b03010e0105060d1805100e0d120b04060807030f1a0402061602010908030c0114010509 82
    0x541d03286914643c104d50401d00c0091240c644400302802031180f004010300d142c2e20700800e414010341110155102d0a8140c0e4000480d8440c001c2030640303442098240c5034040c00ba1a1a08003091150500e41038125070b88035000004401c1d0b4a0f4240341050026003051460f803288104020540c0c0030380c40380010042540d0541c02c08407e44806502d5140051805004541081881d00c0e40713104210940002c2c1440708003400100e031640700842e284d0780b00e61030160042c103045100194080e0780e0340489040340c0d09103010081590030042040855403243e01002038158aa6101e0031018030a0b002c28144944a07c00034200801c0700c000b66402d8a0444d030740d044194104401821201c3d4100d4a9003580c1905040001402190040001c0c002c00050304105401d01c9200001700411811854109889004075042074985010b14410079107201c1c116070094008d1414040704d00f00c501c82111102d10907105042441c0050380705d05901d4650341040d5007013104c6039140e1400716010001034401a01402c0240c0f80c02e803075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 827459379 1250 827458129 827458133
    0x20103110c030d0615441506130b070f0c0803090102010c0801140f131803111218030c0405090a060e0c0a03020909070e01060e1e01091202010324080d0507 68
    0x41481c10141c5202110200e00542402c1170046024101480300104078003402540c0021021892004c541103400c0c4180031f44928240c0c5441401d81d02c842c05a54200460340b03003000c0005243c0e40012004035800e42604407680b000680c000840310140800c08011900c3e000d03d10002409e603685004140309000989005101074000301052045030207055070480e00180f0f501c0042055220843e0848486a02e80039680f401d200e151082e9141e002d01a1f902d04002d0841c80308016100c0900107080e2180040420441c00407019211030741154103402415507c803042d102c00400d041c0c940845800007207811009140c0200000c0307100f088400d02c80940107004482141010981840d4a4000170703104152600000d0f81d42a01040803001a01884404210650b0364010103041102c0c42510b052003000320b044481c01702910304007440f02c4410140d440e071000b5403401c4078520000340c2105050381010707141c444540240300c044400311307610f0704144003200f159032610502e01d082000491040b000c2200410210300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 827460629 1250 827459379 827459387
    0xf03080a050906010b1b060708190c0f0e03030702220e03070210140c0a0f030f08060a03080f04350609060601050d090b0a0e01051305070909020103110c030d0615 71
    0x1305407510780031103d80d250071422180041e241280d060380b5140c41510100600d40da403250300d5a0085040c1d0f00600f403c10011080c04065400c11000d0000003603591041510541c41000b20342d14121f40513013541c1c9021010f4001c030308030754903101881000c0010b900c0001c40201d528400c245500109070042c5050401550001e0405107050142c00d0400c83c00180b000b080116110403500e40c0c210b4401256000511850844035200300b51000f5008555918a4202c013240203500880c440c07000103201c2d03000c0900b903507144415904070740581890450140030105112400140d0102d0400c2500c0c1101e02002c1c401c440710301c940c1401d0707d0000c0d41f500544180061036200180c415080102420103540f180c00088400006104442c4d000e0219100c500600c403441c2e945501880510443d0300080c401f0740d58640003140d02e1a20410024000d5004800401201c00759901000d281441450f0115941e0300c01030300e440e05e07600418400b841c59000010399003100405841784030000c0051560030b03100710b54000c074060 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 827461879 1250 827460629 827460631
    0x5030408070c05030f0f120a0f11100e06011e0608040807060902130c0f08011a07062a0f020a171e0c0a030e1804080c07050301090f03080a050906 64
    0x600003440800c0a40c00c02c09010048809010080d0031a074403105440c520307643d0792081418819031030240c1020490040d0240048035a000351903121600120381e2004d04030341c102c00160408a4038040d0105103200e290103805180c02c40c0c2c2c82d08005007034650610604008081c6810402d001502420408201554024210981c01364001c0e01c45038803000c0340d081510180200010003940808840b41c4800e001c21264807648842103199142074054240000a44180e28203001b401c41c0c0041d603103250031013202006c00805500744118004100405202100344090080c04107521554910400980780f09030320881412480c86184003c2820740da65031112800741a0190700442c0a150015031502e00107030803141000c9059211200d10317610740ba140c01003074554104c094210002810034820740303c2c0f8504190346414001c2c0308100b500b640c0d129941da1000c0c6a102e41c4c0e4030700c1030b401010400103d0740d900b1301c2500440d40c0034614a141c0600c80d071500400c00c1c440106165100d0b07140901703000303941c6000100a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 827463129 1250 827461879 827461883
    0xe0f0307050c060f04090f3804020702030a0c060206040201080c0a080c0901031b050309010608030f182803030e06181c0606080a060506031203070806011e0801150906050304 76
    0x100c3d44c8591140c5880b009114581064030250b0074404e45070340c60001544080030050b06000301c440b2000084025a40240880d004940040c8120000d203003285003680c0241211803004048805840c000c1d135940542114551004000d60058030400087d5600200007036130050760100301d20300c1c1145158001e022a500688400308c03078800401e42400c00d90095101180c04a0507031007010307101000b1003005205a0040361400c130f065081610018460740000145e070013401594844d01d00709018500700c403640c2c1d501d101085074003041ca8101c000410030484824604122041d00903000c50303065050191802120b807085a00a0710200250b007559080100b45011120003260110b48480840ca0310401030500240c010740081e02d0007100051b9804000740c028107451040b0001c2c0800c2c1e880d5403c151315070000070f07500c2c512a103080002079004e0703104400041c0d01c40414144207a07420800e040240a41000c0c050b24000309400200610035001c450865003085c18161510040441c10100003c086000281c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 827464379 1250 827463129 827463139
    0xc0f020a0807060603140106031401020901021e01060f06050a080f01150804050708010c03150602010212041e060903050a0207140a180e150406060e04080a050a020c03030d0e0f0307050c 81
    0xb2201086078680104005642016440c0c00740044510168000c098500c8110741c020110314002040e00d20600076210143c0d03058020b01030500602280c00e901c00c5403903048849656840310041400d403039280c102c10180c12903030344e41516200c4854014250087c0902001c8948110000420107618004420540e052880c544140d43c0c0d21280380441c40c2480a4100354032550805030341200c0e10740d140d0b02820300d008803422060011070340d44609138201c0c4a400c400b890380c1400800001c0200e4030180601c04c81a00c0307640001d5100a1603210308044a00c032101c1200028000904200c40903410071441014240140120507200c08901c0000e04042141c4141411403441203941180039416510540c004100801510700080884150505460044808031400da18080010500c1e806c1c000c14284181d901650091510049090a0b035203500a205104114800d03490810650344050004e42030840c040100860410a006007d500b000c0481c1b200881680c000c2c0480c1001c01e00004040540034030a5030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 827465629 1250 827464379 827464387
    0xb060711040216050f0d090f0f0b0c120703031e1e0f140a0c18030201022a0409050606030c0301090f060c05040807030308070f02011407080727090c0f020a08 69
    0x201081d00b441c40303c0007402502a600120803140004180100c4c820910350f0303860015038580e580c1051801c01c5000d00010b08034904c4081c841800b21000604420783c1c241d0485084003407035190b000095114400490000e910340c4410100c001d040c1c0220341c00c0b241c040e101400700c82026181c070240c180170001d4138881c85c1c1d00c4542c107039249c40d4680d00401001507080b00003150b43c64507140a02c090408210100300003401c0d2481c0800314124101d00b01e0503694140e01501e2a000d1741d0130020100d81d001c4007202d6105002c95000212541c1e540328140c0380070720034000743c80140342203810141041003c030b2040d40640d0410078a00002100c0c0d100a20029500c0900052200d240400454080c0181e410510b21441001e030301100b032580004060348125483e03a13909152101c5a0400c9003a110352510410302c074019000802d4603140a103109940c041c40520340386840c0000d1440ea904503940e25015610812507401e0240048506400307250491141c50030f0540c1d00400c1040d00030740c1d8648a103000351a049000ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 827466879 1250 827465629 827465647
    0x10e0312130b04031a0f010305030406050307050f0d140c18040203220b0402030111070f2402160c05060309070e07260915070509010305040c0b03040804090b0607110402 74
    0x1c070950003500c500034605031900d490b407401e03414190740d40c414041c4800303455000500c03170b1010303008140c184e0358800c02540c02c29143c40c6040d2866000a0f2030001031040500c11041540340c4240500150106030402007080c0012181d004280c100c05414120715010411440c0c100c01d04441c021a0644000d607001a500c1c1da072040c1d500580b0206031814000b103e045e02050081c8890700c46100e000b1070003100200306401080084d61194072401c0c038028070000c6180c0a400114010070240d001885882200c02e4080d103030600144126440943c4000d07043d841049140c0c24413610b40d01810240c10306444c440e1450810b500c2c02075499055118254143d130380c440000b54814480c1c40d400b101c40c0b540f01c0b41c00103041070702e07201e1000d100c2e02100c542d00c007841004501e001e034040340340b107940c015030040e21282d103007012010045000e0300c0011b000356100250b580c1d00159452400008603ca60f000b5020151114100b1040c40150f07220400c1030345c0300d01004d11240b4045035020115000301642110016941c50011f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 827468129 1250 827466879 827466907
    0x20c01050c16060c0611030402010e01030906110c010c09050d0206220b04090c120c090501110c0907030c0f02010b030705040f0b0904060f0c0201050f2212030b0a05010e0312 76
    0x410b12100b070045140ba0b00145440e0054042c0300301510440f014030940210381d014010f54041118044c1c0040c40b500c50344102035000340e000f20802c42c0100740208103150946010702032988550190002695151b0452209580c0320080f0800f9041c00c95083c07821040701d80002c1d015001341d0044241400d0f00a030300c14441c8004021030f81c01000100030080d04c90795108030010050510601650200310a45140c9214040314800c25041100301c0e103d0580b11400c0c07800440f4004010001e40308644960348035070726240d43d0154044e100d02c4d00c6a80100300c7e20300e00342c0300510717140c0b05903030a0081d0b80c10403154100b0b650300032640105648082e1030001d4a540b0a000e07040c0501301003540345070003903000802e000500400c2c0d003061040d8449008180040360003100124200d420441d09421004451004103510082d000d410081c0b0702281c0024411a61081e181c498102c00742c0400d500100355030b03c5880740c0505082c00c10300c00509003405c0a00c028116040802d4854414082c1c06858030030010f81501c0300288 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 827469379 1250 827468129 827468143
    0x1515150d06150305091915020c010f0204030302150c0f16080a0806041a0918030c070626040506070c031211210405100911041a1003020a020c01050c 65
    0x5003080c004660340364109158002ca584880700084e080000152a41d0000a0600700040b20000030044010054840c1f2040c280d8584003c0d0a00d6000c20201202080034012188889988400140d84607e145006071410240e08808000880020204112980441d06850600030a107450036614182401150802c01d014007004109282c0802d02c44e4010354807400c0144502010b580400c42d0250382c5950780700241c04e0090680d8007040c0d034800940c5203a03001410304528084202124148440c0f07442c014140032003030300b1220000703d01e65265401000c20318800c50520728034014034411800c244c0c4440d42c0f5580024401814000003641410404d40300d110411681c0c46400070800405c44c405203010309507480b43c0c480d4140750188800b050365903070100d00d0301c0340240e611000600009107400a02d0707000e04401141238130004000100920315407614081c404410b25641c440142815010b8101f2149021410000b020507105020001c20103070002083d003d50b04c800d0a0540c0c0ba4060210110f2600e0301d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 827470629 1250 827469379 827469397
    0x80409050a140f10030b01120501060e091b0604030816050d0507020d06051504020d020c060903090108160c0203010504030309031d1e0a09020a0807090e1605090303131403151515 78
    0x541c40d400008c4d041c0b04030010030252031042000380155592038100e40d040301800e642880c42a0000c142480d290400500f0740380c400c44000c0c108500f0503544c3e8036104040c3e0424101a10700031580702c1e50104201c002d20650101c1060303814110709010072500460b809072881e50008000700e541c0d401007881e0070b1000240750480e1500400c155503c24406410101a41280701c08008070702c200701c00b10303a40b080c01005072154080c2c180d41d000c0c5141e4407000150280b003c440c03241018050311203590b5026840a0003418072842c000c0e02d0214110043d450028a04013070b8040c03d500d9100d001c54111280d9a840c03548080c40354034048590303032080c02c5100044607280e16610686880b032001484000035600711280c14480c2c003a40d00c81c601070315075888a502c0d410700c1c100d404209841c9070901850a144c06140034116405014088a051480c2e030407103000c05402e035070003025402610b824030007401e1408200c4146003a00c090150007a600388507a40b4801c0103040e03451584541e11303100c07184800411441c10707104040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 827471879 1250 827470629 827470643
    0x31b050f2d1903020301321e31151707060e1804060b0402091804020a080607020c0d0f0203030c1f0b061204030302120c0405090a05090c1201060f03080409050a140f1003 74
    0x1a207080e0700c0d00c091103010070108c0d000e406180d00d0808080b1032624500003d2212100008c40d00e07812000b458000d251070807400901c00720200e804504244401502c0f528a1801c40007095081e051540c0980503c4a400903c0c3c49503a02909050340300801c0001c1c1038116034010008144983e00f1000600030740118000d04da00141d4885040441d0750944541138041d5000f03803030300861652216105525032404895807009a40411184440e134140344e00b084200e60701a41c980a400c041c50f0380000d00316441402420000d038401c1518401c4140300344040b0319008141d00c4204002c0130000c1c0480d42c180184550240c04000980015041c14041c2d011203010900c150144106442c01c00601c0030703643c005002c0c44d406030320000005209401c4502c034140c01582c00740001d109441c4003d0400c1800c1440c0d4000d00d803195211640001e004200c04c00a1001c1d40c4910303c0301e61554105001031007101d03401001102550b080c48042100c0441d0140d0b066008450343d58280015900e200c5c407803c15880b1071380020a00c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 827473129 1250 827471879 827471899
    0x904030c140723040f09051e031b01020a0e030c010c02010e040615020a05060a150e060a081605191d04050a02030a06020a031b050f2d190302030132 65
    0x60b145101d00f55840c0c21a010000d01004c02c6942c0b041301c00c0104010311a078000c0e40422819042c02901d0340e021003c84007103920b0641540e8400d20a13010200d41c031001c0781e40115524141907005181c41c1c1d15404198014400038109000007014030b1090440a0f05100000510504c9078460740c01c10409040c942c00380c40640640520025642c034190f88059655002c2c00012030700240c900e00860303180700c10346a0540341c2c040c1050200c0040010292101e6404022200c00041010080c42040c00c480416144410684d29240038001d9000c015041c0ca1000b0085040c00e0040342c034124513441280040554155070340c0c2c0c8902d08030789000360f140c40c041d60500c01e420580d010807004c0e8000b40000e4007a0f5506201341c880c4d1020390080c06160320340c40d1022070070a2101540070546039024040c510a4880c3e5400c60300062000010300c0318882264030702c030003070000381d1a0340030140da9a078401c8050f20b49400c40c40e541c506480d036101c1c068454264003052040400030a840701c8121541910607000624040403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 827474379 1250 827473129 827473169
    0x9090304060e03010b1905240a0e190e01060246050610051206132904050d08070908070b0f0f13050a050f0904021207120c06020c0904030c1407 63
    0x200e0301b050301c0b4a03031183c64400d21a0ba203280c182201c082c0f071010b51200b02c600f414115007045c1e50705000344045a40040703406a98035000b031203144081004100900401416505185009040445220900c0000410408910b45500c03001c0c075090500c803520682810070480f00740349a11101036a65000e80340d842524280210030f000010140102c0d40100c80314035440207200c120a44641007210010403c1d450300c0c0c0c011020070400c1040c002910090040641010221450f451210303070142da041d07403260310205004141507080700c001c0303030081041c0c10122030552600e065281d6a00590040c030481c4100416051926084a410b8030146c1000f01506611641a452060f40072000c2c1d104c1e01c0c1c80307484440e000003500c3c1809195010b240c80e020b48001d00e0341d51940c0900c20401380c083d83c800058400c1c1d0302c00051114050400c0d000c41c41c030414645003054035200e8001c1c40c01d5003956a0900c1441c40320180000030390061421201c10340e01080107500303c00d40601c0641442501d91050280f81441c00c04050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 827475629 1250 827474379 827474419
    0x2310b0c010e0607090308070f03030f060b030a0c03050609010b0a05040308040b0702030c0a3002060408060709060914010c051c03141b250812011409090304060e03010b 74
    0x114140c100844043c2d039182041219510240d12018101e43d400b0013090000c2425a0f48a82150303000342008a051030f0682600e034102c2c1d0081d40880c1c81d0b00804018440c00b923025028018241d0341c28901808030741018400241a414184614002d821001a01c903510314001c0040d0b030021034101804944403681ca4200a481d5400000220700c64002d41c091b114a03032030030404440560358219007501190b402d4040700001100c0300c96a0100700d020381100a001692034000800c0a041c5903005844641050500034106140d46d8004405200c504031040c040c4600702020140b20850902c4d0000e00701e26181000c07800d050741141c00444400740481611031586e0140c02201c428241c50006c10340d956241d06e0306e1003c02440c0c24040103071070010042c0ca500c09480c1d200b03030100300c9003540704106000035690301c48140e03034002c1500e046892608001080410041ca180340d00005007900c14144c0b0340b400c009e5442c0c0380c2c410380c0a15400d101105550700021f4409600992a012025014442455002c01004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 827476879 1250 827475629 827475641
    0xf0c0c190b09190c05120c030d090513020702030c010305150d031110060806041101051210030c140f361b070f03120209060d0b09090102310b0c01 64
    0x70b88078400c6000c50450b502d18805440c040781d80040e803600364a82403c041000d040d6407610050b03068800d00d01400d01c640c1c2d05004400000c500c1da100c483c0303c6032500007440b491181c150415071030180f0602c40a801350b140442c07603030070b005024030340041c0a542d1800c82c0003c4c0e402c001e501c290001107008140d4101500032400f4807004044001300e0303d0355019890418140c400c203018200e4150081001300780002c2c5600146001c825050610a050102d115010f81c2068800c44112252082c012010014064030a040034007812041c14060810f406920100b5080343c0c4c2d0446607400f03912404800c3c00344000c0c009003c142e0408640b206001182ca841c480d00d00703110113481c40030342005030340d444800014641086406140e0b1141c126441c1d69000d85007929011000e500030744420390204441c0d00306d0341d02c51001713186400000328001107030441d602c140842c0c840004c0401115030710410140e80d074543d80750012017100c265a040804072444050300d0f001038950707560100381e0310840441c204603000700c103412a07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 827478129 1250 827476879 827476891
    0x2120f0411031603020d03050c1c0f0527040b0d0501141e0c030406062c0105040606050f03150d0503040e070c03090b0d0b13091104050f0c0c190b 64
    0x5a80c1e111040000c2545540c80869407800348044603108000506081e882114064003a013440b80c1032483d1520042c0c144003080e960340e0311910700c10315900c6011790819210801d0031290301e0100c0c1484107402e243ca078141d501c07031122001c0c01016010901155a01c2c0c0290361586009403481061901610345030380a1712040681041e1050140300141208102c010081c0e4841c4841403001c03101d40f0f035040d030700750254800b41054030016150f50011466154413003141d07402c007980300c484244904060465024109040c0c22640c80703903080c800100062907011043da030743c01c4102d1380240c0e40c82d03d134582c3e026261002c3c1c231525a0000111034015043c4030001c0040e004884682c028841c2d80d030788130701c2b0844014800c5203004011074200704003482645041c4004d0b00d540c1e002d1000009045c80007100188a20020501e003c40d0b960701c1e040344d602000741d407902480112005440c00d0015003025505842002002407091003580d6001c1031401d5103040800400c2c620312280c503100344140c81c2504207000f12140440303803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 827479379 1250 827478129 827478143
    0x10060e0109020307090b07050a0f03110f0c09011e080d18090b03030d0c02160305160515070807080d05040516050136052106070504030b0a0b0402120f04 67
    0x5920007140c001c8034420005079070707904603032402e20005100d42c0d003000c0001d40b100c1c0b007101001d00004021458082807240030352542100c0f1180d00a100f486d1902c1034180e055580c001064010701615804407140c10748038086000d2202050f00c4001500c072070b449a20078075007482447c124184140d009501c0c00091f0403a821900c01007900d414004040e0341c10a0384098142c0d00411015022450310350000d403581c2d080b0720503114003004010284a00b00b48581091380c09812140c144041c003060748002c000182000d4030541120010041400068080c815000c1d003510030020360041086280000c550180190000c1082142441c2c20525176500050308400c0ca1140d084002140560180e01c0311164a84c45149410a0068a40c214105000c48484803961410301440108155541a80c0402d1550890b50080c0c04c5080b044402480c000016144005000c007c01c8184003140081403d140d10007040f040200c1c03001c0030b180c0802c00901c40e4150721850146404140080c41c606900d060340164014070b2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 827480629 1250 827479379 827479381
    0xa17091302040f050a150909020d092406080a05060f0405030912070303030b061c0906180f0203280b07090b07030315051f0804020d02030a031e03090b01050d0f0510060e 74
    0x30780796804500c0e071217040c6d01188409904011075916600240f89406000d5400300e10070b07555660305d1035150540300c1d0740e0082d525a240454942c244610864009000750401800c100c00f640c2c0301c21752180c0c0d010b0f080c1c1d410155007200003024040c003001210241c0038060110703503c022a01c240b0741d403181c0447c003044002905241e20b0112901d01303a170a42e6801009814400405a0300e1044070000300b4403c901291966140d1406c0948800c200c0707410480c0900030b4048684400c054410941080c0751440500f01002c0d405040c1440c80e0094603440245075801402d06110703031250101564030351650341c072a41c2003000c001000d9080640c0b50700502c40c1c90a258440c20840754036130041090a070103a0110400d080c090742802001d40d842010055000384c005428102d01c2c814507000b0030b040404020040e03020400c40f40010908000380000c03074070060658074003044503000ca03030b4440e0701520040c424a48500f0007140a001440341621180c01000d606c802280c14403842d0306101d4011b408184112000510508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 827481879 1250 827480629 827480639
    0x80d200106061d0f0402160c0f1505070c080319030b01030e19030e180f0703020a02060f0402010216140f06070807080a090e0f010302120a17091302040f050a 69
    0x10084009503982074603a882a040d01c00030501480f0040d01c000c59001c08021801010b0b5100c0d817000340840300e08080e0b81c10354400700e42420b0b008000d42c1e038010045120811820020a0300840c01680b044110745070495a07000c07103003000000401550050300703180c0400226a01101e9110b81601c0d00d203907998034180100040107006608850b490071541ca2260002c840080c0107003030044c0f010036071a2003070a198881072554408160901c02554038100c0b070400ca1020301541c0110f030b2070f0040d0300036046c0ca4250310300f148144000f0344404014043c2c04041c1c51900110b02160b00074401080c0c0408240c140c51440b96585404039414803c0000050242c1800308101360281403140481c5c410503000f004032480e25503640e42d1800240d1024000c10b041084850340441c07080008800c0305d00504000b07003110750035415801004a80d18843c403040c0c200ba400310388240c00080c030b032030003568001d42c003d0256500c0784811004902810102c0081c0798000c1d1001401260400d1500c1c20708080c0c8070151040c908007030b00e40c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 827483129 1250 827481879 827481881
    0xc0e150907110c01050a090902040807080f06150f0d210f26060103061d370507030b04020403050f060702010207080f030a0f1107030e061c0e0304080d2001 68
    0x241180a0700302c0c5000e850f095000d400188542c00c0d0502e0b15040d0300c4d550380c00b500c089801c944c201413240e40042ea400c00582c00108900d90141e807a480c060b00301c4d40ac00304801c00a540c0ca4090003070180250160411080d1740701607101c1761040d04032041c45840041000724a0b450f503070740703401040426500c080e80d5012512810003107060801140c2d09880c81c585901401c5015400104014109034480760701040800d83d081c07021281245000715030340542032544030501e4103022010320b16090881c900345081000d08a1518919808400d940006d450b1101d0390100c000d841c5c2e11240e96082070000400000700900091082d0500560b40c0075100c654691210403400e0b8800d0041c05007501200303000802e4030b41202c400031500710030b580c0c5000410002e54076940301a40e1103609140c50454010446d0010700d90440c1040400e8001121a05c0c80c00802d15203614000d0000341d5000e43e2a682c5580406080008108540141a0520031a41c00c5030711000c0040005401154028a00d91101c507070003059481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 827484379 1250 827483129 827483147
    0x90902060f2107110c09040204091a01090e01290109261207030e1002391203030c13030f060b1302090906010e040f0507030c0908070b0409090c0e150907 67
    0x807650103800c044021703c04201d504040540305907807144d41e406140b0002040c4101c40207800400351004a00c942c0740004e04000c59001022105a0ba410301d0303900c0e480301f10700e03c15109401c00c1d034031185078100c110900126210040e54120350858118103200b0440340070840d03010340c9421650001c6070300c3e03003022820040a0307018055008000c03d010340d0040501e031074151081c0712400d0140c41120b40f40a0081c149046034102e2040b513081a10010101400400381041c0101c10400160f0724402199040c460403030380c81c400103010542400340410707810210860004840011a003204040329820920300b0320800038140300644600c10440a0f4100d45058039500030344200460017045050315945410040d01c0e507505d0b04a40c0b1341d009684150110f012010391280902880d215500042c000101d414060a02c1040e60001c01659000f02e008100e0030542e4021030b4261201c0000224070704405150541803a03126070070100391a4010b004100c0c0b40c10b05000881c034003a000b10ba0051003521341c04d00664101035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 827485629 1250 827484379 827484407
    0x5100f0209040b1e0409080d02030723090d140120030106020124050105160206030406090302060604060f17030403050601031b230f1c030503250504090902060f2107 72
    0x34240000f80100e29186c1d2103071140900403800130303242945885207181285e10440e1900081030813a22222460b121007008101d0803014440b00381d2070100b15100003403401c1c040c1c0c10028480d810203039160208040c290841100b447d00c03918410080c1c0c10800c0c2a51080c3c0003405400015803901c1d240d007118001c0340603801c40c1aa0054480700700c860604004582c990301684001d13082810036020200141c40e8a0021441580540800144d0841601e0000d082c1000600303580e2042c5c0c1482404c2c450101c40f02172003001c40d00d0300e14000540e80240c0d44940d04500a5078406045801014000410300800c11100b10a0410368031204900c152142a041c180d20401002034a40d000e50110070b0f030309030805418840c14184001c00d80d000040030340394040d140e801190300403400598080180005102000b1a0300e6203401500d0443e080c0170f4007068000c0031405148600b160341078643e1481415511044103d8100781c81f0700720b80d10b503181d15580500e04070740c4c0fa032954541c00b1440d0900184159210f0906075443d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 827486879 1250 827485629 827485669
    0x1204050d0c030c08031f08160618060c02130c050d06091119090819140f0a0b040813060504061b02090106030e030904090b060117090606040905100f0209040b 69
    0x1c8403640312032440f030304003d12682d00e132401c5841c04d0a0400c1c80d641c004c801080450018501c20312410230134002c94446600800911001105140c0b03100342d01d08021050703404a16210380c06104500000740b50020070541450250306d440e030340c60f84e01d6920000802078804008818002551b5401c05603080f521409200300040c203080c000c5004081c220720116066447e00d20b03100c1440b540b144501420940d16041104900d031500d4402000c0040d60351035402280301c0315014081466100791041d84828042200400c3c1445d40d400140802441e841a901d444601c0e8100081e00f0b510f550f0082c007251f0050054802080700003007034103031560210741a0350f007040e80548005616441c08409130040c140c40010189140000e100320b41da641c40d648210010f0900648030910281031040015058440b080300b182602200c41d010040e20a400056280c1c20010640e000030310f08010b41030003410300e413807512401c9a4a0070803452a500d02856009005001d0040300c0801c240c0030083d00300503c01b0350410740e200201d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 827488129 1250 827486879 827486897
    0xd0207050307151e02060730020304080706050a1d0105071706060408030c010b04140106170c0d0e061b040e1305070302131a0105040302210f031204050d0c03 69
    0x2c3c1c14908010340e00303d02e40f41460301e001807501001c2892000c04032030304001a030100c01000200d55010603a481c0b00b0b4a84041600d02c105c03503103149030311045c0042c0c08060403074000000c902004000421109400e400030400c000e14100704c003200c0060003181c80c140101240d80499020761001c180300e410302075061a15481c1c2c2143da000100e001d0400024100b5900c00014480000c0511040c4001c3c0000c0c2030041c000248020090100310465801500c00b100307218410740180702d6950003500d8003904424410b2100074541c0e6044008013148600c0820780340c61b600300040800d10300c0d00002c2041c040c20040f198240103140e840500056400381c1d2207010205040c1c2d00104042c0141a401e2161060054003540e805980383d401241d50806d20381052800075554102000541400703204905c0380c8007007442c000380f80c984ad640014041000005520303140d0900306a11050070302d010843d08441466003801d41e9120070100c4100100e2030000c5505940301c1c051501140d102c244210030700e007000c42d45601c2d8003d207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 827489379 1250 827488129 827488139
    0x60a0f0b060313020102120f031803190c080409140a0b0301020a0f080612060c0c070504020310171501080d02060115050301260307121b0b0c0c0709050f01030201020d0207050307 78
    0x10280584004c2c3d0550003181040302c0710410181c004c143d080c01184480da079a0134581c1c0c010805610802440445030003d1012101e0702c1c540301c0c0c8940d0300d83d95502c0d014000c100c0500b0031035140e12441d030007450100d26104e52140c00c40c1c4290701440c403414040300d08105402c0c0500a0501340e00c908074002000845a041c03008201e801440032507040070b40641001182a01618083e24042013999070204603100800c2c4210012400c00004014210540e13040d411403c00c10062202110980201041113a214144101300103080044504400e2810f18000055a65000b0107440c2e82d8032604240044c0541000825503c0e0040c06440400116903200392450b0710705824454550b1003111507680c00c0d00744000005550303800300040c00c0340500852220018101c2c0c10005000c20b03c60090204035420049000c8001c1890403914651100b818440d032540c030b414140c10703181011030540114030500c1c901001d0100b0004114401d40c10f882c402e0302107900c2c0c52000403007a81d48244601c41d2075815402900c0c1846 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 827490629 1250 827489379 827489401
    0x504180201020c040e0c1c0b010608060a080a030203040506030c0d0920120304050f0a031a0f16020d0e03100908030402120f0a06020901031b0201150f0303050405062208060a0f0b0603 80
    0x1f60004440800320611590760750340f00998800e030b0000780042ea01c402844514502480707040000c22150000f00b4400c00c0c036a0b4046d449001301c0c81010700c1a00003100050f0f410640c04d00703e85842c0d017140307010010100c0d039141079400203288040c8051214480c90154441e03090060784401d80070740ea54002c40c1091302e0310080003030840000700400e4001404d0b9070000b0000701c000102c507041105001201035180f034901e4203c003500d6002024560214400080c4400d56034010517904403601c2c042c901110182c00c404c01003132808401001e17685050740740c8800ea41c188202c0c500910300403403007200c1c2b412303403901050003403540c0d1f61640b2103d44581d0000072081e40016690340c02485194410304003c2083d00611540042d58020300b4001c40c0546d446802c62250043c0d041200409010b003c19406a01421520b00415901407400761a01a00c4c00040176554519240c80d0851412500360916130429180c46905482d45419181034100e5400c11480600000b00d0b0302a20a1b0000060301a07819556805803041e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 827491879 1250 827490629 827490649
    0x801290609061207020c0103061d0414070f1502030304020108180109170306010306080105011d04050c03190b0105010309081602011106090a02240708130504180201020c040e0c 77
    0x5540100100220850364075620b014114440d4401089002c0e03180c100406414142c0e4512203504262411009001c00303260f010490340d0500c1e910641c03840740d0780d032441c01c503c98901307035103142d12548a002c400142c001d0f404a61141035401414104504801d44842666640001c3d100280801e00b103d00040a2440b170750368503140101080c0010034040241e07150740c84084d0035821501c95100c8004100070b46960180503000040c48482d0080110758544240c1e1590b2643c0511360301a000040c00200701800810000481400c8008040c0d0f500c48400c0407016113a00411002102c829a80074000035596000c1c2c41444560340d0000c505500d00340340380d020b051038a8041c25080f418441c11401800b0303890f40402c240fa00c00e10819009007480b52150042220740101c00f030314042c3c582c41002501d000134254005440980398440039098403050200007880c0b00e480c580d040b03180c11524010a41c03004170302c6001541e0041d4001e07000e4034103080510051009643d80322200e80080c4d031281c1204846424186059 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 827493129 1250 827491879 827491961
    0x60609080615150909010308040e16020303070e010203130e040b0c09060a140c1e0c0303030603030a0c032006010f0e06100f090902070804030501060b0a08070c110d03180801 76
    0x2e41d02d000c4c4050b0001c0d050b01c100b0f80080d00e043c0d40100d01800464400315009030005c5075000c2c0d04440c1c0e04c80c140b0095491000400700c50070458903084000710717a4020401c0e960031b0087c2e807018103005600c9280c841446a42100c0903198008840d0220b1410f0652070700700e40f16650081e003c145400700c10041510305a1038100d804201c02c5041000e01032241701070040e440d50380725000c020481440c80e02c0a4902d00817000017828884c0d0020400d209060303800204860081c21181800f403030080e201d050a807407111244078001131810342c1c40c18203007a41c803000c1032250581d0300da4010090150744600242d0306582c02143c000c1e0b0881411001c0c81101c40c0680303131551500c40d140c81e203c040251a19001400e9812514048840c1e800c045024420440700380280030217412003c071814103126003504000d20400c0050600018044e40060801c14004038080320b40c50b2200150540010b040359180041400e140c00f00b401541a02d000710205070200e060149120001400102d18401d080316800c0b55080d240729000e0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 827494379 1250 827493129 827493169
    0x2d0a020f150c010f0e070503061506071202010e060f01140904050106051203091e060d1505150306030601060801050a1403100c08040c14060301030602071113060609080615 75
    0x303079841c00400c0308000d01c60208404008203108025101c114140c4800e640504c030142c002c02018040e5803400182645d014610341c0288030407d1191004c251700b8810a40060101c5a042403142440e03501500005a10052182100c0003a940c541c0721801491081c0144042c220708264220510320303045105680080c002c00c00007404a41e284001750681e4540c01c821540c582010502c801b031031a0000a01c075103d030070550828415041200040c00e244214071903959403079aa203140d0000c01d01c17008204409880d01401d00d05031f580d006440301c09680c0003125814800c1c41460000318805100304021412038101a140c2c08015040c500b00c050011500409103806100b09001009400c0c22030140a404890503243c0401c107007000e044c0b840c180c200d90340000c1341029440b5407a900640f1100c0444c6e044a80054005803030b18251b1030001441103881014036440300c0c0507403070210f80e50000d50224041314145c2e10740562890f0b85a170110f0b01d5400842d12142510b4081c42488400e04003401c4004100b040089 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 827495629 1250 827494379 827494399
    0x3050402121e070b090f0d08070803010b0d0b0f10110c130501060906051603030e010b040501080d170c091005041208040e06041407050f0c0601082d0a020f 68
    0x7403154a05140025500020707481808400070040c800e1000f030000e042070842903443c01ca07032400442c10f20070000c3c18060250040c2c84000c4141b10800007903416241d886103011b07559595595000c051a00801180a20703145480759100051402e00c045100c01c48019062800c0241c0c41c0b03009070350009803000183c40600410700140c0081d500d0b1651980f21440342c0c17030000395a50402c200100420a03541010040c08400c0140701a214183d4159507000c1d50301d1316000c00d800c441c004056000d0f10100b900d06030024100f0b0300106a2507030100e6405050425640e9114008501050300b101e4444d041d6150790628104104034501402d150129406c4800a070a000b842d003a603840c4440218092144140c45d0702c80c0106007400861070600b4401d0704200201e0b02440710100d05010780c180800081c00480c00e0040018030403402c0c400e01800c0d25000404001a03458940c0d50300b445640315410030181d031000003a050b0460f01c1c945c94a501c8030b4004030710b400092220620a03428011109215205282c3c040c03c002c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 827496879 1250 827495629 827495659
    0x10c211b0c210512030711070e0a0903050405060324010f0c080a0306080604050a0c1401200705060d0203010305211803030d0507031b2102070f02091003031404050603040303050402 79
    0x1501c210444c010308030603a2442c1000f001009401d466541601a4000c12001c210784401341c20440d070040c0001500051122843c0b8055410344526408160010008002c10034204003154828250019110810300d5000c0d00000440d0000c0740d0051800c086205102940049001c140181c12080f00c0c600300061034035120102c2c245004000c032402c907040c0e03000c0c101c96402c00036a040300000908014181d103150b0001100042d210070811150340d07180f100e0400d411101e07058100400c0c001000044d0a007a5a44a800740040c065402404107946074816526003100303c0c903c01c05e220000d250820102c50612400c07d1103102280c8075409019071606c0188092001000c441c4070302070183e41d464a00140751500d015442e80c4641d060512107050080000c440c42503568002803507610800c1030500103980d60740604c0c000310280300000010390028640020011550000c11941e01500e0103074948610010156100c41e28500c02e9005182d04a0001c2c070101d0b000078041d030005030b0007910092814000303030502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 827498129 1250 827496879 827496883
    0x3030118020708130b0301080d0c0f02040f0b100f03291207090f051909030221070c06020f1002040812030c0c1605100305090615010c211b0c2105 64
    0xc0e4100c00174041c400401008a5442000f076901030480701d040c40d1404c150a5100d100e88100d0440010340156144c5940442102c81c0e0390100f14840c03001041924048865503004101d6040035200c840803d1800318089442c1c1c0c00710100200020701c400402c3c0601481406000220340c03c3d011202c514401d010000ca01c000b401d0040c0c03200c001d00480e0002c1d5900d84000079480000003940b00c03040c0e0514208046000c40e0b8042800700051400408000f001c031810450250648210361000c3c000200d80080841c01660209002c28110140c1e070031600e600d10b091200404a209522800c2d18079401884c407182c0005040700915403244003d000c075800e1600d911040c40c2400b8442d00e40c3c062035a0043c1041c45075140c03050070303510101110704d002c000c2ca103028202682c0e0307a0005801b2500c0c0d0841d1562805682e880b8000d4444c2d420341c426945a80c840040c11043c482203103c0e40054080b40c2d074050031102c6103092400c00400c1d6600400d0003460a0b1070005091080200702910300603210054000401090003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 827499379 1250 827498129 827498167
    0xf1506090c0e060306090408030702071223120703080a060510030b1306080c060705031b0a02030c0d030f14130806041403070c0e100302101101050903030118020708 72
    0x880a00403071810080500140703101c1e0200c080e94800c140030310078081a616881c00360313540240d100116030380d25121840140d203401c82d60f83c0050800c1c80040201d00401c590345d0502d5020440c0c201c2e40554207892010260703240c03180312600c140f000e41c09220a0740801e10a05503540c1114045e1000120a43c8407400315503011624003034003000c6900c4222503c5641400c4501000f420b07000941042414148000c0c29240c18120081a01c60354002c034011044c4882401200d00c00c070000380c004800c0c817880703100b8680c0301d620044d0140c0c824004c2003550400382c00d1a01d040c2c820580c0c56030307603030102c5584003d00307846009940200380380d030fa02c09224441003959001100005020084028600c0e46424980b034403e00c00c241c01c12140719003080c4540d80000300301c640503d0583d2806500768110b540c0310404900340118943c0080d60150212106459050300a0010481c0300300c0e80c0700a0010342d0321044845c3d40d9100c01e1048054104070741240c1d8002c0c41d030a901400ca0540718010b42850f00260708000000140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 827500629 1250 827499379 827499389
    0x8070e0103270b0c1e0708090604260105040305190909240504020f0a0507060e06040809090a0606080c09031005070908101401170a020d05010b01020709090f0f1506 72
    0x1111002c0c2c28081005542a07101c0207042840d880c00c412541a04505009030303404008007040450008100601503041e100b0201003e031926445a40d42c1c001c4a134140500c0122407023421013038000d00f16a10041c000d0310710560b0507485680c58618039208000b502c01403820042c04111b038109001c14030511900820348101c44040710b1800e59504000000c034511700036800b0f503100b5481001448070b0607400c0003d540c0241c0f010704085e52694480e09003a00038100844180899010b900208420003900350060001c417a410f86a00044c0d58a0042000403201e240c080d120100e5602d800040304400ca0000400302e440c8082e084d1000c10080c0c403441c1e000c0d11000c0e00d402010500c519420701071000e00708500740764406840010310283c4a03008040e1300d1804103014005c00644800c444c5e94901000b00409228207a024000d0324401130b41c1d04000e402030821000d01303030050092580004e0300d1641740c01551069500010300d81c84040c2185d880700b4201007888021586070541c080d02c180c4032181032250b40001c00f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 827501879 1250 827500629 827500691
    0x61709010e0a060b1207230d0501154728020606100503011e031a06130902010806190302090c09100813030c050c21100c08070e0103 58
    0x419000410011103100320304004c0d15803020701b003000406d44410710102c440b21801d104400c0d0790881c00c0410400b5a00c981e01a010f0742c24010401001010303061268111641201840903090400700c240140e207a0806119149403078a03442010b502c0e000c14001035003c2d951030041c0303203441031110f40302303104841c040c0100c00030312085500c42030a280c0620131140e10110485403050644000302003d0410302060043c0786501d07103025250a16211107110502c051900400320040c900900c10040300c1a9408130f40d003e020b020f04241001d0000d1a42c041da60801e50305841300c070324981d105c0040c814880b103c4801c40d040c00003032a1001002da110020307160701540b8050101030fa01c041a03000d201060005600c01e108008040e41000100410709004001d10340c0e152030001c0c0e640c00700741801031a004c084405242d108400b0074540c1f600c0ba65030001000c90b101c1c00780c207403044c0c0543d03000c0041c11120b45030520340100340e0310400101c00d14464041e022038590305040016076104003404941207503000c1e0000c1010b038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 827503129 1250 827501879 827501891
    0x603060b213706060302070c150903200a17150c13170f0d1b0609060c050d0b030606060418060b07060c110f1207060f09081b07061709010e0a06 63
    0x80c41d0b10b07000b0302c005407640381019841c201c10360f5038524040d80a8821040049071500040220724460b140d07a2005503000110380c485550010810000404203600c0b46101e071001131400903203401c94980315030402c0345000140104400400c051401180002c0028910b03244c00c00810401181c0281d01d0b01c003070600070707035010303511a009800d503440c280e0074030343e02d01d143da0150b500c1c200318641c80b0b603103a03a810284030410a6400ba05103032030006072910690080901381054a101e425980c000050148091464005d2050103445000e140d22007c050740c8060300300c9002c21051062040c0002c110502c00150345002a2541e902c11417110f45800c104030444065850760f136182411940242801c8101405130b000e0a40100d0f1641150380e50f00e02401a060468000301d8004140000d5a100c07800e100500d1605220000d410b203850203083d840800c220858454000b180009000d0000b9164262042502c0c1c80314518110b003411030140100503e015065926003541d130f1507001040c0004d04009104da00041380d070b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 827504379 1250 827503129 827503231
    0x203010513060f150c02090a0b010909091e0c080a060507030b040506100f020a14061608010b1e0f130504050106141b01140c03010603060b21 62
    0x948403920307101d20045410003000340507081400d16040122040d20340440c120400401040e90740c89038110002e0742c0020010b0410644400342e0704002c214010983c0ea050000751289012001c40b40c0112000d040007a01180200c80c5c10070260301c120000d40100c618800585da1200e400d403600d8001b0004564a41e02ca4040c050440d4040c0a1410188800c0340c0c2400710b840d02d000450b0402c088507941d101084802851380311014000e004d8001c59030341184c0d010b030012058440d00d0b40e0715442620080c0c043c020350040c8840c05449001303039074161691801524075000c08100c2120750101104030070f020400c4100f20b1000300c6001130008100351034114070000c1d107891500341044111a0144e0205061040300b00c01e03210f15011260484001a9650000c5241e144150400728010074102031082c0076121a8010f110030f003a500300241d0304031900795500f40300031a05e50381000d086000d400d40d40310602c42c05035801d490a084640315254002ca0042c0343c0214145444002071000440f0703031021020b0380b41c11412241c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 827505629 1250 827504379 827504389
    0x60503120f030402010c02010908070303080603062212121406150a12090c0b161b050d06050702150c070c05030601030c0b0a1211030a0b0d05030d1d0d0302030105 71
    0x24180481500a0341000740307205144100388401003000781006080742000e0110ba0152003000064488201201e9055860740380140074804c00740d0300148a4807403c00091121000e18503001c1c01107a4800b800d08046400e035a40018800303100c0704081c00e20000750100042d44800f4411490032414000e10b00409040c601d0a0002c10781d241c0405d030b4080c2900700010350402d45c001984262101407424001003040399400c02d954100015084000000300c00510701c244400c0481d9201314281c0a4040c0302c60340210003098500c51522481116003244d5282c4036440400d4143e0705c117a501c600c003070040e506500503421100100304404c8400c0314a080007c1018000d21074171810020186c0407d800a200783e5042d03854190300d185d840e1040c1552814002913800e19503202e52240140e002910005000340c0390603280c100c0d41070300f0440361040c0b000e29103104c82c92035152500c42101c2c142c1d0840003461400d9000b4071a400a0301c418000700580000c030a035160a01d1104003c002c150000c1c603640161a03505042c1004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 827506879 1250 827505629 827505643
    0x919211706040603210e090c09090109140402120a1b1502012c030f0a030506090c12040201030209032b020706080c09010c022710080d09151b06060503 66
    0x980160301c0d203282800000d503520350481c0c60407a14600070503081c43ca49800c4800e001404280c87c1c012078648241b28510106502800203000102c03038108542c0e0b01c800d050001c07500041c9003c001e000300d010220300541828100b44420564901c141c5502c501c10b501e0b03c114042520154440010030b16108001c0d85040d0b0a480715940c40901c005d020301c0c04042e100e025150380302d48800b03400484080d1400103000c003c0045454074441c143c07074191110040e100c0900186800c50308580070344140301c00140704025060403650307551a40c406410b01c0352580d4004400a4202244c2190988518400002500c1c60302411140050660031083d0218040c1e4000a0425031242d100c0e5007804403040610030403403004e000f41e40c02414280380005004a040c00000c020a00003141d41004d400b50b100002c40b09191100c206d440b95401d81f117a010201d0392401d50039900c20f20003c2c4000003450071401840010103861007007458001e0340c5000d03800390480e07140b141d10107400c1a10848030300b6a00c510130041814244084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 827508129 1250 827506879 827506891
    0x71a06030c0a031a0a150602030307090f230a050409050c0a0602010905100f140a020705010606020d120e030d0c020304060e0303031620070807030c05040509192117 72
    0x20301500e103141e40d00412400f504d226994800440c0b0002121480507038803600b001800c0aa00101943c0c0d9000c0294030f80c1d06c1951140c00085083c000801d8690282c42d0200840d050907007610300c542402503c0c6030b40813042d8000283c1c02240b2540000f503550b0750b4025400c0e4540900058041c0c0c82703004d003c204010314544c2c091030540e4103241910723001c0381021500781101861842c0214640320024610b90007808120a803d0850300703a84c042c42154101a405014294407401c020819161030b14010303651880340c071401100060741e00940707040c03010107a00405044802d41003180d00f031000c4a0103810a071040c00c060100142d001240400c5101d5002201320a008005da015510b541002c0c14040c01601d0203c01070b50900c4408a68100b01400d421030310002c103902c00e0151031a45441c0c40410703454140910041e9850120b18602003604d03c4d10f07210b04d600400c56400188010a2103160344102525008000d468140d017001ca15003040c1c1b019030900301c82400340d6803056001652024054161b031000780030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 827509379 1250 827508129 827508139
    0x81003020906060f0d1e05091506011b06230703020705100b01021903030c14040807050409051f06180e060402091308070503030727090908071a06030c 66
    0x1000562118507200e90050000d40701180d6850456014101038445c510300814460703d40300ca100000744400c0c9a68100c4d00d084c402c144602d807120f03110b480e5120514856210300c5c40c840c40c007003803103580101c491500d61645082c3d21201a84240ca0758012030340c1e00381141030b20b000d640d60b00c80c1d0080d81c7d00960552201d10f90804509014880e196103550702000c4813425040e0317039079041400b0b80e6802044410340d200700b252800300b440d000034a402000f5100b80312002011038400a240f0500c035001d1003d41c0e003652710400c010700c00e0525140801c4040c00b400d080c1030710580a07074580300000c1c400d08034900c000342056102c0824030605d4003000c3c2104116501c170078008585000d40c00032000c00d0101b0403642080d0101c0e0840c0c00782d1a0034106954210500c1e800509420000840d54100711000c4091403003189035480c0c102016091044c00804181d03e00d02100030300c0c1c5080740501c0341c29030365030011102d40c1c00384096606116881d0b403125031036184880c1c44490300440008110f00f514040040d80310621081e42c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 827510629 1250 827509379 827509411
    0x5070c02011e12051312050703080402010c1518110a030f260a090509070806090613111b0706090501020604030f140c06041101030b032808030709030308063f010c0203040608 76
    0x1c9c0141304c07080c0640b0003810001540f0b251018021100c241e4106400d20080c00c00200000c86065400009001411618048070b04595841303407401666030313030480b6009034aa4503501599919481c03242600c0c1030b0707400c4484a56002c4420b401807035029024240541d181c503170303480341800104000a54002c00030010000400100800780d10f5901c000d0390080029102c0170011801040c0840140180150400f9861000314100303040d400c607100e65004030044142a80c5651341c40e040103c454400a0260718050303440740e40800c0000b4804e80002864a10a240ca84507200207803d40703240d42d51124a0350784036988550140405d10048010142c2000d1090908014416101010035100c580c6171818400000604503140d161000000b03840307140c1075000c3c0089950b8500040003030580c4586020a50010b0310040c0007a0103410051648905c070320200070304caa4220b000343d6803400300034121200012007030413003c0d18504106003402008103501c504d402131515181000c0e00280342038001480d100f24a00c6290b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 827511879 1250 827510629 827510633
    0x9320606070609060f0f15090501050108041e021009080d08071e1404081c05251103160515130504020a14030106090905070c02011e120513120507 64
    0x11088601069002c0e90100c1e243c3c041c1e00786840101007250041c0c0c101802c0810b011006200365110701c01c450000c038000710741c0c180c0b500208030844909010746408a0504e00100d001301e6081d25025503100c3c0d410f40c40320800c2800e5404158641400c20303070355000c54103441003400410002e00000801801c2858440d60500c4d00850007001003031000381c41d043c0781d03142180c9460b02d03030312400c0c000c84541c0c40150000c0c0e031a940d0b0b0f03035615510b44ca0301040c80050a100050240300f544581e040740d003203d41c414003411000b19181c2c080810312851030340440310130780240b200d802c15480a00101005000b80402c0500075413602061000c401c410001c5c0704000282008583c030144070742c015541c1520b0040c4e50050311030440b004142d841c40c112401c0d61001c4000132000103021680310849074203542c50b8a10501081d04e800006440280c08444000d0110790030300c4590203092200b88009003d080a450440038a0301c1c11511101210000d66240c0d620343c0740300020348240104400104091045441d0042c6803c3e640c0e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 827513129 1250 827511879 827511889
    0x20310060320100c081c050426040f0e07050d05090105041403120c0d0b0a080c0f09090309220e01050f0c040b120c0702040e010f061e051504093206 65
    0x2250b001000740c00080385265000507540c1c0e81111803c0c02c1c4401f040349040905040ca18120030349901c0700802403004030320030b406230480162011074519185201406040550900c0d038490000e10843c1004024411104100602d000d590702440802000140504142c1032441c0c80c268806141911a4002c10a065611203806017040d4000e8a80c1c92841c1c9960780196500d0142100295050340302204480c0800d16040100b104200780300115809800800100305202c0d05650803155403120390414000d130b107070301d007806032100e044507070511824400d0104100001d400c5961140c13a65070340d41e64642c208032111107940f80b441e400c02c0f042e101c81820b00b0714020f0201218400c2403207160051004101181901030f49005680000d58020014000c40e543c58581900800e00a450707040100d052590001d415070741828a101103074513035450080064242000d00a031042030342d440701c1e40d002c0b042100240074000e6120b5031032405600003400400088002c1c03400300d00c8100c400c0e0006a54507100c203000490b510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 827514379 1250 827513129 827513147
    0x60f0d05070306061416020a18050f220303110301080a03031404021c050f0d0f0f0e0a0b130b070501090302060c03091906090b16020f0102090d020402030402031006032010 75
    0x10007000ca03620482003550305241004c961b4001e41140351140003080301003400c1e10f44580303407502d107400708441d80d5443e44801c14500159039041c0e01601010b07507103401c880001c07940c04a0b54041d08002c5000c1100c0340488003280e04c244d1040c1082c1d08200700c84010154140208044440720604c49034940c1401d8000800400e0011804001082040c80320b804020090000007c240108801c0d180c0c042c20703c1c0e0010b000c00082840700c10008510078a0480300c0c82c000c03101707807100350700282c001207102c3d04090078170070158004042c000a40c001e0940000320402001c00820003207100c0c83c004107010496240c064502840503242c004a80028000c020301c40c41e0004200c100000c0d540c2012498102a0a0010081c0ba09800140c8070b0003401c1d00b040070300c4140208110745008a6403c50708440403c2c0140744c202d024509070381b07900064144401c5c1c05450b041d000b41d5040760009094a410b001420205c804690181e44100d6008c90b00000302e03401c040e02444098030152058400540d1b02d2642c550007080d0000e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 827515629 1250 827514379 827514407
    0x70605071a102c22030806040207020607080904060b0c030d05070c0b042117010b030405120d05071701050d0f08040f08060a1b140c010209060f0d0507030606 69
    0xc031410000d003002500d02c80010050010b40c1074124000f000302070041c007182540360140e4608120034041070301c02c440341000c9072800301e80802c240019001c5940c102c078007010140080da409034003031005c2800359070b4840c001d14002d8801d11400755074118850620082c1c0e01036920a40540b007041c491354001c0c090100c202c49500f16035841c0068503a03502041030307801c0d55038000f001d00b59030928001c002c10080500d01c0700203e0030120745035950a000e258411150038140d00100914035044800400c030980d80300016642081c450360a80b00b9005501200d000c0580200361034011503600c40c418040ca04d0f81201003903081c0341d800c180010031507040c5030110788141c00c0417600505c400b029684c001c0c10310044100791005000e0514031030710341ca50740742d0400d6525038041d64580c5919103000071013550214040044030358070382162204417443c0c140040d00d1009420080740e44205540812510a8542d1583d0003030600080b504a20780c0c403482c600c10482d0854000902d058281482c204080c0a5281c01000c02c0801e06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 827516879 1250 827515629 827515673
    0xd03290a03120c150903080c18010c170a050d051e16030e0708031b010c0e0111120f07050d020a230c040c0e01020d090b090112180c0807060507 63
    0x240016012a07400210003006000c11300f5038080c440c00c2d004150483e45e8418041d17561041d158a8400a03075109105541d41403050048201c240d162550268003060b4420b400382c50144455108124441c50513800403180c0000140005101c01900070b2903c90b03143c20500031100068420301414174592010800b404168511401844210800388a500000069071121095604066840c0c1d10745540782c0101c1c1c0c1000300d030005205403000c507800500c1020103454250303544000b200111001554645040c181c0d542c00c6d030256010030300040a050008050668809a916541d0541814242d0410344420210821508514202000700c2da01c044200e0300c0b80b841d0400d440100721a03080b8a0700e040c80382942c1135085428601d4001e22650004001c469208080e000c0d6540000c400e001182d2085c03060081c110402d405000c4440c0651040b2604080300100e00000a480d1500d10300c2031100640c12101102c1c6500004024000003806110500081c281800c10508100140d60b60085840403150186000d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 827517985 1106 827516879 827516903
    0x10c050a0f050702030a06050429060f01020609100221100e0c040b07030f0302040e041103160e0103060902042d0c0519120b030d03290a03 61
    0x284c2d0040250140000e10303030326080105000381c4280c51900218100140c5500700341442004540740340c000220134a0700c01c0c100074090540385039540c1150015410b00c10038510020b00b89402051043c0c015845801307614601005c5040c403a0700c5d52003e01c65a060181d07040c803020100c401e80d51a540d40e600340341d45803542022244600c0c41000440c0c40208030240119201d0350250154251a00e409403402c1d0396039424900180c070a550544c0c602603611900d20880c41e04010080c0c203104600c80d040d200c5c903d40111b0240303443c0c052001500c840c0c3c544000d40b04541d25a072081c00340e04550b0480c05004100004c1f0755140340c141c0994840050728001000c481c0d070707004809580c10400388040c0c040000700c503400c08854400394282c84029076500c0390b07018134896400b03002c403a04c072885d03540c1c00040e000c48a1400c1d00100e03444440300600e00c03a181e0202c0d4859140d030418001602c1e08503090403c1c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 827338129 827517985 := by
  have h0 := BRFrame.cov_init 827338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 827338129 ≤ n) (h2 : n < 827517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
