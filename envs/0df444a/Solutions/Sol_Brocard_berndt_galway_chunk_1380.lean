-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1380
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:40:53.760306+00:00
-- url     : https://prove2.me/submissions/12e45239-a442-4148-85cf-5f0c5922e3cd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 248021582 ≤ n < 248201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 248022832 1250 248021582 248021591
    0x3030c0f051f0b030303090d05030a1b0906020105150102120a09030f08030115020d0905040e0c040905030d2d020703090b070507061214010e0a1508030703030606050f03010504020d0b13 81
    0x310038011183c0346590745000e43d0081c002c000d41c4150014601110301c0303250900d191296103081540c1e0141c25154050070048a44e800907802c507542040d0303003030291180c580003030010b030340d446240c520714407040500140141c0c0038641602c2d00c030000c440182002301c03440c94080c01d507580b40d8890f0400d201c41d24104641c4090b0000c010804040030400c2c006111103944040c110301c8030a80401010840107015403031280303030b580e06100c10b144400c0011181d02000a0014004001241420f035102c0d04108034126229040c5514050440702c031080c42c0324040003d100c2004003038180c1500c1c2c8000c1d01301d114202c050264586c0e011540707007103800280502d10710410003045554180580203080035141200c0d010158200b8184000c80c5085c01c15190664100c10303111030f003598808580e400900500701000902200d501000700e10a20088010480e450103030724244009956100c086406201d180e0072078103040b000740b005224520303160700146009010340d000425544104070000d4139480c5002d82c007d500981d03c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 248024082 1250 248022832 248022883
    0x114100302090106260604060302100e030d0c020a030b0a180b04110a080307030f031b180501050403050607140f03011d01090506010c02120a1b0603050901020a0903030c0f05 76
    0x3002c00340c1e02401c440e10346243c1c0100f480d071540e010046110342c4c0f1202c54070000b0001d4201c1d01d4540c02040159001465403004030b00c0114080d10503140155201c2c02400ba24a80c0c000c414000c1094540d066805010035051601d151a03000e10120b0290029610079252922600341e002c0340003031500458042c411070501400e040c50160001c004540d2030b180541c00d0741d1001c102401020055078005a0141480c5940d0b0302011022402407030391000c245401c000e0a503992600030380c001c0d01c0d01c05846804820440d59522a00196000e014034440148641c0c010000110010311a420703908d241d41d078908910341008c00001c0e0018154000741c000d2a50b0400e61070f070b40541d2580d094105401003e0303002c0200440d04102d00020480308440303502a00442a5520343d50915804001120b1004d8010500000e0340075551300c40d03442d000841c4244070009007440c0100300740100610807a6050710603038458204003450359a0a030b44081d080d6400f80c51000214241001080c2d050111819000410103c0b0092865 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 248025332 1250 248024082 248024089
    0x31b430305031e1e061302041203030b18011a0d020a050306240f0a0c0c0f0e0f01050a05010c0204020705010f0608070b0f04120f060e0307020103050108010902150307020114100302 79
    0x51001c408400050040248420000d0f00c866013251200c00603a480000d580b0040840ca5101d592040d000d00700e440020001906205508041422482903606202505450080084101030b805d881d00c40e80d078455004016481c480b8110030301c1c00704a40f050604002c4400b1407241240c022841541c081200081005941d10b00007105a040410180d02c182403402100020806400340440440c0000c40014070110070501510b00d8440c1c690744901100ca070143c0700c0301081e00024152250180e4060314102103801080c48440d000d0507a0009040114a00c3c0b40c080112820701c01a002a0b030819400c12050010400a0044071646071000d0b1001c2025468211407516043c1e26603c1b240b903c03103041c840c12050400c8d400c1218111a900c484c000c1e2070090030b0408024041c44000c00510485c5802c4910b66000341c00301c0034100c0d45000b40c03000c0045030f907144100c1d070a8803400700c0020360100e2040301c1903480e500001e01664000005d4800050a140039070001c414088042d200400d18100c51401002140b9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 248026582 1250 248025332 248025361
    0xb0d080a1d03061312020304030c09020c0d1d0d11120105010f0603060e0c030907121a1b090108040318030f1203020a0c060207060f0c05031b43030503 66
    0x18064004084600d419500c0e240059141c00c0c1c02848450013801c5c08001c10b00c00c00c00c1d60051074001656030302c83c0359a07281d000700a40c01180d000c03080b406140101f9803600d00a0621100c1c8141500178240044210020000010230203041212076510707249441016882c0d0f050300418010a980c0009990350412051070003102c0254800d500b0075041030340c2404501480c0611076000542200103e40381d442d03c40c112070801006402000440900340003100510118502072102030000e0410300101c2c0d12400354187d030308080c826a800c5080313002c014100c0c455100d454105d60140c000d1409510f04514001d071081e00c0c001a501c161012017180304460140540c410406400c481c55080451601c0d04244015101c800c1003403002e80119408220001884078a4103d144000e0652008029040383e9000181a540068502c07180c81c1c1590340c0030102c500e403010100e07144000300d5224010000062401d51113820100d400d051101c0c80303910084d40c1103c10743c0200c910401d00ca9150191a443c002c4070304a604d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 248027832 1250 248026582 248026637
    0x30a03062103030e0c0303031e0601020706090b071103100903030b0f0306040305030a0603080d02031905010305030d09110603150102060f010e011503140702010632040b0d080a 77
    0x12080c03555004044881041c51081c55516080c04204c4a42110700b1a06250703401c5252900b6000001c200145007103e513207240012591182860b0940d1100d8004a0307507051030303001d103c01184105600780100500340b4083e080e010f104041040720faa2100004c02d0800028614688295485038000000c240c0c2501441c0d04246043c0c1d4000300d05182a00001e5440c0c1001c3c001805100c030000203d4000341e040d412410103903400081c1c481d5100c00e101001e000a5008a800c500b510400084081c503000e010b01400c1d0480f9080002142400c500200c1c05005050301c00d130844075114507020102d01902c2d81c5001d1441401d01010b02000b07401c0705000a400c1c0b44008050150000b031180050104040007520b040c10b407520f5102802c00101d0b80c003810340042080c000791310394a43c0035004000d101c1d54150011001d45403620452441090010548029049004100e034800d518850380d014450515030710403e00303984000d004840401e6140c4a10905502c2014030200044900440061006500500c038100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 248029082 1250 248027832 248027849
    0xa05030d14060904020f2106100b0a0207051e03250b03010317070c031a370e07051e0a0f0b070f03030b030f0f0d0806061204081209030a0306 62
    0x507280602c0041d01690005000a00c01e01007041c4104a030380728000c80240c00162170050410025075980101da40d940300701d85d40320b54148216404900010030038291850b80642e9001408014180810030405000d0461300040c0181807030b0009800d039508200040e90564110800c04158405c0540014105000d070001010040104010800207c0c0d0158820000d1403041800d92500c1c454074000c0d442100a070700260050100711038030700b0300b1601091014080e400d460800400700d00d1113041106440302c4070f07068081c2809080d620209114403904038009000380b140036a070701a51101c00048910009880000001180e400500601d04003031108802401c65a800c00032801c0ca0084000798511400000501c603815120b214000c26000c0d4004842c0d0761002010b4072042c021300c240960752056440d2000d8901d02c908112101458000c1c0102409004060702d4240703080e1145400c072904600c0074104452410040000c800292004460740d400343c0c0400000c0c0d07958498648005083d03618035004000c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 248030332 1250 248029082 248029121
    0x70b0901050c04030c061809020406031b1803240c050c0d030510140d061b031506020a12050d0f1a03070e01120c0312030504120c0302070e0c07050a05030d 68
    0xc12100d400f0401200c0381031031f046c09040303000c4603a683d0321380071a4044141903001140c0801e00581503003040449501c4c5160100ca0900403010403510f0349040301c0021540e60080c0010b01c045995402d4011003050341d41c1000b007454080f141e001040390305226807400010030100314145115814815111050304034581030165040507007000d40400c4689c80340707902a26417928100764a8551035081a40707560010410400300c000740e041c00007200e8050300000c00180c0f500d2101c203600e4180400d4a029103665a004001002d050343d17800d40c0303080b0404045424000240482d400050745030080340080048032002040c1101e41c45c81c40c0780c040d1440807240740f0179004200140706544170088030358111500240144000c0b0301c1c5e8202554014250781003c0c10703002403003900040168044d0800c60180744500f03034514081000b12070459107600807000c000d0042c0c100403001c1045c500400b6400350400380004490b4540607055a800717242000c0908212401d03000469012041c012921480000d00c54041e40c100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 248031582 1250 248030332 248030339
    0x80708010b040f170c180709090204080c06090a0305010c050a11010c0c03030f1401091d0303040f020118081f06050102070303090302101b0605150d031706060d02070b0901050c04 78
    0x1400a0501074444c645040c0480006400340c02c01c1550702e40003002c1c04540e070301ea0b451201070300c00000480ea10310101e42c18000014410500d882210103d403900f4020f00198031070f407020011140c1c01100724030b03444400040c020010074130a01c5507800000542e140c0c60358908405401510b02141010f02c017070183d2401f4264a021904807070400035895051030001201001200d40d000148807200340c0780b08428030f003030001c82c044002e40e010117911081000111044401111240e50300c1c0320454008140590300740850340154041c0c50208003100174840303c840d400782c861425a01d40300840caa6070082086006007680040c065200300c001406080c4003500c101419520701811601c80c500c8001e001e0504c40080380c0c00944220100b14004000d114a000603e0490611202070401590b813200410040b40d601900e0b440c0c000c04c1d41e550598036440716941c124035480080707107007600140044c0e00718000300034180da503184c10b1000340081c0344990303070300911800c1c2205001d0031170303200522030011001c04200030b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 248032832 1250 248031582 248031599
    0x1260604110604410a030b060d060203040501050711391f0e03070f12050c04020c24040209182109040b0f09010501031d0d080708010b04 60
    0x403540140c11000c0e4000501a80d008503056103e19803141c0800030318681182c2c0c01c01d201c6181c0403c81c0b0088580e40741042c059072072140ca180d148240b442d502c04995101000080c0c00341003010f5204034001c261146450b580d40319041682c0c0b0440d4100d480b6556841000102e91300074030341c000ca2422080041a070407180a190203460364410070381d409aa0151601a401c2121058001c1060880030346104118400511500708078a9280c00400126225003003407a40fa0a0000b030712012164007000304410f84d440e208480b46101705041058a16003e0030441c0300d543d4035140000c1080045090052100c1d05143c2035980d2006d04107800003900304040310034400940c0d105038080d0307040b01d1081664801d250803020344900e044640c0c03200307440b0300403c00c00070410030142502814000100f13443c2405440320030010091045c0c090706005a001d81044014000c5504c01d0f0300c13550b2514541110a80e407a1503202c0e0262804110744542000078205100300454261710042d00b900421500710f05505080c1000c801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 248034082 1250 248032832 248032843
    0x10207060e1f080702061f0303030903030f09030509040b061611030a170a1409031b0a1208040602120f030115090e0a0c0219020a0b2803050126 63
    0x2240204608001960555030301c0207400c0024407142400640080707036842000d011408104c031694098080c40b0002022902100c001c3d0031000401503036080064203594083c0e0081144010650402d551806103100c1c0403414403e510742c69000707803075641d120b803294400c000658802c0143d440c000d0006110315032012040c001421000c41d4058010045c8a0301c0801013890038400707220141280704010500b102d51103690000348503400d819901d480604040b50f85c5000c09102c1c50310030540551200005c0c84031080015012241d04800808001d02c55581c0c0c1c01d486c00e2a8001c0c4002d070f800d000c0c0020b0403c82a070f0100140444401d6000c22141400c25412140505000510a00e0401d42c074540f00007100c2485100440c010b001200e40440281c203000000c0c20042004041c0700c005440303184404000075a007040780098850b8000c041d0402c2e00e051014844141e04150280c145101d10710f44094803200d00050074441031100c9980000e00c540c034280310b45800520090a4501902d14070840c1e50303140202056 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 248035332 1250 248034082 248034089
    0x9060d020705030906041706150609010c06182301051b07020a0306020d090b0105030304080703110409080c150a021c0c0c15090512130608041a2e05010207 68
    0x10068481d5610b051035803d52203444101580200001804149040d5480313444003900014000c941d02c0b0703070358040c001c41c0701d14100d4007096102d0400d00c00707116198807403c02c8502c858800d1002103900d542c0c950485080e60150700d81154003040d0040a08007288121058400a1140307500901403414014074042d154000400e0810440400245510a5450b02c0345404004e5a024200f1513807543c01d01d4070080140400b4100b119204d1425000041901e070000640c1d042c0d441c901c02610741d00f45942d503640038444144100f1a007042e101e1006c2c00c042151800500540c207080c4000d015005203802405203481801001840070700d106011120000821031582040c1c004612000a140d00102604ad100740041503801804165407a500981546c00d94210040e1980301d0421107008140d0040c480d041c601500b001d06598079601103080210b240b052a215400a000f540600303d1aa482001c50703803c10700c100c0741d612591780254084c1990034071001c2c1c000c20740d10615500210140c24a40002d407528030310310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 248036582 1250 248035332 248035357
    0x1050406050708090303030f091c0e010e030c0904060c0809030711090a0f240501080405060a1d0a03031505060c070905070318050a0b09030c0606010f05070b0a0518030906 75
    0x745100410a243d021039030b28440003030840351245042803036440f200c402125090741c6da0042c080c3c101c0c0c03230b0002c40ca0b06140f40d0049444047c0094240d200455881506a41c4982c0c548591501e80b1242d0301c40615440c01640210008903200451550140100c500a0122030485d03008110950115160000c241401d0388d0444030044c10f9120300c12024040d1442549450025103400300031082400c007003514160728640e013844000c54030340c0c80d8015140e415081350064400e801680006518004030340c40703444041b0401205250748104d20380d031f0528001c4100c408501090340d9420703044c0c44070b080c0480c120051104132041480c064004003070f070382ca4030740522540c411036441d00b001c210018042e401171041d0b14202c840400c80342c020740c14855500c0400e0305003a0313003600604e0041001440040f0440300309440390070090515072107050044400031440080740042040c20b0000c0c0f4002601c1e482c00902440d00340d100800d075410310b20b00c05090070700344151111440e4001c02911b070498a442041d2010100e008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 248037832 1250 248036582 248036587
    0x9070618050d06020408030c0a03020c03071211040219050a140a0c0b060406090f020403111203180105161a0c031501050904020f0301060906030b040c080a05060d060c020a0516050105040605 83
    0xa1500f540640a1504034110600010079100c454000000b000174000d8025821140001003000c18107031500d0a42c0507000940d2520410440490080304000742d542e180540300510b00800c414206c002100709091000000c0e5001030343c2d00a040e8003c4c590404070001c15416480c080302c440d00904070380411103000b03100c2052240022403d642e05e43c000e00040c0301914080c8107903070550003210025802800100e8441071000c403800928200940ba0b100a42d040400a61030300c1c801c1000550400707490415541042810803941540c008a00c01009a1030300c0380400704c1500d1f503241c091414110000344800c00c1c50000344104111880c6039030300020034450a0034240c1e504d05642c004100a84500780d2050060140000001481c2d035014904100f21009603a040103640541d50400050343d0303041c50440e00040c112404590035885503130140350401d0b001020b00b40b5280956441c2800d54026148500c0541c200391070070390502c081448551702082d03103814a00086810400003900a00172802a4420071802 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 248039082 1250 248037832 248037859
    0x170c061606060b2817070c0c121b080a02060c0c130e061b0a180806070905031e03040603021b0f010204060e030c0307140a0b0409052d010626040602030907061805 71
    0x240440786a1540c1100a1400d1140c480271551248203906208540c500318170f1482140c1c81d4654268002549c0304000581001c51058080100e9a001034a40b40400e024854401e45a07980302032001c4940044500f020940d15200f2799032900f4060000d000300c050718084254840d802c0343c00000c075401446642040ca07820341e082e003403110703512419030071102c121701c80c08040c02501500f010052046440c12003c41c0d01c5001c00780d40700c00e50403102c03001980300383d401400b0074004507000ea00a080c0800c0340b600054400580c022446107040c1001004e01e405135030001e0305101d070b41c0e4081d80c0a00e03141d0040d8002d010421071540865612003140c801d884c000d514001034000d0075078030214040c00402e070700450f054480342c131141d1080c01881b0640760748441ca103400108000201031400b00007a11b15104102e00b038aa0310b030074010341d0a01400c2ea10305130b82001d6200242c0f8603107281c42281e40618014400162207140c161101c514080e0b468102c0c20078070040050085000307544d12050300070341da001e68000741c1c400503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 248040332 1250 248039082 248039087
    0x3080f0c070519020f240d020d290f03032d0301090c1e080f060f03010204090212090c06031303030b210106170c061606060b281707 58
    0x1450000900d20300441001009051030b05034000c0105000b240c12945032000300d030400040703070091141b00d80c0445901010b001d12001d100007400251100c0d074809854641d040321854129403480c00e0440700b1a44444510f401d2500c8160120161007054400310030304849040025500d001d4100c40c0b8030783d030301e000804e00f4030036107540e12840c3d80d00041c04944c0c6e100c0d6110000c84000e001c500c0c0c03259001805412034221644060b210205020390140c0390903003580c803080411401428002c00c030507044005400040da40b614240300500c0105040003006850b4032a4001001c0c80340c070003501b030300d4480e4044803c040c115514002120b411a03100d0b00d0080e05002c29240030f901030500501e445034804090040040e01160007403e20b607201404a000f003046503100d10b1549000c096510307c070300c20fa0303103c80c010020740e0506900414981c0c400050440320b00c202603481d50b06840c0c503500031694041021901c0400c40035401d04c0140310310a040c483c0301503100b0b2a0801000d2a030103d03200031880c0c00a4020405490 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 248041582 1250 248040332 248040337
    0x6050f040509092514040c0e0f03151f050d030f0f230406020f0105150d0303020c030a0f110102030c030a090f02030604080307020d0206060306010306021309050405010914030703080f0c 81
    0x2041c5910f4141c0004042501c04200f4540c5d205040c0155000c1401c403100340b5151003180303066012602ca641400d840b080c203200c03000c200882c2035501442004154110305040001482c415103250180c1008400200c804001041d000e40c0800c7c00b681c4c06681c0c8400082d00707c4c5021450004520f401d0310513642e040c500f182d114080592211000f940729884081e014403480041c41551401e408441501c41c0890741d003405c0f5181161401c49040854044001c907260030070084c80c000303020f80380c054101268442c0301820b6500959552012071000000d0349110768028843c0416000c122000310b042d0720300500d002010f444000c040704540c0d56504103800410085045010009802070f04440a9181a141041850b842660440c0c0584600402411014400208603129010113805800c05901c0e5a6407100070b5001500e1121380030342d202e0404541c4602511460344254002c0740041034403140c5051851121402e806448503d81042103454082500f26204540242d41ca0b14150000d6841d49580406070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 248042832 1250 248041582 248041603
    0x1091104032d08040305160b09130f0b040e1c0801030309060e13020a0309060b0a0501020a0f020f030a0308060118050d020d02030c0301020f0408070b0c19051504051606050f04050909 80
    0x3e400315001c01800000981031940c41c401d216040c0000d40c96100c40c1009000c2c40003203a52000d01401003400c10312098002021118100d45c0100e1110107540004003a1500350403015860b50000c0000100d10f119002d01e442d41c07a0302e900341040c01d07504540700108500a01d0058030244419456880c549450350342c0c0302d04074802507140864880e070304004010040e11070102d00780c0d265820030580e5840303480c0002d000005c85a05030000c0ca841000d5903a08182d107031003200281c1c4d0241c00030713090084540b800d10109507510711075a6488428540500007402e060941003181101c2c0f00d896200307101c9034980d44400c20103c1d4048401400750f20300c17813000914111615a02c00c0d09940045800d071000003a203405041540c800e44103981e802521036000000c14000d040070460203901c4054001c0301024803100c0b100307060303002d0400c1e6401e41c4120230b116145010161011200c591142810380d0410b1000391b840c0002d40380c240b40c44c0e882d003511410500c42c41e02403405860300c184d00210205105071810004880714 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 248044082 1250 248042832 248042843
    0x112021309030201021902010c0e01120608030a0c0b0a23041b0803130509090309010c06090203060403120e0601032111060c0a02060a06120602030c07060f020301091104032d 76
    0x281c030180c90024007039000920b01e0b1081020301da103803444603401030049041c0d01040b6521500b003003401c0801181c0503c007001c035561596a0f100000f090b1201c041c0010f00c00103115445180403015540342c4292100d8004010300900d40c45c040c00c442621482400480e03480f00802c1c90041c1c41e46850070201c03490400480c14400c541c1000c2800280d40340e022015211140c40003d00304445a6150144415210100c56000c4c85410030003a0384403039030249c4041c1c1e01040c0030700350000e42e0320000da01007842e0400c00e54065000c9544841c03a5070500000f80076881c9a07070031030006000d86515554550700919a1512020703103000400d01041d400361b02c03d031148214040441c040b0b07800c1c2e080c0400003034101e174810f408540050047c0b000042e805140390280004075440101100702c1e50b41251250390003900054004004403d04200342e2000c9103841c004d02d0390504603004016903d503d045e410701c04440e040e180c03000801c0300a02040010032050340140319510399408020200c441d0b0021904d4150500c50b800400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 248045332 1250 248044082 248044091
    0xe06010905061c03081017190302070b040308030105120c030c01053001050306070f021902041b080901060f03030e040216080412111509010c1b0801020c0607031401120213 75
    0xc1c50790201c03100b4010a54003901402c2e00d40c54040d0b80ea101200c1c2c1180c010103030f1291501e0140350a54588e840205e074082c3c8142d400903030321141404666400350f40b00f555100e00c04001840703d89400d800c101d81c90346e80da00040c05000750310004243c840311524162414010081242c0d2542c603048811504114520050302400c40c0e2509180d0201d04001e0060354001c1c071808001480d2103004030391185100c0140e800a007a5101180043e2407180000b000c100c0c4c1054907a11030180d01403481120300401c2c13101d51144c91142ca0a40401401c40340b4983c4407502000542408101284c0c11184849120106880140e5241d40182191160b0130041100400e41c1c00001000540c5400060322280e00c1c601c90425020509400c0041110022804484440000c001c00070f404c111340c000e02c40c088035a446400078024640c5440802c2c409450154807149841c0d40000e08007800d58000c1c0700d4643d000246080400c04400d240501d400e200005016040745402116150700556540181d07010880259400078170 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 248046582 1250 248045332 248045389
    0x405130c051c06150302030714030c041706091b0609090606040e0405030316140f0c1c030e0106151e0c080a0e01030b030c060d0b0a03020301060f060207090e0601090506 74
    0xd0007402c0c91303c10b003501c480798030892504062190007202c0c00390006540300c0304c2c0201e115010145a40c4068926800b01a00f0080003400724080107905501c00007041c042c28051070b00d4402e450419041e1300501025005205840030140e8542003501c03040c80b01654050b4840e0758410114125210b10340000110103c41000c000c20014000005c501c10f16103403901c13022041d2085410742c1c002c1c04400d006400361605000c0045004591406080041c03506c0044418080840d0b0000641c1c421001074040007984508000007400800d0060b0303802450034000e0701012030080c100050454881c030100c08591020031400c00282481801c4460003ea0072002c801d0340c6180c580f41c050030454100302d00c135001c241000c0c40c42c0028680459060455000500716500d00012019660010020414190351141b2101004809a2024443d9102420600751024603090401d41c02030318124036a803001d6038040c141540c0003c43c0c0c40108846044941070200494142c40340e100103401001d19901e550f081122140305034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 248047832 1250 248046582 248046637
    0x1802030f031b01090c1a0909090303011e26030705061f080604020f04050702161818170703051b0d0801150206130c080604260405130c05 60
    0x80010440311984028038a8614a030b090903214000d10140c01e8020920b01008036841c00040502108445d003031942c0380c0400340f8000307844002c083d20002035940c8040014424130050458626030421256122203443c0c3c03030101e104208912103000410200808189002030400400c242d809581d4400161603071490304003001c8590b8080420880422104403800091442c80030814500594000d04094814049136081c00080c0c10007818440452040343c0e0315120341c403050395107540a0859044594103942c40c011803a01607520404880d200320041e003503070100080300700894115404030003041c6512140039050680b124000c0b80c0e074105c1d00143c40142c4030701e900400715440114548903110b0300e01e26601c41c4079101c200002072030201d0140e80580040340d00b10407040c2c800d03180c0a12030811003003010f0b190300700c2a040c410f05580c100c03548034013019095113102400000e00d841c900c2e070341c0410b0704203468000002c4106004a00d05000d080d9500e4482d8000c034410340894100911003408a003c00300800d014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 248049082 1250 248047832 248047837
    0x20112022a0a12032a0503070e030c0a09050603070603050606070b0a0b0d11091501050409090c080f0f0d0e090a24080307061a060301060807021c0804051c0906031802030f03 76
    0xd003c120b03a00c8682c440307480d0220b00c0070705d0211141e4403a421580e55202c25140006001d54042d4584500a0001102e90b621a5008060100750784d010803a401c010b41414540222a0414018941000308011840c0c40d804160b0b04038540200d036040c07641e00d482540c0780081441d03c035502d8100916440c6082440541c00200d10f10900a40300d0340101d988d40d22000c171840c1201080c450001d50304100400000d40660407030721245028041c441c112580e07030f1200503d0022a0341103041e164110713a0202c0b0058800b888005440b100c5418041c1c0d49030f146100007214094001c180100c3d480c0c3d00c86a00c1442d034045402000c2a02c40c0d50071180540d600e034101c0d1070f0341e80c000000496406c0e0521905ca603400b000588801d090000292190381141d003884c505841c1e28a00400450444c40359500560354450301d400215051405a140d164590415080c440e042174010010207189400120152900d2603001c0300700400c4540501d80000c1c0300c0c51080a00704c24008224020b5458401c49a0100006401000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 248050332 1250 248049082 248049101
    0x30507060603020a03032c0f22052805060f010f030b37050d020f010210050c0306010906110a11011809060f05030d090e060d08030a050103020112022a0a1203 69
    0x3400f2843c2035a10b5900204852010300c07103400051501030703403a2304d08014003c3c0407132a04902c00e103c144007008900030125241207514100400c0c101403519a01820400512201c548000b401c2c003040c509000030820b1664949104d9040000244400c15900c3c8030394000702403c0703401042441d103142001c51010003480c1c0b0800146264aa80f500c18140200400001c800c40384058a0321503140442e4003040000341c0c807002400d041d40985c0780030b81e502c10710620400f0303c0f5114126040e0303100d05000e80010180000b80d080320040c401131041d5517802060004078000300e00c5c0d00c1014909a404100012601c1c1d08020901107169a030400c0085105107441d0885400e03078101e0340b03042103590360707400805549094202106001c2601d41809200090382820101d511403800391090b17450740d840341d0302c62140e030344100c07490b03106686d4420051003150b91050b03100003072a000e03110030f50410100340c040306580d030f030001b40146282c1c4491025081148042c4150b0a0b440e0b0000700301e540b82c8400e004094081c0281c0907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 248051582 1250 248050332 248050367
    0xc07020127142b0b060d0302070b070507080625090308070f0606320319060b0a0b0c0102090316081e010e010c08041505160302030601020f030409061701020307020a030507060603020a0303 82
    0x4c00040740c504040188007074480c0c0580c020074070503151a0a91010780e01c0181e040c0da07240913a450209400004010b05401007070b40c032103482e200d111000300104c1e0100240805601304900020f0400100da818005d4541280e0480000b0008540300c0c40c003c401000300e94040c0b840c2c1440500c030070758000d01e0704408200003004803507010416803044013016280c410415000701d04000400354080854038075402848101c0c0084c082e400c030f403915004500540d1300000311041c02a900010000b030142418805240102c0309120740398200ca040c2150180c175216500c0c4840581014001116010682500304091050190000f0010881c0d6010000c010a070100d40503100d0721a502c0c1c2c8a400d8000c0d0780700e480c0c401d68090300341e958208800c0030202e019500c090300d110704620600d5410001040309000410003070400e928002600703885c01d100700b1041000000541d00036441841005a030b26004100c4600081d454508a80d41d1400361900800900c0680c001075000300b80044040101034100c86d200d0794840141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 248052832 1250 248051582 248051603
    0x3e04050109111210080610150801060504150302070b01030b040201021b06300c0307030b0102162907111203071106030c0706050c07020127142b 63
    0x1800020300380d841882c0003100b00c1108001103004241401105078000d4085120042d107642c2da082114070f04a0309888402e01c00100e01030400415446811204120760a400e19440540c5882c0000d003060040c2e1040c0e144141c415002c0300ba80c0362190b4102c0d80b0047c1d1044400c0c1c15540c5a082c0302e000c01c041298200d01620921030700031010940e00c04149200b041c024080d40c03a20441900c0c4881000000301207040030070011500e41d500c0c074200c454092007411950000360300c03440e01c0d034001801d031003440300d00d44c0c159003091007a1041400c008580005541c2d110f049406540d1100c0f0004000904084941c0c1c7d1108000c41e0750400c006090002ca14100b03000c41d22403941059030f0040c0743d181d120300300e00203048040d0040340358401d04104014550058085421038140805a1145015200d01702c1c3d00310760714000041c0220866030080207042000d106a408900c04211090413001c11b01c08c1e41c080c100c401c01100302c0884c125500e80c2d45958040150b40c480c0300d150b034031001d10400e42803210201115502c000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 248054082 1250 248052832 248052839
    0xc0307110619060e010f05060711030f010e19080d180503040e0103050c2b03030b03070618300c0f0311091f060302130302120307030201110406050301033e040501 71
    0x209804d14182d80480c0101c140086c907150400840d98040401107074601401d4503064801d90b000d21000010010704000850070207039180b00141001e21a041b10403129600400c110045600c80051f9800304041c3d0500050110483c81d644100c0b090115008105100024010403199041c0b0400da040364400d2003183c2c81951240308200ba201880e1211104071280c12040c100c000d070882c0c400c0210f940c064200020200301b460003003400e0420030703088900464100c3e44440001c4803041c041c080200050724000c004200301d00c040e01514401c0516001881d1038030803501080c4022020400014038100c0c4851a5440daa40760100e6802030710302d046032240600200103030030102c0c00001c180c4c034041500070000405080c41030640003074001d16190003441d108541c0100050b102c00000080141030b4000440e240d2101e417500a00351074034085401910341d028002040001e4010043d070781501d03840300c2030314041c14070280450054100320000c0c66040c10300e03000c8108892840b07010b100050b1300c02d8805005580e00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 248055332 1250 248054082 248054099
    0x21110a020a0b0108030f0d02090d02060d09020102060604090f0f0c050423100308161505010e190902030a0b0601031e1b0206041106070503130602030d0b1002060c030711061906 77
    0x2132041c0d80051a4407c0000c0d500c0b9802e194010503200030010544c185240031341c2c0100f02213030000000a0300e41c0c2c2e510300d020015981c04104407540580f04640034403010060399103064020401990091404009040c5030042092151a603800350030701900c104102d100484030f200016000301c106035402a89800801d40680b0205048030031349800c60302d141d04d003041c140c00c41d11051402080a50704038192980c840745815071400781900825200b0b010110070300386103150300f082d02d50844502181915002d5039400584010401e200a44d81141f4140700d190f40d00b50060b0040c080c0314a036100d460b00c0b100420900d03d40b06511003440a40c000766a00f144a01188060380d07910025240034180a158000c506150300c0e08200401c003042c0704609980c2400d81280b07a0b040c01080ca90005d00240e000400c0385100c00c004d81c07180454400044592412084210002948801010b400da0034403001c0000020303001401803262000383d240040803035100c0d1400660280d0304042d03082c1d600303014a00708500050f0511 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 248056582 1250 248055332 248055337
    0x9020d060c0512100306060b0a022104031e020907050c060a09062c070801290135061008060103330302100905011b0302010b0904080304110303040621110a020a0b010803 74
    0x4040e00104a00915040b42c03a0b00c21007e580a81d0308bd036000c01010001644d24900080440c007000b41c0703103801e0300280c070401004910060550080023020b1000c609a41000140990400700c440701c0094114003505010b0302824296011802c54001201c0c582c2d440048030210100328403442040c3c1ea119911800c225007a1a00c401003211540300382c0000700c40007600c08050b0180303541c05042450301d800703940840c1c1008a038110350000014401925480319240800c1c030040c0d1018044400520565400c00060005070025028604159803800400d00030b03a0f03183d042c0ca01d40780c60381240d0041d1101000c48000c520f105c60104070300554140110460382070140c4101400d0b40e00c16120032010f24464440600301d094010020380441d900c0e04074200b12a11206629802a8010409140e40f407801e414840d4015402a0f202e5000e03078404c210811455a000224411050102030b0683d0079030f28200820000d0f00002000100c06130300051241c3c525500040d0a20b50a84102d01c014100e0380c0e07503c00b8503180e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 248057832 1250 248056582 248056597
    0x50c0a050406201c081605070b10093308060f0c0706020310081b060307230a020c01021b0609010c05100e0309040e0109020d060c0512100306060b 64
    0x510140420b000c028003500244900580e60038200080303400065089291210720010041d500c4031400207005601d13800039402d940540808120384c0c00c11100c1000410502c6485809040108101d01050403625071080040050210700300c01e010f0f490700c140380f60082c420904600400540c66a00485e00050307900032982c200c6000002800040e56840746001031074400400b500c0060340308008400000d01184080c60243c1c0500801c0e580c000d0410310b0044c501846c0394100d619100c402003811a9035940d0b882220f6104c4a58908070408490703094040380315040640007040c0d040b5010403008909580000c246040c2e0000768216007195080b40140da00001510300000d40000c41040220a0755002e03100c1400c0707103803084e02240c1c54568001d600600300c0320700c1c1ca0840155000001c2030769032458a13000e05500306001a000b0040c40d4619400a140304010903001400c5a0b00c2e010b2290030b603030282094882054208080d210545810048401110075601003202d4842c44c1c401d000c145100c48a0070390300b0383e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 248059082 1250 248057832 248057837
    0x6050d0203060c2b0b010e06180f01020c0d0b04021810030b180609100e0d0905120a0c030803090615030a0b18031621020a030e0103060e090c04050c0a 66
    0xd615003e01510880e0300c00003141591444451100c040a040480001103220301050005130544030440010118454015918400c500a200d6402c2c4004a031210141c2c1040440c0e5034480300b91910010f03030400c8160202554401801c50f610030030301c210821000d108038403c44176403403a000c60304003411180c041521440710004401c0c40c103000042102e45880d0300020806c03a00040844c40d032000924189040b0703a603a08941244010318540c4040703000b0f007401d4001d003401400b6008480c51000300b007009c3c030348540782c80f401495a81d542403060900801d4052904100310803074a50310b03424140c1781c40d401512640e0041c800d020008400904030141c4c0d4400340d01c0180900175022468035490401c0902510726884d00c0c507800f6107200000c0080000301b410310241aa0300c1a020420300f0b00711426914404074200018480e01e101c0c074066070116120504581c542403221400300d800004900034203154200c2c0d4450b00480080c424101c4c00014035041c100300465041c02555a0300d00305040324004c10011380301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 248060332 1250 248059082 248059093
    0x902030a0b010c0506010b1813020703021b010c020d0606090c1805041a0108041104020316020f070e04030c030509061c0b0d0201120911090f01050a0f1a09010e0a090203010906050d0203 81
    0x207c45e011002407103c243c12002c1e00c40800702e14000a40d0360f0011600070806164002507510030150140800c01400e1140140e244081c41d1080000c0c1446242640081c071400000302514200009548000d01514031404200468034002c58007406400c1071010f500b50010400390000382e81c0c03030180140c41510042d020298800948000151001000500211800014405002c0d15610345102561007068000f0803001411031800700070b0308150b84403080059681001c84203100c4446403042c420307000381d45498907079854901400c0c00c8901d4000c0b54091540220f00003100d845002c3c40500120400915443c10062075810380100410380c151804000e02080e050480205c4590190b0f2240c4189400745648503045014800001c0d402d2004568410866a24030700500290401b201584042d0079480c032606441420000c1e0300d2090728841e0140c510300d18002402c02c003d40d11a18801c2d5010001801c1c5d0000710740c4400e00d02002c0c0d00700340102e585413403074004005414502030a0070600c40b60042c02410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 248061582 1250 248060332 248060339
    0xe3007080f1c09090b01020c030d02010203010f0b031e13050a0b06090108060f0115090b030a1d0a110d03030e060a0912020313050603101a07060c0e03060f0603070803040902030a0b010c050601 84
    0x8045c0580454860641c05180302c0301465850610007c100302d605030380016640d41c1003502d8048050019080801e011401340b040040342c6009206001c2035818544148800f541e8070300d050241807001c01001005070041c00480e40400051080c1280030304400c4075442c12507030701d42c8001591002d046504114210581c401001030001282c800001e0307200c9031070728550302a11401c681d00141d00c15140c3c8143c85603506102c4401441c04400f5440c07440d4014060500c0c0c41c0d05031204590840d840180911540d1030030011400c06001e60721100001d030003981598854901400507100401c005041590fa8501d240700f403451052010048070a418802440a50098100018064190401802c800060420101c003081621002100e84259405200b0187d51400f4900d000300c140c0d56817813110018480710300442c010725078010a05940c02091915250540d956510000f450908142d000841c01c3c0400500441d0303503001a0002d512070842c0c80c10501600c204c13200110342a245002c0c018090740c01900c01407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 248062832 1250 248061582 248061599
    0x5240d020103020f04080705040605030a0f0b09010b0a03050a060b0a0f09051b0c0d0f05070305030402100e040f02281713120903030f0e3007080f1c09 66
    0x195005030042c0340040c142502c0b19a10b0340d42e94003e800112683c2c0c1b04501c1008145058054140070b040182e01604105199941c0c0040300050b100b00285070818910000324840c00941c0b000c0280d900040040c100190b07a410840d4031070803032085c02d0768181c1c1040403803145800c00c074080c0c1d4100d8141d03480d41001180b400c86421300411001d42140c0c01030358450005104c1d0451040078140b15520b0344083c0c46c40c06201c80c00548041684030345181402410700034100820340000580e684650162803040c00b9102400e000c40f030209040311010761082c0b500c52504030701d1030725501805010a0400080700d407900291202d1004c04079040040c0c0000f04c0b10307607111800d240302419490300641140d000202c11311580e5124185240165500300002d414444100181944100c8030f03440d120441c18400001041c2e040415a8841204120a81290500b6419083c44802018440c0a8580d002964440350301c591606440d4407200601144c684643d260009110415008215800e0300790f4a8aa19080c07801d03550 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 248064082 1250 248062832 248062849
    0x1205070e04020d14091c0f0503010b1b06180d080402100c030c05190c050103051306020a0507140705010f0809030d0c0c08030709150318060b041803050703030524 71
    0x14907440307501ca041c90040011404c4a182c0185440030103807003441c0d0400003000f809400b000030b0608112a40025050158021048030f0544c0c02040c081c5030f98100c6110502d1138244079007200800c07449540100404502040c84070a070010b400403d8a074181da261100321a100c0c0103031800395001d10500908100c25000d85c1900107503611900704081100d00301e07210b41c2e040000c01d080220602e940300350030004004440800402520007424100054104141c2e0541ca49045c2c19000300303c07a90000d48140c10350b00510555040941c0700320350200c02e1218502d110340b150614802c003404198409140100c1d80d0240c40310034460221003000314240f0381c585103464080c0001034040028420b00b040790201160640c40218464101910b0300c0c01d070945051000c1024207925000d00c020103241c003502041a000211100d0790b016000381c4007242004203100064014148031001d010300d501040a13480405030840c02818110b1300a0310104029540c43e041c0000c1000084010800840c03803a0311007009140035800d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 248065332 1250 248064082 248064097
    0x50f0423100b070f0302060115050a080403050c010906060503100216170909090c01090608070507080d15080607030f020403020904330e3a0314161205070e0402 70
    0x1000c0021030b903214805602503100c00804d942e01060030f90f907a0305042c0c04200150040c140c54148c051041d204d164014158010400e00d00c017004180c0f404a0306140c860707002d6443c1c080c00c8500030000f5180d20f02e081c1c00100424452280a4020a0051440c9090071701c2070704d5600c00d14001c0d501c841c14455580017800c40352901c0d0012028400e2200046540b01d52601c2d51254041c000100f40241800d030001d4008851603001000b0045803408100700380f0b5222080d81e100344da02408103502c900d902080740000e46000e41c82220703210540c0710002164100080c0c0c1c207000d462540c40030414044940c880310140c0c451408080c0d040183d00707010400048503402c9107100325160040000c4801118403a10400c14840d542100f616038440b182c0201c45141403050701032245c40c60100c2c070501d03502d0344030507404d803500d404014881c2c1c0c6c12211f40c410850b00a400c22800400d61404100c00d51508821000070300403400c60040028001d140704aa00c02d0302442894080d102030303203445110082c00341c10171010f9031001c079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 248066582 1250 248065332 248065351
    0xb0d0204030c09091b031203090302010617030703090f0302010e01110124051206100303080613020a020105010608330105130f030b10120803040f120801050f0423 71
    0x200000100c1c0700c03042e050000e8501c10b500070030f42052904055140e03d4010404103104007000e41c081000a00e515035a000c504081d041c00b140550890500b64014030040c0c1c0076a9604c803070b1b1181d0000c1d0040100003883c0c074912a4840203009901c2da074200c00e000c0c9140c04002d010940c440c240c6103596000d19802c8181c400032130000300e500114000c1090740b070180764001411028880000b44080d1402c68800c02c00403004000030b0201c1d1500900941c03180b8103070712001d000d200188012610740d8844030781c407803070082c2059825035454690310030007802032609214810003d807800d07020a01c05620b1141c0c404075005400c4c20110300718507403440120349004224145061050803c07540141005d01c68994009022411416010a1840c140071441e450010220300010641100601c00b0b03c4e40040e0010701c083e0071003095626507496141c05080b222407114041d06004c1c07032401820a040d0f00a11250582c0c01c1580c880c6400c08141007480188c401070302c29010210142260364100318074450800c0d034802c81c06c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 248067832 1250 248066582 248066587
    0x30f081909080c04090c050d0507030c06020a0308062407080703170405100c1107080307060b060903060f0c09060d09030e03011a0607050a020d08130f15050304051c090302030f060903040b0d02 84
    0x2003000440c0300c100b00c8001c036456041034102f0400d00c10340c5580703040103012500203403400100954000341904001000284540200f84d404070880d820a940700e807428540d0900141d5072002c60400395042e40010200b02c000410007080030301d01000301d48480380103030344c840010071031466800d13503d030041c103518200c0c8404c0100703000c0055002442080504001c3c210700002d10756a902a0401109551740d0003851030003803008201240843d200050040c1e0b00540d135000b89045910340b44403035081c500c031f5800304581c0310300c0105020710f1050341d41d0b0004600c0d601c01d4866a20491101301498240c866191142e032904182d43c1002445081000081c00182e204509507a103140c60350340021014003042200741c400030004074200540c1150344002c0c10191003900d00f80061146095030f140f00c50b4441440c1c40040080c0031012500700181000382c12200d0707840f4220502039003104100141020001d201c107074441e100707408001480303040c04143c0c00d0007500b100028602d01810000003401036400206002c1c41c580c3e08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 248069082 1250 248067832 248067839
    0x30305310f0f15020309121504320601050d08090901030c0f060c020604090902040f0504111005091f11010e06061503072106030f081909080c04090c 65
    0x3103008000a010060700340ca40580c10640d1050780e404941c0c21080040352140100c102c09500042a1032415204584610f4444114000d41c0c2c14444010605d17021040c0b000148400c00402080c120461010071840806040d0807200e40142c0f1010004450b800380c10401c01801103041070790003e584140607850320f030700d0302d10040301250802100340c0c01901d054030a010701348040002030a40c03100400c481c1c03078624150106500015000e120380c0c454064130560394925101191a1500903900300744010300200f03c0c519080c1041140b0390040c03010342d03108140003803003403040d24020700030780b40144009000c2914600e0520359040c803c010240b0b10303d0620000506240d4500002d0082a50080008026120600741001402032200045160004243c41401004005540b0129103406a507a445440385145c00c2c12030b8510040403107130400b404842c00c4020359410700c55074100500b4595445104c1d64250300c00054100d170081d4445c0100d403003e4104a03041481450700350000d190041c049c00107100403039070313 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 248070332 1250 248069082 248069167
    0x90a0503120103030906020a0c0608062d040c110304030b150909070f230f011407030503061302070b040b0a0f0e1006080106061218020d0308150a030305 67
    0x720380030005640d03001e54014010540d00035500401060107000902405c10542c0e5000101d48650050030100a031ba840014120380d902e0000705840e903503a030b00b2801609290915117100340c0d890f412007405075040c44031000c0401e10840c111107029800e80085c609060560351a460303410b1026107403444015503101505016603a540e011070040c900d080041c580145000100c11448015500600200c0300c044101d00307101070f202403440c850030340880d4400644028800140d8441c00303541008401000081512810990010003e60244038203c5906240706040311001041e0f200e10742d001000e0a14180c0801c0000e8512403d032904210401408142c048104090701c0455001d00c8983c400365001038800c4254008074031900d409844844d0080c0410f03800c1c04005494200b110400e90360050b0b9230f41503202c0b10720b0350389072080708550300511085145a01d400e00070800241034681c0004030248086100040c40e040102d0800c0325403545455060180560300b100c204207500021545404817485002d64502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 248071582 1250 248070332 248070337
    0x7090b041508070f05040b10032003010b0a020610030f2003030d051602010b01020d050703051b06041202030c1f0e010e01050a060611030417031318050c03060d0b090a0503 75
    0x40d5002045207038584003040c0011900c950006025070300e8550006c81623221001040344125141c1404200000110030403540c0000950419124903404000400c12071038000040c2901c030100c0d801c440351034031018030007039030201c043c4001882002d1018040c1d000905508164081003860b02d04200e400c100c1c0b60100782164403031100743c003400399101d01301300040d4681d2108403092800c61008001c030001e1900040e40e948410187d50042c420046011400c0503c50000c41d081c204035030075280171001d904203045583d071401f03440850b544000000340602c040d00c0041030b1001e803000b1200816200b4a180407a91100c1181107402d80c206803603082d6211080c509001e50500800341e4000050545402600e01d001c488954202500b001a042c0010a00d901c0000680d4203450b2940203013041181c4409a0a10758407624003030b10450070b490070340081c0b82910255122030f8418161014043e59603019941810751108035122648041104208008a210041d2065102800c5400c0320340c0e50000c2d490303151039074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 248072832 1250 248071582 248071589
    0xb190806040213140a020d020f120103020108011a0a0302030714030907050109080a021e1c030503061801450501230108450105070806010207090b0415 66
    0x340e00003400d12086042900001405880702d803410004045542c40c0820ba0000113829210035070380118800d4040b412070b074100e901c1c00f54400582c1d980e0b0001c2c1d610103840c2910901c000c2c0d0115101303030000183d0710381003900ba48900200c10050740c9018824401a0003e4002518600c20404400800d408030400c0c80006c5005002c1d4000901040e494480010444001c0360807400103504809500320040c1c440c626000e03012001900d0147c864001640442c240c40d0b80c04589804980a482101007810b401000950241e0419194a085895169a904203100081c0700e55030403921180d05034414100000c589403082010340b4900500103581088480c640c000300c2c428001990340c2c59004212386d450034003035001c204410601014015031290000382c00c1d000c0080400c1a4140400318400459100c0552213000000c0385901c580c3d0041081202c00c08145800c03103012041d843c103c04199030b18000e0300200e01c21101640104000ba00307000304040079004200c00640c12689522940d64400745100b40c21015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 248074082 1250 248072832 248072849
    0x1303051204081819090207020f030307030816050a091e0b0301062105040215032503020c0c0a03151a06041502061509040b07020c030f010c03060f080703060b19 70
    0x11040c080100d00a5050104941e51181101d0111413059940d036041082c21aa440c00005890380003c0c00800c090304240d02829506004c0000c800c41055000b1200710300079000540081240d0a0601c1c0c103885c50300c580c491a0703020900e07100c0101b0802c8040344214a00c0a10544900354441d46ca00d031000058000f0303000b0070042464a100e0000c1984c05c0c44200600e02c0081c80140301604207074010800e15612440807600c0300300000000798201001c0c807000744c22800d2407542040100c1408000030000e4000d0100e03c0000e020380500c1c2d001074940102c005085c0c0350004022184010010b5000000f440c10b0601d041985101ca2316254466440401401c02403001104d00e8080c440e910a000782804c60080800101640c2030348044490b031141200b8541c881c0e4807155444240d00c40c120f0591508060b9406941d040c403c4c0110400075800c1034001034100130305601c00b0700000341c442c3c050001d07808440c0200601c6500480342080490001d401400c4650000340151540082c10800c443c089607040e0000c122 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 248075332 1250 248074082 248074087
    0x21c0c03030e12030f0405040506062514010c021c03061d010e10080a170f070c1802040303140a031e061a07111905040e0703060608030909130305120408 67
    0x9500b00840d43d220f41c02803500140d86410b00800d2118510b000b94061b44d4021030b59400024501d40715101200c5108000d034440d80e907010130524101c18091510402201e001c0801242000100d1050145040079080c507009007482c0c10389602c0542c02c4126442c2da032020907885142c00110b0300c2d2080800c1c58402c41e0303954180308030340c1040d000650000c0050b0900b100070745206001c100399131000c1808840c503a03000440103150000000038030014015071407454442003002800a04024500e99280100e4440001080c402c20003a103001080307005512014001c104075944882940e00d2540013441da220b800d090010f040a50205128840500b0000042445680340014402d010441680d040030401d6812054502201039071603209144c004401280070316180400099807451245409000c0c000141c0704001c40e90300a0840ea55405140c4002d4442c14a0907401050424011044071504000900022445c3e2602024950b211000d10713015000c2040503c13012041c00000000302c3d01403402080f45c5074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 248076582 1250 248075332 248075357
    0x314090406080708300c03070606180b0103020903031206030a0b09030706050604110a03150b160c080c0d02120a0807030905030c01080103020102100f0f0f060e070905060403021c0c0303 81
    0x189170622402c0c5110005c0707015507880100c000021541c2c4181510042540e44501c3c4061b8500d1850181c03410061a69003054408500b021070710340300214602c1c440c1c00c1400452035500040d4200e2003050b042e5034060f0030400602d880030340481001900801d000e4100e40c0c0e41c0f030ba1506c0344401c2200070b881c03001160300b00107444002d10402e8040d00e900803d0444080000e00826030a0200511031281c80340306046c1c40c0d02e034224280c01407442040081203090041a40d030a803500100c40113514001c03049a03011b01c0f0400c045801a00003605520600c0041c020008404454013041007890701e1840d42d10b198856100807400080c202000b9000491203034130b9800c0168204010075081407038040722075040240030001000543e0340000c02001e002100d11002488881c103400090191a80001440c0345034144209010001407550045044654002081030592a2500215020002441043d9101400740410b02c05442d0103192070150500e010f20b00b03421856aa6190b5003001c6ca254000c0d00410440340110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 248077832 1250 248076582 248076599
    0x50d090905090601151101090804050307080718020f04121b08030307170711060c0c06010608010303050d0b0f0405040f020102010b0609031b0f03060f070912020d03140904060807 78
    0x440190410010901561a00d80002e03652810144035001000703105c0050400083d0040001030109501c000080c4514102410400070302d038801d01c038640c000e120321400003800110105118003a078005500285005207940ca80201a402035181ea420064040000048402c0d01c92411082240720700354071004803581003002d010414555201005a030000c00c2001242644031801050240014528000b161a403910869880f000c61465090341d101d4201030240d0f0544103406458030310f08990448200b60b0b01d5503011030300a1001c0c8001004280c0622001400c40c9507900460345903a806018400c010011400250580d00d0580713069410064449000080d541d0a00402c1c1e40a00240c1c0e03224a030480c40300110382e5038164015a030386168880d00744100746a881a46c1d07070f04d010500070100c4905080040c284185600d0986400307000c240c0d0a80700044109410007040c6005800402c02c503400211610700341e642900300c1400c1600400200024280e5070340314820007015010000c0280401e508040a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 248079082 1250 248077832 248077847
    0x30706030b010f21020403050a150c0c080a0e0a063f181407060315060c061a060d09110603091e01090b01060804110909060109091509050d 61
    0x8010103080c0744402559903003045004001c0141d6207041a4200a415804810010711084130b12181d40001000070078000005006854039004101ca286116410348030702088811280119000c81c02407843d10000c038071004082c2a40c0540d904101060010b50400141c4c01c0b2140d8121401203001c440056901816881c2c9055245424820141c2407070360700e140c51001000000d18101c02181c49035200e004003e02d1020000c03e02c1c1e4407a0f100c08083c0560b0000075210190741c0030300c43c006858805280c01800e210700912084030348a49403a0082030039520b800b03000d40354188a03d8049003030a05040ea460300d444008109900c2416400207981810780b07440f003100324140e002c141c8555028004d010040c00c002c50107080452208042034070008840c8085400340009ca0406003840a1080000802c16009000340340b00783c0c0304a0300c0100c0305110004100d0103c405031044019584103d00500c02c12940343d128801c1303a4000c071010b055800395000300505840e004c000880f0a50414418035003c01c0e00300e0b02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 248080332 1250 248079082 248079089
    0x501050c04061e23090307063506010509010e0907081801020c070b03092a10020a0506040209071205040501150515030703050709080303040f023609030c0313050307 72
    0x1a104181012810007064140e0090f8907050101c80035904144c000c003100c044a90b813a60180a45a9440e641c59018040c030802e1850941c101031842941d107e44030f204090255443e19002100b6007031744801e001120701e0341040c14450b0610140380d000360303915a00c00000034407030107065844080d18588031103021194403002c030558030300d68014841400c14540210b401300a48070010240758a0b0380c3c0320f800680c0361442c0d0361548203009141c0c44071019090608414215040c0382512900303140c50786000300300c0e96a00030f40317000780039500204082001881e02200964020081c2c0c40d04a03141c0102c0c801210456000381c500310b9881c1e54841c440c883c0682c082c040c48009210469114180c45100348108000d484010011800c25566a0009800d01d0049114401511a0b03034212601c0c2c0c54a4075003641d95280800c03090b1b00c200b100070802e42e0713501401d0440d1400000d000407181c10789040e1580001c1402c0c40a000703038225020034080010103003003c0000d400c02003440e0100d00d024a02d00018541000050341 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 248081582 1250 248080332 248080367
    0x90c08011b1808070306110f070606080d05160b060112020d1406010207080703030320040801050601080f060f01051b0316110405160825030605090f070e1201090501050c0406 76
    0x40c030070400c0f844003042c241c044940004000c940c1c3e000c41528000d1034418000180307503d045c086188000d1048030340c000d0084c1c81c4220100c4400f141d2000040c0c845010705207059082c1c82c0001c58450010f0407100c2d0080d000201810003d80c010380d03016000050382c0081d25078900485c0c1c0c0d03c00111040408107059a0425000c0c0050417a041c00d21507040c1e00d0304414080501856202c03414621550316000441d45401c112480064503143c450103114041d10301580c0d100d0000791910042138444080c803059a025110007030084403200e08100064955400224035060080340e4507804084803003061004100c1e1b041c0c00301c68103100010314946201d52003824904507019078071f00400c20460907004400381b1304c15401c5091100b0156150b04c0042010b2807800ca210255010700384800d40f0158040d00508240c030012540341d081035440c1c940c02072900070212003840026102410382503190601c1c201c1c41440301c2030900040f4a1310084c1d1031302e81c01d644040c1d440c0d064981002400300409580034a0820040d11600c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 248082832 1250 248081582 248081627
    0x20a05060408300403150c09240903080c06040218070e0d11040c0305070f02031e0f13030b0414010507080c0310091506030606140409090c08011b 64
    0x600340d03690303400c1000b5568190b550315056662903111512000003100190800f8655036684034504a0204000d20164a004a052004100d04140503030f044070207880d001c40d9044200300d21942a10820702c410317010380701407058424002c001300715014000c0041c0100034009000034202441403001503138601c03035035007084000c040a0046507503001617070b03030b21002c000c60340d45a03801d04e5070130880c034840343d580c1800398850318207804105030320f8041c0c1200b803090760030b500c2c3d1003544504000e041c0c1c2c9070b200c3d001c00382c2c2c580203040030045000c0040501800c806503005580c075041402041c1e0443c1f00b841150800d86e1404104000c01003000b40082e880702412180c0002032085081400b40544002e001518107007207910080006460000c60384c1211004244050040c08865a044200c82c0009540d00488000a0501d907003c2080f60060402d40400342d211841c3e64505031400c1d9074400200740c4910704542c03000515100081100090254100c0310644c040c0b4422000d56841c80940025a01240718690b20f24a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 248084082 1250 248082832 248082839
    0xe0a0c09050109180c050c010e070e0105060a140f04080706020307050c0103020408030304020f13090c050906090f0f040602090603010902090901170c060d09140703030f080c0304080c01060b04060c020a050604 91
    0x5103101c9442c0510b50031000b20701c600c1106000c1d1103c7c001e42240304500d620f4541c2a1108000010f8140100c0d00e40c54a4800035903250f9041c400d40d44200d44615000c1401c114070001c0302030069000382140d00400c484181041c0d114014242000405c3e0306c5034006038804180c0b4000d101e001d0001203040d01090904516052a010945460f03020040019126406080d0500305c1c0d41c48249008034034207210b5808204c0e103a40c51418104001c1113010b4a4013844a2400094046c142048100e015208110317100c802c0d0b60b6600400d14180c0d00c000c00c00c6840580900078082581c8500780654040c001040c405622a0304c2e0340d06000c0c0200d4140d1003501d0030003182c4c07a010070307031840404c0754101158290384603903580031490300b0480540304001c0b0082c01e00c54110003400c0c404001090700380a480c880d50b01d02a115002c820110b0700a0b1003910035003c90107007000070a00240d094002028020042000491300a58940c254005c913003196000c10003195098444104620782415800003034001151070f141450304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 248085332 1250 248084082 248084099
    0x50718021305060c0703060203160305010909081905160c080f0109170904060506180102060f07080106080a1506181a0301060e0a0b031302092406030a060e0a0c09050109 74
    0x280c2d02c115402080e00044da800d00c000b0500000c5c0213190400d900b90741d6030800420391070004400304c4414001910740000800c200c3d0050040d10841900b1428407818540001f114449850468000c04e0a11404201148281003501505809240208015400c1030318002015080c10a09081e6801c1079241285410005441321603801008070b030300d0903070340e02c07071028401150007800c0541050f5800280440e04460603070100101d04105c1c2000c0e400d03250582c450001410000c0742c2601c0407070100d540c1d00010b100c664807811401e540040c44180100e0b0140110f4240e03001a501c60300f007000020003e02040c50030303402e9040800c005020106884050b003090800040807400180591407c100075031001262a0b911500410050003101180c15501d0401e5810340ca028484200224080c10388540082c0009071808024140b065940a40809119040c020001c5591008008052040d5500e0012800c405076041c034500c82c40d82c0c1480020710b140080c6010702403044030782c0401c1c10400c040c00c0600850f00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 248086582 1250 248085332 248085367
    0xe06211213150906030e070504090506150603010e010306020a0311130608070f0206061e03060a0f060f060503040b06040e0a14011406060f160b070c061109011d0a0302060705071802 79
    0x300d0905e40040c6c0c44d44402840e9007001d602ea0701140d84075092138051814010003140e224010114114030b040503414143c18410300b80002d01c10105044007000041021981a0f001496545c156140001d0140d6440310140f406811442c2000100715800d2000e1041070f4025242c80d0304201c03282000c41203281e180c03100030354031440240a58001c1050516455250085550744018110003c00790f4010b803400007081c4000740f030280c5030a9100341c21710200280038490030f0740d4903003030307400c59510306103907a4035500c0300e401c040b0024148a80241d0b540600d10400602444000f07181ca20075110301503440341070f41a250a40b001820b01007034400c1240180315503607464804035034002c8580c02d0140c1e1505000d0035a0304274500240c1014003e5085017040008407607020380f0f05400a0310520080001e541074503003c0f80b0350300600304118040b58012940704182000d03405035840c2d25000a181c500940e80f290301062864020312004c942e90781c8070701c80a00c00000d109504c0d10304030020700030440c20706d00e01e02e041e1000304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 248087832 1250 248086582 248086589
    0x8060c090f030f070b0a02010b06090904020d02120d050d0f050106090e07030e031b0d080c04060e0a080f0c10030b010c06020c160303020c030c04060e062112131509 72
    0x5205044541026403030a208900d03c0300c5074201900c00d01a076072a5029890b034060340240005520303202c520001c030319109040d40c564560240c081c0711659241d50070b02c480e50340c005038241c1c1c0c00342c0b01e403065020400c820401c0340401c0c4515603c06d40c0301c0c1c0d261103840040d21042100540711504100050000580c00748810040b0340800c00320840700d84032008190700030b20503056141c401303020000b4000000003580c15007048402c580411a40241d10486085400c26401d9446c3c4548110070002002500d20070f0307042c2d03800140c004101034a020380d40c0c18030600e401d51000c9600b1250f04881e001402d1840d01c100c0c0203051540906050000302c05071000240003103640707180286901d0340483d03c400000340c20082030300101c0300400c21108498032400c000c0d5031000300043d8030344203200e402d218403850b003014000d8104481403150702180c940c0f01c130707003c0084e00c03604c0320420805400d180503281c00142c2c003084541620f6222241e070950b22104108686d0358507580703401c42c46602a40e010001c3c4000d5000700317520120b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 248089082 1250 248087832 248087839
    0x5090406110d0615120228020c1c03030e0a05100504080d0e0c0a08030f18030c1e03060a020406170403031523010311040905090705040203011d0108060c09 68
    0x40d03049100c00600e03501612840c041c0c401c2c944000414400d100d8507005501d001d55403501c1d05e4105071000b0103410b81c4180c1c2c00f1070302c071039255103032407400195844690341e50241c0d24016140010702000100c4c503a943d070803c1e040507040c0420032140903d50144112220300f8100d00181c44540400e0300c2d420b0703452100c40b850368000f0341d58200103010f1149080503618080c2d1a070720248032041c0c01350007030396840480f4103c0c50700c42c03010040c0006000310000103c07020524444121818500002222004200c070445815054041d04c1c80d400c0300c66481881d1014050000c0400b0140e058042040c10300d00340340108400250b9104000c2809420780002da80c002c0520070a0146100d55a00c1c6030440180c421496070030540e00b8019130104281280e1450744040400102c103405607035008400440680d240c51118a4004000700010b11603007045820440d070140d0560200c2e1100c56a842c04034040b640242c0c000e503c10b010004001c5004c54111a5070b0b401403248800a229034185489914400d12948408520 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248090332 1250 248089082 248089091
    0x206010315110d09230a080f0c0f0307111504050609040f110c10050103020d0b04140304120203061b030a0c090b07060e0d080106140f0c0a0305130b0405090406 70
    0x34072016504404400703012900000d8540008540002c00f034041881c0464130381c007801410103068044c4454842d03922000400a0854103002e440d10b15041e80181c140e9481040c08004880e0511400c0001155640e01c0e840216036445c0a030030000c3c2038050312000c181c031641030f00c3e003402001c1500d502641c0a40c1c4040f104280c0d80c462650007c1d0040c04005141001c0505010003203101d016140050203000070268199400d4962541128007202d90902009500c00600700c8180003107850080dc0380e5200e4884c2c111261081005001d041c9550050380c4001c8003070814a100783c04604042c031025802c10b480050201844102c01400a02800000e040c2451940e0751244502030300d10500c680303c020725000c0005682ca01960409102070070f003040c00c81c1204c1c814188407803942d0b442010301c941202c00a5503803206030304d9490510100c0c0c0e800590254a00c5105002131410100140b03c214603652081d290345540700c1c1512503018480080d40e0061101000a01c0100308a8617080c0c4a543d100b603200b4070004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 248091582 1250 248090332 248090363
    0x62c010201090209070509010e0d020d0b04051e0a020406060e03060402100e06030c0909010518070309170a0201090c05010f0c080c07030c080f0c06072003070902131403030a02060103 80
    0x3030060842d203001a500181d038000340035110750810020004030320b082e43c07100c440d00038500500402280c0300c1c0c7c0c0250007a111298610100e16908652a0040e00c50001d9658030407044820001c0020300d0700f040c9000c1c0d000b2080007421403030b01d44541c030010001418001c0303a00d000340c40040c1d01e03200010000b070300a0144a81d2000480d1240030040c0910f18010507050704d0b8205a1100034080e0045051b4038094410400003150514140741880e19498480d1318204240d5210b000450141c0070701c8500303d904110401602c1d00c2d40c0107200180031041020380c00003036201d01d44c1c10840000c84080c1d104038107104445020303034042a489001c540c04150002402592402c440400341d2a01520340d01c003070502d0070078a00c081040000440c49604203a50a001c480c04290304804001040c0b10700c0324003d2924100352404448030038408031003a01520002c0c1502c42c004e03510034a0b4010382e0b100c494540040d080c102400c1c884200c03402000315144e20203600840c1011951480a9611681800050080d4607441d10f5039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 248092832 1250 248091582 248091587
    0x9190506060d150c08100b030919021801140a0e15011805040219090b090609130f0f090303141e0c0904020a1d040b060f1b0316030801062c01 62
    0xb1040320f06010100f150354034180004000a8050360002c0000c00703400d00000307990792031900b40e0b0f00490b41000504100d410f0f4669803288095203020898110420000d100c548080103200d040c000c00e22001d8464120b801403080040d0503409070000411010f10b078080c410022146811815a00d0003030a002c1c0c0d010602c3c1843c8513860030785520869100d800019040c1d61074100340c5440007405429101c21030000d88400120415010b20740745550090030601006040f450703c0c51170b24102c41c000c0100051000d54602100701075581c0300281140c029107c0782c1003c2015814440c00d80c1d810001f41d109865401d082003030f402d107810140f6104070141c441401040440300c8400840e1400000108115507498150002030604400e96203c1c1d8100702180780d001184d0300f05402070700b2144070300501c003500d0600880c7c40c400194000166417640880450700e040000364040000341b0070301890365000b050209203460700400400050300300d10100082c061802c0301c1e8080d04114072460900031100695520b001c0c5004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 248094082 1250 248092832 248092853
    0x615030c0405041101020708010b0607062f27060a0c031e090e060103050402030c06360a15020c011b02060a0e190315090f0f0501020309190506060d 65
    0x395900518007014042000a29094405014002e0b001c1e2220a0f9640403060308980c801c0c0300c202d410200403c40c040005840368066000021008445d180184400b130038085480800300b0b4072142c4c22000511410090340b0011a600500c141c07101c6c410268065001143d4a4001c501261003400b081d440b02d6010107000c1d042140c0410b42d000c1320001c8a0901c4400103001003068030408680c0200000030030704651003805000d205540280082c11640c000809015842c1c1c040030310071668003800c9480940399641091440c1c0c140c1144400c2003280030b40b990070007803415603a6000c4c0e43d464101c207100c81e1505402107003800d5100000d0900c0200104d000b1000081c1c020000700c02580309000142c1784240c1904203850141081043d101003589003490110356220811074000030b0304494200d66000c000c1040b64000b4082c1e80c0c443c010a031201507099681252081c0441801c40b0565008000c00a0b00403040110b0714101c1180200400740f0740c2e45486041c0c960a000d80304074020a542c1d00c1c442c040c0000082c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 248095332 1250 248094082 248094103
    0x180605030d030906060905060319030210020a0e04060504052509050d080309300c0a050106080709050f1501080a0e101a064303030c11060702061503 65
    0x3581c80d1800c554030010000d298503042214481c0c40c0001c04601101c0d10301c07903240b0444c0064003c0102800780040a07411000009007241181301e400d481210504d8a4005440d002c0200c0d140d62600094a604004c00d0b02c80e950409030140740f070081000f1030100d4031012509403920f15421051031044459044542d0007094200790380040707080355403400700003032500114810312190f41a6424840145200e114410488401403c07215051642c548203d240f5002445149280022908629076654565007503500c140c1c82415943c00030501041480014051154444401c035241a4030f4a420b0804038400308012455504000c000340004503916290340c003001905000300c0442d0074844024400101403c03242c1400490300940400e01e40d03107400d0103c01d94000311000c0c103a001c149042000703880301c0c0c40c07400070314400105e944018404040c40555440d8040c01d000c0da602180c070540c18180540004458070354241d550b4029020080f150754003051107900000142301080c003260010340080d150200250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 248096582 1250 248095332 248095339
    0x32202040207030908011407080c0a03060302030f030c100912050d14010305010c110303060901050f030703120203031b1204060b0a1a041409130f0609052a100504180605 74
    0x10b031100505402031400d808a910041c000e00a03800b003003206406100003581e0b41c0022500344c1000c1032101c00e004001c1c1002e29000d14000404a6803900081c5c079081d1800880f521f55000042d080005060900500080c44503003031084c440404184d850f00c895240b04c142c0402080030201d0342242e288515001401840071040c101d5103a540c40c0c1c00c1c0300d802001034030007039004903900c400c0c85681540044180e034465080103041c8401c50b032800301401014041c205009505000b070810120002d003003141121b014418680c0155100d2811b90110030303040741d450855125840041c001b01544000c10b00c04182d00503030104020449200000c00b10b2408161030700030f143c0701d5200108480d981c031a1403004c0c008480e031001103001e01c4038601c2e0078807040c0d520594060408007008149600490798a14000c038178184120800900c0811548619090040e608a082c0500c40c4010002c1040701d1000f41140d0f1a00007110040c0d664040c3c1840a0310130302c0f492260b1201d0501c018040c1004603010f5002030004c14014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 248097832 1250 248096582 248096587
    0x90b0f1b0d120506040605010e0f0301022221080d0c0201231f05030d080735010501030e10091401090302070611060403051605100606050c01200322020402 68
    0x740c1e0054012042203682444141c90035001403100e03d414000d820846606071500700320b40c4c070910140300003000c00c4003009800d507400b00080c0e040900040290700ca070703100c50b5002284940c03e1021308030040150761504130101140d49100c0b0003080c0c0210407154901000c2030b0005004503060b40503400340c400500d000f490110160580c0b45540001202107110301020b084e525407000c0c98524500351840300d0301500340c05500ca820309c00c0501d405040b000390813661034201032502c5803006d186940e1400400c40c22000c0c0840a11001d0b400b400d041c8880c5002d0b2900742000d1051001d080c9400d03981d00c03611032000320142e450754884000e0050008120303030310b0110a00240450105420b010350b54001d03510640c00040c610741c01000002c14003096090040354165100c40ca8010741000d030020707540c22100281c609000e0204030710320f004403c0c415500144100d0f101d641e281d527403281581c0d0071504800c0c00300801000ca00c003182c806901d980f0840c6e520074211445d02c104422895064042c0c0010307210f0013034205100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 248099082 1250 248097832 248097853
    0x20a0302031f0b0427060b060d0b010e10021b1815150403031205070e030604050c0f01080f01120510020d02040f2123070b030a0b01090b0f1b 62
    0x4004815540c1c01800c8814000900000c0c203000032030b01144039540b05d03a000901070800c603040103d00c0346402405000041005600700c2c00203030050744542c002c248040e0791240120319658000420aa20642c04c070340006080040f81000b07504c0d500c5581041002c1e03107a8400b111065601c6819013001181d442d809185149807016a804224140c06001e074814291295003140f040100c108840c1502c1d032560315114000b000140002c0640400342161701400004548035107592010030115100703074041c800500031102c082c3c040c40403520361007051604000a10081000820071042280d04641699910030780050481c00c0c46820302c0c040083c81a1040d0000500c3c480605450300030f031040e15090740580401c682e45a07042800310004d503000200c145903c2089001284410b03230040080501510310040c5220545c0b0102d040c40703416008020342400100902c1040c107514840c071860081d0a0a006880f03500f031001c582401c0c080c00380d010101000018a100c007104c4840b164407903840d403010427169885072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 248100332 1250 248099082 248099113
    0x80d09051011011a0103050108030a022121040309050126070c0803070e0307051f0804080c10140907050619050909090a061a10030e15040c030b010602030301140607020a030203 77
    0x7030b6613681c0303000904060000c00d500f00c02000f256940b40031500201035025040d10502007c13040e10180c0d07611031600b40301c0b001041800b9411a0b40000c46141d190714a85814074020303040710495008ac0d4100103542d0030008030302c902c008421f020003030804079144031a500c000040714003c400c6d640003040c614000c0144040356400050b0600004012001e071200691a072003805001c0d40c0640b40b8003100394188181c0807082e0300590f452a0030500070413003c0e26040e126410186080b00807103404441355035800a40c20780301c240c540800d4014002c40040c0541d6440c10000503e140180b203250220a5042d000264030103014204588000b0b202602924481c42c0c100b0b440323611007803201803e980480c1800c40350414840d01003a07803c600b8070020202c400c0104045e400f04c0060400a10744165486030422045503da08190054411449a80000f020500310300e402161414107034456030a540c020300046c00400c2000030381d00b05d010019100242c40f50360b035000284482c6620b42c80a50180902d4583d40001c0c0ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 248101582 1250 248100332 248100371
    0xf11030109050a050f01030b090703050d020d110304120b1306061508090f1e150a0b0a080105010305070515210a0c080606190909050106030213080d0905101101 70
    0x40718070200300442d5841c2c200c0e50302980c00840307a103182801480700520001d80056503054001c00c1b40e0b411240616165030b5094601507a0620004c0583e005001040c10309a11a648015010003034014500b0f2502d03092078420309204258004000205090002d601a901c1d2081c071052140c000c4001c0c08644d035107841c009030030012041c0b00d500180010300040d801210000d200703030b81c0141850040c2454100040d000002c40c0c3e0349658515140a0002c1140c82030904031226405542001c070700203142d01c0a1010031140f0141c55000034280d0b41030000420105002140310800c031002911805903110046921600c2441101840484120b84800e441c1c28885120036082c8151b417800420000300f1038482c03041d16600030803074640e54044001c00c846c80745815140990f01080f0460304080280076129403801003600ca090300140e000981c00303d25012903810503030f41100100300800181404021000004107104014000c00e8042e508070b802c01021248164540040728040303100070040c0b03040314608101d800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 248102832 1250 248101582 248101589
    0x150b0a0e0328061811060d09062a0f0909020901090b0a0206060103050c0f04030611121e0f060f0d031107030803040210080f0403032c0610090506010504180f110301 72
    0x124600380c0500c640c240f90040041080350000381001c28904007a0410665600800c103440d07c1c0c1e030711408148005141409000d914108400ba007501840401d030407440c683d10212542e0f410420546d00b005c19650704a040001a1085444050303a02c0e1402801604c5030f80305035208034408000061690945607021a11900410342603034240165182e2911817000c50003600d2086006103002c000400000d503160344001400c00000e681c590070400744105030181d40d0300490b03140030440016902d000105840c64201c3d540300c05a0411492207081240204140c84860170301280140c1600240030207160003214124110508002250365903916440c10050a41040d68100d025428170a000490079020309100b520034140a980c0644582c0d0790f490031001790100c0c161441d903d0388000d0380034014562016228040075120001003600d03007044d02c0252524060350340a030b114075103084c042c0724150b80d00204a4044425151a1070743c10030b43c0103c584001c101c40840d0216a51604442c60003003513801e40514101d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 248104082 1250 248102832 248102843
    0x601091211090a02091008040213050f0f0f070e0f0d050d02010204140936190b16081303090b0d06060f03020711040f0b040e010f150b0a0e0328 63
    0x2d52a031100c55416030180f0f1032580d41c081a0710034160a001c1c400c0c03017040d174800d00040262468800c0d146402c0100d602c15210f040c03c0194a008100c0106801c0000c56048190030001c1d486610b4124001050407804051b0b0500c40c070314901d060400c0b666141d103c407070541d401030140c4903044070055000c0d0007540b00f44260010703203649007041070f2a8a060355a880c49107e1601c116401c2c0041c048444040e0402d209100c3c14403484080d030000f000c1020440d0b0682c0301071010079091140d4141c1005030607524010b001142c0c0400c000c9220300e0145c0d00c01040d0303800c540424000402c00303540d41340558480308250030681c0c011401050008074440039404c410f0441d001a00c07002040342c130b40d1400b00c0c103a00c61044040e02c0030398500c208070b0380d030b0400340e00844101041c507800260941c40c00e00028161464181c154040e030b91101c008032014021403280405030011400c12079045441d095400c0c0071405558140014890543c28401860720180484c240403001e00001c48405003050180c3c120384101c5034801e0340c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 248105332 1250 248104082 248104099
    0x4021b0c12031206120f030d0501031401090c0b09030a021f11030f0906131d0105030706020c0108150d08040303020321150d051e01020c01052d0601091211 68
    0x82008000c90b90100a2100030110f1561074006002103d8101d4030400050300c00d500940c03500a80a1010304001d0900041c0410b5a51441c1820010503100a1a14140c2d0f49000982c1000035250440541120184240c2c076440303200980c000380c140104450013a4106048421074100c82c1c540c403800910842458440f0306407100c41c0414103a8a029040780c0c020060b00070800400035240240141400510b1440841d18883d1520f40d4441852110301c0c50751001c00f22040180030300d00d414030003070000e40001c0c8000e1001c1240d1000091080c14040c281c090030170703a1029400107a440b0303006000c4441d50003483c001d6681d9036030b150096980e448100c220701e4214820b18080d009001d82c031f0790103001d02502405402101c1540c01000565248034808803010310501711541c0c1c059118144000901e900c0200040e2948035280050f8207480d002482e11040d010300050001d600f81100600196a1144000024242d0f580c40c00503074018000da04403003034000102120408015407903041c5100700000796003103107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 248106582 1250 248105332 248105359
    0x10c0905030d08060d12020a060c031503110d05070618050a0e010b2206020d020c0301050c030c03070e03060f070e09011a0d0612030203070b100e06060904021b0c 71
    0x116011a00e015440e450b401008640c0800c078814400e264200c030004001a245142c40d654040814048890001c0981c00a05460007800018801d007407024a403414240301c1c80c070071210039500a03019804001d00d2100d202038201c04940f40e514440365150740c85000c03078041d40d0325150701070200401c5c00c1003a9124101380001060328140310b001e0104655a500c103402d510303400c00030800d000d900018078500700b81ca20740190036490420f2200303440041401e600685241e100c140002424422880c410718060303030600081c00598512001200d50110b0144201d03502c944510504860803103034a540a40d01d031103100c1c2881610361f54244800e00a06058844030082514801070064840091003a4510404504100c1041c8100b100040c4148030201d80002491a1141c0e41c000c450b0055070802c3c1e0043e070000c41c0300d404010307601e40c005400c8081c4811070380a20b45040200044500014040307401100c021505028584403a015180102c08940b50b0f080800003402003140d44040d500f99a41c42071003c0030092 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 248107832 1250 248106582 248106587
    0x130b04050a092c0309031b0406090204050901050d1524090b0108040206031503030403060905160819080d020c06102c0705090a080105010e010b0a020307030c24020309010c 75
    0x1d04195018010700e0f840e5048041c0c100c03020001c160b0401e505000c20401901c46a9041c880c60142e0060003100c0a82c244140b4144402c9820743d4100866642c8108814455030f9a0fa209540c11108100c2c4e03240d146c0145860718038101c2e01c040200c00040c5003040c407160000c1078a0150070001c5980000d4214145560300340340d0055401c070070340c12404500350401240c05402c04800641d40403100307110003043d218241c0046481d59004d42e205640e4903036505400002c00c141400300c5003011520030000f034005800e02d24000d807540e120200401c0709100b4451031108100000090f40e990b94a1200704544803110101c2d141d40741c490885038030001c800712000201d00c0d1213007190304011030011a1034003904440284107005440402130580030030701006005154443d966031000700301170001c1400205041d4548000b021501c181a006a144198280000d002107030340001a218095018a480c84100815040a07400355428a130b003000d43e0850f0b020089005000c0b034004502504203071300200403151840b1001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 248109082 1250 248107832 248107841
    0x13060e09070c0605061c06020304020a0806010323121b0606012303060604092c06011d0604091506050108010b071a0a0e071508090604030807050f130b04050a09 70
    0x19200403032400002c1d00c020800c580d11165221501a01c0251045e40918620078940350740c0c0c100312940340d0000200310850900d0701e14074004005001c02407840f541150b039803c0035445c0e000d00c2616401c0d000401204540c0080002c0d6009201c617121055a443e200f42c84c0b2511110744180b4154540b0465020640030f5120b03c6402e00c0543c0e600000801500550540c1203140e400504540da21420500000c00c800c0300034030400d84032170000300503107201c504001d41072440c17811840c0030820503410170801000780105180a040807504142007954096a8000024000785103500000c1c0045032882c1700640f0345911680035a06554098071001003581e079540340c0c849030b40b140100c001d2400d108c80071005996140f00808541203840a10f000c0360303200b108003800385004466448030260050b03203410b04190341d8202c443ca541000400010300598035040d10007920012000e4092010030400150054910300b4603019607041e5440000308200c0c950b51101e2542c01504507004461095900917800258203003d41314 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 248110332 1250 248109082 248109091
    0x3090c1c120809120c0705090c07140616030f1409010608010b040213030201030b1c0602070c0b030709031b170c0108011203080402090a021c05070206090102041211031213060e09 78
    0x5101404c8600781c0c04100350020b22420781144600c00e40440d240c0c0d503110a061082c41050f8a6680b10314585c1092000e41c0c0c00c1494291541e0411400d002d1440034001008040392550b003008152088450300c054010440002c44650340400b0005101c46228190085011101c0c9900203115800082003040102d01c1582f6051580000000b010401540a41c00042c10f001c1e00908052003d6003600d0307039007980d000800081300c1c507a0740010481d0801c014a40080064640101460b05501d042c202c0070340b10300301c14040a07260240c0c2e40030301404011581c1c100005001903500039807564000c0c5250301e03900c903c5032900601144d020800440c00c103914200025045800d9a03030115151140d40901004070009000c0743c5030036400300174884106148803003200041606500015003441c04510003070901c0c5020702881081d90042108001b03c03140e0a1400d664250442003a144c4444128000be15103182c0b040d05448298010903681ca030310aa00b07440d1405ca0b0781c0c03916a0002c00c0c0104040000c044011103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 248111582 1250 248110332 248110351
    0xc021606030b090f07020f070b1c140a0e0309030a031707020f1b040b040c0507030215091b06161b0602070e070c050703050303100504060e040206090603090c1c1208 72
    0x240044c1180c2c0c014002035420249a00640301c0c032103070600015080000d243c00100010b1000240d0303070740500801d00c085484008444041003100042064601888000f070000401c46442c5c7c0d04025480b4400c1c030460344039150040444103048150300d0090f000c00ca400300403202c40050400010aa41c0c00482c000418017810009005250301100c80e54246c0d1000d00e20700c58009a40303241d440345030740355803058036500d88950b25896120702e01803070b00030314000041d1412140d141e004002d1240c3c1c500009424042c2008145940490300085d0000c613469020f6a1081480070314110602014003440b40701190740c2184546a400383d264998000340d030394101500c640d0420301c0c22a40080c4040788070340d0448809038425000d0f9400c1c603541c0e4031401e01e581c0040c0c4102d0321540d40c2000c1001603103010310604e0018a250036215449240a0f0000381032802103107803003030040100100050b13414400740f05100a1003001000320001c0c050744080300011107807096040741c3c0c1000010b445c0e0320450188211600c542c9001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 248112832 1250 248111582 248111599
    0x909050609121902070e0717090a020319031202030a0c112805100f02091c0b06040903120905031e090a030327090207050c0a030f06110c010c021606030b 67
    0x8903a00810760f1240d070195085004400000c1440340c040030704103020311070603034076070802c030a09100601c20940050311442e4194806900c0e00010784000c01c482000306114641400450414141500c02e102400b240c4600a803001003040003812003984540b620310508d07070715042a0280303007a0f040c3d81e40e801c11f01307d150840840c0c7c01c04420108003070f0221510520960a0307490194200714604150360541c0000b40e446a0040380341c1e240c034244030b8454515107002d955102c0c0c200c00e00342c849810001d800750419010315200c4c0c1c1140d0505000d16803113402007038002c40030886a41c050400c981c50341c00140d82e0066142c50441108120110f08041d10109040207100c41d4000c0d25694003560108880a0001003107401c1000d080d40142d00b81c401d0074002e101085015a27180341a24000f0300b4803081c440c3e103070311441e400346003400070501c4001010a8542d000000181c51040261111840c0c0900c41c5070031003940c2450700040c4040c0c0d005c183c0902c98080c028003440c20b01d4540100350203841d0340203a02a00031214 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 248114082 1250 248112832 248112847
    0x3030f03060d06020906070501050601140a09090209030f10020315040204080c010806041d0f0c0307031509060f0f0c1107060f0e0402040521070602010510090e07090501090905060912 80
    0x1041c040c0b41e90307100d940014500040d12003c14555002040e059680b40d55943c10001c955800c19901682c2e04244411303a860440c0380300c0d0141c80000b2034090038960650100303114000c0d481c2003050081c00ca00c03a004070b81403e650603402e4000303540300701e41c2d0348032041400318804240d040c21b000740d41c01e4601007400707081c1c03c403810001154840001003420b60b002c0d449414102080a1304102d0088003a058005050708104046925207001d045d40e148500036030020200700080f410305410002d994283e528040303000c42403410701001034100c0002040300c0d0b07460300000030703503402c180c0c0c0c40078840055030340319007240c42c0c8848040d035181d16151252502243c0305840c0100d46c188650801404840014401802c00b925400812103000090002d192001030f45441d100100c0c4080110b4070003040d86100900c0240b0740b142c0c6400420000d80b180b4401c95032901d50300d4010390802d025447c0a00201c02040103203680da0900740b0060040b807201139506001c1d40c0c2c04110140800300d2002e02c41c12100c4650303480c02d0b6a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 248115332 1250 248114082 248114089
    0x30e01091203051308041d060d0b040f110405070905030d0905011d061603170c04030c0302061b06090309040605010507080403021c050a052b14130f080304060e03030f0306 75
    0x8024040340010007954018000500d0b81c102030070150111f80b80c810440d450f40c030380e03986211101a19551056001c0800302c00001c005800c0301764449d90106c40c5c200708502030300c0e294101e001030640d1950b1281c1404104044d20354440c00e030104031002241111f850f0520502d095404a08500906000a24280300285d403e460b001034201d16034006004076250440c5080c5039074101103185401c9000415421b0b41c41075100040d0050382d0406000f5400c0d5141c180781d6550011000114032009006110114450480c0d1034208050406040081c0c156646440c025072420b07205d40c4101c2400740719900c0c0407030100d075035446903003594419940301052601d098115001c000065613203a090310428420314402c1030014030705002e02581d50344a14001c04015030400b1940d8001c600000b800181081101a0300040c19400a90f12211621100100390385490004001b070000d542900071000172000d44800080380b400000c021b00c1210541d5a500300c0201140e03081640ba071107000c031a40c00340a003d1010a51914 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 248116582 1250 248115332 248115341
    0x609010804120903150509070b03090a020907110f06010303140c19020402090a0801020715020708031311150304170a091a0d090609150203130b06031608030a030e01091203 75
    0x501d41402e00340a6500e030360302585c0000c0002032808803a140c5c1c00b40900c0e114100089400303804103040307042c10762038001c4901d9074446031280c01078403640c034480c04221300b280035810bc600349071040015a03401c1651007a2080c0d884c102888200d000440c3c00d80c02c0c08070b00401c4400d840d1400001400340071034000e28484548000900c1070160313803059007040805000e9944a1869000700701c814005030301c500707032418100d003500b0400d00d03482801c034010030030140000c0c4001c04603a4440c00403040a40801000e05095110744001e141e00e50304129402c01c8181620f100c40c5c0510700c914400c441e0000480302c1c0e982c05000c1409010b5150020403091002031044690b00072030301240c507000030b20150500c5501c0e040340003036496032001070300e80e25a40c1d070690007800700c1440400000003c0c0201503183d810850803070018916036207409800750050070b02240c1039540500044040c840c14018483c0ca194032104d00c5a1203078001542c03080031030f18211010309032082c18080d8401a5400a0a021000078491410380190 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 248117832 1250 248116582 248116613
    0xd050d05041106030f01080606010c030c020103020d0e0708030706110403032003130608011401020f060106030b06040902030a0e0609060603060a020a1806091e05130914060f0f060609010804 83
    0x40820303506091646400024500c170b0400400160419490200240c0c05c00d400944040e0410a15407121004241c00400c0005a95070a280050740c5400300c15502c0f008042c0c20038078420500030400d000400d40fa002010b0042580115000c00240c170001c4040700c428171980c030008020070070594019065500b4912012186a0040c042d030349840084400500d0344005504040049a240c200601c00c0506400001036400300078002400381c0700c4480c0000d661420140328240405132100d05183da00e8943c00d050302d000b00b050100944d164202184000007402c10400c0031406441000e0009024400c0069018056580500540b034180c84140100d0041e42c004c036007260600006c11585080c0c00b4050320598002c0035242d448880d42820f04424424150301506c00079184c5c0c101e80028082070b650032003414242580300d0400100c40543e0301d003074118070060b2141d4421034090001006802184d00c240c86200f0007030302c2c0341030341556038620821000d0301611039161b000031106030000e00000c1e180e60b03411400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 248119082 1250 248117832 248117843
    0xc030207051e030d0510060e03150c0a17040809011803030504030b060f100e033a020705030304090e160b12060102280606050108060d061806020712020f0d050d0504 72
    0x9019540a135407080c1c1e1015150310016466159080120562101a60350049002c80c00741c00803240c04d0005565407440603043c1001401e00043c50740c1070307034025080c9110a241c1c000c44551a0b00e01403c010780070350032843d9039074003041303135004d003007142c45c9034005064107890381500c0305820709086440754000070000038000c41e08403222440890543e40d80542071403040d07050381e80d9400c0110040081c942801138020365403140d96002000c01c0e1141c0100c3c1103015601610100b405961821048203e1034a09154030240d0103010025000c211804550082c00c0b85101c2c01c0119403080c40d01a0031125544014800e445e400c0d80d0910842204c400c0280340903410040500c12100d140d0801e04888501000e41e035000d6035030221b02c00061040000302d000b0b150040c0000d081c0b154491400c04081400c06004070402055580d80ba01c4402e948242e05d00321040542d000030f01192565101e260509050541403804005032007000f1030103075900b2001481e4241d070405596a503051020700b0112501800c0003810440d003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 248120332 1250 248119082 248119087
    0x30c030f090d02210c010e011407060204090c051e090109180e010e03090901081501050d1a07030b0f040504021f050702030a030c0c08070803040e091e03040602010c030207051e03 78
    0x340c1d403a108513402114801031400c240c02002c46116281484580e404c40c1440f10a90078480b15a8001c0490801d00b0241c400242e55903000780f070103034024801c0d50048140e10345016142201650710030060284041c0b5030307800c0000c0c14032003214281680554059180051003c0c0c0d0188199200440e91844080e440a404134045500c2010a802d41c1d440b104030803616400410310540c1803401c102c0541c01020144040c00440d81c0307080c0c00280b0064140907981c0200304041c000b10401c903a4401c054201c0e41008010200c0b41041c0000601070400c640c80340740b08070041c0e00c061a00c0d190034803881d401941d008003e900c55070042c81c2c6600f0180300c42c2005e107090140900043e00503842c1070116400c10b80c0b203581e90391072090a03803601e60301c51250340c2c2001049506c0741906111240300041118107440c0480c00c00e049603500d03406000d2510001d20001103003500c4400100010f024000b0151040d2800364000344031151250300202d08900440380003406940c00601c817242e007a807903a648142d40174480c00030340c0d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 248121582 1250 248120332 248120359
    0xe060607141b0114040302060306100207120b070f0203190f0201200409150e0406021813050f09011505040f1103090604020a170c040b130906150602030c030f09 70
    0x10b050030103000540c601d0b014512402140d80d0707403112011400482041da6241414219008507166000052113240990079a41104403410b000700175480007414022551201450325143c10705026106490500100340108001da03440f50021080d64005140d04c90b511390150010b44040310041060101d900c107555a41c6111501d00483d404210721246c1c1d6100c0095485152410600440d41265001c4425164540c400d000d09802e00d8a01a0401e4000f507000d030715510101c4e50340b018440e8441c00740c1d5201035410040c141c07546258011520644240325400c109595140d001030030307504c07030111101d4010401c0806005614007a4419140c03c4106e050014180e03480e1040ca42c0d26610a4030034030034070f92140301000210300d402c1005501900c03802840c4844420a0641e207583c0344506004644030341c0c0c071481191255150360840d030400038005403041c07140ba00b00d420004002e01099444442c072043d004800306401c2c1c00041114000d1450100a503e881c2035403061141d1908801480c40d0700c40800201c81 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 248122832 1250 248121582 248121623
    0x70908061303200a11120303010b070203010216060e1b0a06081b040609082a060a02010902150c0c120703150207020a0308030601170f011214030c010912090e060607 72
    0x40c544216400c00801142060341844528283c2c010b00540c0315119400b212400c07641b022003564111040d50007060307128440351001901a020b060385c1145109032105210080c080641c228016100307054003940d00300ba050780c010302c00c41c0d0100820b080d0000d00302c1780300f00314291103407071380c240d000d885810144500d020350407900905a10a0b400303400060b01c5c2100c1401040340500c044d6038003038064030745c1ca2080c1e0180c0d48404044000d030903d492040c4804525080303114000c3d0400a00c0c0c81e8003e003040d50100800003113180540003481341301224440d6503107a030f1890801f120848a07090100000300205072540c0d0303d0b010106d1202c032540388010b8007849035a0068481020110107944038000c120340341c0c074009000500380c50342440c012096100d01410300980130019001c49055074800041c1d0341c0f02c0c0c0f402d0b0401142c03003101d41100c11154480002c54804000040d440000d90500c2403000c12240c58008208413900f4885000d00481ca14900d004162107203403920041007682d104410030380318094543c805 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 248124082 1250 248122832 248122877
    0x207050a05030a020d030605010f05070602070b0117071d06060325030603030311070c060809250509010503030310091a13200f09060706020403020621070908061303 72
    0x11500c81d030010583d5940035805010b50350243c2214542086503a19100008041c0e1088070005400d0110010701c0c0024400c5507012505800d0700603408110a503903480740d0140c0482400014800b6002c1c0c068082110395040060b4001c044000807629202e88403c810451264006414403804030100d481101c0c1d1400c440c40c0400d120070b040d8a001900360f01d141805003e49000d000603c00c0c1e00c204004000010b510000150b0a074ac40c06d03c0c145a1640d551300455240441e140c0000d000320580c2490a0750172500b1086002c26604240e6640d107050b41e07550280f660340d0009558503821690344000510041003a58442200042040180c0d186002702001080b64040401c1e40d254815894610ba4400103140744040d500010f0210001c9240c4607030309800b4007090242003034841c0700d0303074001510109018440e0103441c06190002c100325647c1d28140007481c0440340d80d0440c202c40680c41030000780460300030003107170003103072085005420a5138400c6150321511003041011002d129000800b420103103642c8d0031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 248125332 1250 248124082 248124103
    0x7030b0a1803050903061e130804050406030f020f01080705190c080a080f18120903160b0d06050117130f0b181204060905100203040902030a06050f0a080601060c0303020705 76
    0x20340700d40d1600040140350a00800400000035060740b0034458181d0021f296010740e02444d021510002d001c41441c050000c0c1c810f03540080e034080d0610300e01100340060310481d104c0042c07023161440080505a0010369105808030b40900108ac1c0600500ca64414511442528600313035182060a10f003855480e003080b070f08824204400207100004002e0200d81e43c0380115000009040804800f009088050381d41c4d0714103503840e221400000c00c1d0140291403c201826030f00c60502079040b5440e031a6040b4507031740d40106148040241c2802c0c00042d80754000c0b07004a19003c50948140c00ca0350b0b807015500d81e03640c2034590031103803011110609000300d04600031140c0034103801c1d44d030100220301e040421841c0813681020811448401c120400c41a5002601c1000721201903903408100300c00340f03030180e00b1070203560b12103809a8000802c00c0300181103a8071881c05c1c0e6000710790050210303410f0070074080c0300d4607580039000c0103901034001400b50030300a10000d1041482450054036254003070b50340d0b5041040b40303507 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 248126582 1250 248125332 248125337
    0x816030207060213050f040603050c0418021c0308181203040206070c0e01091a0907140403080a030213060e0904031d060c0a11010507032a120221090307030b0a1803 72
    0x1c03040c405c524211800500d840750454050000320704517100c141e121558403501c00d01c02c507a01c0c0071110b000016102c0503042950000e0401c0c04c4040e83e845404e003c400400f40450000d42001c0010b8103107a0540782c030920110b1018001c0141c00c41015183c52a50701c0034001780c0c0d00000038006e510000b00a0107519026101c2c0c0810b42400b5450a040b10080d01c03090031081e8000b40707103c41582a10b031a82481554080d140c0e1501100c0140f8084410540784120b420203442da060002d0710003411901030f0000c0c500300e01907042e000c0d101a80c41c10100c4084107046590365101a800c2c000c00e01091043c44000040c4801d161703400412500240000e107943d020701c4142e09507800c00c18803203062000c06400540c452000b070a00c540f0f0b11201e171f81c00400500030311604154109000b040c035104002c00c1082100e04035441900746101c1d441c00500a582c1d00d0a03040c02806080882c85691080105403064074100032025000303011070350440c0e0750145017039402083d140c0400d0340c0f80c4201e0101a5044400a2000e0194 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 248127832 1250 248126582 248126617
    0xc030f032001060312020102090d02041a1c0b0c040501020604261810080c07060504030c0f03171b0405040518150109230408031302041104061101050708160302070602 73
    0x500e02206140305c2c98450b84150b9105100c03607001910f69100488640c1da040b240000c485089201301e1902c0031002c041503401403601400000b0000d0380084c40e456060140c44045210b50300e4140d260114480e030f005060060300050b02090000741007414803c4040944118000035000c0c90000c1a51034101c5400a01c1100983d03040b0702c1c8a08204502d41c14215582ca420241c51070b0246048003e07100301c060080070700399252300140c107141c429880c8264080e8400058441f1340c1860800811aa0003034044807440840340c40841d403502c6040100690021081500c0b5080c94540800c00c401014001c028511907200381d103c102d28240140850700082c1c413126028039165060052400490b24030b11802c050025900340701c0e86207810f521440a910a911004295480d070703503c442c001c149006003000a401c68100b000106a14283d0b80252080d241195281301000c0c1e41e5420781802e030b40013903454501140e00d140210b0a400e2004a0184481c02c0301d042c058a000c1c003564400c81268440841031480c031204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 248129082 1250 248127832 248127839
    0xa03020310021201120f0308100902070b09060604090b0a09080909010801020a0f03020c07051e090c031602011413030903051510080102120a0f0e070e04110307030c030f03200106 78
    0x2055040c3d4058404070f21704003103c0b69940c1da04098400c100b00090144500c020014500000e40c200c10070242100c03460540d110042407500d0000800309564003181401000d00080c09800c00e4400c00d0203507030b0007101241c0241c41303240507240107010041094444007402c000c11985074503030f013a659008040e21000180d0319510098001c21045001d91a40105801007000c601402000260201a1041111101c4c610440c002d1000c240310b80c580d000c640c002e8074101c204a0001d160501540c0700d5055156038001804106204908079a1102105080b4003510008140085103401c240c0108500c80d050007007465449440d810b1030980003113801541800c400781007004411414210302c000303102e0700b00294144450301403000345112009080110b841d56070801c2041041d5140c0080e4040100001513501c1d040d1a10070543d4000003c44080d103207416075038100541c0e03090000e51241160782020420b410281503a44541c070400321240c040d01005085900d110700b040c02e224820218484100000641a25 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 248130332 1250 248129082 248129107
    0x50606011403010e010b03070306260606061608030903091e0102100e03090904020a0b07030806040b0a06082212020a0c06030b01020717010e1515040504110f0a0302031002 75
    0x54051110003107100c103200400c903c49045400030306403400013040c01d4803039139409030450003004503902c501800c5030040b00300c6861101d403460030048908148240c1d08140c2d140300c02c1c0f0000e842030042290203180100c0f01a0701080e030034800785410106110540e450103a106000441800003600c54814a50402c03903c070441d5a0104004c0144081405052103075143d40041c06490307005420b5845d0040c200c1d44009000c56032103010a80c003904034000059103c0b80326080003001038008a400500451070711000003a50b141182500c0100c519554880d0820f9840070001640c10100c000e091f100f1601852030040041d8520500301000c400d10760040c01703000601c0c240100b004545500c001c080c18607214010255903800b013015000e035000c41c0c810480a038070340740c1a80d0040c240803a04108500490b852161450b400000d203501602d86420b1001c40c0c2c1074180c2c1000101c9009980c0180000282d214800c074070700b0405034041351580020448500309590360003085c208154a0300010034668009a100d10300782 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 248131582 1250 248130332 248130347
    0x102072102010605031b090402010c02130b01030605030a0f12050f0f07203f0d1130090406060305180109050309010819090c0311010c1104020306180405060601 70
    0x44200e000340301e0700c64041e00703008401c0c00d845145401007008000040959001d10113540d4155806040b6180c81cdc1c100c0480e1200420616440e03a00090406200140074540041e03010046500801c003041c85030019075811409002d1101080107005007030045a10130b95103140580051a54140181d54480140c5030002e50050340c480e280c0292032085070f46801c9910f62420b2850701c0d4a036a5090340c00d4814001014803802c244c2c0c0700307a07002c0c4010b0000c1c2080e1300c44081075440710281141c0314030036088400b041c0581c544013400c1100310580d03000305110808040c503c003145101c1307041c03080241c81c16100d6004034061340c0c100c2d0010400b0030303100c00038021952090100e804007068054002c00014146503541ca442c0c0c80f508280c2410000c00030046141c242c136042582045507041a010000c039005450001e12005940c84241c41d0b074044412201802c0d40503040e00003070581d110714114444007104080000a40010b00082e8100b0301511401604c06485c143c3c00b40614001d00c02810940307494400100b064 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 248132832 1250 248131582 248131589
    0x120c0718060f1212030e011104080106060f0c0b060906010c020405040f03080c09010806040906060509011203180501020d030c0207090c11121603030507170c130b1905090301020721020106 82
    0x4144000043e001c609045104484400d09140202e150704016600034090036003507100c44a011400280040c01d500150701c0b1400312103454840003403100090209031100118208060680c0c803000b000603da900e041d0410990008050400303190304207294011504448003101d00312a003909c080701d038105050f04054550b500816620040e841c05150100080c00c04101501640c081c58032108100c0802405400281c050580a05100d180e907030754040401b1042c1024906a001c500d100d80005003540d2070345200c03002e40d001a001060211013902c412030003480c0300d000703076821801800c0c40410081141e000e01c04c1030810a544103080c410520040606000c0c0584144a00720000c00c10b48644000206440c10805d41508002a5a6440034800d07162450718140039000c0300450001c000040c55003034041c1c05483d01c224440c0c045107032280403120080c442c2c01c20088941403100d030001e840c1c82c41803000313200313080d0040c0c00903050822030340c1d4010306201d0440e820b1001006a00c1c2d2160700950920a40005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 248134082 1250 248132832 248132849
    0x30507090b0405012a0519140c0a050603061f0207030615030b070c08160b09010f060f121e063809181b0f030708120c0718060f 56
    0x100352411001074100581c0d1700680003030b10f00595507400c3c240611503684c1c10154000301503842d20700078104201e02c005980d5404460500c9036141c005041c05002a00341003204002d0032819801e41090200036143d04028130080c0e019030031700e2100aa136080740c03402e001480d1241e0010010f00b0308619084094400d820524103406080d90402c0000c62000d424194000d481828007001040b254100690b182c401c0080030900341e1390440340e9004001c01d03551058801d410400080103407a41ea46002000c0c0c0c0c209218401c440c01d0001e07003e00048001146401d102445500c0d0711100440c41c040c01c0c2000343c40700100303490981d6900300c0e405001000d0418294206071141c09460014940d0044c074800105117900139001780350107400910072642c005003403c8100c41c503004482d48100ac2092801c0c0e0403100c03541c2e160059442803c5c43c0c00e1803e00296410035540380070050140401407501c90300d10b07500016281c1740288500b140016070403000212203510200b2001000c6241d030700300102540803100303e40c001000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 248135332 1250 248134082 248134087
    0x90e040b0109180804060c030306050d0c06030e070816060215190b1507060e070501030e0307080d0603020603250f1706030304180501150c03020a06050601051306030507090b 76
    0x3034060340a590658800090000302890091244a90050b0036003006044080018002c5102a000482d11600a1203a90b0502050303445100780508443da00d80010030f501c9070081d00380003250098000c803401e00040c10445602c1542e0b0750b1014603101152498008100005000713206250f41400307004060790300300c21482841e06011404200c0c0c1d8a04a1400c08115030300c5403000910b40d56900d00140700a0032003182e0b5100e80050522070001c12400c1d403100c1c07142c458648000b031313594040d0203403000c80c030a80030140d4104011511184459400400c10085a80d9220400300040c3e484101450059650031982c003050048002c0d0729103118114a1400d00380113030706960010031544429a51841070280c5248031b00e50b141c00340440e2640c0507540142c00c100e1040700d0f0380c58403c00c26502043c129003c600141d2210908020107a403800301074440a00140c00418001d80410340c0c80d04000d030810010302d403a07450f10210b03c0c40315005c00056000320f00040e480b142404185540300f106103001e0482203103c2072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 248136582 1250 248135332 248135341
    0x60a0509071809060501080102031e1e0a0b060403150f27110306090309030106090501030201050304080310080303070801060f090b0a1206031202070501080f04020609090402060903010f0507090e 85
    0x1969690079100781c6940244406144040c2c1c4000d07040b02c039995600c00720030302003546c4803441c141c00b0f90021900343d0040442401d091851502c003004141c01209000206440c074420358648056000b03004010415682c1c0f1012880500c2c2c0ba401c008000450150400e01c0a200101c07403104c0a8400c030840020b1840d050004d1000c40d1441c030707003103e0342020b00101201020708081c42c1500700c2009a00310141e1501404c000c028101e0300c048000c0c0001e407000c40007040183d8640413404110b5100b030202038000740c0d0074000a00000c032080700440c2c201403160100b2503801d5440810741c0c51641b040f1000c000080107d0010440d0395042000d285280806041081c5518140080320402d4002d800c101001c010f00c490026100d080180d014402031070f082042040103581315480a561541c041c882c0070300290442c000141050008000300e40500c1e40107024a24110100042040c2000041c0c8242d0740314504000181159600748120351005d0b800c020080348130700d8282c001515000b11507104102d4540e0980400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 248137832 1250 248136582 248136601
    0x105030309040914010507020f0d1701030f02060d020301060e0a0e042d080403080c0c0d030c0b04240f0f0b06070615050607030806130204051f1e03020301030203060a05 74
    0x5400e403050556000495010380c1c20013a05060701c900c26030455501c1c0c0010311006a07404200340c0d91480340721040b180d0305010280c0c121100b0703814810325180c0c1c403000d00c01400055690700c001401c442c002003082d42040801000364040343d1080e4006030210340211040035140c1001107024000300902c401040d010302e050b80760945c3c4120380c4408900100b00d0b00c11611040305000e012180340a07003101c40a0b49803600c0c1d00d80600c180d03000540740c5140b4803a0004e00c0050345401500d1402c901e500d680e82e080f094075180e441c440ca18401a0003218082c00364409010300f001504802154014681c0010803603d407031f10103a20444210888041340300781010b035884e915840f0041102ca010368040c0d800129660008100d1100f9181600410380c0140001441c1083c107900c8a143e90080408035000700410700844001c030124491440f5641d080308018180d92525455061004c0e400215420011030802c001084100819480303002c250110382e01200500650400b00001540400310103010003450500c80c10b47c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 248139082 1250 248137832 248137837
    0x5030f031506070f0b0c0f041d18030a110c040f0c03050702070f0e060d02030105090601090c18090b0f040623090c040e070c0b160e0306220204061a0304170301050303 73
    0x24100040c550041010107040c0300881303250103410300a00e0b07100c80d03e41410350030100141d034900d09c03040084404148484501e410100d00881d405004510b0490304142c1500d040c80c0780015809180900d55540d411516140590030045982e00c1d800101c82501080250403107002078011011076020715000d00440c1d0000704120305841e035150711940b00340e8803200050202e0f0000702c0000d40550804052003080131000410300e050fa508120207201c0a00400030480d00b2007a414800500007070300480410040011b0b0703200706011103018161101d200e41c0d0030042804d0350503680c0113244168010070400c044841e403402007049400100e4035004a400c1c0093c1032a03a40c00b4074020700342261220404110740c0c0380501c1c00d008100341c0c4403d0f00a201c0c41c28550700c540e140000910000414844d10f04000540340101342e452141c1c4503a4424441f84103450b1181d24800d00b251030407604955548400704030f000c2440642c4001d86060401240e99203400e180c01100184a088503014400c0240b00500440c0e03008002d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 248140332 1250 248139082 248139113
    0x30608071a0c0114060a09110a030504030c0506191a0607020f13090c15020c01021b1c06020903010b01050f030604180f050a0303320a02040305030f03150607 69
    0x6400079000095000c554030988103041159072034007042400c0200030324030035071045104840609246590b0780b4008140c5d1100260840300e40d000304911210a03000f40e10003504a4064689002c6c41005660340b680b40010649a0301c03212a1000307280e1041000a0051101c81d001f00c0c0304181030700850901140704c1d4090003034005e115459610888c01e054840b0b0072844070342440a80c00303011300e1066080c055406e041c01c1c050541104904101780d44118000540c001d00420706038001c0130fa07030f0b030070100d029845c080224456034030002040216203c120034082200341d0501580e0016960401d280405003110101000c4606001d001c0c09003c100c0318040d401da0354461804c1d500407619140d404000708a0b51116a0014000c607a000304400a0020000d007201c3c0b441d2290b1802c00200c8118003e035540c8201c02c0b004000e600301e0600310816890400c40000da000340f15607902500b032544070795600b800d40c0c105a0054200b0f00000c820800e000405503000783c491041526290b00c0d0074040c2c2c503400c2c0e002d0000d41d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 248141582 1250 248140332 248140349
    0x606040b090a020a0302190e090f060d12120e0609060f040317060d021f02010506060f0a0e1306061d09070906030b01020f0f010207022407020108100e0c0a02060703060807 75
    0x114100510300a4044403e403d8802480b0101c000038000094201c3e00b91f004040e003d0700c0342c54000307400d41c1600d02152f0300840d0018030640140c811a91030060039100400e0003020031803101000e001c00d00303840c002d40d5010904880030305194640072604500d4568014001d00b80406d03481c0600000c03d0300320021030102c2840446c004440d590310404039081071002800203400407a1900e0300144407561300c0000c004a80c25a00a000383e4640804100c460b02070950071143d82201000f0351801c10b8007604801000402c040c008020360804111000c00700c07013060b800080454588403401800302c0301d59400061034034040b5007120741c03402e05810040c040c40c402e0140ba400d0641d51004001185e0007013105d215581c00a0003140e419000f01841e0038041e4020000c12401030f20006071b064115456000300c01118120b0b16100380c10710009070011121809c01034049044200384640120312a00700c5e900c040d22032802c00450a5030346891000080c44d00310000e01c4d1004051820405104202e00032501100325060301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 248142832 1250 248141582 248141587
    0x301050c16030c081303050f060702190303091b181802040c18180b030307080a0c0c0305030a0c1109040215030702031c0c031104150c0c03050a050a050606040b090a02 73
    0xe207420345100d101248080c20075103001c1a02c0900203e02038600c01940e07c900c0c143c075610895410001e540712001d5801c0005608510100c0c0312280007182c0200c03140707000e482c0101d0b84d403500d92030300d40c000c400c030b84240540c01600f29000e009140340348400b41d058007040c40b010403420b815490f070707034a24405803c0300070b00c071b0313a1200c2540621503c06c1c409103031007002114007401c6082c1d4500c4549102604980705110480c00c00c90240d1151601006598146030003080880c64034034162411210100e040701e007100c001071040d41c04008282c00700093b1915607010b8a9005201c0207505180440380701d00324002d44195240030811005803560284114400c8400d682c85841e601d4050007a400c50040a1441050301541e442000074140960000031720824951000c00c44910b0709602c1d40741c144200d0068101d07620500000da403029105241100e01b8034019800004501d441e035880780d003081003070082030f9059800030035840e090120612034140c0005e0101c40404c019140500418841d00f80105840c2107a0f601 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 248144082 1250 248142832 248142877
    0x8010e0c060f0d090c1d040302010605010504061e0915030606020c0f100c0819031a04060b030f0c09060f120c0a090e0406060f08030a03060902040e0406020703120203070c110301050c 80
    0x5c0d144080c080c0441101c074104560402e0f00c4080200b804a030268015803c141001405500440c11241030f0f80380d41c0c0e2140d0050007194080c441c002c4000207d4401c1140304c5200084103002020709820941d00340d0747c00704000d45001e0000f850143c1c2c1101c1e03140700d1908644248a19611001e00d00c103400360508029074480030342d0822a01c2d50280e4600c10f192541c0c206001100d645e815400303200030b41a0345801001605030242884101e403807a00940a0041c01040450705054010100030761000000c00d00915290458020404541003100d0815170000301003520000c0020b84400d43d60700080702217440d81401d4101d88020010b020900c01c0c040c1181e502d40210382030144680190f409000b20024003244150b8a01d001c036940c0c0e1064040400203807400d4008a182e44040c002c0346e08981440c00b100016460340e4541c04004c0d80218401c50a1001d040c003441111109800514401d40598403904018074960902803001039140140070311a91522041102c1c9603260810340d0034011a480604c50052072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 248145332 1250 248144082 248144093
    0x1081f1a060c07050310050f01120804030c0608090f0f0706030218030105070905090c03040308041104230106031413110a180209011b0c09020a05090a08010e0c060f0d09 74
    0x3940c20050303400450016a40c0611440020188104c900980845051a0520040e141100c0302502c00310180d8141c10700410925408485c81540240101c800a04e410760320765411000b26203540c4444007181d141c1c020401a55410300c640c0e0107480c0c071440503020004072406a141c03602054010001855404500100b94411040309d0f12200240a002000300f0f080c52034020f0580c0ca09881170903c5852000e000a0308014444280d81c0034503850b440e00c0300c242e00d80740c0d40e00d041d039850114401d401c107945150a0f030f511885520038080310030f041c100002a0354140f4400405544090100418520a603800c1c05401e29031125a52170460300081e01d0103c01c001075000900b10f946c2e541c454420b0104e000d0041c1031030607143c0e000300782d03405003601c40010703105038151002c03100d0b41e40d903c01422032401000308000015032500288820100d916001e85000194000900310399699080100c050799202102464100b0400860b41c062030105d40d1b083c02c01c081013500c03040c0d80c4141810ba80301d154644040104215 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 248146582 1250 248145332 248145371
    0x80d0c0b18010204080a120c0515150d120e06040605120a02160503220501020c0d03030e0f0a0507140901060e0102121803010605040e0a0206090312070c03050601081f 73
    0x2821038000f5942c580c0c5da44410340d5161080c060030b50b07480d1000e080b2880d07070f00d01502221440c1507106003c0c104840841900d101c40e0b10340204110354145160300e0300d488699848551880040c40b5000c2e9000b8480358510081140c807050032414000c1d1000c1005114003600719007500c0d03804001c444004d01540d21040200c1c0603005030405111200f4003030203003a041080c0880541450820701c02c7c01c040814190342c007441c12510034450b181c00b5800c000e20044d21400c1c030b40144d00050340039050108041c440006002e14000040d01c00520f0b942107034601e14104142440320302c00410381c28040503c0300c90003000003610b2400c18406c45040c0212110b102202e83d000384500c06504504824803911400303080c1400e09403c802201c0c91744694031b4184082501e28140c0b00f0a0300d0502c0d84001411200e0666090101550001c071041da0b01d4400c08140500507030350903004195041c82580c40200c10751031494002c3c170b41035040e00841c000b40c00101c40e031090700080c0c21403005210b010f0040414203102d1a2903000914 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 248147832 1250 248146582 248146621
    0x506091905060a15080f0c07031403040609080408150903090f120a0501050f01031407180e030714030702100801050603190b030d0306083a02100203040b0402010306080d0c0b 76
    0x403844804d0211096003010743c0b144201a144000e4038680d0340c0074006203503480340401c020081001c3c01c0700c41030792271143d01c0903540c0315103e200c00240508258561050302d030080c0e4414090ba90040350071282c400a0230003900e4106d29240011403c011340500000c028007916003401d0f000308209030001e8000030b010801000700c00c0e0414020043e07802c000d00c000c9401e04090005a4102e02d070b1080c1076106810005000b01180e441240b41810346500d10381c0c1d00003070207001c80d954015110070722450001c10340780d014805948005100955a42d1103600c1440844038041c0c09240511240800410054032104102ca5001d00310303000c907400d440f940a181000030300b510000c450b018490f81104c0080590154400f00544001e941102e417440100310030341400c21244091000104400b46180f02d20303100000710310303010f0040703030054400c0012024851342c2281c0041303074240c2d0369800450604c01035503014030408020b005444060300c155100349001904a03613030a04020840c640c0030700011f2004001280003080c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 248149082 1250 248147832 248147849
    0x315030c142b12051c020307021212150607110607020604270f021303080a0e0907080610050304050c010e040e0f03180409030f0e0a05220506091905060a 67
    0x1280280003840c182c0403201c4804941d00d000b500501d251080c0180260307440001011440040d41045101e844042d42014081c0402d510071116680840110400641039a82242192511038030308017456401c003d03110401c01d8041c210400c02d11000c038061810030220101c0c2aa0300b43d076a959584041121442180d006e1210046104188545494104002040385a46c09012322485541071380d107100720301c16183c0301000302d808600700f00f000400d403601901d03038100c0d507042560901c8565070104201c424100c54103800140c250303040016614100c480c4103585825441e10340c0c21031a20781c1e503807640d44105c0042c0b20306000303103140c1c80880303940c46401420340854200d055501e40304500c156503a507500b10f9084284c01c4000d420030721042d42070510031100c82581640c2d0311100b80c00004000d4030360440400c241a081035084002107050b860303218503808044d1480c00440d040c0da5807618420121180a4032852003801c000f414000fa00419455806d00c6040380e5800003900d450300310002c1d0f0618000d074425043c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 248150332 1250 248149082 248149129
    0x501030506060906010206070903020f042003010f080705060f0c0c030706020c0a091a06032a0409051b0f0a050403060c0203032505190c020d050309010315030c14 71
    0x42000201e295401890241c800b5900c81d10f4140c0107907200c0302c04440900000d0b2030403004001514100c5050405200c0241c0001600481442c04c1d521241240c0180c14140c180000100000800c14160700000c00210340030700b9580781440006000b038458046584140c0001090038205590f0038001048808401000c488526030f5904d400394480306ca5903980e40c1f151120030000038401c90030740640011210700c10014140d440d0360f8010030074180c0004c4e0540031600b848500542c0202c80200e00d1440d80c4105005113602d86141400d200d041e07680007803c400d4104181194490a00c25420681d0321a5181c0c031480b5031681000e80342118140116070029001c203041c066070b21070711034001c4021405403c00702045800c0d0a001c0700c2c2d405540c5202c5601d40e000507410001039154080b1501c590480d2481da28091558901540001d503490120b41410f4480340c0001804000ca0b60709845030304045910085c00342c00182c510303115581c48911a01c244200e64001100f440166614044000f00703d001410740b440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 248151582 1250 248150332 248150339
    0x3070c020f040e070f0b040e070c05031201030b012c040201120b19050301050702070b1c1e0e10110d05060301061e08060601080906040f0311030a0206090724050a120501 74
    0x903604d000c2032041549044110f04080786483c606400c80d820b580100c0134045043c1ca03505001c41e1b4414000b40c0640b024001071040c00b221559460b10540214007421000d811941041010303004452404000c16072001c401051a850149044070241c0c41502400c007000a2102203e94030007400c021740909500c07115480006a008180d00248020b9403800e4000b001a6031300e500b41aa620000f500419451520902001017480009142448840320034030340810001c01d0081000c0034010805880000030b9101c0c0e08a09002004124480c442d1440e498148420a044c444d503141612500782c9440c01d032074031760340000d210343c0342508200001c0c280b50554030812001d415141c400c1068500640b803a41c003811000c03403a603603c40d01105002e500d400c0050580360720750303684022142c2e080c000220207101c3c070600e0b4480b603040c1c00e002508110542d50050030181c90304036200e40c1005400d0f0885045003d85800c41d8644004070308144121a6141c1401650b0304845001a19500c2c07490021200c118109030004c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 248152832 1250 248151582 248151611
    0xb0a030501090b03010203060321120114010f02010c05121f0f060915050d020306010e0337051c0318080702010305061e0d0f021206040201080901090803070c020f04 72
    0x381255500341e001c01003003a0f901c0c209400d034481541e001380d00d50310894006c0c02440d002410f001d035002030201c40600d40001d18200c0008440c00340d00110001c60081100c5544d0750b0000001d5580003650b2000f0000c582940001a205004000c41c01c4010071140e40010102e45c003819400211490b102700b42505281e4a4581851213a6180259000121091000a08641010070000720355103982c80c0c1c1402c000d242440c3d0b000030340004000904220000c2d156800e15201404040c0c01d18031100c8c2c0d200c070800d112010806502074100c1343c102c0034034038412007640840e20210307020000f08600d01d0303424104000c60000314040c0285090242d03000d0940040740c000c10004200800c0840e1003a20140020368900c003c0000d031018400710449030070f0000101ca041031504140c00b0540d9845050103202501c12500426000400001c8100460b070181041c40207541c2c0001e00c4543c0440e11100a20111141d41c3d00c18440380006441c05050240c1d080c0d100c800c41d0b40f41c40d040003541e400600b0420400c448002c54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 248154082 1250 248152832 248152841
    0x6010803031f050a1205010f061e080615060a1e081b1e0c01061e06031103041a220b060a050a030302060103110402040503030a170c0a0215100b0a03 65
    0x51034200e2507190112000b82071808440c0c000c941c0d00a0200700d90780e00e00f2a07810b42c80f0560980c111225542c03440d2201a40340c0c1845410041d101140203800101400c0d4090008400310303800002455214004000c4c050300d0113483c01192100643d11251240000d90099898481000318441702c560b030700022490f0130b9805442984143c0003510390312440c91030100c55100c0ca1190f14240d40c0c3c443c50090310340505003d09402041e07800b9039a030000174211758850b4981c0c044581e942c9580c0e420300040c0d10400500c0d82c14024107820040c0d20007031514505041d5288230380102c0740e22400c00c040c044400010b09502c10440819110811101140b03100601403410000f020380031581ca9209032070540300802d041c01c00c41090815681c1c140c00030801642107898110103040700800203584583c0811000c201ea45050018004031041d03611945440c80440c41c1c041c0c0c075088010481d0032454424414210782581c0020302c103600d00200f4000c4061504d0300c00d108490201c503600300000581c000516034500b04c4d4982d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 248155332 1250 248154082 248154091
    0x30304060c0b0a0c0509092a070203060105042a091505030a0516021b0d0606030c030b0615040506030a27020909060702150a020403150f050a062102010905030601080303 74
    0x400001d540c0c0c800c800e03e8201e4901220801c0001c0c0d081c49400d815040405020f82c000440017600e281054800080307100f107000c20785103030070f00000120729642141020814103000d401e041360140110300e0070f101000e0080c03d241c900300490f1407000813061121401103007660090310001070b200d0b8494000c5000a0b1241d0b01c199030003071455140c500000d101002201d4481d1700001c05034081c002710440a0fa02c07203103c0c04a9240e00da801010311702c0c2580060030313070701c03c07100210300c6140524001460345c10004404035000381058020350303031003c0c414107020702d03201102d0684004455198413a00d55000d01c500400201d8102103014600e0005241c0390490410118001482211018030319503a841c506a250b40f400c0d696480580d016900b00c20100020300100e59020000b030b01c0050615580303407a03444041c11902103040c50155035124801c90f111350780c09041d900407020710301030203418507090b551119502c124041d00d82c10001c074407402c803c6a2140c07801000612006003100c0e01e550b1034a80b40354683e0f2054030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 248156582 1250 248155332 248155343
    0xa030b21150603101a03030c060106120203010803041a07020904060b041119034205030a030c02060a12050408030708060d050a0312020c03030910060b0c07140f030304060c 75
    0x1560880d8846944071288540300240250000c9034144403058003a105090307070003040c4020b10001503410f850802c06000c1b981101d10050540354500034000e49660312269001422600400061011602c0001160200c4004980d8180205800c0840c0c099901407010001e501c1905d18040c40288041c5810458101c2d0741281c00304140d42000f59007901d01e00c46c8100b42c142000e10a0210103145001c0d502022030008800304bc40c842d00d0206a501b0240e50500301c03011a401a600c00540000e814050303600d001d450141c008000180094402810340c070a4007000921402000070a24000c92142096a521042c02c4809000d10b08007403a00030003540003110004006940702001400d10301d00804441740c855001009800c0c03401040e201150b400312010008020141c0030401004182c1c41080103620526400b4040d01200c510a003900b000d503610b903071003065045e90034031011280000104031003044400c02a080051404801c021403880420341540310361600020038005030079500200c0ca880c0382803040307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 248157832 1250 248156582 248156593
    0x14090d0c030c050a1a03040201170708010801061403060f060102011104080307020301141306020a0c23070501020d201002030c0a11121207020708070f0509012301050a030b21 76
    0x52091190340601c51003410002c5c07000100007007408605000030b54001d0f00600d80508504100000070803c020180d031b04400144564004001074002031154002915038000c03030320203203120b40c4000307642c13520040c040030300605000011a00130f078001d501003c0392485400b00c0d161034075075440c6003076100d42160f00c05074081e500305003103e802e100d0500d04103031041c0c034004280b0740707129120345520000b13410004083c018030131840d81e0b400200301c05400003020700c100f0f403520f004c204034580200790604603d948054103640c0310701c0c00760343ca458005103516611001e50100e40c203000c90004240d40703032001540302c40c41403074800000d02020021035401400414826164030209a2070040101e0303a844180c0408503113807602307011912941d0520042283c200b04c8a1044444c9540c45503001402e0160030790001100c611703400710801c6682041070303019004181c0e003200c0c94980e403115440011301e50034696010f41002400241c0108640c02a480410b4510b00030f01200012640c41d0031000358612030807d0f402c0c0d10b2085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 248159082 1250 248157832 248157839
    0x30507060203101802130f0515030a0b18041412091e0a06020705030601120f11061207091403190201050f07080301080606150a02120c0f0a050d08090a0b040314090d0c030c 75
    0x11f0101035001c888026004040c0c0d06d000604506c41500003500c2c07040000d40706d41b214009940d03400c0d2400d060302c2005402888500702842c100802280103214040c1542015541d01d001180700001d41d8800701003a102c2105086058107009000310005100039031100c0300785000f0501d55400903446081d1482034003252403030b07600c0c0c1030350350350000000718020b1003c000c141c11500042ca9041d4007034188400030340014103200302c0040c80561010125030040c001040f00c2d004100031512188030618540098000e803802c40301c1018100010000c00c00043e040c00740008038841001004000c03211001d81051009440396141c2d0211929042c0a90b0080c4c858404003501c0380035516080112041802d00c3c0c3c0052014040048907282d032500960400080c1e8000c28011820b4414140118041d0b90310030300103031842c0200c00d003020340301324006009004075500100b800780005248140490700141c1504010711083e03104c6540010604c25001603a811400440c1420204a0a40d80d0f4100f42c1c2d1041d020214816203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 248160332 1250 248159082 248159099
    0x5131203020c16290d02160203030c16060903020a05120316052401181e02040308091302031308070507170a06110a020d0e0d0f20040203010303050706020310180213 72
    0xd0820b00501621001c120303801c40c070400c0f0360091489200310a6411041f03c066000203040d50014840140c0c3ea401c02c0c1c550f80d040034451105000030348070030304041302c0280c01c5802240308102c00c1d009039401440d000b841c0703c000c9602001a15505100d8000d022418100c82c503107203460340f07040903800e41c00ca0440308501c1006c0b0419030401c2d06071440950400300090f10389d61014040c08004a51666200c00100410454641400240301031030090f56440d0f40e5200003000e000c2c110400c8031201200510520a000d80f84911401d01ca003183e40000029807a5011810068205072050b0f200091550343e25400c3d611601010806041980c0501000c01c81c196005012502502c10020f002c0300581021700341204d480e0180300c140c3e00082c8003512400d40b9400650350400c1d03000b2400300580e4031204a0810301035541e200d840209140c1000d950039401d6500d1a80c0151450003a000b00401d0b140e00070002401399089800100010301c00940d1403058010304805060081d171013010000095841303e00042382d840c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 248161582 1250 248160332 248160389
    0xd0f380d03050a0e15270609090c0a11030a09060f1d24040902190201020a0909020f0705010c030509010617060604091e050312060405131203020c16 65
    0x54041d00d5092a007029a101203525041511046502404201340c43c45140071300c802800303e80a00c4407406c1041a80e5000000d040e00c400401c0078440e0304200030b545000d0315008003854201c0c0f80704000c140c13912000c3c00d0076183c9000c1c0f50409003091001048414103035610046d04e1080300d580c0d807960900641032000407207100d080c0c0d4001041d46150240808210b041080d45038240b003411010b044910040782c01a00403076402540611045900407400d110581d41d00800814100610f000840c5441c4010902422100d86440740e000c80b00d0340861440d4040c4c00e50b904603081940d0102c008c220310328001d500600142000c1d00c4401e503561030190003281d05140c0149000c220110315004007002d680c0c40007040701038000000200c5160f0030207c0a010030304039001c00309446d01d00c18409584c94807541c21500c05444001840d5520480c1044103100922800d040c2201c00907030450900919200128801d4000e489540c226040038071420100c014040c160801010641d00e01724070380c501021103540c90004c1c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 248162832 1250 248161582 248161609
    0x402040b0f0d15021308160506130b03070e04091a060307030818010c051b03100216020f06090d030306140d170309070b030405061006090b0d0f38 64
    0x802240709401240d411081225940300043c03015180481c44070035030a945030554080c014961010600492011100f040c8801405040d5445410030310313410f1880e82c0c00d420910880c81c03030b080000040381c910b9100317030b044840313484003d40180020b02c500d24004410700c85400ca241d1a2080010105800d8500860342e6000c598000000508044860a4521407812450240c0b410f01843c50100800a1814403648440400f514503605580d00c07290b082c1402c24600c450030b14a907520403c0f0b007804548840e040b101111f501a229600c003c070100e0046840d920581030240d0340b051044c0243c0040551503008001619801400c0d40106190b0f41c05110344a80d0021004081c95249201c88a024440b071000c1c1d9803107492981110701d0a96100c00b410244d61055800391555000001008007801c4142c0d2410002c00040c0f4010203480c2c81d042c050750325405544410007400740c0729298090903e607160410300380b01c42101c030707041700c40c08280c040070a000c03a814042c003900006c00c03011110940b8040032140101c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 248164082 1250 248162832 248162839
    0x4091a0108030c031e0403020d0b0f07090302010903140a0803090106031a01030c030f0c0b03070c060c020a08090d080c060703090201080106260403020a05100e1b030a0602030709090f02030402040b0f 87
    0xf40808000c1d8164809165885c1e9509901d0030b00000001d66181c036040c0392101d0003800c060050381401440000892401001035050050302c000c2040142d03804000841140c2e0031440c00d82420038049603090401ca003154002e8100308020080c060166010351044085030700c07075207981c8542d034088002000402c1c024480909440451101000410320044880c601c8600c6184101c003050348034a90800e090300141c5983c00040c201c41c50403001c205040c07003001d08824050004210101c000d55036154207225030f24034940650303c1c03100400c041021100c1502d01209844c030980c6d440b450131080040003440482004c0c0e002641a000001d0801d0156140d0700d99110690700100c0341c29840141000c0280018000320111303c02c90400a002c00c2040c0427942a29640003008111007211549240c1b40c5150513031960a40003010800120b50350b000215030b41c072141d0012000d030700ca503600703031003036030003038003d81c0100c00203418224920782d90f4440754010b40c401d900c2114200b02d02130b00d5001f4018000760100d0302580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 248165332 1250 248164082 248164087
    0x3050709021e070c0e0f0412200111030402091b1801090503060403031d01290a0503070e090d030207020d0209041511040503120721050904091a0108030c03 68
    0x41160030780040030500b010680400056228a8800d00740342c0c0030480564101e039211506114503240400c1040d0454800b84801c515801c042d141c01c0505000020754206215005020005c880d401a4888071400a40c2008119284048603076240d41ea004031412440b1b040060b0000709201032003a0300d4600402e042d0f00041c10408c001c0d4520b00603180c01224036042c8600a0300001c1e42d9542040b080e84158865a000324a06420b400b80380310442c0304005441c10303030f418500d800c0071448d840e0508140c110765403000c0310b419461401c08280100d1064104035014003410030041481c0040c950410b01600038202240c07200511080214100c0c011120300940c88209059981c01601e00000c0044d0000e019000781d00b441c00d1401c081e84100c6440c047c43d07641078900800e08020300e00d400c4c8a02c0d6502d000c00b00c0303650300e482126600c01ca8030280000403d03440100403040c00043e1440f5105492001078050001c0022900a0400366541c038946c018a01c500c481201c00451800ca0102c02e0304c40341c0c1d4103c0015070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 248166582 1250 248165332 248165339
    0x6010c0c06120f18140d0203071b05030604050604120905010e09041a010807030501051e160c02060d0506030c2e020c030d030c080705070203060402120114010312090f030507 76
    0x1100b0418000c02c01c002d1680703482d1211011a058800c00e10305403c10031040700c0c18222480c1190f2084038103807000c1103c2e04643d0b880f01c280c0b9008011500019030002050359407108640c0d0003c2810065004550580305881c1000200440001c096000d02d0090549481180c1c0b8000206d50615071801040c0c0040c030007160700e81e0142404502203810920500701810540312100802e100600242e02c8018603901c104020004d1080c02c1c07162a4001000c041428107540c40c0c03001c180304811014010001c40b80c4018201a40c981c0f0a05502001c668014800e65403512201a0000517001c140c03002e178070038000c02410180515164542e10506039000c1060380300000e5000c440c0c228611441941010360180e864601c06a540900c40081d05d8542c5840015a2601c0114014005070004081d21f090001c00c1200300096035000030a1548140e04645942d03580e4001c804003809060b00d0030051a11204840002c010031280601c07020030102c4556810700d0a03607444150703000140c80b030300c0b001c1c2803a084080c060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 248167832 1250 248166582 248166587
    0x3091503070e0405070207050a0602030915091c06140702010c0c02040f090b0109200a020304120309052218080702040908041806080c01030e030d050a180303050108010506010c0c06 79
    0x45034801981d00b00751842440803404501640d2080381c0881c01a044a4014461840c0c800d29041c0500400d02c000c5081400010205284010107540958900400f08801000d90b846443c1c2c41d0310b100210414080007101d42c030700701c8040c0c40c004400107609400f00380008c501d54414440c2c2840d0011070750310318403407c0158090000078846103074000c0b10152152921008111020344042c02800c0000c00028020b41a0120028409119a062162071010445811041c0e400015501a07655002d9215495101ca180607200b070040fa5201c56048042030084c03007a5840b0001142c0c0780c1995250003401610f042d443c5504010b0746a03400201000c009001c0703d000f601706680840305161007079003400d04d0726444a9101800c4004001c00c2134a0f0f50703d030340c400d003d540ba060141d030024140c2030800f400500607003100c468903070041e55088082550354100280c0741c00300c5a00504c9001d0302d1314098000743c424034203004010707010034085c0044940c200b01c0450491751040e51002850b5401040c01d4040e0f5007484400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 248169082 1250 248167832 248167837
    0x50901030b060a020c0d020310110715061d10090603080c0c040c050d0b03070504110309010b061612030609020c0d02070b0c1f1e0507120c08160323060a08030915 71
    0x20782e058842d0004001200c84244140041c10ac0c0440324181c42d076510f807421aa0080418050707001c40d6081c00401c1001075550a20103010f04000302880c00c10755a0039064144800e182d82c014010141130040000a000c07150000702030408a90b01aa102c1300700090a01c81500e11291050001410400c00d804100900c1d90081d031030064002c3c10365103581c2e03032440060280c44640244112020000050000d109001d110341e4030100380580c0d480d41040c80d00150031020008140001d44284011640c14107954420f0b442075001c3d01c02210212f480384030307440500344c3c0d400c40111200d016200c1c0340c801146003162402500c12601300c100c01448600540700c0d1040c103218007090b9042c100e640f180d84880905030200c1030005030001503003000500d40382010000300710b0000710311170340150b5191650003481c490b0700a820641c80ba200f004400900103010404078010600da000c82c8071018402c50034100e840c9440c0e0b071400d028140407101d24000e41d444a41446e2a48101203070703c0e41c403140e54001d4807107840bd060003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 248170332 1250 248169082 248169109
    0x6190e0124170a030c060c0c050a03080106091202060403022407151a031513050105181204180504020103111c0507050c0c061612050901030b060a020c 66
    0x450003151003920784280e100c1c001c08540c5064a402030034820718010003a40c6071a0515100244503051450324041d03d075945d40400a000c09403201418030402e030152800811195201c011504c010070f4030309000348950401c1c0907040001d401c43c2c0300003450381d8024900208040d001800c8520341484c6d58200051103070280e10940a56882c004040100741004016202842c000c250b000c0510040c640703048126071a1710883d00c04284000c03114039503520f000443c0c0c5a5800792825840840c0c5901141d03400e03119008500074220740c01c001c20084049070101c10803502141d240c04039222038440489088060055003e0121011040600c2300c01525042d003150b6040740c01814006050071214110b00c155a211460503031804040000c00d40f00b12850b846120782c000100d1404034204184c81d004241c4a60344441440d00c5036a0200341e40e05a64045001d511250f0340c010307141400360103044405491504803211175400320349411039000103810321074122507002c01d290380070300380c400d05040400c02004041e24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 248171582 1250 248170332 248170361
    0x30e041d0d110705310209120307110603040b0c0a0302040b0f0a140306031209041410030c05030a080d180629032e0e1e010c020619 58
    0x62091103120041c081e580c4004a20740d1a00816400340b0119494040680e000301d004400c28001407080010030181981c0310800341541c40701c544903010300c410180c002c203041181e000c2c021038048d40c045a030000041140c14418600c000b43c86061070200215400101e4000d8440241c079030000300700b01800d100601c0c0f180c820741001400c25031240003001c45a0000004030814040000d1102140c68000c021038070008a0024814990728000000ca504c41140c03042c49078410380c3c0402d94090302e0365942c001c070202d80304444850706140703030002ca440a441d6040c0f10503079401d8200034000c100c0c1e041c040f45203080c1c507802c41c140c42c0c03038103401845100040078000240740d400b00100380001c1c0040c41a0280c0510b4191448544050310506c9401d000f5000725080203a21035803080d441036407080745001001d0030b002004403410304503400c070360031040160200e0140850709009070b5424034a01d01c1e40c0140303c84c1c0c44072040001c010001c0d005c002642d0302c45043c3d58075800406007181d40304503010030382c02c00e01c942c0c0c10700b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 248172832 1250 248171582 248171621
    0x9030b0c0c0322030b010902030103150516030209040212040b0f070f020a02090c07050d050a11011404080702130608070e0711070b030c04091d01180c0b091f030e1009030e04 76
    0xd41707070b1501e03181086c0c000200700d903000401003040c080895034400c11036802210810803410280303103416a0a051031646404c3c19004115aaa655699419034945a2a00903400b100c0e103090b10340000055401c403802080201000b001c1011248107191f0b000303045902d0780040090951075000c01441490007072006227160000c0086134001102403102003130000f2a5212075407101e03d69203001d4080741c20a44600c00c03581c54013810620034460720341120340040d0081d080c0c0c0e83d58001400131038070300c203a000300e8280c00c6400c0c40c2c1c0000d030030800099001d080701e03000d00c0d82c41d105855001c001c41b114070900d40e640590740d02c122010b0107054058030081d90405043c80000d4a8295141100d01c192034044240c8020319801c040d1004000c0b10a0107580c0009207114655000c6d00302545d560341a200007030058015a2401080d5101e40307454150030070b8194000600c0141c0c02c05801a402000780c608180301201d02e01070310f00038407a1100703103002d450006589900c9c0d100e4601c88002c184030042841554003104404407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 248174082 1250 248172832 248172839
    0x40816020402071523010b03070216080a060605060f0d0506040b1e1003020a1b06020f0f0d14070e090402030c0a031407080303010612020901030e010c09030b0c0c0322 73
    0x701d2000380314040c480e0403450a00d501d0000b584048548486090700580c91014210074160000c01700503064a0f06c86005507200e44980404034038002ca48241d010389408480c0307010400180028420021510920062001c141c90324180007160242c240300c411101d209216241c12190541c000303941c801e2014200003008055000010218201e140c400c0d406a907640030b8604007420222850050f107002414150310340b0402050050200000c0c00c0025800600710500b0341c00c003d080c1e0101c40b0203415202003542c9480702e10440301c00a600044a0200c0586440c02c511041030760503140c18410109030302e4003102c05224606008400d04020401ca138180604081101c1c55640c880d6150b018500428810a0860905084514141a642110341c1c07a51007400100310055101b485280c0c1f0b04d00150015803181c02e4900160b01503d0740340c108041c00d500b4000051102d50380301094a040320300517000d80307250b0349540d15020329a10500300e68141a0f00b0800201c8000d403100d00e11103e8040d81c1070340312000d0301e03034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 248175332 1250 248174082 248174089
    0x20103090204050a0c080105100206061504080616030b0a0f0504090606080609060106080f0103120c0501021201080303060a120503030c0c03040b032401030c0906031104050d050a0b09120304081602 86
    0x1140d101c0b0071076545d0240745580750b5126804030b02610054032000100315003090084d41d6100018500da100301d00b1800500340250101040d103000704514411101c0c0c82c146245220748010240d449480000e20707004602d40703949060700d202d100b00c0d0980c0000c0c40324907044c070040c000640003400b01692015165a40003c4011040144c18442e0655001505180d4100035000300100300107800f0203402c0c817005005002180000701020100c3c0c80030301344041001c0d45485c0c81030290254110050262140600001d0b000401000451060304202c5945101c13540703070542505d0440c80444058815071050001421710b10b1900002c10b00003031034200b1a820103950b24800c0c070382917101f210b520a0030b030b5051003080d000400780c1c01c4100302101c0c2400c007444405041030004100401600c54502010385a440390031001503404104d41c003400c0050107211070808103060a9684803014001101c0940c2d00c00000b524200b800709800c1140640d4584480c51a10785444160891304a1481d18031100d41052480006a6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 248176582 1250 248175332 248175341
    0xf060913170412063201090b0f0306040b090d0f02060112081e18060403031d130c27061202090301020405060a080405070504020a0e04020d0605270a11090d020103090204 74
    0x6100d6a00801c03220f58011a900341e98007403014292281554070307045010382c0041c0d0201c9047d01d280c41030016114000b01d0000d0003d204654034203804d80580000c0c0001e000d0704291040c407030103040f0111040c1c4249a00c041390301c035402508090040e00070f200144504222866111070007802110018107008001c50001a0301d2024603020450b103100040c1ba002000d00708a0001c50860116112418a8556100505036500015041300e407240c48454868035541c1c0c810b807000700b000a10000b0805070300701d00c0e005444d42e048500301c3c0024860b1008000c5451100c4c1401e0415100d0070340d10800405c415140d0440a9008400d407654103540901002ca09515100054018003107240d89195032428103003001803e1521940046000e14010000d00081c0d64000421421b1540142c60040c1d44004100d581002041c080d0802c0d03900003a15445114000c00104650088a078400c010b400c254840c580c6c00011204241c000510b104420f2100380d18074588004007158250040c140070690702c40a5000a00b04c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 248177832 1250 248176582 248176619
    0xa020f06090306070807021b100f030e0f03041802090d1e1209031e030503010b0d0207020d03030e15090c0108090319030f060501050702090f0712020309060f0609131704 74
    0x5d04a40300300890760741e0411926500c01c41c00d909503004000c134000030a4001c00c54400070307018403ea44084648071403103944602da5241510003070b41c030a683c030824055100d41c407a1140041c4980095881d10600b1502d06c01c03611240c1c0000c001440c0185e07159100940524a001c0b81d01d0850810a1008003242000c140c5188502455880c000c0c3d00d4118031f080000c41007401d44425024544081402c0000e401030100c905450b4450062503c903074450b0860f0010b071051002c0203400039401480c5004054258026404000c84a0140c440203d503150b000c01d00d24000700c5424030194403012003000c0c20b501401038260014a90411307a41f41141408a42013030720300e080c5030303000002d54907041c102107180f003445528090034091909501e03089941d00020080c1c072001e80b4207443d03203541d200072540050207031300940c103001003901043d502d03454526900d0b0740301c41d0122107014080c80c4550008200b8501401210300c14100014840821102a02c980c8401c003001010070407001810880411740c035107031100c030544c0c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 248179082 1250 248177832 248177837
    0x10509060d2c0d11010e0d0516200108060d030210050604020415020f01150e012c0408030a15080a03030e1e1c05030105010212070303090213020304030306170a020f0609030607 77
    0x83d4080b042c8020131207100c810b09202c030342c0d00d000c0c40000081004200c1d690011814600603480301c84c56445c500f4080303148503001304101031108241c80541a0078044584d0124241c0f111039840d0384540502028940a80d030042c0180c006148045000115034440c03074001d00c3c007601c0141803030740307070091111900c070046410b8015a006050318400e0000900444d200100724900304500c1034070301156a104038106005c3d0040700300b420740c01d010420241558040d400095220015101c0c1002d061284d180d51040d0740308000107081854060b0318034104031802c0111400e4400600800daa10b80307044000740000a444021402040145a01c1070754021000c4101e5407031001500400c24100c0102c41d281c800d0400602c18045e00340010402681c01241d10401501805444c03a070f24906c516080300200b10140c0300950084d410b41c080685d6014580c055449907120f0345080005984540125503050103090b0f1041543d4006100d12006007081d40c102c40441101034495420003a401000909254040b91751070700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 248180332 1250 248179082 248179093
    0x5070e03010516141c1407030c0302070c230a080c0f0d02181f03031707090509010b0c0307060c03020c060f01080a061d070b0315010509060d2c 63
    0x241440c081c81055080095401245035211040e40c02401e012448428008428004a1040d1244140c3e500300800003000200c100011252a0318081d45604140c801c0c00000c0d240070300081d4914060b2080781e5810390840300038041e807403425110f02884544141040d6501c14182007080c00341c0c48900508002d4401d41c2c0c0600b241007075101c14407042000ca844081c1c8900044001400503880f0030458044072400d54402c041d9940e20702c008002241000407540304085000d01c80042403550110450ba8481c2080050690546440c20200d070038109038010546e0054200d0010010300e40f40000402801e0031fa18140c900740011502c4002c200c54240f40c0c4940801d800185a441425051120304d42c0072100140040495041201c000d40d43d0049090040c140d81d519004d0001a12103201c0844210701404111740d0300c652192201e80d459081669401d842d13007001842c6180071f41c000c800384e410205015102c64100790140c407800c406007440c0708101180103952100340390b2940d210310a01e4111203c0340001d05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 248181582 1250 248180332 248180357
    0x12050a02040510061403150103050402120a110a0602060906150d05250605030f04080306040915151202010203180105070213020c073201020c03012412050601090f09060507 75
    0x100956001036202200c2c407002c10800002c1c2501f8008203002c0740c030038030300000d00c1e80e114401304240b07061403030104d203551180115100c20000020071074401c10005403080c00071641d0341e0030181c0c0d65003001c0d1906035094020a000a2103681d1290880c52500d000400401e0a03803000c1c2c64185c10a40610586d100245a2104c0f07070600c02c0c4088050001400d140c905079203036250290020b22640d402510041010700000f002c42c27462356894101138078058000c9115500b105415101c54000c2c203100d070b00c2c1105c0740b01c101d00020700e40f1420320039291041d4042e00554944ce03800040c41c5c51092420302250b05001003807040785e0141e211010f0500014145850041e6248c00d40e17070a00b8a45100d83d8040c1c620b070054504481e9200c106951104440038400084607415016100140e090054420034660550300c0e0142901c803c00f0050413010010201216040305151110402c03880f01c2c600a10250856002d040100300340006540103095a2141e40c1c40000c5003c00307581c0d44800d031002540e080d00043c0d52400320380c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 248182832 1250 248181582 248181587
    0x20102090a140607060221010b0c1005010803090108251110021804151707090b0307050105040b0d0b0a0605031f14010309050a0f0c0f08030a0912050a0204051006 71
    0x40261a910921030b9000d0000740c006000c0740b080c00740040c421900031407042d102c924500c00d081802000c41c001c2401c0c1e5a121000658950071100b03031080940b040f84400c0403c06036500c5818180c0d40480040c501c1c204464005403100640542100c580c800e80034402007440d44844208074107405c0d03a955117a0b000e02d1030741d01117180c21001c07a0081202e40c810442e11401112a030000c9601d042c09503404910380300b41700ea4440c888513090303110003040e144134115040d5050001c01c1100581d242d00c241046034034200d00a0541d20304140c0545800b041d410081440740c104800701030404100400c5000c200700500d81c001c07401074030865000c1c40100d41c001c0140a0201c007200c00340d020100215080c444110724040510098a003084041414140c0c1c4a07030f4203092240074401409455000118850801d645d46000c180d84440381c0300390301801c1003c480100c0c4111010089950407011947d87c1528079080050407036002d416018211035501ca10342c0210010307160350040520451803c0e856115071403501c18003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 248184082 1250 248182832 248182849
    0xa17070e0c0c1009021818010e0601120602091207030c03120309050709020306061308031b0607050a03180210080f060301330305070f03020f0906091609090c02010209 73
    0x100405051050b14081e075070009066000401442010400c080c45001281c00d964006d60a201422003a50420001c100e800050304505011702008100c08405400c03155241e800a010300781c10507009480c444c0c0401d800e9001f0b0115668010824411050040f8145151a03d1070b403044a044004ad0030410500c2540002d036900c100007410144481115035031003588440c00343c00b98003400b0303030302101050b2151901c2c810351b110005900e02ca00d0140ea2500da40c588c0e03a401000e00c0c1da0030b81c0b2524a1218600f10089155400785070544c486034100000701c4000c2d40034200b220200c40c1c16035681000540960f4a1503424410903120342c444607950b0814070ba903420307000707001131030b06000340c1c10a075240d154484201d00d60b6208a25043e89517204083e003109211003900260b20103000d5200c0c0c0540401c01705c116040da182103034805c588070307951481c400060000c232032001c84070f0943c82505000024644144000b02d0024a54603251141034240c0340c01603203044130b0b0302d4640080103030350110b600300709030520707208 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 248185332 1250 248184082 248184091
    0x40203072c06090103050a150219020709051608012907060218030f0327060408031c15120201170106030b0109120c06200a06020307031a01050a0507020a17070e 70
    0x35906159811621000d03170f118900b030402440d0540071540c8c038034440c0d2a581600c6440c0400200100200c0c0c8800c402961904c03a030240b041c00b01d2030100440c490724540c041414040c02e40c0d49401d500790b03103030130403c050f400c003c90409030030402c0f048000c0568502c0c034001005e405100b08001a03d0b860045412242e4081940041e4002e520a1050315502039000088d18804c161112400401c44040703036080414081141610303400040114000c81d4036240403015160090703020300384403025500280041d0590fa1a100c0006404c442a00184440b01e107849d40c3c1440140181400841096941c00b503404200e000d9101c100001c1d40e55400c1c100780d40c0d100c00341c500106001440e40c1c0d650701164594540e00300c0c59114510500c5007551090303030381942800004081d04101801d0302c0c04100d0300d04050000c1e42c0304854510009c3e00c0c2045551003816000c840600c20401030755038a080c400301e01e0b02a0346070b901c04201643d000e410302c0000039512051400c01c3c0505002d1345d014003034071480c115030b9030f04824000c0c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 248186582 1250 248185332 248185339
    0xc0c0c09010e0612010e07030609050d030b010905010509190905010510020c0306010510020a050a0303020310081906050604060e0a02070201030e0d080f04060e011508190206070b040203072c06 84
    0x140100038282c0c0340401c854104000f1106281e080083c80f41d418014546021095400c0c00303050346c00070070322040d0340c40088560b0241c02901c1c540029070a0403421244980410b07804100c56807420b00142d4400c4000d07004809000c7c141134418030014100d002c000440f03610408209844900601440c280314110104010180c0000c2031448003110001791142c405000741c5000350345615514408520821038042e000c2d07008800e8864000300c0d42002030180d071040307444504611114000040c8404000385400e201c002030700c08000c002120303035500409005c015007907a030b00a4449201003191209200c045003e45592100140d0387d221318070000d42a076208110901d442d130807800684414a8220380847d40c4000710003210901c07661a417500c04000c0c080d03501d035410076600e8559101c00e240d00701000781040d5005a0100c426640f2040d1f442001071110ad00001c1d04080f060110000003011062140c1c1c0103071008040c4e40e00c0307079204d1014051064074402a040c1d514140a40000c00c40c15000203d40c1200d8184c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 248187832 1250 248186582 248186599
    0x3011e060b04061704020301021207110d09080d0e03160803090a050d020a03030804060f0603050109150c0207050108040809180a180803070e0d060614030f01060806070f03140c0c0c 79
    0x18601900e0a80ba03845200403144c0c219000408655080d41110041b0705204000851420040401442500585941c200910814840800c9a8041e981e100101d504941c02060110b808000031201440101080c640520079040d003590400004960b07100a041e454006580780c1450108010100000e0f50081d400b85c500c401a03500543c44e00303c04030042d43d81504119486482c2d038941701d0000d0400e00c041002d002d14002d40401084419004207132410b0191440040415203941d440e4101c8844140f03c0303015902ca1802040740c0e5015600d05a0701c5400384014608041e58840030a0360a46070707801c0d1484c2e0016040821195400320321600c3d295646820360003480305165900c0d90128030002d4240410320a1070160384201345e4504000851955202c20284007159480c0c109000c00c0e5100c801e82d0703101c0c1c010002e81c0d42c848034052150000700c0360050300800c4ca58443c18000c0c1c507640d90084c8041c0405494400404d6a41418198140510400102d5544d80c90b004c04c1c03440d0411800808003072181d0440b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 248189082 1250 248187832 248187839
    0x60e01080c010804030207030b04080909250f1103040f0602071502060105040b040b13020a1202030402090408070c03051b1216140406030f0b09010b010215010902031503011e060b04 79
    0xc1d0007201040030300304011503031141d0078168070b03294031a40010040d8400100700002c03c00d42c48040e01141070155a0720700c19440d140b00c003144c10f0808800144401625900c034201041c45800d03140090056410580100c4400108841c00c0d40e100340c120b105000003640302008160780c104074000c002c0189441801c17010075400d100a4550006201e880d01c107545031104c80c0003d41c0c45034409003144000a1180e82040ca51818002c0a90043e2204a000c40c3d41000d0b91108120103008680c407407a4001c10125155071142d850080d160843c0b01705131000b1501c0000400081e1082001c0702511281c06180f210305001c0300c0030460041180b040040e002d800c010f03010000d9840508641003035030484102c6d4000038081e00e000ca0300603c000e03070020341602c140e42c0c84c800c18044c2164101d40100c400200903c03041c502ca8006a9503003080d03d011741c641da010030b0010092011168059a041183d000c0201c3e0107079520360000c1d013521f041941c1c00a4101004030030074043c62a0b8441c20005202620026080514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 248190332 1250 248189082 248189099
    0x2030f0f01050109060f08070909090b07121401120302011b020615011d010c02010201110a21020c0a1509021f080a0b0607080f13030308370207110a18060e01 69
    0x2c0c588001047c003150401060556009180c0302c00a040610020810111141000070b1484003d840c448007040440c11360190602507809103c4c00c1000720001d14032a40d02e060010011181d80d0704003507085558817040c00b00c80c1551170401c14510201c1d03070b00804e2607040c8107010840d091100d01b4043e050100ad0b011420200c024020301020458017400c181a06107618001070340505105181c0462460b40007541149041d0410100482a00000c3c0411003500b1180c0401c0200c1c85900030429442e0300990746500015800f060f0f03100070300240c2c0c0021811900e0b80c3e01013003004600402c0780d00030b5410615403000e911b40c003c030a00c1d8000d4102c0c03170074000d422441d0080b8555229448001c0d0040d01c00243c0d500c07651003040c040ba0100001d81038281d807140d6a07414024181034054400d0410440c0c80c400c00c0300107400800c0804e107d400761000f5480c0c001c9905440354000d41c0302042c112415248190000d84c1c59840b51303c410018101e0a40e00c9101e40100c0740c2c444102c038016000b4200c0d000e500c2006118644 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 248191582 1250 248190332 248190347
    0xb160e0108060f01110c030709020d0b03030a0e09040311060c03071106061c081b060402120703020f0d11040608010e161401030e25180203040b190f02030f0f0105010906 74
    0x20b02801c01c0c0c419540c00f40185d03401e00368410aa65090710415400184003142e43e4010822901d49c040d0030010204602c0c101034480c820364807502c5c00141d4498030440c1c549041c00c07225401c14880e080c0310b441c070000010341c18288103048a028a81c2640401088a12500942034826420000c0080c1c29075207400c00000e0070580022440481514401d40300108010700c0364100c4001d04402c0c00b800044d1980c2c68419603440300101c07000c90044004081000e0314480024805080d0f0b80d0081c0007000450012061080d018225901135886415180003030700152154800ca41c040c1c0101c400100d0311045100505142c649500d0001b01040b500200c201b011404024889154050910300480c10a000303802503498414150700031000900b00d0504c4445440b03000141c0c008641d410309204003050503014440003240000c41e4054145400c24000680000c041414115070810b802d000140c403080603100c480480e0400c807001514520b10781c05100c84950001d410781c2c0103110901c0e050201c60b08040d402840030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 248192832 1250 248191582 248191609
    0x11b060f06060c02150a0509040e07060908070b0d0c0912060603030801080a03051e07020a0803040e0705090306061009080a11030601090b100507021f02100e030f07080708070b160e010806 82
    0x1721400315030814101d105404451010800400a2041030184103c43d902c5141504c9080085080034400003076481012803580100c91200048900b0021585d0b05d85002d040480301c101c04201e0b89402c003003207031204070030050070507070155400140103402d62078003030101441a0800c05c1d0584c0800011700009510170101c900c01c01b100300b24440003010074142020680141040254003d0140b90302054425000003e030044503100201d00c80c00d900c40c040161262305ca803071199600750b0841c0f00012020f0803d0000a1401a41c13890912070f8a6910500541054003203102110030b0f4544030481d0840f441c04200240c0500346440b030400590414100003441c040b2840500010f20002207031010a550300c01c000000342c3c071018021030340103062514009480d1484c0c1c221104415182900114090f0b07800002c0d210302d594020a45c2c0e18001c0c03140c031039021980140c0012280500204915400920314060b106e0140d6424504500c0c081071030075004e00440100112141000515420040181d0b2680d1481044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 248194082 1250 248192832 248192869
    0xe030c0d0807060203041401051608010b0a09150309020a05040b0906120c04050403050c01290105130f14090c0901090b0703121a01021204120b06011b060f06060c02 72
    0x64020381d2a110807a4015800050080c91011040000388540f64480e6903408050100130841507407607400144d110444c8280e4100000c0c01100144001d400280041c40a20f280e0308103011134035130302c9240d0321030841507010510001303480744a40411410300f400d0000181030100d80c107208850400002c15240100200170502c165006015603d8030407007070007142c240e0300d00030307105110510b013a00b80500b16a01815104c6860342c07916110611807007407010010716200d20002c200076030000400044034160403038041440c28030801880082c50740b410101c0c0b400100702c2400310324001c1c09a403040240b122002080a00d503020f042011003400ea07800a004c3e410f8039030704450300f5105e004c10308044400344d0107141c00d40b11203403134036801e106000008052603603440c5c1d0903401c5545100c01d049400b8031a000714400e0b509851000d0309a01c0c002804062000e170b010340189401503901400139a0010300509a05040e03408030ba0b243d050050308005405100058002d6003840320b0b42c1c0020ba40403462000d10100d00b07258 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 248195332 1250 248194082 248194099
    0x90503070b16140a060902130b030d0f022401030201110304120201030c03060504051905011508060f0312130305100c0e01140405120606090f04080703110a020a03051506010e030c 78
    0x401203c0d42e0100664142501141c02001c0503161100c001d222412003a40316400c0701c0080300c4001000c0c0150178052078058003a04001840000a48104c0b01400204055004448118240d4142160300c1c01c0008800300020140b940356000240c8512005540f0040680042009119a02c1e42d000e000071100c0e03080c600050080ea02c007008800600075908401e5200381860700b0b00c6012050307020a400c00d0403c114040100303076a561808050701002e00c04050124600c000019138929101d41c085603905001343c190380d0b42500755600c8e808a0b0707100b540602030030084a101441444401c00c002d51042d0003007a010444070b2090000a4801941141510704014011516035548000c610a51b40140b6015060341e00c4c0e04003545200f9204c0c071080b40c0c01405420b000340003c018108018405000e941c210520515014068804541011001d09194481e100b8421940b0050b2130303100c0c14030021401440a03129001c140c0c5004000540d0142c16241006102c030300c40d07001075038007040803075903035000712840c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 248196582 1250 248195332 248195377
    0x30804080f0d050901050402010f02030a0e06030a061703070c060206040206071b0509160810060e060c0309030d0f02150106080106030b010918060602120708030c03090109060608010c090503070b 85
    0x644500c02c207110502403d04020070b00c1034a2005401450040b8406d0f00c1710605501803a5080b030f0b40340034080d00100003034101f80701c181e40d900700040215042010284081090fa80f103850b5200c089209846421895000050810a100d6038085540241a1a20160045041c00d40000c1d521b4014104d001d425001c40c4150b0700e804038600300c4100001e00c03000c0d001c40310514085152903849039140c0d6136840450000800540c2d50180d100882c021780d50540c84198103001304000b88509d50300305501c100320030310040191b05520760303080100031520441642c0d841e0000402c1c5000a0405102c100c03a0043c2142032401444103a402000450544040d0700c0e000801b0450400100c823258000d50008082022011002055030702c1c9401580c15920719400f120100300d1139450b031803404d10503900040c24403841403010804403001d01c2c0095400c03207801400800c41c01219150750040b60050342c00031920780c1d0340d040c106179819003004a10703000303000c12005051000e160200480981c841c0644180c040e030140c01591 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 248197832 1250 248196582 248196607
    0x70605040e071e020705100503090a030513031a0a0b062110030c03050a030801050306010f051003020405041e0b0f13050c0c03030f0601031802033c031804020703080408 74
    0x1ea038241050f060201c00304120703400194440c0380c6402041e0047c004904009a041e0003481140c0c003403030221004010000054804036819000b05074001c0b401382d2100030000115000250450b070346100000400d040e810040703801001c441043c14540c0c060740d41444100315590104480094040400303c40030074981c0c80030f014101510720340d00001c15460b009007011042c170000103000344649102c1d89940e0403e980f00e00416940b100700344034500380d02164910510203410000d00d40b040000032403d000d810a51504009815252403025480400d944620b004047c55881d0081d03100300c820580d41c45100d80048004103400e85156050fa4502e076803644040b4440c04a40000c45804080b080f041d0f0741c5078104102c140c040c128007900c07142c0c002401d2820307500d01580d01d8600300c131400da23008000b00b8920740d0901c902c0240d19105548018440000c21400e0400c2030095202c0704d2440442000d150703a0032004111540541040c0d001074010741c4144252000281c101c40c40541054000604544400000303403c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 248199082 1250 248197832 248197847
    0x3071709060406020f0106060201140103151e0b1305150f03121201080d0203130608090c04020d0f18111c0f120e090f0c0c070b160b09070605040e07 65
    0x100364012000003000101180e000c035503038140c0c41e11980203000c2e0683d0781008a00380d5402c0700c22084056009001080095414541002c00c00c2c42c00b40041414802896105030912507441c047c2c11280d1183d01c1078280340340c01d0300c007000f50804100c1300304014201390301141c01481c00c025101d40a80c9114103010081c1d0b40401403070a541150000c0c3d80d0340d8a80481d0a0b10b0084420700c19115940306848452107881d0022055030a90b00d0760200d0014010b10b8032401701c4019501601305419402240f0521075144c4540c0001c0c880c440004101151305216001c01e0411070b1150ba0341465000386403503c05000485c40603c00030030040071a590003494541510014040300e0043c0010f0100c03104018007401c03c24403008500445e00c2d26125200261141002d01083e400c00f1240084c0c603520460028040c001407001a090990380102240d5240707441d840d90300c1e803076071011032220414020500c0c00c40411460f01d080652100352034026203521880c2c98030140080c0105e0040210300c40c40c0c0000602501c1c4118176 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 248200332 1250 248199082 248199097
    0x70f091e0902070318060f020c27010b1305120d0302073306080a020f04110f22060239130912020109020a030b04081e09040f0e030717 59
    0x45646082914001d0203403484540841d128508544000886c0c9001d00607440020009802500d200d01c4008200144070703115480c2d00009006402e0f00801b02056889c07510301900d00b8184290b601c95040e400e8044507400b56011602c20000480b903c007504601258052128846041c09600d81210789025400c81a01011301ca003910400b00eaa0398109801003014880314801e65010001c0c65228200381d07071100758032180070350005070b08000000c0c1170a003588103c2c01e500c50312820a003460380310300d880388456100069006144600c8074082c106140c445d940c1070002c103000d00052403840340c0c10200d0380c0140c03128190043d072034500e03901040e0004103208100901813001484201c80002d50f500d100000c048e92a8282c0d0380124044c40e0604850051080c84a581d070001d10310074010346990340d1107403415401002125a4581407103121103d08094020301603449848482e0758681801905000c21107030719030744d61082c00d810049010010600442203624064201d09145031003080c881d95110284501c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 248201438 1106 248200332 248200349
    0x9010614162d05060915040618062d0216020411121003052e02090a0506030901020409061508060d0507080703080a020105070f091e 58
    0x1a00c030034600c290300ba070b2011401e800d110540c0c0c444103a514900810140c58a1041150610585a000303007150000c200380c229103580002c6500018001070043c96851140b0b20060804810700c000c1c40f504010f06000b2100465051207400102a0052042c15002d4200c448591041d008480704100c00d40c0b600d480b078410503020440180f0304c29038100b204060410061000a030f9501d0384622a0f0500c0220030002c0b8514100281000c2190404407011503040382451000b80c45030343c142d5858070040d0030050700ca00300d000108a803a602c64100d01e0f40150013004004c0340020540051082c0c803c10a010f0102c1e0756100c1614490704c0c2001c41c1140450301000004584c2c0c10061414a04140280c003191049592900e0460501c10160000c2d01c011000003910781484d41c0901403550401d0051510041104040300700910500060040300500c1c2c450b00421590350302881c81c03920240c400c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 248021582 248201438 := by
  have h0 := BRFrame.cov_init 248021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 248021582 ≤ n) (h2 : n < 248201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
