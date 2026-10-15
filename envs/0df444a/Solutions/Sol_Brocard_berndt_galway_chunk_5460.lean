-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5460
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:58.556006+00:00
-- url     : https://prove2.me/submissions/f6b4fe3b-6b42-4c47-b326-8cb06a704dc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 981834532 ≤ n < 982014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 981835782 1250 981834532 981834563
    0x402010c030c0803010e090c011110200409050f070e0307050909160306050a1d0c060a200105011706090d050d061a09010905010c030c0204050c040e19050105041503 72
    0x2c0728400c0ca00c0700180400000b00010402a810b041a9440f806000c800c4880b14030a82006448001d11311183c1d025640c0104140c40e400003070b941124180c078003014000d0b010f0000d285880c2c20a40c00980040801e25921001c20410240481140b904026141030807a003284421010a4450486c1d006103405039105c0310200c0d088481c2002184015000c1115000e065a120b2820030082c11065421480d41c2c0c0c00c00d42c40400c0e410f44020418a000b001d440280107412550083c0540ca4024400c010188a101741000012444010f0004169107025000240540c10411581461440104901c0c12544103030108500108001441d4050160b07600380252078140301410140541102c1e00040c842155a2143e00f54426034480038140c2044240c840340880c0341c0301d42c011500c09102e510003a001401c007840e50005414250f00082e041000200c002c3d01c4c241e1546410091160152911303c00440518080803090b1818403515014080464080c0444200a240c075421080980005070003e40700a4600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 981837032 1250 981835782 981835787
    0x9020a0509090a0b12030c3f1e0306060a0e040b040c030b120f07060507081b0a030810050a05060f040f060f080108120a031808040b0c0f010908030402010c03 69
    0x840031607000030411005842d020710003402504003490400c0c051031100340604509075002c811750f48024042e41c014a81035800300794448055941001c95800c214284840c020200040044800071441c0c1e4005d0307551307034513100c450025820061560182a01c0041c000c0c8011540c40a0071950080218601038180c243c5c200f0000c0c00400d0310800b1154028500310010104603010f40080c40c0d28441180e9105003244800c04072900c40c0504494000c403504402c07800d025044c0901d01a0840500a414240c1002c4034003140313980c2000d14010141303031640407a8250301050351013800e1541c0720325074221074100203180c64081080c441381c500a051007a980881c0007000880c1c84001da400400c2003c1c0100b59480e520380c07025044001704020f01d00000d404000205c0d410100180d0b020303101c0f0241046518040001000320002c00b0418141003181c40d213040740c1004106000701038400782283c00302c80ca9603502640542c91500d1140b280352030b20399040c51f0b80c110104000c0001e49900070740a0800910071f0030b180c40c08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 981838282 1250 981837032 981837037
    0x1b0d030c0b280c030b030d0203030103171e03150411030115030f050c0304120503060901030201080402130e100e01142e0e04140f07060f0512130c0f0f09020a05 70
    0xa403900c440c10300c1007190b80441500402d141880c952010031090103613000345a00e0340074810392100540c0c410030040001600b40f1034541c42204100c100d1505015140f103100c80003400340304006c42c6003079010042c0907101a50300e0384410444802c841c10003c810504a1141d05404140310b144d131002d69454514200c54000e411005001584120801841c902903030880540d4000781e401b40ea0202d4810f40d007840c1a0f004008413801980c000b0301d41c9415a0ac1e5a00446084000601c101d0b0004809114140d21034001d02801d4084400301000c0d114002c8082a484112040049000c1081e030400c1c45180c10111a4441140c001660b501801d2a0301d90413020702002282d030304019002c008001e0780000b60b404e00400c400b40628400c80c0b800b46000d80003050a9540c0e40484e9003481690060360040040d0f9014440b8000b100c43d1a040842c1032141030000c8007017220301100e0030314036411780100150400005035100d1018045500d010320702d05051030b03c11540400c0724090007218960004030940ba040c05a000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 981839532 1250 981838282 981838321
    0xb09190b0709090e0615091b2104050f06160e040c021c09180b010509010c150e06040c060315090f02040f12060c09060215150a081b0d030c0b 62
    0x5041c0000c0380302c4e00c00075079140b00c02c80340b0900012220a94022514184606034003814400d4030100300d11181007442e42c00c070783c403c40c6035010710f400300e19284450a0301c000c0340d548510701600150220882044c0c031542410401410000c141d6800701c0c1c010070042c0c0011807448076401c03e90b800101092503050036403508007180084c80c6000daa42c240526103540c4018100c064540400d01c0c01c42c0b9840c03203020030055901d40c0400501103402800009001e52040034064005c600074001d0b06040c2c0703c1c24411108840151a0302c54a0b42c0000040000b446000ca040000410741490700300204520040be4040150150041a80b03440d1102580c16081d0000d40565000c1e06040f19000740075a62a144a20700e60a0140200c64141c180915a01440d016004000449032243c018007658901074011001c0e0b840024501d07240352225003051462900e40181e4440034018100040c00c80c0805d440200304c0360900022000d20540203c45110002507101070748500f07140e8018035456440c6c640404508581031030301c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 981840782 1250 981839532 981839549
    0x902030f0718060506130603051b0406020d081e0c0705030f0a1d0d0b07180b0a0e181e040305091e10030216020d15020a08040b09190b0709 61
    0x840204003001e041000c1d030480b5410316000c1083c0c0c3e58900502406001314048003865124a9108106e458000c2d040544e2100a08084a9071036030350030007804682d0001d4010b44d0043c0c2c003003204548401d0300042000d802c0300404400600d14040104d00b4100f0200c01411100c0c40480450f101c01003050400584400002c01075010341c45002000c00200b46d03c64420040c20b6403024a00203c145080842000c074000d034015000203080d650f81041900d0681031501000b51032603a1500000301003031181d02405440d0090313070754094044030160410052440001010590500641c140402e042c14485400c5603204004c0c1d000e0460754a908040c0c50600a9147e000d0300146e004001500e410341800c007a01d000c000840c0e0000303861140d00b0b000c50403070051031460350903030320781440d424003500d880303a06102107038410750030700c040d1880822009090b40c02c80d20180c00880c0c00321043c0820803000541040e032002002e030003449c1c182141000e12660f20b0702e0083c043c0c03100f200072010581e0280719440c148007404418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 981842032 1250 981840782 981840793
    0xc0203130e060109052e0509030106030507030b180303070c030c061b0206070302040b03192003090706110303130606050a081c030203072001060518091015090902030f 73
    0x4507000c05041d1401ca40302c1d800900f81e4000421146841603814081d05044480c0002550a240c4405c4243c04140e40da2000d0200034001d912255400f402400051880b0b140078000c4c0741e00d50301c0c01c11083e40000e810b81c071440c41c0002d15446d07000750010641703030320441515002e8880b4035681030990720124003a46c041c24450038111044c141540355404620350010703603030803200b82d580e400d0400c504900071400741148000040000c151a410105401d4400b1010314000090036944040c1d01c410624860f8410f81c1641c401000700815100c007403142000401880c2400070b6100f44400710107880b0310008101c0100a40728840315014001c0a46c0720101424000d407000e0600c0d9281c0c1211035441d440c14007040821004000040b40d841c0c800e00030781e0b02452113030722801075501000344028a24803505403401640d650702c074400074a607502c01c60004111117080b551401030f820804612810314400c0c824081c9500c1c00d05003e65000b41c5100d00031821116040d400184011281c8002410500c040c000c001103032054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 981843282 1250 981842032 981842039
    0x40303021b062503080606090d2a062105070e01050c0a06020c1b0a0332030301030c1508061513050612070219020901031e1211010f0b0907030c020313 66
    0xb80024141c0728041e4560040554075041008048d11600711100e8001e00000300740c0c000241d9945040145030110b00d400300040800c0c1c191485289840d0380f0400000d41e014007540c003124041c80c0050490724402c0c209000600e08032501401c100b2030310340120304200002690703004140080c480480c3d41c0d80e000c01c0030743d9500341c108809652180010b0291080070040c01c020419480c22150701c004696004210141c02030b03940d017030442e90500090030901d21071000d00106285210a200840c00b07144140c0d000344401d400c03d8801000c41d501080c0c0101400f012005110ba2a81c1340344590840c0030400103000d540e17450903080c1041201882c1e100680019000c00d0440304c0c401401c2c0b202e03124083c1c3c0d40c01ca5040005100c0c411007070f0309021b08041d4004036800c0c01440400c50460188084011107903a041362a8416a986c00003240d03055800d40005020344800a10702c1d000b8012200c4036803852509012200c2e2490015187c0350014045c04103040d681e1820703400e860300a00542c0c4242c010008080300c019503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 981844532 1250 981843282 981843337
    0xe0606070f06270203060109090302250f081902040b0f1c0b0f01030b06010318080a0206010e060d112809020d140405030a141309060812040303021b06 66
    0x1050120340d00709407070110741c14403c494007821034028103400030000e0102d41d1030314448500a007000c042c180c0460140c0d287c16603020889140120b154155189140d501c01d24010b0754606510042c2c0000805400890401c00d0741509207903002c0d00140c0480740000e10703088000020340c00005100485400040552030041240c1e08001081c00c020b00480403800c140c0e44081400c2c408044c00d0000501c945a44000304031694802d900c036005440c4802203000004445480316a610341004640d480140d001c0d100501007080c0c07200c01c4a4116800740da04601c1d05000760740343d0a11070354450360240035100e002c0c84400181c540d906070400700d2a00404071101540c940384000003079408070000d0b88a030b41c10451079040162305c41155a02c80c0390090041d504010440201303e60f03000540071802c00000d8144684041c01070300782003c00091909010021307000345003c8626003000d0f190b0783e501002c03000921040000c2500420550349030303820b4040340f010b00c407a401c002605030b0064080210503c43c02c2510000f2000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 981845782 1250 981844532 981844541
    0xf101e0804050d0f05030714122e0b0a080a11160606050307030c1202040603120203130b0909010e07030216080301081b21010b0607060615050a090e0606070f06 70
    0x740a2410f4403166003452000762140c20403000b0309000210200002a082032080c0c0002800c481a21084c52038041440c0090901240c19142030541c981a888222240b60382810100d04029443c002c1525662610360103810314040c02c9003d40922030050005200080140c0c001905801310781071141c2c65015103d40c0b2803103800900004c032072a82c43c1202c00316161900054100031254850041c40070a41414255411030499040803030f0400d8031403002000140c600b8512900c00301840e401140c071400c00908108100c0040d900104003c1005c11010701241c5078a0702e25415140c4e5916203d503641c40d1290110000e1044844901240201c0110403041000c0c0b8001941203c46000c221070242c44200c000400034582c0200455004001800066004c15030000c1070312505085400020480600d8011442c9079014100858040e5511042403150289041c0c4060340221586004c50610742c09000180000541d0300421000c0500d58000400c555641011101c800380e2002010800c50b007217150980140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 981847032 1250 981845782 981845791
    0x91309030530070509030a0f110f222c06010609050102011a04180204020f03010518090601031b030f0606060201050903160b041b080615040b0f101e08 66
    0x40c030355601e030800c010120040b441c0b00c0720880380c400c900360b8441400c181c640307503c0b014803d0707014007900c031580000c111300620010200d40110b81c1c0d028410b00110812219591052159104440458110101030b00f03054a00403840780c2d00c080040c00d0040108014580380d0b403402668620019664110014440462800c0c12a4025254a44529120001a400c7e189800c40301440560800394a0344107180c141c219908100221b10301001250451b00404d0590380914401491400000010080d0381000c5000c9480101c00c001d9010160901c2d81519841c1c7c2d0041c4230240816108904480c00071080000101c010341c0e00003002e900740c5416250000250816100307a2001d540703050001a600000401240c1c44c6108403043e048110701250741d004079550003e4002d48070100781040105066043c2031080025042a00c01040d2900d40b40c240705880e440c120000c4e41c0540d040ca2200011030703c03004c40403810301c03c048600001d1465146812140c0101020700d00b00c1030400d4050f03400d8155000382c4c50134000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 981848282 1250 981847032 981847057
    0x18030b04112d0a0503030a080411121501091107080d0f05162a230a080438030910061205060f0f0c0d02041e060e0909120913090305 58
    0x9102c030358410060300003c0b51142c02e0b0540c104100420340b0621514085038401d20691000b800e1004007004030300c09031a1404010f2090781300e004160961201c1110f10760041c184001d044c440840860081484c0340146c1d00c0040841002140558112817160003c0f0403a800c082020000c5281594040b454250511480700118030201200000c1100d03000742c4903106113520b0281d544160456403a02140c003969181d1070030781a10341c429500c505c601404203080c0c460007180529242c2e414024402c1c2c01300b1844007409071111020400d01c9402c0c80c0c0c281c900142503502d14580d6207940d10705140500b084024090f00c141d252a00300302003205000f140380c61036030f14010801c503003059589070080f02400e982540c8224070060a440001c000a1081c001040419480d04e000341c20203907203980300c00d181d01700c0410840486004250601c4016848540d4003040002105e02c08040e003800d860303160f107a02988040d00300388800040c1ca618580c48849601800304002c62040003441c1481c14024025005501031410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 981849532 1250 981848282 981848359
    0x504030e180f0624040305010606200d080411210c060702060d1e09050309011b022805030f071e03031b02011205151018030b0411 57
    0x3240610105054401d0706070340b881c400c1c141c840308204091500b16543c4008800c4200c1424032905901c8405000107620420000c14424140030015220f0781c2c10304c8207503074a0307034070380124081c4041d00045003081403020b8200001d542e100c07030034101440c11070940c5682c1c104c8001a504900c00c45520b50041241c400c01c03050b01c019904440030010903100300c07040a58131aa05100e502082c1600340c0c000c1311840d28030000c44031582101e0501c4015240020002c1d15242c00c00310b4004820358014514881e030910342d400080720041c1540c00503900752802e940521007907801c0c00071120900000d00c80200a81801001c844021103005071042c5d859a05009101c0c0c81e800480f00703140b1000e010b00100040d80c0d419202d0801500425100c0040400b50410a9041040400444c0d210794803500c1228001c00004035244600440e110a100e5001c1d4265034903802c02144074440c0311600e05007c01c5038280d1340c0c0503081030000d440751b043c2008841c1c00941580c1d4040743c01a01c0d1702d4690014600300b10300c012588504c1c2c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 981850782 1250 981849532 981849559
    0xa06091d0d1b02040b010c050a0807050c18040b1009060b091903020d1218060c0b06030706140c030f0f0d0f020301030b041103010f0e0c01031a01050406050703030603060504030e 78
    0x1101d00365000c402c581d07545040100c140c0140b07031a401481015006151079001c1e503005407110391600101c45000d44d4142c0d000601c000c1070080502c00e50310f003d03500381c2e902d035424180964154418517000308050880075950000c284148801d00b4541b00802a05005014468880311003001e950300415140740b14001034428450803c890050040417a50003c0c0103c510340040d07110b0094003000c61100034200310500071440280b40c102103503030f005403401c0d548007074001c041031a15071100c140c0580f0a078429404000e042101030f9020a240d001c2c110803a50307454581105402540c5503010f0000d9903440d000300418000b080c210b00e40094013103045448028015115200381c040100c0c8020b00025104c078010b5030004001c02c0d08d01c0c1e4107002807000640006038504000c1500e10840f003103602409040d420075640b20b9100c2da81400341c00003107032508000b5440c400d6030100281483c8510f00c20501403100104410003854000c1c0d001c003008540107030b028402c900c2e107458001e04034480e81c81e070244150b01d40030310030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 981852032 1250 981850782 981850787
    0xc0201022b03060f05030d1404090203010f061215260f06091b011d01170f16020102090f011103040b0a0c0c0e0402090f090a050a050105181906050a06091d0d 69
    0x35086480241c094003d95010f010122340b45040c25007105460803041000103503c101c036200660003000843d03000e1b04c0b00e80c1014001466050075207542c54019060681c05c0c0070103c24059810b0071030f103201110706a014007004601d000c0311000d0400c80b0183c0224214a41400c2d0046400b900c11054041aa44555512860f44800781c40b0394040c50b0004100c1800c2c1025851800d24110f10110141018011000035940c0c00000032000c6511a240c40180703801e21854152800000e00c034440356000940c2085550004105254202c420301410003282d00701c941030811090044802a124100b0f40300d1340c803031b0380c0704001e440c80d42200e90448102c050702d00c00003a540d81c011701c03440c01244d000f46001c3d016200c0321052140070b00b0140a4940500520201e0f8001440401c801140345110700008a1903142420040c8515415400812816001000228070001824010280540d40306900203003545505102e440102031680003101d00d580b0b0a001d0340c00d800035401e00454650028400c80e00f440300b094808 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 981853282 1250 981852032 981852059
    0x1b010c0c030906200a060e010c0311030a020306011106070201090201140c0d0309080d090f020f09040203030a08070302121314030c0a0f21080103061118010c0201022b0306 75
    0x80c0000d01c2400c814001a0b20904c5285000d0701901c5981d5503d090720a10311381404a100c0b003c844031303583c900b62403003400310070302507501d640c06113003810460440d403500d07101170b144401052000d4040d400400140180c2c01502c0102c4a0340515048901c107140c901f0000c1c0c020101440c05074040b0300302c94510486001070000304c0e1800034415019103000d04080c0c500307401421841c04200d41c4044184040003d0b80290710a50440d01e0281d0004d0690101a006000c4c1c124284038903507010b903040c1000c01015880000803144130181c1480d102101d50ba480f10214000c1c044c45605c00e10f5040d212041c8080340450706203030380e0702c507004151150701c0c210740d0b1450940c0d0303200b040f40a80c4141c015502450201d823030a0080c00300203019a0031154403c0030142ea01c54400304050903a000700c1c2c0c1580040c014040b162286400504040b0f21062070301030083e0504842c0582c1401480c10002c0c6c1c684001c003107903c280444061000c440c044c1706510050064003510740c8410080e00b50020340760480005007a030030200c3e03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 981854532 1250 981853282 981853307
    0x41106070c12050c0301020a030c0912031403070509100806040e07030c0b07080706050106020a14010605010203040521012a0c02090a1d0601030507030204050a0b010806040218061b010c 81
    0x2120380d603501c2d001c1c1e9a0b249000d00d4500391080c1c01000140140f684003800108030154040e6000200c00c1180c90008c0d040c4d03c150381002402c2a01050b01c040004d800c4100001000c03079032404542c0300e43d80c20108960510800c82400d40040b010f01102e9080d5402c28800380c014070302110144800090f420449031307031300e0303007407001401400320701030104254200b000080c10258080d00d081e514055485c0c6a02d0161030081e800a40186c1c059015182400b003d80c0441040300c0c0700000030700a603031030400000d50301c5c050fa009080c0302d0010765016492601b00d84072504040d13000300000307101802403580c0c4516807681d5035038911088001c54480c0350009204200d14114580c1c000c06020f815125000712100a040c050a100920509520841c6110108200c100c0c0218441d20040c0141421340c070610056440152881d8000c90600c00101d0345a81c2007007441d6401762043c3c0b001030f141c2e8410191510f2510f2011581600b11400140140856a03010200d5080070007400003802941038055044920001125 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 981855782 1250 981854532 981854543
    0xe031903050f060906040207052d0303090d1d0405090a1110050f0c0a05060f071412150301020f07061a030c0d201002010f060b030601090b030402030a06060e04110607 73
    0x1801d14500a01e134140c1004c000b41005083c842d50b5a1103030301e00b9000212022218001c030303688400b4820640c0307510880f2160345026600318100380704035594640d10f03104610244030b12074a01c14003045441c01d05060360b59006000744007505000418545031866008241d0302d0020b402005e594138109486919205152686c46c540f4081d405400c51400e6001198141500d0140c60900c0010a4080004d03e00940d44080152450304010328094114400d400e0f04d4007100105000000b02e0125400c500d41d0700c4120102d2000d590403c900c00240244500c40719925540c6000c1480c4061008940c0b00c1207030640d0400c441c1200d40082c01c01c156a400088a4040c1e00425202d00b103400110f1500c92012001c042c06188440c0c1d0801d0710000f2100d8000f20f1008006030341d591499107070618103001c0e21008181880d501741c99410a0300008118450500483c88080000008181103460400c100c0030307555080074042000d01e03262a08c0429205080d141920300305e404e0000030b401890310300115075610307a101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 981857032 1250 981855782 981855811
    0xe2d151905090d06050a06080f0f0d031b0827010b041413021c05010c080703140405120f0c0d181a030a05060102030912060115140f09130e03190305 65
    0xf40c2c1e0341380142000522500c000c0c2c1c1c42ea03500240c521801c002d201c080c005104040c1c950394a03c0000c440ca00344031b208051003014244a00703c1c07034600e400b9201041480361454004019034440f90b4a02000d13030498000420b0345250285d0344036052040d8050000503d007150144600c841c9000794440103042607d1030064081c800041000510f00b17007181203a5882c1a146a110b0708001e07894003801c4500c00c45d04040802d0f401402c1001c81039043c490b070003a1200b0b840d0700c40d4590078a034560790354422540c810650003810000322002800e040030b0580c2d03603040f507802c12560106c544c90300041002610700c0c15902401030200c40490030f0a9584070404d00d012807410141c0c00d5940d030b12201005440c0262255041d800304000c083d40d140c41e50302e9907810490b140c80c0240015450205100003029122441030b04020441c0c0c0520140c4c104441121480208200c0301511105d01400103a4410500c071040d88190385041042c810b80c20010019000f01e802c640000402000c0ea100c040d019640c00f21000455181c1c007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 981858282 1250 981857032 981857059
    0x90f08071401030504050f0d050d060e0708180a170c01110a02030f0a09081006051e010503060d110a0909030f0e0102030d2d15060e2d15190509 63
    0x3e81d00103540240a802111132081d1070856440c10f08020b002a440040c00018180c10548502d000c5e900082c000516a040549092807000b001c2c03207806450760b080a26010a82038521600300905c00e440b60300035103280e02905c20305003540f04daa4032005007041c8035406d02450142c151f01c0c0c030043d10304206494000e14034000c40314112041c0b641c403280d290010302000316804900200c08100c181841a0119030018035203007070008200c0410255500e161a2664a040f190000d0340d108060b250004019900041c0f070b04e020346003c2501e0b40840b11070315001141c0d44000140400d103600640c4420340a038032400c0c0d550314685001c5590700140ca4240b800b690007004880301c450699130000c0600e1000c500d007041f8001012070310001941018003504049038031091071180c15501000c03480000c2c203940c1005100d40d00a6000325409050503802c2c6c44144500058441c085e914002c02048540d00c0200700041181c1d900740e041d500c68000b9420062050141910345954600070011104044d60003000060a42107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 981859532 1250 981858282 981858287
    0x106020a030509061902010c02010e010b100c021c1a10121203150603020406170f041509020918011a130f091a19200703050910090f08071401 62
    0x3c460035440d0010010084520014160402da00700e8000301d50010a240903404d000a00b5a40039129210740e0703914000354030001e691540c25030340044010b401e2910700318013030780001044080c401940044544082c40402c003082a5114040d4540c5094650410184c4800b80340041da0005800380e907142c0032080907440c010440c181582c207241300e842d20b80820940c62803100b08ac54117409030300c40070100390041070920503690000180584d0043d141540d001a140424801c4182d44d4040e00103880304c205000c07000307084150394104021036a0094840011070601d45181182d0001000b0b000c0840c1d460944180400034040c4804102401d000b0a411083c412031038440c03009098075141c03540304a5407003000c500014074480c06040e200c0d00c44007800700c15142490011503004210f02043c00e44624100d5981000341c44155140c6c1803080c840643ea0721440c1910b82511070b071040704942030b44000c0b502e0400b250340c2d80c003080354001c0e640f8180c110003032169161029a0744124900508904209800da942207d52 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 981860782 1250 981859532 981859537
    0x1a300307060f1d1507080a02160809150c0a060c0c0609150c0305060904082b050a060803070c0311180a06170d080a05090a020603040c05010e01090e04170d020d0617060106020a0305 79
    0x40050001850009c8003003107044c078041c82d41805c645201340407615444510300980c951510407103840d0f94610f041d80c00d000f00c1d503c41d51103c200825030355440e021460070303a00c2500301c04031855002500b040135071040c1c10319561102e000c141c0300740000e007440d1017444114444d001c0c5502910f006048200a0349030313035403005d4468014040c11030b0034040c0030a4034494950305001d06202039038a102c0c00251801c065001d50155200340c2c200204507882041601c0010381f14003e070303104a0b0740145035620200c015100040c9803a4031080500011007241082c04904525a80a001181c00304100100c0301812101040c0d2202c0c004400000460b58a100141403007415030401d0307505c83c0d244401e48020250990005019410031340b8241d91040311100c0611095810040034100802c09007131211a6529162962800d0140104004c18032000f80092050105a041c2500c0209050090075522654101c001400900c42d07803059030b0307040c0b5504003400302e04480411118180e400750390140901510540b0140c07180d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 981862032 1250 981860782 981860791
    0x100302040602211611030601050f01120c180305030a0305061c1b05030d05031f0f14030c0406170c0d02030304060c0f0b04061a300307060f1d150708 65
    0x1d000801100d038044c140c040c00805564420100655401344000505240c85c605800c0740d4080c606050041c02c4580e003100e001905059000e40106504ca02000c007200c0281c000d00b407040075012034400c080200203010000d00180d00e4142e40030002503680344c0c1000080d400f0b55550281d8a14101d00180110b680018001001c40e9501000b1030785541d01d1000c0b900c1d2540300140000040d42c0403040c8110042d0040900e40c4000030155403150340790400d10310070b000c2c203040c1c41000c000c070404100c00d100070389080c40f200ca91502d001308200019681d500d03405440d00b00c0744000d101780c2e0240e04911900303403810000601c002c0d40c000d4001c50401d41801ca00b41c0301c5280742c1c0020f9a00c140e2240c0c241c40010001e034007043c4503601c00c2d1800f107080c10240350051400030000003000c0c07240549040c0303081e940d1040b03440381724101c5044040300d00c42c042c003084090851251440150515052050a1a41d00d040da049800d05d000004c180902000d4180042074468007582901c841401d5040c0100314810f20482010303420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 981863282 1250 981862032 981862093
    0xb180607020a0308190203090102100c1e091502010e03070204090224040f0603090203151f2616030f0c180605090c0a0e06070501140114100302040602 66
    0x14020a0740028000b2466940b0448403001c0018040d441d10001c0c2d280110078145030700080d4207103403032070340040d4582c14035110b00044070f91341ea0810401e00748100700000d41000402e8000c4c4c130480390f00703a0091030b140090050201c00d030310b842c011070405403051254550340901500610300f071502550030403000e82600300d81a82d000a040b001026224411122000c000a070300e0902039640d1b141c00030f00090310403954040720516140c00424400f603203000c9000d5480c0000c03240b0004041d034668421a14040080032016169964420049007118815203444140481e4075510308210410b514000c1d03580ca0100c03401c4100000f642c0c401c0001840120001032850301c601d01d11000c2c0340d16414040506910000f90218a544a5000300000d0515001d84c9406c60945c40000e45828503030302c005080e801003031905a0140e1400504107041c00400c0d445203240e490315106196055940302070121018982c0b510b024451059801304220241c024802c840480b020340c1c000e0040074210502000000e04d541080c00c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 981864532 1250 981863282 981863287
    0x9051c02150f0301080109110f0120030c0f10060506070f060c0210231503031c180b090606010305011d0a0905010c0207140d020a05100302070b01032a0b1806 69
    0x407140b150340003840c007801803000002158561424216120801e078040075000780081c00512829036801030300c00e811964034100e5100d0044102e0300c480c0c03a5200d41c0c0700048460080c0c1c1182a008280881c100841000c1c414081c04041d8a49080125621940710010103242003200390354000f034641d400c24a01d2003500d005407640c1d5410350b0015400c1e0f4010310380c48000b01403850080d01d1606440140340f90020840802003440060420211b9624820354901311180b01d4000d441c2c0c2c0080089410850000e0800440c0d5a00e11400d8a0b1584500b1f03426620303c0c1c00c5008000004a0319440392140a040311848000c400803280210342c00001030001602400d206030302c544206003c1030090090042e580916401890341078581001440041400c241c000c1c815040001e8441c007503540c00c0007603019940100c891100721b00000505500070312520340c0050440012500010134044c1030040807030340d00014103500003030000c00aa0685441d0650041c08481003080c00b0709010b0000d1030284098000d0040d0940780b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 981865782 1250 981864532 981864547
    0x30e03070c080f1609090c1706010302011704050c040e101109010207050a0b041509081c080604051b0c070e01171e060604090f0f0f0309051c0215 64
    0x14116400950192041c5191450400129804114a94200e1095405041c2c09a011010701d01a41458400c5a403820b0300d480240040c008040f6040000386200411a00500340d0200c6203600e50b036092109078007041003d05450381c10480807222904c42d036840703c060039038040302204000007081458401c20903440796480c8000071a80e07a2003180c4100071028000e41d12605244c000914003101c40c0c005500a0304482030030860f801c40c82c400d0b60152481c2614031618000c502000b15001d0007640e00000b110320900b50183e0b16a40f5440305e20b00001101c2d0740b500703416a104414072081d00c1041e5159903034896008005100590b441010b0a0091005c03002c2c4c0c0c48040e99580c2c0d01d028140b00380c01c0100540c0005800c089110340c00c2200c030141c86141c0484101c80c0220f03480d06500c1d2580142a1800f440d1210561000c100e85000f014090b40c0d407101d613a00d0f180205007030a54403040c2950048010403000c01010901d031500028004812412441d0714101c2c8506e54240441410b07000c2103004146410b0020301c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 981867032 1250 981865782 981865811
    0x40302031515030c06030c09010e0634020d06091403040806100909031b050c04020a1706120c0103090c030c1e060e01080403051b16051212070f0303 65
    0x51001980303141c807421981000307400c05600c1c4900303540c024440d03440801030511603261201a281e01c0240b00c03045948610712080140c507280410103034103611901c0003420341c88130343c1040f00c86029240d1198141c00c400030151209000700b040d0100103075211401c0d0628000064107a0403c0220038031070070790003080c40a211500d0785150096080880e00b508140204060808145810300c01884410300c140f00000482d1009443c601c4203200050342c20710005800418850708000032603046001034411940d0f5410080c004002e803403601c10540c2d0440d0100041081864400f800c801140c01050242c111102154010b40c02400750302021916014411000070114041000400003041d025107d0b43c003140c842c0900303030600c2c0721641180c014848541d031440c5643e40d03c0314405034000e516050040e84ea41c44024000140380560f03000e0310186c8200042d45d003085c44248a0241101c4003039031460f031942a8a00c2a85d1030300d040c0304a42d0141c1c001844218080303028609101c1c071160003030900042e1280d040049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 981868282 1250 981867032 981867043
    0x1403040f150207021c1a070c08030c0a0e030c10030207020a03020406030308161707080604021b1608031e13030503030a1d0c030616030209031c020106050907050d02030c04030203 78
    0x8141d101c0b40e0108051055081c01503815015200c0700c61284904640c0d40c0d60f1119241002c0f0044100b0b18204000554507405a6958000070760001405038030703441c2c6040740e0001030340700741450300024034080c0700c1c4203503800c0009111440070313002170080c00c1c040311008040b0000e403c8000140d078044503920700000582c40300d10860000d58065a0b641d902c0c0d00d4030b06249480800c031802c00c1400c0140c81540000c1a140354410a40c100e40c140c905110540c03225070025000c2d006045107400791300b18040c805070b2000d0000502d040c00f44c03041c0780c210607156510601203442c4c1c0602c14501000400e41441e034440d01c20ba020080c4031911242688000e641d40b291156403440d00200c402884569840c43c681141e40340c807040302166000098000c0c405c1d404400e02090310790b50054044461400341c2c08688140c2030207501035a101880103000ca0314906407900640c0d00c401007020081c8095460507801040c6424210a190700c1210306440b803d01e420780401041c00258001131002482075000d00022005a130144070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 981869532 1250 981868282 981868313
    0xf0203030f04120e180106022509050c0d02030a06030308010803040f090b04180b0a06050603011203120e01090f14010b0a060c15091401510b03190203071403040f 71
    0x5c0c0c8403065030410034007034640700710040b000d1038190000404881d0340c086d440b20603080d21040310300810b07030703469907030829555002e2002601d100c14000f00800c460070392103602c800e040f02d01a40d1111400d0361380b08030f016102e200705d000381c0e003074400504000c0c000354040ba001034144110180002030192144000005c4449202c002243c0e0030030701c0d40c03d0150011240c0198000341c00110345840c5507500d04102c11911004079032000302449031146102802c2811980880d2608100000a02200c1d00d18070307111040c0712140c1011501180300c1c0e01c400c000d042c0e05100302001114054003110b10035080a805490844080d0411906011740040d00c0c000c000c0d5a00810301036500c12240e0f0100305014060350740c00d540d1807a0004450465075084040c20510140a0049503d500d54102d02048402d00c0640190482c0304072001115615690002d00f821800c03009510422000c2d074035008502c401e5078a4410382c441900c022001520001c45801102e07051001035070818810300b010b031880c0e69240e0b50328824030749411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 981870782 1250 981869532 981869569
    0x919020a09060f050a0801050112060305031b01050901050126121c141005010318061b0807142b1104091521050f0f0109030f0203030f04120e 62
    0xd5080100c150042403c60841c19642456814506000001003502030144107160410190350b000c0514481a548510080d5800909403a9160300003852441c0c41c001c81d040e807016561074440040c1d080070040c45400d06076103207000d140d0390152546000074010203954241d68814092120050041764201d401400d4880c035019904030056100c0c2810401c88911040381c40910080904000300040c0500d201425500b0900340011203440a680120282d030700319a000740003514045218207201c00d48001c01d0240f504d1555508200d65074800110303000c0500715480070402c0002d1002049428100c0d010501d401d080b01030407000c0301c00c081c005200352100040408451400000e06111840b014000c1c4460340900f9560784181c0303031a003284111818150146045001c1c41206008104402070022052442d08001281d460b2107140c01942d0003464041411404141181c00701101e2038004001c1d24465002180c1c440d07065502c1c0d866015401901400440c100011050414055650032021420101c40f0b032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 981872032 1250 981870782 981870797
    0x210c0903030e12060612010906060f091b050a0e1201090c080609010e120918071d010f1205220b0109060f0323011d01050403120e0c0919020a 62
    0x14200038000a0202c44940c2c020b036900b82c602d06030700500095080c2c001ca4191103c42102464145840c014010b41c2002840c1c1400e0540003c2e00b103640c00306c480c050700c04001080000c440000b103207044401c000b0400f81d001c150240486520f1a011340e9034200c0b41d61010307080c40e0340b0109070140142102c0c081171007150740012101b4203000d06c0404000e1150b111140d08001c10040f40903112103076881d240070b04039194001001901590640380c0b5048100d010314540074001550500c01c0d03000c0c220301c06500c0c01c000c41c143c3d110310700a003d40c4505c400c802c01031001e46039942a501030b0b403004000340c00300400401c1c88070403420b21402944a40d1034130000380c40c01081c0d1007400c0c0d41407404603019149907070300c116040c66400000784003190304044480c807401e00a220480c00c4141d00c200c024050401c1c54140003148042d1098400c0b83e28040d00024402c4d4420f82d11081d0034030380700d54580c7c00ca500007001e0141c2a40701200b5200c00d42403054019400c0002610b641680c642e80c0241002031b03900904048000943c03d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 981873282 1250 981872032 981872039
    0x4090527010204060912020402070c23060a0801050d0c0515180f10120e01060906090c090e06150c030703020a0c0812030703051f080304061202040305060403210c09 72
    0x1001080d85403500c520001d601c1c052900d1802002d400c824050506803030b400c2e02c1c1d510115951541151a100d40c00380300100035664544410310403800c65030640452040c00c3c00000c3e0180740240445000403015150b8040690814041c0b05010700c1a400440b07010138039a44c04590f55562030380d921051000f42280e00d41d5151400c000504c2000c03c1e03801e403405a03083c58001c0308580d4803c800001101c0443c50038a041000d40403071500601060350387d041265107031810100314914650800000d6411142e0240040203007241c0880394101c1a200d4560119082000300b13409180203030381e4003040da284030030380e50900010f924000c0c10f55100d008101d001d680a807601800304509940f09070024008030018201c04541d1102030380300e03440010b000a00305aa0b0b00005a00400c0850003408a401c4107404a48065240c200c102e0f50307036002b8010080440d440070951201e28045000711003d6030303440030140140e03440e641d80940720b00d0b68100a49503030040d0128100f500c00c5040c27155180d1004c4a40d1400e00d014139 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 981874532 1250 981873282 981873331
    0x5160b0906100f030b06090c0403060c05090a1401080a180204320c07110109030f200f0d020411041e0e06040c02061303110d0201020903240c0f040905 66
    0x2c2542c0a9038100c0641142003012504104580b0b50010061300e029015503190482c00c42684166040200071030f15060003282d507a64800b0241050714401d4401c54145903c8504806000b07015405060000c0e40500008042030080d0f0401c1c05801b2011442241c0341c03140d640028240c9910003a031400280340f090110680341da046a80c4543c00343c118441103180d041c1110490014840c400020b071414109507582d412036441482c0d50f4008540281484100c17800914203648806e2001644d088400340308000c02c081460906030094400c1c0c1c00601d9540c0c04900e41e820f01014081e400804a05217105001c001130900c12000b04040c0c981040e9001d100c140d051080b03408020310b002d03000c140600c1c07406440e0b00e0015000100d250b085868504c400b4040b640c0b030700c5c003100c07102036400740c0c820240a610110360010b5015000f030031a03a00118182c071007500b401c860340c1c1071000452042d1000b0040340c5000c00ca440c9849002001054500c00744140b51a444280c1038054507015540a40005c0403260100351800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 981875782 1250 981874532 981874561
    0x103021b1b06130317090d0303050411091e1f0f0e0705070b180f0f071409040203060106050a0309051203060f040b030c01030e010902030604030201060f0b1905160b0906 74
    0x80c0700712586030912403902c811a000101078000101290840c03041e4107541003640c400d07038128080c001c00c00c0c460400c182c07800401820080c4c40071242c0030380031008010140740c0011600d208c1c84940c00c0500c1050940960405501000760161444070001d860b81080a03c100e41b000c0302920320300708128906403a00409140b4100001c200c42c08100c018088000000c6140c54025000552008409610124035200b181013802a024050141c0720315501c3c19500070b00443c9440417141c403a60400d82c10130640c014490080c10845009505820280c014440140554090841081076180000e40b0517190790b12a40b400321001e500c2d110307100e400710402c5010b180881510f00f06000136103060054501c60710100c0d540f03030241b61075903041c99200c8102e6000c6003025400000450b40042c101c03001d50825080190084c0110b0040b00c2c0e800c0c442103004600501400304503681c0243c65010488000d080f6401119150000001000c440c0001000354011507240080180560481005495503080c92101d111504 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 981877032 1250 981875782 981875833
    0x402090702060105101116240e100507170412140a0f0b06010c290112030f030507050f03040312050601090806040b1f08030703030f290103021b 63
    0x10742c000d20040c4469141d0b05402c1c082c4040ca41442d1511081c03042d50107003012030b040321109a0705850000010088010705400c900400130400101c01c80d02c24004c22511000c0550f40150010606644601014414001404147e001e441440c001e0000b12124800d190710503030001070120108207a440501010380b40d04529000000001c1040340d05a0341d0320381c0e401c0c900a401400c0c0c098078400160040e4040c00208c1c0900c8d5120142c0c03000070891900d8681340c0349074000303104160400c1c6400410300c010380d6100c801c0c60321740603200d81c1c1c40001c0f2450110f018040091010003003003014850300061a45440156010754800c0e250410000d52001c411403c8501c02083c8034100405940100007483d4045001a0800d8001c45104e541c0d03541c0c5210100700101104242c900810500d100040064004c805001e8551096409121401e60240d414082c2e5070a00750380a01e1104403103200c0443d25003441c01c0c601e811418100941860380c485c0700c0120103140704040d800b044d040707210000034451030020f001442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 981878282 1250 981877032 981877037
    0x10f0501120f02012307080d381305070302030411030601180e1e0a0632040201030e031912050126120f07031e050313080702100804020907 61
    0x1c8001d95160240307400071080c4082c2c1030000c00c8070f400050780010703010b03850900302445181d07960b44850f2429058640c40403410701041454100b1248000f8840401c07901e261180c40206416080c000360a8500741413180f10680d032002c50340020210911640c0182d51150455071070050710ac1c0b4107400c0410041d848501d00303a12035046000180b00a4601c0251030325088042c0500207076000307480101924100400004040142007096258252400005e00303401c114440c1e881801030204a801c40d1260020781010f220140d00b0441e007076007416044042855000d40140340202d4460304000f0070f80c1c116480390200854500318a02d05042076604441e1034190b82440d0b0b0001c100c02e40c94a0701020488003000f024940d0b00e400303030030b81c059488020020524040c0d04540c2c2c0b11b0b0386020809080400754000d020031400301e0b00c641415000d0624000e4100d2012f03045031180d510710740d40c41402c81002c101094040380c581600784101c2c0c0240c2c0f250300b0180c41d01160754441298604003070040000000e0700408a404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 981879532 1250 981878282 981878309
    0x2070b07030605240a0f09170729090d02010c21020c030f0307020d0f1202031308011a2101021801200c060706060b0a0e0a0605040e0c07020d0212010f0501 68
    0x3040c01c200c2c007100e13640340d420f2403c00c0300a450304c80115401c82c0300c0c2c3e08c006042d4600c03040d80e0855250103e000412102c0714001f9204071403211a680c8140c00f61300140344501305050062000301c0c01d18203290010544140341040e0300701d031079075150101810328410983c0e4000184c00d404505540410100d07480701001c60051010284040d08160340e4852100002d01070249000c421003044000361860420541c403d0703081183c40380c00384d0000e559400055407494658070f00c000c00501164188130361030203028152004103c2c41c1d600d0083c00001c2200003102c0c0061281081031480c00c0c4001e03c017404d004420908030040c807031001800140500d03824050706108203c1004031008c80040050350318100c2c5419140c440d1512218102003008140f164042c4408040005415099541c0105802c110200407a58200c5240c0c585008132105d01886c041d003004000c21002040882c03103031402500010f440205201016605580403e80907881403c403080c407a9110300c0040d9042001d40142400b50502c20710450f07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 981880782 1250 981879532 981879589
    0x1014070207030206223201080108030703080601110129060301120605040825051e070915030c0b030a0f0902060702010302030709170304060206010803121902070b07030605 75
    0x1022417140100c80004405015800e0000841ca0418017005007103d4400c0b8914602071090030300c8030284c444040c00d000f00b01e41058855507010341150750688000034011400d001107a80e0550b049640582020706101c07400d40c40742d80c0d10b102400741c442c090b5650031407040794420f604039450030340040c0f50104d80304110a100600c180b034004100003103100d40083d0082005e4035542095084d5200301000d40c0482107401a019007203001c1d90f46110302a41c0b2445c1180c0e0600401001114014041c0c1010030503604000001c012410b000c1d040f0304004e40084c903040211564954540b910504140c0c02448500c101200300496011140304401d00e000089406102e892b050340d00080741446120310080c149030307011010400d054800c005000241814002440880001400d1207a6941280c400c0700014400d01001040200000c026104655140f6400300f5032910303204602c017801054102c04451499003803010001061954015500030720440c0c41c0080c0d06400c103414094450070031544c00801560001415 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 981882032 1250 981880782 981880789
    0xc0506040b070803190f0507110d09060e01020c0a08281a04060b220c020c091803130f0303030c0302070203060601050c0109200907021b04020a030b0310140702070302 73
    0xc2c0e0300103500442156899484581c504402981d81e94810f0200b031400c107840c651414141d1000340122200d49840304803144400300b45680c1d12005c140040025100981001041d004565022007400f050050320881d4001402282840d24251b00030308c002d0380039041c0c442e110a803c0d40c004481c24081400c0c02000101d58660450f601203015504080c0343c1a41d000a0a019455220b216120b030010801c0b0302d4070091024141c0c0d860000b000301c00080c0e2a14041d90780c00b50000925641c10b6001a03c1019556109a298003000180c1000d80794240000c201d1440d00490084c00310700680103880c1000c40460450500030107d460355800c01c010306104114000150740c000036103d60100c02481c1207036440001d43e10480c090305500400600101640301c061b0034880800c401ca03000054192603a09403943c0e07008040365581c3c1c554504c60061400040b64101c1820309400420700c0c40c5180c02d010a00d8004100824504004030040c41c00841d5112010b2054a40c40580740d034200200348003e0440342d0541e00007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 981883282 1250 981882032 981882037
    0x307020a1e08070507030501060f050a1521050103030f2109140a050109020906040629040f030b060316060e0f0409050d17011508040213270c0506040b 66
    0x20300281002011507a030039440760201100740b940402015269105490a1503854269000c03c940035401c05101150038000f841d01042100d0300200040f0649151007a43d851407610484031004000e034280c03400100e50440d4003002203801c0782410000d42d41d07266080040c4000f0781140400100300004e0807140368a0340104201c20702504141000540c0d001900e0705035003245007410001014042c001400b014020706511621849000b0380303100c2455074a500c1003104440c068012841031b0100f15062003050f0700350b201c9070005c000204400626068540e43c0c40e0041404551048801b01424400c02c000f070305080c071001c0310240345085030441a60030000080d004200000180f400382e00b2840c000a20f0b55070f01c2d040142013a030014262000420780312402080084050b00324107803d1805400000c485d015000c00b44883c000c66524841251201da0802643d001d41c15011a0f00ea0f441d2000410040024003c080041c000111074501c56402071910070500040c0c0e900c0184222403c0c0020003140b02041d04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 981884532 1250 981883282 981883303
    0x90e0307150b0904021e040c120b0d0309030f0c051c02030c0d05190512030a0c0f021f020c0a020901080d020c150901050a180303030603020901050d0f06020d0e03070605011406030702 80
    0x7021100d46d908018000315050f082d000e115402400c10041408607504421003180e40d00c244003090040308916070500c50703844c204000040014441610400c04600c1141003026070328030800c40c00000c99a5600040d06112010034995813545400b030340c490440c9020449040c40c2d10742070740c40101411003500e400b92201410300003034011000750108101000700130320100a24078030803000fa6480c0d04000941c2c50041580c0a186000f19031040d48140f2414000100740d840501c0c540c2c00c0d40c0f4800d0304074681d10003030340214201c0022881060300d098010b07610079038494041c150400046c556030070280c000924083d0599282030090b074010361000c44401c02c0c0400c072003803070070203080c0385569002e252022105601840c002030440c01c2c0b0200d0120030107030305400c81e4045900807200d6001c940d803205c04000b00c40c48a288002d00900040a0213000500300381c000c1c1510320070312030000403200e003801e0140d404d59000c0b0408460890b500c00045c0f11240c058042c501c40b0103010354809081d85419200a9540d164808 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 981885782 1250 981884532 981884539
    0x10605090f091005030c060322030e030d03050703060f0b070f1b18051821160b04050708120a2f0319050a0e0607050304090e0307150b090402 62
    0x8805005480c1c0c1840822001406442a140761030b0041449600700c0c62401075a1090140c00e1641190703150400649001e03c44044440c0c03411704542901e9800d50070300b20303001c0b001d21030b00d9081c183c0d4666080c060000784e0405910041498508520018115244c40d0004011016005800e009040381d50303003507880c1e49510903140034664001e8106100c45584060700400c0c04041c0c0c200100e4010010740d00440c2d030400d81e072130134801074545414100d5580381444240910790300c0b10115940f1540e5090081c0c0c1c81caa0300c400c08030724001444210200e81c80c0c1c801c000b41d07410980c103403d110030004204014001000c1d0800a41040515480202024480c0038404010030030969070400d8044102c0000000c140543c2020031140402e00c000b540d2641c02120818181452254640d600300b80500211080c4820305d07076845640704402c900300300c1150003803403084ea00f42c8010310000c00c20b2211441080303001390b1250001d5440b00d820745400c516110001e403041d00d5103030400100510f01c2d11441030103a01709038100e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 981887032 1250 981885782 981885787
    0xf1407231c051b010203070f181a1c05100315061a0c0709060608070e0102011406060a020c040c11240a020f28090501090302060d11040b0408030406091d010605 70
    0x80f505800c031100c41d800040da03d544008140400c03650408004402c0c000d80c1c2d22400014041705410380a000300d1071007203007401d03a10030000b034004481e8000200b8007111011140d031500c0b600e28101000719441241d0402c6441075800007407003444103441d50605000305c1d02c0c4040c40311508066800301044410150441d040501003900ca02612060080c3c00140410340010000542d440d98020f000303d90a54000d00480c2d4000c00003482540306000d84d21401100c21107101c055201c400c180040d941c0810700d0a800c41c0200c1c4110b40e11541c90f400390800d0103032a55900b1000801c06200030307050105800751503664207010391202a00403224200740384c0c0982030220060311404d452511142034403c003070048403810030401c1c080c00386541d24239103a0306100055035189800f0391540010345140f5486e000c003940c040424403018260340d100e07170010300402d10080420340c20660340d11088000c580254119541513000402c007803251743e502c594120024100c20b56480021412174410044510303040c0122001c10400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 981888282 1250 981887032 981887047
    0x807140d0503090402163305041211010204091407020f1b1e0d06051f0e0c07030c020a090608060a0c050a1101020f0c060603010f02090108070f1407231c05 68
    0x7410302e5080450742010009400d402c0c02164070110000360000742c04441c7c041441880c049010307101d40f51040b680240c0e0510035800c1e510f015518500d40d4490501a5034007004003194560a41c0120803601c8a119285011810300c10030190601c08114100c03078031940191000382ca90a001003000001e600b05440c8220040c1d0382d0120811026401c400c00d64000105003802010081c0f03960210b803040851101c401354075214420554400d200c0ba10450b40070065550114812150203802031610324840d040820703494000d0b43c0440c62415940e800380701000e5680038104070424052103501d501011021b82002080c40c1e910300640103004c1ca0100800300006402c03403002d424401d6044421001080d07002a0320342c200744c1c50309a500c1000321441e074001d508080c030401111599000795420a0300585601c201640c0e095401c40d120036501d0300980800c0f21404110119400290090481c11b010b5000302c2c054214a000384521a0402c2d0440011580000e0b00c00c8041201e048400150102c98a02560750302c50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 981889532 1250 981888282 981888307
    0x130f03080705040b0a08040c06020d0c080306032e050106090f0620060a150803070804050d030c08030f070809060601081b0f0c071a03060a0509040f05070807140d0503090402 76
    0x5260411301500d000010303000d64040d0018110b61045200b07016019210b81c8500040b610707900302590310b0000c11800a000740024070240c01865000034040c040350031052050965801d400c0382105141c01801500d007004090241a00a0a025050070b00780703604120b242c60aa4812100c183c0b290201300208980400302184400e905040444c40100c11501c15090041d0004018950700030f1152011054410024030204040165820503411030130b8a03041914000510040704940b92045080ac1001061040041c120340003941c010b02c0c0d00c0e480f41205103061903000d0904603028151004690100341000749503a0301c40b01d9142c0c00340760820034615980303840400140318028000e400c01d2610000c903130100d00480025900007100c0c0450742910040d4880103660711103200c1550041d030820400201803095040076410f40d40c0043c401c40d815a021306040d00e03001d08028507034002c0d03035080e086290304200c00c00400011042100c0100ea4a040c4420540d9034595139104000d1070602564000c21840700120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 981890782 1250 981889532 981889537
    0x2091c0312021608301f1401050a020f0d08010e090f060c0912030403120e060a090506030613180c0504140412020304030b0408090301050c04060c0f0215040b0c06130f03080705 77
    0x500c204c56241c100d41c203280d07141c20045e040311000500800ea21003565101c541340c0004003215040b61082c0e500d503c403400110b5480d030042915030150311458581c0441c080f030801a0038541e111035550740d601941082c1c8904510407028004000540c03211900c503407801c0010444c0c64208043d203c100366030f01c0b008030206801450b641c0112581d400003080c00820b01580020920038510f195aa1501d0002d001c42000b400380100307402400040c0e4206020300c240e040650085400070b000030401010003180084400568031000508601c070b45001c042c14003004182da000e40302400040303c2c01c2c00000c03061402c00074141d500030701c060031008803800c1000f0313400d00a20031100070790741010000d40b003450241800b101690000c9402270281d86031034005003a400a0b2002d54041e15078a0f554075034040d040f900c1c1c078050700321680e50590303011000381d01551021082c9070042000b00035074400c00da103840a009840c7d040400c000c040a500c081c411040d40c00140e03a071809201c0036545402c010001d5201c0910446070350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 981892032 1250 981890782 981890827
    0x30911030d0e12120d0c0201020f0301080c0405090622020d141b010504061e09081606081b030402010c050a0206071a090f0303130602091c0312021608 66
    0x41c018081054042076000000d5109000305940c40750300c4907203d0018665030300c0e0fa1400708402d11014080e90005031070b190025a640e900901c005807c1101140325403c0760f40c0280c0c80b000190344a00b42d180b940d81014064154000a02000742840380340c148010281680907040141e250241321107090119558000c0a04046800c02814540916201e050356a540c440d0403206244000c100040460f5611407400c0340c050b01c7c240d030f403030081e1420184480d51010746018842c0f001d200e4018030108225008001d941ea0200b030348203419150901c1e10030054070310304010b0b01003200ca1446405800f130900d506422a5085682844c241d880c440310343c20316a0909102c020001d5100c03000003074400a1000c4a007854441507801d180c174402503225201c0003aa40c0e500b5007a13215045c0c005000042c0410451403d07242002e000c0d0002624201411000a80c42c12410b89100a64444040030200381075220310800342c0000e104204518080482c403005102c034070210002080c0b40c40001d0300700e103140d007000d0b0b1401c0700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 981893282 1250 981892032 981892039
    0x70914190f0806010b0406050d0506010c0f03081806160c0302070f12110d03080403030e030c03040f0e1e060d1401090336050d060e0d0c020102150105060a030911 71
    0x35140c01d80c0d03614407065441000c02d00e120f9000041403040d00030040b5802c64085888030783c502090520350002419000305003d0520454100000105607082014058113101c1c1c1d4640625203020a00218224205000141507070f104e50204034464600c04004106602c2e103040021140000385030032490038031680c120419460b040600003031220169400380340d1440c41000c101c40442890300034000000b00f940c0c40030300001e66510118002c039002e03a203c001e42810754003c0d6442e0031100c4500d90700e980c1c001c1d400840b00e116080303801c2065048042109400c1112400d04000c4c01c00d0100201c00101380c0a03101e98441c0c40f85048980401050303400e01203600440b0402402210001e0402400d0f40f0081e08d035009046500e03020354000d240d4010030480180350ba401408111501b08024400ba10400d58012181140d5072000a4146041007090122030b00c1e0941c1c5043c50448544002801d003071130340d100314590312800f40062200e0754546055a200f60741d6442e0004400140741407080055510740001d581 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 981894532 1250 981893282 981893329
    0x504051905070f0e1504150518010807060e01020a0b0a02040504090b0403020d0513350714040606140c070f080109060e03031006051b060118050f070914 67
    0x400c034020400d402100c1c1c0b1010f56440c00796030744080055090088503440041500c010f2820310914240c5d00580c00b001c402258030000644420126010102102c01122401014401000400c42c10442d44001c0c3c4910324085244150300400030b550fa8401d0140103007502016000119440350300c3c1d040d1001450014001d100c016424100740d1210034017541c083c1d0040c0103885803814014080c1d01100c020001c100f00000c1210710304034a20280f0701d02401d0b0044000100502c0c1001292449a1907070600150070103402c9441c58582e05015080d182d61095000341c1c24404104810741d0015259a0001d05a0100680e501e8882900b50f0030706101d13420081c512071907807001041010055201c0411188100b40401440c0b001401860340c0c3d010860302e842c0380280f02401404454415800740150007160b5030042a00c4841c5030409060503000d81180000100f070071402c40b0840300394010b598000d030800c0700c3c1b2903041c02c21040003400890203000d0072b01c01c40c1500da543c030b4458a46400662811008400030407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 981895782 1250 981894532 981894583
    0x120d02030f16150618060305030f0c030702120309180402030c1c02030f0601140a0e070e0a030602030703050f0606070f1209170f0d0203040e0604091104050412120608060a050405 78
    0x2001c80b405071110b58100c407174024040408a21803030055a81000003541010b56044102010f0340c40808000c01900081c04070030016100d0080b626440c030300900c0519103c2030100103100808000e00100010181440203010150b00c0218250186000c1070b03998103110047d240a003003410303140307000080d007600ca151a03c00105001140143c140d5250340c9100320500800010440907a525004060b1840c07801c90200b50014083e50320702a0741800a00f844209a40e03c0c0c03036540881c3c20407908040480e03140e00030803210405004180c3c2d0710100480c1d025052401c80e8540c3c4a9240d110f40000f0801400300054a0800c1d0144220100a048041301c0c0b20345c8010f10446140c4070702c13076610625441c2c4110403402d40200c1c0040195010381e501c4802c3c030390b030b159501b108002c00340410800c242d500880e062080082ca48460113181d20460107044042414000610010036845503401e68105451502e031061222040104419030813500204000c519503e982c140181001c816803004040e0400c8503100c031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 981897032 1250 981895782 981895823
    0x9050907080402030c06041a13050604080d080105011d041e09050f0c0108042d17071104051506030a021b100c0302030606190e040c0e120d02030f16 65
    0x14070980c825825241000030303070406d1200703e000724001d641a08146c00d03014412403050402a02e0341d00e50003401100c0b080c2d900c2c03000c117007145d001d41c0103000290440d4541e2140c05412800190042c1000e1030b01c8002441c1e040800000007a524441c00d10868031064801c0788083c0d110000d480c43c0f410503004201480c00ba20f06555a940070440900942c05014041c855075030060040303600c01d40d0404241c40d01c035080581e42c0b481419007006180310041d5080360903c040303a6201d03400c40380d18400ea02c8880d81c680d401d00b042a040c05251800ca881103041500b000b508440900b90083d080906071a010303100d0b01c501c1101e4011307008080031100c4496010f0300070310241e0b000113030000c011418900708105071022030700120264442100c0d210f401070703000c0009242c10b2400b071000d001c1b110068036180b034481d02e2100000e405d817880c2030500c600082204421100f5460302c40d009031140c0b1a60001004038000740d0383c01a4580c01a036100300410b0502050302010328801140450303030198001c2101a049903c1c0410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 981898282 1250 981897032 981897047
    0x60801020406170f1b0712030506120a1e02120a0c0515030103020d0f0201031b0315060c0b010b0f0d020703020a0b0901050f06060309070b070809030d05130e0709050907 74
    0x1040002030545980111941c0c003007410700c2c0240405003060070156100d0010f0f140041c80040410017421082124401282c04442061308140d9a5500882e0a0030319008001c1c0c40080d98151420301d422107450000001c040303a00e00b03080c0064103002101e10100741e0000424280b60102888150b0049000d002c04002c1540c2040041e18400c0398140e0f070740150000c8511250009000082d00034030304405000101e201542c0301150030781f051402183e08210181071004121a24860101003921140080103800340008618003502d200c0c90190b00c0341140c1d841d00b0060b100c040c8a483c20700040021415002001d0804481c40c003111780b401550744007036514000b943c802d501c100960b03615400a001c640b2505042c080e02c0c0c02480c507880e1000c0503031201c004104265001410000307036449001c1001400c3c0304900080e260842c000c190840d111080c80c1e0a03d800d00034080c41100070480d0800202004140c101003190a03107007210b4240a8030740d1203040c00d403240d44003500f102d98000018802c0020b800c3d805600e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 981899532 1250 981898282 981898289
    0x604062105070b0301031505131a01080f030c061f0806010e100e01050d020405150411030412110a06020c10050c070512190c06090b090703050d09050a03060f09060608010204 76
    0x1202c000c80e540f10401e40c41c42c0800e010007031403d00302c44015072425000d0f82205030014107070302c1500a040c0c520350b683d1411b40c4001000c0300707007011000010882e0f00b0043c064405801c00e4a00550b14160030046101e44442008140700101d210507480b1814044541600c00e0182c454030040310401d5840c1c00000f59488002c5a81c0c008940c120b2078085100315000440c14102c4401510074845101142d0812010300001011907076080304d4075045080702e968034003903d44100720b440d070701c070303689052509001c881144030080407400e000600f100e0465041c00024144141600108016207514015520506010500300030703040050910046c01204e00d07028004240c1c85100b0f500302d070245d45184a10f150342d07001c1d1804200313011000b0302c140d480d868020076003040064441c8900080f01092903454506100c420764025446038410901441004810170010303800807000d06210500d14504400200d041440c0d001c0207298503103a031308038a940c2e840f0341c2001080c60303404802406095112203955000750020321 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 981900782 1250 981899532 981899543
    0x40b0406080f1018021b0717010f060302030c13230105040f060303050d020c030403080f03041509080d1a040c0e030c09060f090702071a09040621030806040621 70
    0x200880c150383d20b03842d51502121414004109018030091541d0025000211a918400d000440d40d509080b414801400608080301250400c030b6010b112450071148044040d40603103250110610140c0d0303000485080b80c3c4030031502a44103082c4102074102400000d403401cac90701403c9044001e002c0744031440b0309040c1d6006031003c1114015400c40e1505580a0344005404120b08020310283d05040b900104640c01c41c0310212454603036030fa40c45484c40e03400200201c00031040801400208071020356030b0729030240f03c40d50078400201c0c56191040248562000c01000e0345d036407107486c0e084005200b106201002c000f40208030701040d407600a00507040d4002c81921a001d44c0c1c10001043c0341c40381c0100d00880c00540045220200c04050161442c80a080802544a0408000b98148440803e100c4040d20449016254003081c0c003408151980c607008000312050561500302212403040d0b280c0d542030b81514003454140ca905022400134485a041020030700f16009032030800016010070300030094401e0307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 981902032 1250 981900782 981900811
    0x307080304111018140f090108030d140108061302011715130e07031b08070b09090f0903091e030a05011a0609102a140601050301151208040b040608 65
    0x26041100d6400c59503011820141051005000c49a25824410000705010344981c1b1200a0640002c8446400341d001240590001502442c0314059001c0d40100500152540e01c141d41008615600c5400080141c120301d10b41d13a68030340070340e880303000c9420715480b01c401c4540190600d2280c7c00118170045501310300032114102803038080c10581c81480e05400521000e03005060a5030360700d440700c41c240c00003182c1d200d922a0000c11903840c1402100020803691040a9540e58a05d044c4145401c0007041c001221095800300600304102104a94640204403400300310800e0360122600c410402c405c020713405100b80c0004c2c604100d0150b020200511210204124541c41d600400c0006c3c86581d40071500f00e14044168120140110600d40140030390400f20300442d610705084001544800b9400e4840c80300103a50154001002d100940c007400b02907009010031900760070304410560192040b03d2845000110640a0050322004d542c0689038014050755140d541f01c000134078034201a00da552656110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 981903282 1250 981902032 981902059
    0x20406210f090302010b18090718200307030b0303030601090902090a0902181f02191518030f08071e1412180a02031b01031d0303070f031a040509030708030411 70
    0x881a80521a101c000000d04415081c4a40750100d9403034600b60a0215448289502048218103404400e0f14a00f9003258cc40c1d15100100405540c0c50b2101c0e24025001001030003210703644a032105068440401003d0313510072a9401080e002d9105a02401c5818800b0a10b403c0032035016101c1400404202c450010fa0030074526002d0340c007a0001d4010000d0b03440400c420680f80c80318a040392007d40624861813256074000c0f0210701707983c0544082e144400303103003192004064000503043c2c1d580301c8a207030035910b500d08510050304814404412264031420700f03000541c41c1340319503d41c5006203100701d443d42c0c54095400000c2a5030074255100e0006040e28031005128040010740d4401c4160014000c200c810002500030f100c03010950b4016040540b2000840000c110311100c50003440c1d903003402103640380381c5004010560f500151194042604120b440e000a410181d80720403c004122000105611420401450340c8120400100400800300400091081041307060145d058140c5021481449 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 981904532 1250 981903282 981903319
    0x1510062f21130e09190803010f170a083109110708070602030406110c07090e0a050a080904060e10180c08070806010e06121504020406210f090302010b 66
    0x7100c00b2070501a5480030204801481c0c0c502c11508000c1c01c42c107070f030185695429481d110b05420a002e8510704400001042017181030f50f40f6074024010110b13001204800391008030b4990080d41c402406104010604a10701000d1a6134506030710104180d0001c0043d0542070082c00201e81d00c224141c00e4500300c00700c52075802220480d500071b9480710f105807030590603540e83c90003904041c0050710103039a12003109250707020035001015401d09030070042a4080c83c0c00100416111500500c030b03402d0300051070003000241d0004807140c2440d0b200c0c50460300d906503503001c02d0080405070b10000010030107005000d103c00c2c980c071805040c1c0300c502c160810041d000d04240b405171440c0f11000340001c4c03840c81c00076031081d110b1800ca1381c000c401403421030340c2054404000390840e080500c404981031852000e11030b882400c010070f0308a00c28147d40550a0a150500140180000142e0740d140000c0017170698124022661200e0740041e843c00c410041343e8040d040c000d008180d2030314414001c0362148602c080140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 981905782 1250 981904532 981904537
    0x1401091407050406300b0901051909020f0906040b04080f1204030b0405010e100b01032a050a110111031608010f090209030f010c080601021510062f21 66
    0x1070301a29058580341c940f0204540103034403040050901c1520766581c007400072912041c005040302d48070012501032082402c105070004182e0100344103180c6c5c461407452400040c20100c0841d5140c0c0e50050300c031241c01c1c0501c883d522424200f2540100005400300d1079400070301c0a0800c1d99100401c40384450403120707115a0f150520a800300c3c1c002d1052104000007203100719001d42c850b01c22000800c3c256a0103540038941048103807418841c2e41c49460903002b55a00d4800c1e8a07840b80300c80c0c9808085082d00b05028030f28141d6815000c100900082c00c0d103811406881e41c0315409407058020070028542e9400303c1065041034801d9245e04200c0040801142d10540c0c40505840151140c40161450901c0c00d0009500240149406000380c01e4042400c6200303224006003445a522240010b26198000a0420800b04031480480c103801007449001c0c02c0b0340c00309406071801410721094040000ce41c44055100f4081004045072980b4801d00c241c100201e00208030640b12074002c0c1105400403002d20341c60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 981907032 1250 981905782 981905791
    0x40305070f0f0b0c0307050d09050414010b0a0804031b080d0501050105130509060406030b0c0406022e0c09030210090614160213020708031302100804120c05030c0114010914 76
    0x10707541000300b44103490500d0f00030a6080655003c0301d140039000d035225401c0c007201440203004202d98103030401c0181072a02072812110314040c6c40e5640ca604003281b112450243d21022070030443d0110018081501404060b40a000e4040b541e10842c40149086901503100361140c640060808000140950203441503442c1c0c81440030807081610705000a005c410340000f800c2c00c0d4440c0d1581d2001006c1100201f410f40191181c4003095030302c0d820315101030300e801c01190b04850b800c0100340914224030100944c402c50010044004504244407040484000d030050304040c2d80a9100e004104c001e5402001d0f0300125503054849032000c0350803da854034180541d50306092000e06c1c006600c0010700c0e0244c04410f00c42c0e014080142807858a44950711160400c5406000c5181d00b18404010751502036220b503103034800b518001140e40b60a07074845101e01800e010450500003405038110410400344141d42843d56100000c1184481412040005a0003841200380591404404501001c1c050b18540e108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 981908282 1250 981907032 981907049
    0x120a031d06060d050c061c0b09010f0b090409170c0105060306070c1106070c06050a0806060f090d050111160c12030915030915090b150f041817040305070f 68
    0x7aa52081c06110306040321410031142d0b40990507004c403241c3c0d03610b000740c0340c5170818a40040c4d1085981d100c010860f020700c42280d201d5443c5c44010032200080307200103001e5440321010345071038070002004a006000301000c028140201c4002004055600358064540421002c000380003a4450805154035180207684102c00034015141c0640498910940700008100162046103050030700d85440c100302245400580000300300203254000213a02061880c3c108a04641c864500156030160b0101c9108800030715004240c00d040003010302ca000c1d404101c64001c0c00300c0095480402015100502c100c2441c125420f141e0f00074081040c0360340c0704207507003042e82c50340f120064641054600a040815414808201601c8059240c005a058010b000904440520220b9440801d185c5821100c6008050080b0024508242031040d960240d604186040075100000c400c08a4040341d0741503c06100c0107804440c41c2c3c156610a400b840004000722802001030b980707140e88612521071407200c01d2040065 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 981909532 1250 981908282 981908293
    0x3051915050603190c1221361802070b071e03231503010606030b030304050f0303130920130608061c0b06010206060d111507150e1002040308120612120a031d 69
    0x40304502036015207444407124022407008d079507038000c1c0800d1043c6c105109104075004112281000072842241c1e421280e1403d150a03c03508070580c2c00094555014460101a110400070080c0100c068940702c0e220824900e0040c585444450011084400342899000750318105d80080c03074034424800d04078241d600901440c9024900300800c180e041f003030701c041c6a1600040004094200c12101c0d05030082c5000c0c800440c80c404400c2c1c008402400c0303028060b84e09102040648a0044540c00110513140b243c240521a510b903400403810300189101c1160810203040c100c42e05100319425800d100d00d109038216a050f6407031074280004a02e0752003004110248104942255140c21041d103245041c11416903401c011103501c812205491703501d20100c41550702c9881055211080c804d0100c0c40300258420743c0380038a0741d034404425210b0f00c503000e20703000f02102c08201715030340b60454105288a03c10840741c80c0020500c6600e51540f0003041c400210b441c0031038038941c02e90780110303821090040d50b0140a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 981910782 1250 981909532 981909587
    0x3020a12110f0a030e042a030b0d0606051e090a0f0204150801090f140c0d0f02070b0601171e06040f02071b1a030c030403020703051915050603190c1221 67
    0x40401c07e119542405068230f07001c4000c140e4442c06260000107000d940081003181c90003050011440801742c814046000710b850b103806580f0384034191a0085c2c10110001000d00013000804000d01440e082030182488440d6190649580000310b0b078182d44025a04000c020a00398541d001c54094901d0715540c01c09003000a118103503010f0141001502031940400c03041000c1140d0002c83c1d1050300d0440d4420710800a100302541d0103c002c003415030007203406a021707007000300804600c0310000329048400c428507400100180c88a0300f0070140c3c401d041c4801e640752a01458030042c544aa00705400031060b4100b0005203403c0d15500301000d0f500b644590394a0b603202c4030159481903000400039000c0d407048010010014030208410b020641004402c0210078090b40380406400518840b0f200a590500041c494160340105a800111040b14801149080c00d4a0b01c02c200190039071001c490004220260401d002082202c00c10352040001070015540070550300f6200812142102c10010300c1441c0402c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 981912032 1250 981910782 981910841
    0x2112070f02150904050a0615020c032a04061401021c050304030c06180b01050f0102071d06031e0c1804110108060607060e010212060a0303020a12110f0a030e04 70
    0xb80c44508180c0c10062034000f80d4400304007500c00c151400da26841d50340c00d0400100354012042080c07801181b014105403411200001e554040b80c00d0b1310008040601c00100c08100540e558094850006d4020b02460b40c2c0c0f03000c40541c1c135031042c0b082e5004d40200d45801c01203a043c08040e004a41864070b40c01d0842e129624103c640078203050046600c107030f0318540114001e201120516001d0300c9a0034421840d810401840b0050007400301e0241550311800041c041129041c070010510300c0720082d1074103250b489a0000e8039007620016001e04602e0040c2c849040c60101040f12101002e0507203805004903060000e1702250081210060084a201c6003096210f610800c00c45811610050005007440c9070f03622910b0494900c014408550303075000507103204404030382c07000c2540008200c444a10191440e1070180d03d90841850090079868802242081d480c05441500c1a034505401140c221800d01c0090316910400c0c0d103000d90200300098400e00641ca40750056200b08807001840005120310680d02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 981913282 1250 981912032 981912049
    0x4050a060501122d060f0f0b4c180609061b020105091002061e040c0e0a02040f031101090902040b0d11071b0e070203030408030f040c052112070f02 65
    0x2000304c441d42c40b80c081c0010900700c0c01165400003442c0d40015034040005500c90445800c42a04d0b80100f520b00320090103e558140f03c100c60001d0746417644566044005030061909241d4031a41c005041d1410b0032040030303400140441900c601c41e01c1c484981c1d03110380060750b644949205280000340300e00d401c030004407031465080802c2c900c18101541090900c4001a4900c101c54502c0801a80940b04009030050029580c03400d02c844540d0005150a240d250380046081c230303000e54810b190817103021628000c080d0b03040342c00030088118140c0c0b00c243c0300d10f004501900120183c5001841000d008500900144210750440d03c0001f402c0785002a9903002801902a4035084c5503140010302025000c0745c00241c200858a80f4510702500140c208a6610001c12000e000041151b03c00c0c42007200061030002203d81000c0c00704654141652103190540c8084c0a0380c01c5907410001103c489580f1481302a20700c0c584450480580d1055910703480072113598001d00390082c210b425060158409030412051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 981914532 1250 981913282 981913343
    0x40f201f0c061a01021c0e09040f050a0c050301050a1a1302040902030a02040f0f05010503070c02031e033a110c030301270902090c0f07050604050a06050112 69
    0x1c0c030079404001a15000101c036410b5100f0a15006082030010702982d0602030081c0c5140000100560300c0d4098000070000180040308038061803201001c1410701c10400a45002103500a003180e40440b9a407500031420f5040d803084601960800e404500212201d0080840013810140c41002c0900050100b0000b035941600d044200355082102040c802858002580300b158400009a1746034600540c1c00390110880d440b00d00000d102100c00e0225a0344901203d03003040c02d0b0b02d01202c031a200c9000080c10b00d0300c0504118009645104d0a08600b000480034210403507807020440038495803032960041020b16412007501c000390014402814592645c802c0c2510003c4c045164100304a0a908a186a000303805c800300d00b50b285c5c031481c400ca100600792580c1c0381c0806d0a0510096101c0d030b0106600400291241c2801d0802140409032842024203030f910361034008046440e507041504007030351540d030b4500342620110f00b080c0010640303098001d0720100c6540d101e10940800c100d00350800d0085482c100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 981915782 1250 981914532 981914537
    0x1a01030c03111215010503041e06110d1a0d17180306010303020a0203010510120215210a150b1b0712050607030f06050319020d0b040f201f 61
    0x161030008a9851002814190302d03c0c000100c2d00e030411320454151040c5a0030040c0c1045020400c00000801341110f100d8080303010108210b00c5000c510b802400787c90095806d60a034070002c10110340008490700402c5400d0440c4d981c110030101a00244680403241403400783c066008002c004006602c02c80c0201020142604098100c4000c040001d04005080e481540143d00013550301041d4602846520381000042860750400c41c50500c3c4c0b945140080500a031282141d80d40001400b22040101e548500c440015900380c0310f4009480308003020709891820210b46001405032480600030709400079107500305045030034000c00d810042120340c040c00c50303000c05005c0c0410009404108001c0203449501c18005020350349084080281159034001e1200405418800f08110b03d0714081051480c54202c0260740c9030280301030010604800c01840024a100c0111041000b80071821440107600340c4039802040981c040004480980044003d00c507501015044059500d841d0b0400c04a00c078a0090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981917032 1250 981915782 981915791
    0x1f211502030621071e0e010b0a0f020102190c050a0501020309010c1b0309261009110f101409030a0c0e090a0b0c0a0e0312041a13141f02011e1a01030c03 67
    0x1000015030501082c0d00c00d10401c231003c500440d9160b0010020218002d2600c000c608092034410080c00c030440b003102c4a0180118100d100d0f00344501445483c0d4080d4201000355030324100700120034000c114000c0c0540c00180d2005045c0311403050406103004080e01aa00d40d0100750811303007601d244040a814400c00d0030030407030700091880700c20700c1807614250801c1c600065541d80c60900340340f1650240e1505100e2041d100c07030380d051a510f01c002c4c07040203451442c1c606828088041134003140c3c030458007100d5240c4120682c507030030000000341e8081560110344800c051034690000040d078880389550f004026209400020341c1140016010b005950014a0a64110108213001c08d041140480d01c00704030510004003404000742e4603800791039042052100a2420203031003051060303141103006520045050b4482018103540744001c4007031288030182d20280001554070064000c106040b9410b560110990003800e80407814400d6249404c0c00c020310301001000400118020321019202c5028959103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 981918282 1250 981917032 981917039
    0x290c0d051f060207170d081f080a1407080f0307030c1a0a0b090c07050a0f171207021221270a0203061f211502030621071e 54
    0x70302440000400c010f4016012070741c02d200141c0c02d5849140e582000d598005401804a075a021460715408170321107030070108940e034a400c04907461006502c0b81a1a03c103620a1600b401100c50780b84040d66030010450311155a0349041541f00d450342e0040038190b0300184441c60100f401140e600c000b251149007404c0d403941d030013140207960170000e0340c00342007860380c0303840000c40e40c00d118400f1a003000c101c1030414100700d03031540c0e140d95402d40c40000502442c8820144010001d0440f40741c1190302c0400c1050b03484881c4040c511500c0141120b00b04014424040e0811607082a802210040e1908000d805000d1207800c55a50030040080c160101c4450b500c010b2500d10b15114000b8944034000380007501e0680c5150040500e031507805884400740c01020400c0302c50102c429402c507802c8562071544c204541e083d2512240c4000328455001e01240c0d07080503102c4004100342e0046d40309081c11900a00440c0440d130300034000c441131840c2c02c1e0481e0311003c0144841170707602040d40303c02da21100700e22481c82d48 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 981919532 1250 981918282 981918331
    0x60a1d040501270c050312091c0203010504150c08060a030201080423030c06010f0609031212050f1f0e0117070503030a03061a18090601020a0b04290c0d05 68
    0xc40410380f00c10241c0a00314108407000c0c11000040500300c0c001c0418070065088004e6601c92648010320034400c4051220810407003103103050126400400030002483e090900702010b60303171445142c008030300d005203801c01580a14042405498040c0030a0038450460780117540c00304000d401a14141081c081241c0d441a82c0c0c551200103440035809103480d03245841e00117242040607086503680540420041c03100503407003040241100d41080d594203046414034415076005504290703c4452a0420301040302150009520318007a060344445c0c0b46212280b541c81030340d492072a0042e844850607002c0108001e1803040c68040b003481256044d21400c0340d81d003001910f5a0b0001c04443d01182e10fa4100300003000e03640309403103071040d803080380f082c6040190140c2c078540348110410640700366680300118159034030800160340200c2d0b012a1203280d9042074201692001501114410b81e81820b0b4144011600c148000a000d482c0420540342004c0d1849403400c050080205151000c84204410741100301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 981920782 1250 981919532 981919571
    0x71b14060f09030607091a031504020f0c06040f11040b031b0111150115110703020d0309031415310201141c050a0603110d081c06080105060a1d040501 66
    0xb035842e22000841480c000641c6801a05080c0c19007c0303200134410001101048000880c1c1f2080445005a0f200e4003040b454006001c1c150308460f151199008220800500da401d00b00200c0c0202c010040d0395000d2070402003a00e0182400c540c2540006d44090502c4413282c901c260800f005040c1068844661036086282c10415000c0201d140e280320010010303085440955210003000c0d16101c003038601d107050059034030061480300a00482c003140c40142131510401000b4060b5600c188200e03846c0c00b030642c0080c0d4400304541490f4040003c0d4010401c2c01d80049800b003009402078030341002282456285c800310401c0d007081a81030242c030123102103c10800f40300805c618007000303030018400c01c019001ca5085074402480201c80d186440c50034000b26206008040e98000c0031642074042204600d000c0105002e00b070113009813005031000e0b130340c0d1010054005d50207a581c210000c04c09555244100300e00302241c0d100300c207203440c015002e080004000b101d03031540c030901030000455400141400344c003601 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 981922032 1250 981920782 981920791
    0x203031e0912010b0a0b031b03070f020705101d0301022a15042d02030f01060911040f0b0c012306010f0f020c060a020a020a0308071b14060f090306 65
    0x140e00000c40304030501c2c1211110b030091024500801411080502151a003006400303000b05010f400f2000980c41e10000d11584001c4a4554070141c503400c0c600780150844801110b080051300840802080301c0c242416010000b003495990b0480080000c4c64044128549040c1f5a800d035408000d40f650b040300305550100b111118184a01c10b55500614042c1081d80364804020017150503c24000420708100b419117420070782548041008084e00f6440d428480601c800035013500809041300c048d440194050340407211003000034440200c0b000008101c07031041d40243c400c2402113134020311071100e400020780304201d04d0800016039254000c000480c19007121020058016901c4104019968001034900360b503034180c10006c80e4150810400303920388280c02d0714940103902c003051080c1001e01c01c00001d28195000307030459030202d441c0c1c2040106540254004d45003960700030044003035000c00b104181c080300c0c1080f0704915803464410400025920000404100321828000300c01780c3c0c0d03410302005015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 981923282 1250 981922032 981922087
    0x1609021605030a110d0816050a031b02010e0c030f030706020c1204030602071703090717100519051609090c030e0114010e0915010e040606032004060504020c0a0f020303 74
    0x68840c0618502d44840105c0c00010014810300b40702c9106012a10318248101c6420700c507031a0281e413017044004141c01d4003940c02c0c4031950380400d4403e680650000d605c00e2070640030364200123440313410b15941d01141811030303229074800c001c601c0100703615501038801c2207110025101c9022001200c43d2640d00507030001d981e99070340004c1d11020440c041e0840540713100168802801d5203040300c240c81c1c40300240d20600036030f00c2c50300543c175508030360034414600d0115103024100814204440e45041900e40700c0f01503050ac03450040402c5515551507044030b00022540d59000000382869500d2000e0318446070507200341500c8000e2840c840c0b1b001e0007042012415808000500d41c034219086004030130203000014260001c0e51845a504501b40c440350555805462002e505e407907a2070308200401d0907500c0681001d41404c0000b20312420030407040d00032041285c003030000f00c4d1030b5003c01003203110b04551030746203034025071030b250005a0380f21441942c00d0008080d603040c251803009100c0480c06e8011000d40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 981924532 1250 981923282 981923297
    0x30307050c010b010318060c111506120307121103090d050c030d050f2709160f02070608060f01020a0215070c090614121c0806121609021605030a 64
    0x19081c02442444920311003480c061014201c0c01c0d45d0301101c1409044017402c03c980703030801003500a00407260146810340306021260703101010599414100b02c1910003c2c403955441805050000d00042583c42142d088000e4801c1c0301c494020603180d400d2002d0341e0746060300041c040c11065507a0105002070490003440540722181c5001c003054203090b40510314a080c82000d00c404000640b81606460610409140303207001e580f4044041d40218038603c24807035002d08900100f00d20641d5401e260148400907480b032203008044c10109a890b40384030b0103818006040300001902c0e40c80c00070f410582406040c010340d0307105103c03500465180c2c44000fa00300034402002808404100e44000304000070700b20074800700230717042c207007540b021208104a400501c500c110310600d600800040c4001020000b1409600b80114440c6034060490782d0111460b0b4860940c1800401c00c41c5004035560346090303450014101001e0500103141c000390814800302e0303c0c8078190008a030010b101003000f0040d201d441e880707282c0e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 981925782 1250 981924532 981924547
    0xc030f0c220f090f15050d0503040906080a02010807050c030901030911120304050a09140412090806010311131b0f180b0316091406030604090b070e10030e0303040803100803030705 79
    0x2a204000c5a02404c2840c2c6000300b92401180510780b8141d400480c0c10729480d00503400c01c680f540c040d6030044007040380340000004040c680080d00111007032007a2614020355650441c00c1e50a405403401c40c4916400401c00d401d000d6100754064038805102d1007d510700042c3c85400b00b501010000c102c0741e540d03400054140024501004545c008000141080c40b00c004000400c0b018040050002081c0d803c0075420f900c01140102980005441201c04540c5507603900d0401c3c10b2540a1021503a009034601c807030104180380d25001d40f0102c4c14045020052030031029008503600e0700d101c1c100d03604100e080c268241c0c040301042a80401811900c40030340e01c908104260001740141420315005100d9000302c10000903400040c0c83c8100b000841d515a207a64580d80401c001d40380b0301d040100b000b00440d00300610190403010102d480038007520b4502e42e42c108040140c040394145c12260303045a20038400240003e480c00010741c0d10400021142000303a554a807118034542098070f1942c0030420220703401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 981927032 1250 981925782 981925799
    0x142b060c0806030a05030d0c0c0f081e09091602121303050c010f020601090e0715120e0c03031c02041a03010603051509010603020a0215100e0c030f0c220f 68
    0x41d042101107000c1c00d01c4243c107540c0d170b665a02c151000416850384900707051000d640200d01441ea4107800c1506445001250316101328181e000c105101a110400f00d00b07044201c1e1140d06441e00c184000d01030010588880c04003107080040c036001e040451160440ca02c600700301c100c028100d004410001c0401d80703400c52a00f46c2c18000d01146e174038100046102411801907002442e5070441d00c00c520001020f0f29441c00d0f213801c0080c20741000d403040d1a541c07a004031156100b00d010030b02d000c0d1030700c3c00c0059200007080d168840c5070800c1810743c5507105110040700b4002d003606050038010740c56801444c0caa940e00308a402041c0c2c03401d050030703051804401044a59058065542d1215042410801424403000042c10010781030140e43c080550110f42c242e9070b1b500800ca030445558006030144060300d064010042c84441c103014040058501300c000c01d4a00c205182907a01416090103102100d80d104514100c85421600135a0000020100c8003513661019100380302c050142c10310209211420009071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 981928282 1250 981927032 981927047
    0xe10050108010504020325080a0b06100306050609100309140706170105011403091e0609070e0903030402010c0c0f03110f10092606190510142b060c 65
    0x80d0300780e9041108202c0103942c0440d2032200000c0c00c40c50b4001075901c0c14140d4003072160036000180f292240302c4041c014000000401c900c200c0c000c40d030100c103521030721204800703030f41c81d510480c0c0e08444180301080440c6006102c0c0c805c901640d15001178421440e4655071611074903070746c1c0700c851030304800780a0080c140d2180200110804808000441d540b4150000b0710244d4008410359000c02d002c004290100c400b4486c80d0405140707818a400000c024a034181e8403240300340d45140541c0b02c3c0050008001680e1410341e0710940440300a11304547e15500190b40102075140c04585002e6004400b0030b400f201302c4403000245000340d4407031500280e84001c0c45070703110960344181e2043c09001c241042040d0b0103040316050b1110903400c3e2035000c80c0c1901c1801070740c092042d039500a008079410050344111100c1002c0b0b40c407050200602445e21010900340404086000e85001c42e008035a2005160602c584042c1101600342c402c08071681c0081c210100b00385074090300312840d42d19041490380ca658054103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 981929532 1250 981928282 981928289
    0x30501050c1602090402010507120e090a09110d02060c061006030b06041512150b09090106050901050403081c090b15040b0607030315050d03050705060a050123130e100501 75
    0x241c0e40d01c0c01e44120850b00b510006108024811100080000c0c1164800c4040c1c03001c1d903074041c00c00142c1881c2d0000c060706001b486641c99004001c50000117000d58540e00030b2156443d08010721000c84410070f0240825480207140681c1c00ca18100705161031004100302403849490586914038109003018001000d4440c06c140e414400c06080c0028405075a100c0d0442c00c2605903410500d824071905441c10018000c419850140190406000208008401c0040054203c00c81d1010805d1780c1708d0009a60074090810002d000500510040c00060f80040042c150045c80071144001e401c40e40c03040c0c1c01940e095910860b070341c000000030301c00400340702070418040c803208440601010041c600480c0c15405540c0010b002c05888401121003140794a4496000d024041c0c00706070f9030b52171814050940c0e8450b0600300d88034400c0c1000108159090310031107040e20103850010920600e045504426070300c0550b0102c1d840022440031050000c458070072502d208104501602d880b8804e025210708850b0140e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 981930782 1250 981929532 981929551
    0x4090e070e1014032e090b0c0705060f0f0619030507231008310b090d020a02030a0f050c0a0303030c030b031212040c08010c0e0405130209190f02070c03050105 70
    0x141e60308020814100c1039202084140145d007010b0600300c40d08015100c0c0d000e018003200c0e00b9000b44007003039030140c0050440601900448020b6165148202440c1104442c1c1452504e000004504d8038a0005141c00f0748071209103800030b143ea16500c0c0c0c1c5081c00041da114091001210350079003c42100850911420f034400c0303074016812000844041d0005000506030b1031505000e04c103010b0030f0074155a940c155040d988404003550442881c09040104003941e0200c550b10a4414a113a070340d03c0043c6404140d50302a0180600c04403507601d08551006d034400442d00c42c002c04144074036649400c03d2007402180a543d000c1214100c0ea14060700300c2d0002401580a50062084103921752410021207000e41c44a003080b002c2a5500d007810004c10304540c103e0282542403084441c02c40b58030142c00e040040d01218204101d484848400394030740c85200009401c1701081001074010100001c0403181e0020681012620030740001d60007040ba030100030708a603001031155007841070100920810354032841c0c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 981932032 1250 981930782 981930793
    0x109050405070605090303041d0601030501150219020112141618150c0b07030b04060504060518074d120306061c02120c0306010504090e070e101403 65
    0x1529065202c00035400380c5818000c000030340703010a4904004440050a110840400b4000030000181c42458151086800207003048000300f030b041c841e101d12009201d080d4009009011800107000b101010960f42a81844040351004c5138003c40c42c001c01a010203030104113207542c504080607030840b0241111841c208498003929840b60451100d001003074034551204410481e50745c0b50115112a00c11500514824030030b010300c198250584c00000f20b00780116420320403107440d8000d01045402520509500020090148841e01e509440f165004815850010750100329103518854011140340181c954007105c4220718100c211110705003006004408041007059084109180d491200490108484100102182a6a4907041100c21404500800702c6104503600c0c9440002d40080303607401d4004149e40000b0b085e285124085910554050312554241818410707200e004101d080d0a1080a1080a5003c50951071401c880d5104a02c8090294041400c0405201c0c4049001d189280a603201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 981933282 1250 981932032 981932041
    0xc031812030201290d030c0503070602040e040507050d0b010e060f0a0b0c070801050c09060c0f06070c03110c090a020f070b0c09150403080712020a150c1706060f031305031809010905 80
    0x40955582c12140c061038810044001400c00d02c1c1542b1a61200030440c80c4002400106000142030043c480c50050342911542ea50740c50a00c4088a01c503a00140b411161800501c100c0c00c1041c0d02b01d401c20f0b00988805c0c1300420140101c0d8400801d500091040c0001090130481d10408100303543c0a4030b1040f0080c0141c0c14100c0413a0301e18021800300921076030003c5280000c24008001c00054101e81400311402c1c1e04040201400303e5440c1e9009a00045a0500740e4030403001c00a001c100b03444000c0c02400c001d036a80700c980070003500314001200164504101000c003040300300908600031030781040c4007903031824035600300001006640b10301c24a620b400d0100b00041543d00044d505220b8016020260300110028101c1c140005204000c01174419030004034002d0599a0007100411a19120403004d4400700d983d08040da44111021342d44890100903003491548140050340e00a416608081140c501d40d07a01d00741160032207800d00c000740c413144919010310700c1e1000d04240141075a00040009080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 981934532 1250 981933282 981933289
    0x50f0105190e16261905070801090e010605032a0a12030336050609010b1c080403021314281e0603080309010e0d0c03181203020129 58
    0x400030b002d58052a035800820300524040c0c582008840348980d11103095031850443d100c11040b080d40d226505c85440949014580100c2c03103264082d82c1281c4918a140c5c2c6054016000740c4036071011038072555242d00000175261810422107581241003030100c40c118502071030f0482d0200100801c64890b080044017081190316207015150242d41600d008240c180c109202c180301d025680f10300005140070f484000d1030300c0b210804103600d258416001d0ba803580c1c461825141c20303100c1134151254029000d04c1c50000c6c148010b6500c00059129210301402e040e0b585e000596005451821700e10f0303994680e01076070020022025a42d6006c1410407500202d00c40e41803010840140c005d5402c07011a80e941c070070400c442070780c030510003e050340e1420903c030762500c80ca01020035400966000c8890341c24030328190294680464103d0761081269544110071406807011030320308400f9282c65148034006040860010350403074200c0d4a581c040d030000704a00e01e08136440c4024400440c140403c000d4000e130250029074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 981935782 1250 981934532 981934559
    0x201080c0c0715110106060f0e12010f051008010501080d05040b16080c0a0b0c090328080d06060e090603030a030903030b09040302061b033106050f010519 68
    0x10800308415807980d000010a0749040341a400c29040322924203030016071164454003610072110880300078044107640e88000d43e1440710741c1c01610089507141d0084c000a0901c0c2d41c01d00c102d014124000704814003455031200031200d0564090340c4035412800c0902040809008030703401403410358010102d01c0c45148000305140202d003e00601010b002403092030700d20410a182c0c010f00e801422107030381c4004030006166070300a050001c03100601000002101d14101c038044e034000c4813016014114207114030051280c0703d150f1480303007203010038903000e42408a58001c014100320110640000707034082c10298081c01d011412612a482446020f040120300e807004000d440ca001010300700424046007a1030141c01618a03044103980101c040c04c204411b056000803580d0095284075420380e40384070b80d5101074013544001c94200040114149241090041112000d28072a6990040000b10b0304182c0d510b200345d58007550b0354207072040300310014019071030180741101000301d04115140f01c2524008010705020b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 981937032 1250 981935782 981935791
    0x3010305072301030f0b0a0e060f09061507140a0605010609150903020f060904020f0702090108030f12040812090705040c11151506070503070302061008061501180b071a04020108 78
    0x54403a90801030b49040b50300040c0180900800d0300f86ca0940788c0a2800c07440c102143c2540c0f10f0108170200a4041c28a005c0d114001c13680a40024000c010000b0a2889030380b140d0401c4a00305613866910100d5101417103c481d0480c460034001c1115403400000410000154120752800301842c0e80e400b0515422980321400c81e603043d5a20302c64011039000003001d42c02102c4d4215000747c000100d03406103169072002003401c84d10841e0310003000c0c0d80701c0800c03640d0703806000080c0550b000100620a4a00c5600e070342d0580c01445a18800d140c0002d440e014201038034155800b00342548520414011b0b403402d4002c40100640504d485c6010400544102d80d0703a0151160320300180c9000310100b4040840c44003100714211026001e55502d500030325016503280e00000064005011b45c0c404503011150f042d103007004551200c0014421a02d52052a00001241e1340c1030764144030140d003462a139003140c6070000d001002041c451540301c1c4424107011082211011001700310013280d80c1003000503a000140c0c01e400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 981938282 1250 981937032 981937037
    0x109060501020312072001020919050a030f0c181a01020f030414031002130305100b0609041d1903120e0601150302073f02060c0904060f0b03010305072301 68
    0x145e160420f0507990450f4013804070039030418800141c3d0080310150018241d0550960304a821140015400340900e070b654040d6588c4882c56200c100042401c00c082d08440601500f058607400356550b01121544e4080090340b0f54054988091482c40c054004040c1083d510a00145c050a02805885901ca01c950700541c2d59241c1d0084407001d403074404000b1040c0200340e90f1000c6564801c8620300300c03843c000f00c0c80126120b04ca2800e0201c04803801c1d02400d000f40c000506824102154042008041d042403e0f81c0c02c0303036a070f07498201e001c10001000803040139407078a0080c04a903110713814014803c828035845c080010b41800c82500303e201000030206d0444040d0110742030601d52482045029100b80400581543d000000801702c004601520201990069a504000c51303d00404c0c00b2080751241d4112000d600408001000c441da0640200030220000348005403480d01d03044061542241078001142a08001c0018000c100d0208100d801808031a168900040d4042280705055080113107150304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 981939532 1250 981938282 981938317
    0x15030903210e060703240302030c0103110702180910020903030d0e03070c0b0409230103151401030506180609060105061b030d200f0909130519030801090605010203 72
    0x1d0700c01903030010781401c90306010303540c2078100564000d024126a400e01d002c86140752400c04c0b03003119822904c2080ba64040c01400000180d08015002011008424001c2c004104060001640d503501c1c98621122a1a5000440c1c10b010030301c80d180041d03055501e654a4410405043d031a94001f007a91000c40e15140003040510800340254298024040c0c010711244400c0004184101d1400c060410390f480c1d4a4200308a88600b80c0101d14130855141c150b06001480005202060f0103507596400b1000174a000302d80440f049100c2c46662a09030310555280c0c105800f440810030307500585c101021030590003003000c1c1c00e01170382080e1500780620071070380b20703d17800202c1000c1d1010101d680c030f01000111040c0da40b00c2c10f00d0340d094030140ca44e0f2041e0915045046001c0d01e282118802a1148070542c006000e0a04600344284980a03402400c1c050b60450f100d008000040c9040040740410080d14460749548540ba01c1c01505035001038000c0c403c0f5909041060003e40da00000b0b54a4a00711001c1c901d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 981940782 1250 981939532 981939587
    0x6170103080927040b0f1314030f0a0e0f0a0e340815030616030510030816060b0d1a071814030f01051b0d060b07060615030903 56
    0x1000c640c0440d0903a03038441a00d4400034007403443e000c0b2880c4a140203150320406699182d4503a6104001117607500110700583d10003101080016001c00d440241e010304882c9040118031072140320703400903100d91b0f0000308000c480701d030f15042c02c82c14038000700c3c02a1150400030b0b050941c1641c184c100200f00c80c0d14240c04894842c41a084402c03282c090311840c8066881d2141c2c50f0400418144040303410007114501d20910f1981800c000500c80e12410449103405040c2051041c21005030030041c04c8246884101080800440c4d10400200003d40f20680061314229961900105a822010070300740f1818010003241c011a130b0b03862000440c1c00c8850140401940c0b4004155840101e1480b000308903000c0050201d000303000d400c0b4550441e9822000c030351010328001e0000c2e00740e03a41140c0300340c4658032102c01068000e040360048c0c41c810a5410012405944410102510342c00000c03040e64125218071040107000403400e2000f00845887c542400740280c6914090858100c4003100803246001d40c0520 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 981942032 1250 981940782 981940789
    0x20a1707140333030c0d050607030c1101052707050a051017010801060815150d0305071401050601030c050304050a02090a11030411040c02070602060f0411090916061701030809 77
    0x100c0207844200c03c0682c00710451203043e0406803080c0030b03140c000d204240540d8407520f00010351040c520f41c850002d189a0740c60480c120082e22890110505104594820760346180c1c00b8003482d4491003100810150b01841c50521010604000480103510b03040682d05100c5600c840da4080d041d240c0a5a40980b0001406002c58400304c1f011701a1118110100020035134070b4040d0000d00456080d0411952621040c41002d45820016200407004c82503800560807242804282880c01034000c0c1040f500300207444d00c03a000030b03482c1040d503903000e40d54810030003050b0340e050300c81e600c9580c1061070034130f0a40c40c1c5035940541e80c5070900c0c0c000e40b0a0702d0341c10018010810b075420a80d00d00c4101004691242050714210015400d6048903070305c1a41030002c00143c080c07000540300d0449a00c3c2e8020034040d100c0c60706c1c85200801c0034000740d4000c4a100780b0318000703480e1904440d015041c9000245245620759001141c400310075040f403010040e034045140c846103800604513055a41110b00141c0d40c04544002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 981943282 1250 981942032 981942061
    0x30213030204020a030c021011180103020c0307210809030a1d03070303020303011d0f13060b0d03020c1509060417010603171306030b0d080a0e13020a17071403 70
    0x354418000a030152000c3c5d8950442280c2130619000c03554403c15a000e490190360002d00b45040c81003084c000c2d142d8040e03460100002c2c15070107043c01840e101149840c82e0845c0e0014a041d03c0844000c98444107001100303551443d44e69013032400d9900c9082140d480c944910070622140c081000b06000400303040c41c02c0d145d52000c000d008040303908041ea02d2502075140d400034840c40070000745408400380c82c1c0e100069034038800c1f10b00c50300c80c1d0001c0d03544482d4900700d0303001c0c2c00c000c1c6c44640e651940f068081d2500c844401032030380642c000f030194007200000c02041d40050841041c10072810f2245140940740d0409072002c1d00c8000610700c05040c1c50494060043c602e50388050300300b1200d0001105060a6140103180d4000500d1500042e03c3d05c50009600b626160b040e54ac1d082140d0350046404510721001800d01a511450000c4024028500190200f04202c0d401000550300040601e0500d80215012030882d0088420208916102c0409081c4c0d42030216000e01010000001840846034140c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 981944532 1250 981943282 981943289
    0x111040e180304090b0306061503010e07050c0303070503191b2003030a0e1212010909060209120c030c04140406090c0915050a080303042117040b090d0915030213 71
    0xb22078481d41d07a0a0030b03801810404030024001d02850300400d290b410305410308a02e0410720f01c10075145910b030030b0184159040090924080000601c24040314440c20b00043d0300985040d5146a00c0342003403014581201c4004d0380100013189450340b421416109070203503000030f08040c101303410384450f1130b68855028424501104081d000000812138840c1e040d0740708038004485030040700d00e15150b00c020441c00303218400c121a41f805417180100210301c401c0d009001071a118020241c10400d4000200d10448044d200e404c00300d80005007254454102000046c2800d082120103120300402d45100301c15035070000d40040c10107038843c54407509010031b00c13459030f0042540c03210401c080c0403c0e1820041140a900466110386a5400f002a04c40303400400c4e82c2c0610f400c4070740505c420b004030000040750070b00110510280709140e43c00c018001c4840a001b80720303074080c00f031808407407904401c03090500e0400c41a0343e0501104141c00c0c480140c100b100c400b40319240e8200180c2d00d100200c515501c0103140d51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 981945782 1250 981944532 981944581
    0x109020a0c0b040c03032606060a12050f06040e1209090c09031204061814041e0f020714010903171e131205041d0c0409021303140111040e 61
    0x42c180010081216003003030807a40a596268404c0300d0303805501c40c1e2141c1d9084c42140502c407a0b804100d2500c2c140340108400b0b001c1c0c2c1401081c1194034401402591022248828000703400e504000702d50526002c0c0683c0401c94001804405604c0c40004000c3c0c01035091141c0212640d40014990a412000300d9452010080c219003c05c3c1d860305030300361158014003400000403c010078040080130711110840540d84c484094170f0034015182c0901000b4005543e003002920302107800ad00940c5054442e601c40e03004000805607484180d4180f918406280c40c150150f181c2c508203409000ca98041a200e0040d03400c404c06018944841d0480301e900840f10402d15001d03c42e4005001d948038000b44204079079807050000486100b0f00050036903840c06a4407800103040c1080da001d5260502101c59560302210b01081a0300b01a00c0d0701021049802800e14a094020304034010302c10310403450100c4407405025030080c8401140d4100c40943ca0081d88121180003590202159020114901a080205050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 981947032 1250 981945782 981945803
    0xc0c0f080703140c102303101a0c0304180908192c1201140403180e0103020d0605040201020a05100b1002070e0c13120b1006030b090109020a0c 63
    0x121442600c810030751104603801c2007001201040c4800128070a41c5080c001800080085108442030310b42030a100a076900e1041d0701c80ca415200e500c0c00000d580101122920001c0c01c0e0b040180070800b00000c07201020019009000792403039040000f0482d010303603540e1109000039881c030a0744000a420110f2009100c0c1c0000b01e042200000c901056501c0c4d5101907584183c86145a841c803c0600d0203105c1d480d000d84071811101090b802e181ca49450100c43e083c000085c0c031007030700c00c0300c0d074403010103035811000074002400f50b103140010b4004520180c4013501103c445540b550b40080c0134a004502e005205a03112000501503a000b40900300f503441c0c01c0802c0d1943e590700d038440d20004000c3e55419611841008228000302032001071201d058540d40b0401350131070b845241c2004219000030400582441700320f0400700300800b1250020b03555610450f100c40b00750406490a0091600b41c1c2c0101c0101458940d03a03e4141ea104002d6078115903030508016900e070113482c01100c1c041d841e2071020f010754000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 981948282 1250 981947032 981947039
    0x903120e03070606050907020d14161a1810181e020a06020d0c02040e01110c0114012c060301150b03060f0301110711011808010f0c020304080a030c0c0f 67
    0x8002064014030501d020000c01d03849100300111b000080c1e4400006a0001254008007405030301810701007070000d04100e0504203441408044848288011180e080c010300c940288150b100aa168014040500044842c13000d0440d4035650702e03880a681e01c00c02d45500707003010f4410010301d4209500b078100d0142003d034030346c03043c074802c000311440000c030300510900754005000c51011900c000c05070310a58883c440050103400f0007000d01100340046940795030f10b484c5111740001580c000c04040b44640004100320603440001c03801100140e124400ca908030fa03601c001d440c400d40d0074407400c141c01c5441403503280c1c8520303011900500c13000c1580c41034069201070108150100c440554441d060845a40c00d54816000a240c207a40c6040300042c403081c0140510030005001c620ba00c40450f104ac03511500900b1006014010030019a01c108100d03559080c0580020509018015a40d8080d000440c5001c2c44c6c8488a662521101c8000d8100001c81018000f0450684951002042c0c01302c60544050388 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 981949532 1250 981948282 981948311
    0x204140c03070e01050a0c060203150405040f030f170105011d030f0307051b09061309291312030c050f04090606120501052101021c0629030a090312 65
    0x2d540460100300440044891907100350704032080754540c5e41e16100c0358001591080060340001d06a00b00000d480380d280c1c541354807a403081754071075801508a440e078400c903824040c3c100d01101d01071504029080000c0314000080403800c07411a04280b1380114002e07004001070b5074100944070000c3d410b015007030b403c451200c1c0000141541d5405103040d20131b0b20303080300118240f59840e0201d1940140e06072000034400c0c03a040e50314203d04502100c01041540381a03803901340b210b46071a13106c29041d8554129200d20742d00d81065552010021160301049000d9440c1c400403880e0b0300c071000b81003540741d65804e400305210300140c6200001c003060480d01c0e50340780e8815001801e51405050001100000b91b0f690303880300c6000b4a4100e178405000c5a0807415500400c070060001d105048056640030420310b049808403130760380941280c0f42100020424100805e03904559001c0306044444a00000103440854030310088035001a0a40400200360001780340c1507400e24100c80144e11203c0ca00002c6008202 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 981950782 1250 981949532 981949537
    0x9030a170409110301080a03031e11180f09180106030b01151e0e090a061211030705220902030a0b0a2c060403230c030417010e06130204140c 62
    0x44850b003003400309044074005400300b400244900d61940c2d11258410f004070b0b009a02100564103c640c1d0981096480302004007139070307a01211114410300001d8903603109080003e5500102c103003103e003003003038010940000340400c2016121000d02c00c0182c0e03c00840c1c0308254400300055a0021122900350b07551498250000c0f030b50110380011030107064100e01c0c030f024000400c21740451240c0303941704119116000e111400c00c0040401070303078641d00c05010a6001000f60b555480324880c580304104403110600381414a10720f5842680101101d010248948569070054203003100d01d17090000e03100386907000284c50500c00f001c02408001d920010b10140c410303a50002d5482e82642da0030147c20801c6011140340880600c9041e10064200700081400284107201210701141200305100c002c0d23540460301c600036403000000d0701c0c1170350002a082000c0d415954001015804800003081501042c08013940c40d404020070222440f002c0302d012000710368466001c0040850849c034981150701c0c081c1100b502e540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 981952032 1250 981950782 981950789
    0x90102091302070204240b030c0d0e030d14010b0d09060219020604050f1501060e010e031e070e1330090303111b101e02030301030c081204050609030a1704 68
    0x15810112002441b100400da80c0c0300505100003081103452905000b4140c94101500c8007034040800c0001c2065072005009030003080c10000055a035848081d820070003102d01203018a04812a0400100311a004035426100c0b6981d1402003c240b10046203445802482615040d22000c004044a40403c990000d60fa80c4245e10880c210380300842c4450300b4554400e01c0c060480b904034000d00c014400c89205031821020480107041c000000300703c4200103410a8942c03e200c0c00d000b0098404800d42d840700700910b02c002c1c9100d581030141c42c20210324224075001c1046020b81040613000b01d070b0f1041240320440d1007401c00101c2d83c48016080c810030042024060f448140c0025292214a0aa915022a040b87d940c0740c50a6111403058080061044949800f8004800d003d051080700c030100d07681d4103c2000c207110a5000e19980c3d819803501c0070761000a50002602544a000c0c00c400c0d2001c000120750a032007085601d96190140d580009141409220000b4440401418115100303000000070300140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 981953282 1250 981952032 981952039
    0x150303110d020a051914060a0e0d0903020310091b1215020a08070f0c020a0311120a0803070804020f030a060b040c030207050601050f120303072a05030901080901020913020702 77
    0x4812440310880c0e81d07115010024003139802c002c10300381a0b00c0303100a030072600d1441000034011301805a40c400e4100b10040302c8a814281d10fa0519020a11003489005244003c90406841c07036420b5401084e0b94503c440c40382510f46549a92010600141c00c1e07606503014012030b600301c540c0e5141c01d800c85c000002013800321b81070801784c8441d0310b6250040c02913980d13050a0382d88070780c0c5565490702c003150b52040b0100100240300715901280c001d03841e04040440607500680302882e90f0f689840600c00400404555044240c010020090004098034216500040b242ca4400c1c2c0702c1e140c0780000350780c0c0040c282441d54140700c1c45551804121054111002c410005c840070005400512000d4060340b01d047d2004056030001c100600040c60140510303143c0b041c000e0103088840008406141c03842d8001d0361020081741c1c0038141c0c0110a51010000340e1060301c0d8585450107942c880c0c0d00c840d03680c024003c030381e8103000640c1d0014820380701c00d41c151000104028040d44603020101c07840f10080d40010740c140d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 981954532 1250 981953282 981953293
    0x170c0607050a0203070f12152909011a040b0a12090b06040c0302041d041a010e0f09030f19020f010507031a09040c050105220e0f070e010206130615030311 68
    0x11b01c12031400c4d283d0201d13000d007110a070100e4805d50390607214400346021440002d95601380d0f044001c0028005c2e10078900441d00c441c40b2038501c00c0c01c0100640c0d0580c40500e1101000e80200004032843c81540c0483d2074506141d5110b4071102d000792040109a096880c025107891070510900c041ea86800e4041c04080d00c04000701d1007005402c0382030384514005c20b14081c46082c030980314040c030500f00d680d01ca80600700711456a203206810810a80e030030780c00800110004020301904a00e8414150f4000350810004e40c0342c00503000d20401e15001d4140c0448003140301203a07903c0324a00170301070b64001e076684c50f008019516150704040c1c01020011400c090b4150070f2040307041542425840f89020310b40100018500b149000011111507100400c2c20020201d090521000d928800c07042c000948400503501010b440d0003099a8442c8100902c0b200c01c00040f1f4032401c05590700400c5140e00804200c2143d50803a03100e0600101824051400b9540d80700324000001c1416400040f9042c80303c3e2510544a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 981955782 1250 981954532 981954539
    0x21031107030206130e060a26070509040803011805040c050108040f02040c1107080118120c150506011205070807120e06010b280203160204060e09250609170c0607050a020307 76
    0x29601c180380103204a400041c00d915030f009402e1244040e0300c075808d80c100c80d40503456a0218840f514255000c58100c00040010f000414070400d485100e603119120400103803038551992a00da404600c1402e042c0f040000210341407141c040b044008554000e0018404d01804c0e907001840c550a50002d641540681d1402107100030041c000d4800410503207040840000c1d640e01d0b0081c40002422403101071003401003018000500310780307882c03221261a0000094602c0e10b0000540602030083d25a1402c5107404100110940c00c0384400f50048405d05d0041680bd0108894900074032403400c041d29030f44141c0d40001011b00f4078400400018404100c43c1c07400c07000e1400b00b0003886400c8410440541c20034402020722034100d04003410340b43d0005101083d41941c40d0010041d0100666405020f500600b03c4c403c10740c58541c84402400880030124280c3c80d103460002007a00c011401004900380114402d0002042c0410042020820007000d4503542c0d505807502641d524480c24049000f4014005d001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 981957032 1250 981955782 981955789
    0x806040c140f011e110d05030703050f04080a0e0427120306030302061302040b0616030e06090f300a030f020309010806040e01060e0a021321031107030206130e06 71
    0x40c801c80685440c40c2645410100e10504d0b0360001d441400c10104c6800244041c00810801c1c00015068840580e2420007102c024159031008043c1f20304800382c0720900c0000b40c01001201da14070814582030300c2081d5461b0004000e00094400440400c03090101c0c00d001039141d48980300060300c03c441140d00c070074428800b0340070b81303207035103c017402607081200028210045280c185281a1006100080040c404400074605401240300070081c042c02030500300c10981c0006801e07024000c00c490590401c003401e4001101e503003803461054011140064049201100d580e01c0718410516140144c41c1d010401d411640d4900c440101070300002c8807040345a20481c004001c0340c00315141a951200640c0d84c90050001500c90342c0049440d543d81c84d100011080b501d03c103464001d8008510160755095810f8003400d080c00c0c035801c580c1c408900c10075100300d00007000103480c0c41603505080c0240d8960349819410304264a692001c3d4010800252003c03080b205c0c41881000d684404d2102505071302d501050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 981958282 1250 981957032 981957049
    0x910030308042f1e1c03140d050f0604060312050703120c0c1502120c090d0b090102030a2d090c0f03150e010c0207031b0f0b09121f0203100806040c14 66
    0x80f16000313801108068460403c001c42c08082038001c0c1003070241c4500c111f586800703d0380003000295049a42d9020f2181404c8494101500700c8070858050080d9400c41c0c40340000d1000698006042c048002240d400301070283c0080c000e9a601072004100b08640210054088481104100e0352007401500c14020720340644240c0e4060844c40c4203050341a9030b80c01d42454150701074403800f517101d00c800c602d8000003403800d4011840f40030088005600c0e4107244052005031001c1c080c88001c9036107100f2099400c4142104009840e1249420200300b2000c4c6061448140009400007a100000050b0220512030300ca1015041642c0710502007243c403000d10112402c0320b601c0500000140c1100c0410800f141300b00c2c405041d000310410307400203442e0381d60100b40c0900260394001d0301801e402094041240c075080c50a403202d156014003802c4a09080e01070840c0c00b0b8008454040229400700118800301e100b000240c1c054210310049820a0822b42840d03140021144100201d420005012140500304081c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 981959532 1250 981958282 981958339
    0x91305060105060f09120106030c05060a120c030b030a0606050f0d050c040903111e01060b09030607050708041511070504110a052508040609050910030308042f 70
    0x1401541e428034080020a9204254010403d10140a2001705990344540840c1c141001030000070131514614029200805aa02240c41174100348644004560090301d10302e42e14569200000b02c14540d401d0690003054848240e43e054880c90604c1001c001b0140d2010703094034401c1b01c1908a82103d2820040411030144000300300e41c01451242001d8101500510441c0e4441d081200030001050340e501e1400307200d000d85608a001110050500c54400c0c856400a4140314405034600302a0304003080d903c650180c8503138208000094140248113006061b100070345501d0041c800344d081e1b2080d00070100d14042c0a80855801400702c00a080c1c50107200e0240f0712490141d80c00d04154103001c00742c07102c2c0c021034081076042e01ca00840c43c010303000044603104800c0c0315804598585050042c01001e06e103041d002180201101018040000e50b00700d607403000c41e549480c04410555440c0f07050030312118012455040142281d904d801d0300c0401818100d0b40316400e990381c44003105460103454011a0114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 981960782 1250 981959532 981959543
    0x60a0e1c05031c1a040513151e020705190813090c110a0309050d020310020703020d180e1314100b010f0509060d02131a030f090a0302060a02031005060c0c0913 70
    0x1d40d00d8a071030a19402287d07002106101c407031003016042e01c4604080c010350203420070142d03030703039520404031640d2410500c0499401d203c00c60501d401c540d1403a40d1158603d01c0b00c0f20340e421000d800c0303003040655030071607800c00c0b540c0454591050381c903100c980c003414a0b20311490109403584210180c914000840c40341c51601540c412074020f10301428060780d044001c009a03094019010301c1801000540014001540300f980103005a4406072001010f0000148481e01140680d1200700901690a108560040411411542041c005180050410314801c2c800203441c002c1c1001d034031140403a6805401c541e20281c803640194040c0d0003045400c1c0c800d036090b165200005004000340511550b002c2d091035408000c000c0011501c40403500010107080b0030040c036032040007080002e80d12424000540210082c4010121480d1f1580d02030740742c8800401c0d110f0b0003507020000410302d09a60101c18014038016004559401031044403d49444041203201c1c014508040400c03250302c1f800118240094210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 981962032 1250 981960782 981960821
    0xb0a0905070e19051504030b09030c070308030c0c0f07050103060b120408070206041e03050d0c0305030a1517061f05010f0c02040603020618010e0f060a0e1c05031c 72
    0x9004201e441c07641c3d40360202e80c004074184086080d88445060100000c84411080e03215440c3d0310300107014800080145030960014090000a81d0380040d941095980c8410100e440c1e40d1a4540300c0381d00e028000403140584a014401e03044e02c80701160820581d60f00b03980502c03580d510344540d12400d1103545030a0041a065000040104103040003408140d4401800245070542da221410b1421404400b8035440740711404040003001010881c1d009070740e40d50f00300701c80c495000303480140076030100800160b170954850705088001244001e44001400030f0007469207904103040301c030507600c900c200c8008e030003100c0c640481d04a80309000b004004540050356640402c220301041100d1048a91108981003a100c10011006a903000701500d10002030741e088074818649003000401c41e01a00c0c7c22140103010104c040c00303260f151501150501840303424030003201c804807404030307100340c02443c9403401d4030f1520800141042004401011400c010341c00d10f054400d0302c003000c2c100301d824000356801c910b40d21 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 981963282 1250 981962032 981962057
    0xd150509240603160e071101050105060f09031c1d030609030a210c050706201821030405011808100b0d120f1706030c060306150d0b0a090507 62
    0x1610485a07000c82c0203030544180e020403000c01c4803c01d005030004c40ea4918004108144580e0001c0000c40059440000780f15552404012030f0003841070a046918032500082c00340f0054404010480c010708401d844140c408128182c01030041c00c4101c0e440103102c04a2003203540d40d190000e907183c01b805025001c2c614169031200241c0e6250750ba0b20444080076240f80e4449900c8000d80f040a040110039200d031581d40d011881c20ba4202c0320700054036552400c0c98150012007295984c241c805a0860081c2800341682c40c00000304010350700b0748480082c242d41003011004141c080064012502d082e02da42110300c0d00180381100c000480d00900c0c1c040d40c031940d1101298101038012800b0708201400306450340c03180d601c030183d5070402c405816001ca807401caa424043c0ea4804040700721010114440d45481c104080041d498103520500e1621419021000c20300c60342d030347c40f05060070808040200e9551001101e045010301028400580700d0240c80c03000081c0d902d91030192030700c0b410032070fa204c8038200030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 981964532 1250 981963282 981963343
    0x2040b040e10030506090c0a211401090c0906050f06070b160e0907110d020c06040b0d150e06030d0e01170c0d0c0e0a0605041a07110d150509 62
    0x9250b6910004151000000300b002400504e0203800050080d04015a03028144102c0054a501c40724025041c43c0c40d91010308a07014180c84501d034055480701081c1c004e078030014058894040060080070f0207901c00100d000e100c0d800003080369030945124a03040c502800308080b9002d26070001c3c20140c403840014014054484040070b000c82d2509141c00311401ca84080303503255200b1107810012031014090305403036800400414030800303024070003820003071090740c04900e03140110300c5008680c40010078000303011400c94100f58000810a8a810701c41ca07500d968140c40c00c2d8043d54114001e000c4c0400220445220343d03a2000032101c11f0b140c3c0d06607151300c1c64100d941854010001d821406050210010640c424020300d1040c18190380e8959408450700100b04089040342c2c4211309200040004010103a1501100c00200d801d09507039944034002d50400034401d14240c4507550380300b100401200100304084030848100c0445000800036580c41c110344580c1c40b01d500e80c0c4155641c0840441054980 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 981965782 1250 981964532 981964559
    0x50a1823120d0c0207170a03030e0111160303050c03040201090e0601030e011d072112050d0f060e1b041202030307140114100b0a03020702060715021c02040b04 70
    0x94100d0444403401280054001c0541116032107200060b00d42c44504180e5604100c1080a007001c01600f451091035181000e658240f22100141031645a24081150345400c2d4021800c0702507481d0b603103664050005140450502d504c204070b01180c580b60114040311840401d9074880c0d541030f124205060300b01950752814500041515040540300d003185100d40c0c0080c0540010140342c0c580030440314940c54541d44c02c1c94420340201444081650307501120140b0700d00880b01c01c41e00301503021512900d000c0100c2e414415210700c50b020030308000c50031060401580c001012649602c500803040d44901c2140069410341c1e01d00000340e00c0003484148030716404244a041554402000c80b450b0a00c642e4842200000e80005441940d655070701011542c0052a60703194425040c40e0a14885810300049114034062900040b040580c041074074400c54031550102e030780154028000e18031243c0468180c1000c1d40c029480342c4030380342c03204540d40c5941515000b44c4082e039070b01100303032420a420401011107130f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 981967032 1250 981965782 981965843
    0x306050405090f121c0e0c030a1b0b03060904020907091205070609081605130b150a0314091b01090305031306020106120b0103080d1d0d031505030a0b07031e050a18 72
    0x24060040b000d007c5950421089440d03500c038203500c00c1002400c2000c41e00703080855202c196051801c100301f0030b140d40e480000c2ea41c400d9040725020507985440c0b42c220b401d03075016085407486940401c00c0c170040c08000684241100c0081c4e9403401115201d10312030b42c41d0140c0407042004031a00c41010f2040380b8240020207000076048a0000700f008112001451801c0c0d0f0b02054170703078504009a01c001c0150f02d03010702c3c140201d040c5448012814041841c0b0795600400c03000070301802c01070002c00190317841040100d00540c0c202c001c0b00d8940018401c084c901d214030380700301c0016629142001400740d00b2190301d5100c054005840080340d80c45c649802103582d10401c000c0048569402030468100300b100183d5803281e50790b20003405d001c403817018040c0444041c907040342c0008141c81d004005556000a1803450281d00c241c441485480c1d0810a4003e0a000300800746203a4640000c15445a29940810f20a17490158140700510300190769092503950440c02401d21030441990810f281c8004031144a10f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 981968282 1250 981967032 981967061
    0x12060d08120903131820030c0c071703030907061115100902040f03061808030402010e010c0c06030c081f05120a06090609020906040e030d0c0306050405090f121c 71
    0x702101d04d110b403441c1c44910b40040c98845595940c52011410911400c00b6050000e14000c89801c44007101095a010050041c0c104070400200102104020f0040354024094183c0c0702450a4482c1106030300d0345c05c202c50700e00344c500c21042c0000b0128410344000c2803000b0850003505074801590644004010010881054510000000141441540300402c0144000c4415000450451420f0310075500e003d514003a070b5a07090022074010900d10801c99800650900306221202c0410b001a1003011100700c002d44110f0300128000390154240c2c100044001c0103903150700881d982c104441200f03240c0f00e05141c038500c0b002c0c14144541d041510100c2d02e0080c01c04110f40d10742c0b90030303620784085d070718a02411641241c48101d100e00310300340790035810b400c100111828800c411041854680d40e0141440b900080303034440d210040d207280070b0351000d00580809481070180d0300c0c03c0100c984d5100303882403804d5090301c00c00f034542e02c01d4091501a0b410300c0c1403001c0d11800c511220341c4220058500310000001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 981969532 1250 981968282 981968287
    0xc0c090c0a0c051203070c03020d0806030309060a03090b150406062105090f010204031a24130b0312070b130c12061d16080106080a0f05031303050312060d08120903 72
    0x40c80c19013100a14404d030465070b10b4410341400c51800a040600c680c13140c41c01e100c02c180500403d642e0102c01c2e00d000e00340a403415516513490b90007c5001d4660081c01829800c000014855613100004e400c1842503020b45062040382e6035420704a400c100d80300c48090326540324501e888041c00c2d69401031038000190310103d48d800d00041090380d089038482c1c0e004a4404c416022019400b180700c6800d5a4403550783c504014021005010004a00c5d5005105501c1a6450481c10881078a998044503030300c1c0c009001c5440344003040555540b00d500c52141a100e169042c07002441441212180810b010340c0400c1e41c4c00c000d45018401d0307642d1180980c0881d0000d440c2d480765201150002454500b01000303200401805501c0a44690440c04a41040c95543d04148003030101000001d1045500b50f03100c80c8a00020200e4200942503018020350300c180c050728030b00008184a400809400c060042001031009a261102003250340d400d039140007080700300c0500001c640304030700100d40399200c8404001d80f403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 981970782 1250 981969532 981969553
    0x403021320030a0609060b0f0d05090f030a02060901060e01120b09030f120403090501032013031403041a0901081303120c050d0f0e03032a0403080c0c090c0a0c05 71
    0x1ca107034000712104510745503118410050200d86000f554010304403039805c907182c00340c1a403201c44c1610850460201c025194070200c4c5180400700226074480700d500050b01e071079485444000b511104165248001582842e00115000e1035803645903040325281000032021050b40d560b000c04c4520010f0182085000501c11040000070400041c01521690691f901c1c044c030300751801402c030790719a0700003504240c036001200029084040200400100350180c83d0303128000d1721000491140a500010302c00d040d041c2240c030a504001002c1c0051b10158907014100580755008030800c1d0042e1408640050b00060200b1842100e5201034200c80e8002d19280011320104401202070707810142d0b074900010000100c82d40f6244440c481c0705440d6406401c14001c000c0484412952400050700800c41c03c80c2c1c03c03408031070154902e40f0842036492401075454445503641041d520307903000495610814051018a1700c035910b40149090b214210400d0150b0500d841420101c1c0c0803407940344100c4003803040300002c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 981972032 1250 981970782 981970841
    0x71b03020a090609140f130f12050a02100902060d0c05130303050405030c031b0907090e0702031306030504030c20120c03160312120f1e0c0504030213 66
    0xb4115100010548501e001c0e2680c084503042141015000c9103502071161030604c40b1140c1d504061000d0702c1820105141c01c06402d1202240002014241100c845040840d0030402909004400783c082d0b40100105c411010309607944404025841034041000101c00f902e1a03000a1a8061a14040d0f007480921800712074803038029001600807400c08103041089240c05c1008a03070141050b4058400050401c05580303284030300a01c050b01c100e00740c0d000500c09510458006000301a90203008089061803078000c1e40341e5010301c850031540c400c442ca01140b00341c080c1c0517180c051036241d0b0b01c03000002c4c0e058840d90b040301264140c441400074150202d0b565a9603190701110b11851090107003041c4401c030820140360000c1d5110004d448100c0342d03010008a403c0d07402d002200649030500d91034202c02040c110300280328048080301c500e40307040b40500300710280300131840104009803410800000401c2056a560040740b100941c02403040008071407101c4c0a03045520400c00343c00b01e8400c01150f05000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 981973282 1250 981972032 981972049
    0x140a0f0309061508060714040311010201090f060c2c01030e030904062601060501050703030c0e0a030b04032d1103090d0f05010b060412020d050c1315050303040b071b0302 75
    0x1a16081003500ca05004c4000e06000c0e65801c0b0b6070500705400c015042003c2c24800c1c0c061480098104015072580794190b9000b9040100c2c1568002601860010740d4074110b002805803180394000218101c1c0d4408034004035200520300d104101201030044208000118050045441151010702013802144041c2d1154020b00010700a91800e1948000c240c03842c0c03241210090905294a80c18050100101d076004011200c403603401d850301140044842005840c0041c4007148640c00408020300001804451f0192340e000d01e1081ea641203050041803410107800d030040025003104100c100350060500d01076600c0744440614802030303d08000300c110004481004681c0f003035031503a83c1201d032002001803c1c03041c0e04018404640182c2801d0a10369040c0c0c5d012600c410090080d14007144040600108010310100718000800400e501c8511103a16800340c1244041940001c04424002c90240780102c00d8501755041c00c038045007003581d140c40b403079040100078042140418110a010002d0b03143d054a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 981974532 1250 981973282 981973301
    0x50d021206072d1b0c030f210206060913060e03040b041a0414060f0904061e050409020904240509012306130b0301060806090a0308010501140a0f030906 67
    0x3540801d01c00300c03100c0c400d495440100c00070f074441080000c032072038182c002c2e603541c0d0030202ea80c50021500c00705150800e0034940e01c2c1c0010703064480c29107102c1d0030000848604d040b07001c02c25200022400007403a05903581c4c1c005459041c0d00000c90000180f01410740402280154080c01c3c010400c0d01c1355000c841c2c01c503480740c2c01240e501000041c051120b490040c2010703002911034043c01c0c1c505803070b048240c4200303203040c2d000c14814940001c0c821104421141075412010009004010065070360715019810400707891001c00044005000103001d1400303116000a60f500502a1130181e03a0304d81d40d40441d4115201d0181ca0b03460268035000c40b450712841040d10030341c3c00100000785c01c0704501154100d540400f9404500058200406c0200d86602140d440c1e01070103644007040348250200081c1c01751001e13402046903031140750100289070394001403500509002e0b0b1601001c0c1c0e6214001110260401d01d8030002e120403c00400074000d04c91040380745070f15403502d00054081c2e02551a030042d03490091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 981975782 1250 981974532 981974537
    0x50112021b06041a010e07051309050a14100f0b0705010213080c091501020c150c031215030d021506010926010b010f2003090904080d06080313050d02120607 69
    0x408100030030042051850880600c4a88541c181d85046c2c8040e05018004240030100600421882d000343d5035182013034042c024000c001e00181c42c042c40d84c6402000c405204040035110903000c01e500e8110500b4801c256203550780048000c0341400702d03031a203aa0008004807450f6508015811944d0320120780d00f00031b84842000380c40004189010021003072405003504440640400350440281c0e00026000b01c482c000f0740b149500b50501c10051081801088400d010303d000004007e11115200210148114200c60071200e244c07581a007850780c0c4075070000701640035074040085c440e825420807030090f600820514208205584900f2746006000e4100d1032001e10340f4064049440d148130070b004a404407842803034050580c2240c00c200616a5038207401c40000850203151845050a090003121b040080c0601f001e5850b04161502d8502a072145d01540403407490840c5c04a48010040b048801e0a00c07011110a500da040004204104010b10720072644081c5006070440308807070034020b181c0318a0154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 981977032 1250 981975782 981975793
    0x91701140a020306136e1503120c0d0237060516090b0f0318190b15011409011103220f1a0d0e011e1508060118050912120402010324050112021b 63
    0x45503514900bc0890f0031304015500040b03100c0c4032003e803203054100300c41180c00e8a0048103001c0e48543c0c151040001001c0c146074101420420b07003a42d02d1400b2004044159a001602c3c1e640301343c0d0000d1402050100f103540e04040021500549800401c0e40d06800502c00341d03901c00d80c43e4140307105024400c010858503400b204007046600707045298003026400080c2441040080c90355640702c000e200781c00030241403140701d081c1d840b440b040800580b00100803024686032100d496200c2c60300e6400b5640f141681c6011001c00c0032a0901891001004001c01440381504040b0301000801c040d1200d211030346140e6584403070b00d0a01c2c3c8100c0200002507111000005031000700f0100b81061019076400c12426a07000c07c00400954000498907149131210040001f200e40f00c00358058140b40030052086403090300450240c030103480c0c08040501482c402d0700c080002c103408004052100c24a00201d040031a20341c0f0040250b07500885240c003800422400c0149000c03c4140d120303100310070140c3e501c07015a004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 981978282 1250 981977032 981977047
    0xa0801090509150609090c03011a0a1e030609020409051603120207030201021002160b0106110c0904030e010c03091701140a020306136e150312 63
    0x1441a1508016a40064009540040c400c01c2140301c01070200350003000000001b81000500b4080d650358900700030006d01c01100740c10f100e070a04007507a41d52144207520300f1000044844594149032001c04001146c8110a455511404010090303000705a07041038981c071035070f000508113110071030b90704d503201468a001c1803c0d403c00a22103100402c40500350741c4400000c2c4050317030700002c1700c804074540c151000d80c0c0c031032460852440709d0b03014090040102d00034a001040039030f00f00d1100c0d200c00c42d402c401c5030b40b0109a0780c00c0018090060381e000d000300d00a90500f203102e500c0303458052100c50090420b0412a540d42c0d040340e6010607a110b403c00031341d660740e044a12140000405540000c0400000e44c258200440050304001398441440c0c41c0300d94403202515480b00002c41d0360000080402102040c3d4401e001a540c401c2d901d042081c044122410f45002441d510313444464581001d0801010485151180e22440400a0040d410600c0030400c80c04582c6d4041085403540044070340d2441d113030307200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 981979532 1250 981978282 981978299
    0x403021507021c021e01061a1b0a050f100c09090e0f06100302090a05100b130515030414070f06050a120c090501020d111915150f090501030b0c0c120a0801 68
    0x41e0540c41c0c2507590500004010f074120340c801022000c40182354080e501c1d82c10001c50316114038040c2c0e50303140502410082009021011407191a0042e01105483c80440c0115200c0202e804001b08100032450000051144103229400360800700250011a0060b00540d00c115280040c21920000e1206150000f44210700f4501d08840d0050351004003031115042c004505611400180114004110042558445607180504c1071000709409080c49110420510340d0110ba03034012202519100d004810a00c68401d000880d501194000f400c442140ba050450440d6664080d800304000c10404504c0d019190380180300f032040210441c0ca9080b001c0f8900800a400c00c03621f6800c0e0410b000380140d50004595010401c4d0b106142000380484804620b4500302600c0c50b030008082ea400362a0007200300d01004500140010f07502e100b801180d00341e0b6258542400c4c0c490134007004000b10401030201d07403000c0150b0043d1600d014950283e9207205102e001c0c415064101c60001c0c8001000000100134050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 981980782 1250 981979532 981979573
    0x319020111072630040315020310080309150d110310030b0610050d0f1e06170a0507091515092318040606051011010b090403021507021c02 61
    0x10200001c1c21440c0c0144411542d0701c181c001c1c90b802c85410302100c403040700070b10104840107140d0000700042c04c010010b5010000b5080ac4512020341d054622020580365400429200203400080c8444d81c070a400080310502e6400c190000301c19a9140c3d8104940005641c0c080c41c403526610a00599292450404118001c401382c82c4034066806200b47c071070040d602c0001c441110b00c00b4074010516183c0381255100602a81110703101d480003914007080d2510b40b54000404030360429490110403d019440c0380c2d01c48804183c0103000768061070b82041124450380022203020624019004071968070440039011429104144001801d024024003e099949103c001e0031014602c00d105042400d002080e0b62100e9030000e20030444861002404120143e0440c201030b07c0080d022079480300d02100082c4c103000141428080550030801c0f03103459400c2190481d132060f60075500500d04000030344a030750190302000d030002c000c5004540c044c0c400b17a048030a185da2491925801002c101280c0d400d07021948 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 981982032 1250 981980782 981980849
    0x30906180306010f0e01060309050c1e03010f060b1210091407020105010b07030503010333060f0e100b030a0f0614030607091a0a12060e01030209100302031902011107 73
    0x200941300091000741d19000c01035044d0340c40e9041c002a03006d228180300c0e107000100184603600c17961005c0044a403000002d00084898400da000340040811403c040e410749083c1d00803d0200881401120210f400c2006840d401090568005403129126082103041c0d031052001c00e50344100305010701010507424800c0d40d00600d2000040d41c2829560b580c014401d00c010301c0041c01441414104403070300003800342c00844100a050604020903013a40841c4090300003072141c81c01000f02c4160000d64480c0c101c0040d03216003864040300072a83c0c207025400701c2c2508050880500c503130f034420f071400100103140f10751805802070000000004480e28201460007000403c210104011a1020400c07279070031442d20045400c0304010740391034807146c503001c0f184005041400b000c0c1c04d0412400085012002c80d03071a05032402514030143d03030f030b0740c54104044410091100a42590000740f1090201c400c20184080e540d02c141f5040c502289081140c070301d0640303960442e80c40320001c06102d941c00e00000d00c122645 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 981983282 1250 981982032 981982049
    0x31209070b04030f0311011b030606140915030408040b0d06032109031103030d0504060e0d020d0c0b04061b030c02010b0a030b061c050f0708190b04060e03090618030601 74
    0x4203070851340e480a00c5090500020181700c000621018081000e42020490031404c210b48000726445180080207031240d0701c12000492980104030b25150100d034120303094094003800c0614000c0e0340422080c201d030301c01032055840600c103010220b02402c001d402409400c070580c030003207902ca0950400e240f0703407000c0f11010505410284030320b044460700501c1107021260405400c80840e03003c000880d00354400c3c5010f40000c41e14040c2008108840c981c03242c080305203144120344120a102005903943c8103040c2e41e07000413900e03454202c00003d442200f0a94014400c41c0081003007000e0322022401ca4131040200004651035034080302c03941e13509209603800400101c404031501480c64445c8881c99002400140c0202452580c50621913a440c0110805c6980001101c3c1011803024591f61640c1d45030203142080d0140181c46d07003620a007407150403050f17904040c411f0340c151a65554280100181c00381b80c072141c082070280d02015602c82000d422500c0e424404000040001802c0600708081608603848 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 981984532 1250 981983282 981983287
    0x60209011b020913050106090f020c070501020303090307060515060703030b090601090f0e09150115020c010201060f090b190801090209062b05030d0c0c050f010524040e031209070b 79
    0xd40c1c1c902c035a207a00130040c12105280c04030703142800e41c0946031680003070300d000d8140040780f4001c01c5154001c1106040d41c0c1d0a5802071501e135001280c41c1c0c030054a00448c640d2040c00f590001c200180d000355048040c00050306601c40d08000404c02c40d03002020140c0109a561070040e00c3d50414840d4154040700c00d28150800c40e08107990355410310054010204010307090340014400001c1004150340c13419020f06060a03660b55000c4158890b0304041d1428014082c202440c00b0b294014003452041d50341c4003000302081d0b414016075000030030b040d08c0c03440d90080a414405488880190010015114480000c10152424014040c07801c8004e40881c1c0260700140c3c0d503083c070f0096100300d9100403460400300304000200341000e03840e500404072400c85442c5400c0c40d01c50210340102e0038000c4144254140d5010705240d0308080d080702d0084030100c403602d484c0c11071030520b080030004121301090300030000030f2003400f0b000d0014a1900400c0d00c4169503079904090041c2d8420400a1200420038800e9451 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 981985782 1250 981984532 981984587
    0xb0a0806030606010f030c090e0103080c1504030e0f061216030606020a022b330209090f0712020f04030203190521120702061f051c1e06020901 63
    0x70001e21205c081d5204040c2c0d644840c04c4828400c004078070007055264451001540c50b401e000701c55a0049a5100040c031403230010007844051440858403940e0582c0343d943da210003000c1480b65000b0380c02d60b000d41c000c5003040030201c10302188014074007484040f0901d41000300e0400c03004d82102c010340c200d082035521035142007005994032440c1104c0c0250005074010045070f2203e03c0001e20502c0369000342700b10b07114540c414590a401d0091590300a40703005400049640c1540e1208901c6812965900004004c0005041c3e25007410036541221041c038114000520900e8100102c1e04a008464040003000408100754a020000803400c45030b903446100c880d004c05d9450380e07940d00091001b01c81c140c0030b410a16445d0f4500d18107031048655001c410b03144038580304800075140d49086561642c40e010075040021140002c0b0f0801059070005800b501a40c0c60700c095004000c50030301801c5074a40c00e40c1030214141c403469030b0389280042c8105070158841050500242004c1d80c901c800040320f000d5003070180c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 981987032 1250 981985782 981985787
    0x100302120a15200408030304030e0604030b04111f09050312131719050a031205090a06022206080a050f061c020a05041d061312180e010b0a080603060601 67
    0x11032005441502c0094611801c8031804a03a0040da514952851408140042c490300301200840c03149200b95a007240e5050740d84200609801180009414404080001f600141c60080068080580140084401c4890045080c8405a900104000140740d1101000700d414100b10b03904514800646950a08050030030b0750410f214075200715a42c4110341c1811407880e51040c40700d45514a90900103152043c654105142e5030216074008500040c0b0500b202d0721000c01d144140740c041c2a112010b0324a01040e0345a0201039089001a251040300300300c00200c030f503115560361078028942900c030f5000078609081030104941c0000e01c0081c14540c990b080200031740e5241d40100d41c641100c41e214850540da400802c03404030b003a420141e0070034942000d1100710482090548544c1306144120b0703c00740d440102c40202200740303410091801c0c800c0c0d15140006402200052240f10309202c004081a41c1d1307100907031604000b0b900c401e452903030018410f80e2543c0e1003202c0691090040d002052a0700f080c1000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 981988282 1250 981987032 981987053
    0x50a05070f1409060423010212091005040536041e03050705060720190809060712051308061e10050d05070504182109090203100302120a 60
    0x70038040100108007400c5030340101c425120b07150b1002d440710341c0340d5880f4065400c0c05140d06c0320002111240082c0070003d5840000c4001c2003032482c41c00d45e0704014400f01401022044002c944007404010320020406032618034143d140c1c84041189181c0c1f004100c0c4401e03031080c400e0309200c07031805111820003022401005500c8001c09214141505980c0703107040c100c64a00074104000c101d8060705040c000b000d6030203940982140c2052800036040ea044a1072284d4800d0705005002d6001c00354840d800104005101900b60110090441e9150071166034a640c0c05659192080003c59400304008803407115441420000d030040c1c2c401403030070f41030580b1084000342c0140482e90390612004002100b03045c0d8120210020079000e004041303868000e292064a651050103580c0c042c0d40f62141c116161000103058188841d0007030005002c0b0216038100c0504581180c0002c005c0c0803041d0380000c0c40007205d200035881212001a01c600aa007148100110321204c03141d101041d50055a1500105042c60744 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 981989532 1250 981988282 981988307
    0x415020f21062b15021207020105090f01090c09090611120f0a06030209040609060b151c290f1003050f0903180f040b0a0b0307020f03180603151203090301050a0507 72
    0x544184c10a5821100c0c0d01902c03d00ca54402e201c0e0355041403208050b01500018045d52a15064980100090101900302e42c9400070140c01c00250840c01c2046803216400426918055000840c000b002c1c3c0280c0a44e03680000c2880c0600360058040028031101007030760325006400b00b042070090b0b80c034540001782482c81c0500045c062594641d800007c202044d440390750060405030016490418450b55030101d41c02c0252940008440c00d66880c04002a80c031a01c3c40008498a1207401c600d441c410010340e4070a00010b403a0082d034481401e504070b41d183c3c19800b225014036038010031645000d2101800040c4007610b002c185900c188951003600c0c44150300c4640201055030480c1552000344001f40160042448154000d0449400402e00840d240300451141d980740d005c480c048441400010341d284542c0360032620401041d03c6203242442c2c078000464000b801e029030a260f01c40c8400001c4c0b244180100720304413541c00028030340d03041c0c1003c0c060643e03c014000b031b0070011480c12400103003000103800d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 981990782 1250 981989532 981989543
    0xe010c020a051c120f020c03010c0c03050a140d0209030c01090612020702030313060825090308072406051903150902131803030b06030415020f21062b 66
    0x590180f1106507821802036007001c036224202c25844006000013103142c0200005004504412078103050501400780c010b10b041e41c901803864081c1c0c40813202e60b040100c90008022000590300e040c44d030b06102600c1108440040180d0311295041090300d00340e400b4200d54184092600e040002ca50828103214070780c10a4100503946034210310019086214003000f250402503041750100da0140d00102c0548141e04008091070900c0c00202d40803000c8605000000024403030f81c0e01800014104d40141c420343c0d114000d4065038010710304075044540340841d03014031170a61b140402c02c0240750440c400346165442d0b8040051150468598580003441b04130309000031600ea03040f41086450700e1501035401c0760240d900704074011182c950841c801d4013448054000904104c1140e0441c904501102d010302e138810710006049010900e401e000c3e41140140b006408014019001c01d603414001d0514101750a20f140741071441c11038108203102720443d100000e03000e800304405404007102c065a1001c0b40c0c022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 981992032 1250 981990782 981990799
    0x120c0206060112110f040603050609011406130305190606090b030604020402340b0708010806130201110d180f030210180b07150c140d050c12160e010c020a05 69
    0x404004013608500112100709440090340002c900d114101400c16a40a07550902c020b4030740c4820030007002d40a00406007070003101d10303009505180c00700080039800100008445081d0352625000e003440d004440c808542c0c0404007218040050f50f105041c042e00060f0810000c0d00c404201203503442c0c030010402030241e03a00149540456510200303c0100c0c40810452801090385400d0311074461041202c100c0742c1411800100300d17254041e200303803410380b00e001c0e00402084c0e88100d41000c05070700c0c4880a9040c0240d0745046048020184440d00175008181c5600c40c241d000c9000000040701c1c00e500142103a1301010040c0010b80c3c0364051004924207501d410395011403506602c11040580d07030320640000c500090120104203000141044030b080d50070b0108043c081014007030750000703500e0344112240d5004100501d180b0281d5840250403840031400c4900b440c000e03d445110440090700c0d5101070941e47c01c4c00805a90b403040d03604503501d09c00c0c604a2079140450380856640440c40c001d00c3c0c4200d401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 981993282 1250 981992032 981992057
    0xd0903080904091707060c1b08090a0b031e010504090b0117033609010b04051002030705011103161707120e0d031a0612010323011b120c02060601 64
    0x2d0350081008541c000440403044030416085030000e80c080042191071906210b04d03658454020080c0e021016100c24007a505d1420b13550714001035510024003c0d50010350070710080743d000c02c1c1c080a188154030700f20300d44402c6005941040c3d0100416440203100341d0400c5064000102d45d13100c1d160446046140520142d030f02c2ea5281400c602441c0c0421828425130000041d4081410044901ca148a103500040000c80041030040c032090902600c850840b041204110a045c400000001e4604501c103032418030180c2d80d0f415094403c081080c54804202109000d10180c14806c0038201c00001e00300002c51043c95808006e10900060001d02070215030440c80e00d410405412004a213010f100a58481d014855070141c000e102e4170040401a80c041080c810701414030703804079a0610b100010b5220340343e20710350b20010510101c06010311202c0e040c03061000014024012844400901c4150441c14400c0c075400400031849442c0c1441114100101307050450380204d010754001c6402e00c1d000b03902c03c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 981994532 1250 981993282 981993289
    0x41103062115070c060f0b0a0314030c0a08030f060a180b01111e0105090c0319030c080f0c1009020105030f040c1502010609150602100c0e04110711030d09030809 71
    0x212a03a030400c0402c00400c00003d0755120a40480091203854200b1202029080600c11550942c0e82c8a8104068804c24408903642a0510045115110840c0d01c0e0840c40c03001603003458269030007103504400c0881804207141034543c0956104005582000303c15280c10b0542089030100c2c2d010781030065454050401c5644510721140c204800c94049488000050515503025070799120310905a511b41000b0032858480030880f91500c03d0300500070129040c82d14078808840001013411801d125141031075070b002900c07000142030720480c6204007544031100c1c0c44d0715905004401c3e0160724600d240440d0040180e03027010560341c1084600221042c56030f41d07450009040802604041002c0c1e24401c1c40303640d526070542002084c0e07070110303d0500c14042d80c00040050040f1074087d00c1c001d600044011031003804a030344050b0040179540360510340000c0e4034000c681240c04e540480d00348044001122414460329003c06000828150024268130b044007800600704225070000601d801000603c4600a58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 981995782 1250 981994532 981994543
    0x70204060f0b21010b0a18090903170c03070507140a0b09010f1a060712052503020d08040c1a07050102030f0106170c03010506031e0a0b0411030621 65
    0x741d1000e001d20300035103490070310800350405800b000c41e88403440e00742c075104070034070780e1441c1201c0025800d5424110b1038802030b81d20302d0140301605e1031001c6130500094041c0c0d03140220340380075009491b80d81c0058810300003c5034980b4010102250040108140310280c0e502108445061f50004080030401105900d260300f040d01003100034141c00b0f2248144001d091066011040e001c0000d8810480100365680312034030300380c5040b900380d84800706200030008100c1d800e1015440101601e0300d2441c00d81c40304014000c00503181d41e041400b00103d82100105501001006807160039410120014a010341d03c0441d240382c54007840f849140c00300c0c100f14121801c0802e682c2480c4e4414005c2d5200d141148070056010000d01c5018009240a200a1600f103c0702d05600d006c2d15015030950701e16030170b0030300b4087d01da8800b8180c240a1b00c06130311074120342c0000d80c440502819020700d000c00c148514004020981d4140c1c07210200031442041404156550b00c5030143c00da08030708159028200082c0601800c01d13 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 981997032 1250 981995782 981995789
    0x22120e0301050c0912070e0a2a0513050d120315090608010b0f0d050304120212010207051b040e0c0405040809060406021507050301060e01120e0f011e050c03040807020406 75
    0x40d820b00042c070020800e82d0015240340342050794031001a02446003a00d50700e0465224007290f00c2d6030718002c5801c01e4001d40000d012200d000906568486a0301114030203143c010701b2000c009040481d040b14a81900d500360001408121885800c407003a548400300321820150200003031584d81c440c0f1080c43c1c50601100030050070590030800410b0394406443e4064102004100e200740e1034591034085501d0101a85240c1a0300400110300301414203c0802c00300302040000d0b684144100c848109591007400101105841100541071019903840d60f03680c450144d4100700d104a08160b0300c42220340000070081d0b0340c80401c55000c612a00c41d03041400040c4101b50340560041d03c000380c046a40f0b034001175940d010101e1020b03894070594032030008441c45d0000f80146000240300d041e240e1001c1d07100e4603601e0342040150a00054107407044060314649061150141c0e41651030b000b41402c80800c030700c00b0001182c3e0414081c4564035204410320700300c1c40010401082c152021550758290346a0303521034800f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 981998282 1250 981997032 981997039
    0x30702210c1908031b280b0a06180e01140714180303160b06040603081801021c0309031e0807121413141209010c081e0a0822120e 57
    0x9680c0142c1349101200d24070010b501851007040400f091b0702c0301c0ea5070312000c5800c48007480c1c0b4003a030303d50b43d443c00c94a4000d4010803409071503060205200d1941d9841c2c40c89021408800190464041a0b0350b09448030b04a40707000005800c402c100b031154000540140703410b16414000d40d229460303810721040106141030540c141c4800715040340200105200e00d0032580c0a41140140c0d5952501040140c4081d400001c050300d41c207100f400c807441c03096944080340d020140141c038015200e29150060b048440c540d200c0000b40c440b6411401c0c0750f001040d4041c590312004100140303c0500030f01500c4888041c00f45d1040100002000e81c12340c1050f03020300944001030304141d04a042c008280c41662190308402d580028040d41070448202c0b0015204148020712111182000c107540015031b00385240e44030a64440104220348005051080e8803c080f165182d210340303480d1228004c0040c454000103090039a01e1101030840f0f5903410740b01d074240c0c101075070145407030010305001001200e01d4401c3c04100ca40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 981999532 1250 981998282 981998287
    0xb0f131103070201020319090309050d020103091a1005120309090c0c0706020705120a02010e1507020a03080315060429040306021308010b0118051c02060c030702210c190803 76
    0x1140b0f42c0c1900154000d14001a10000500326022140211082d00758002e01165401c0020003060800c4c60143c0130247c0141000107114109894500c080300c90308040d565403243c1c8804100000500303180f8080942030030f0307030407451140d51342aa040c2c0c4ca1050001051146085030002481c0054034800c49a003076003460b00751901c0c0d903940c0c10003039500c21541c01098850250702201e03901d00140015410705140c0c050b52008080c15401080c42a02e510941394520002800c000202c090380320399802c100114402c150161766450b141c080e840008000f01ca00354481e6004000030410308082041c035040740d0424100d582641510283d85040d5440b030307503000600c5180081644032500118490880484032410000d1001c441840f004551003041d00c10541403c81c0c854105100740e051001e00f6000304942013000e030280d000c1c15000211140c0106510510560001541200310b00f480c81c0c64491070f400342903180a03a01204960302c1d0f1609203400005000300c40d00110601000004200c1a0040c40340c0b0040ea42d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 982000782 1250 981999532 981999541
    0x303063c03021201230c03041202101515050702130216060c02210a0207180f020f071a010b190c0c0f091a0a05130608070620010b0f131103 61
    0x44c040c1129a411480050000d59201c02e40c0c1c07115441c0ca80f0408a450041d45155526076a14960001304040d03c411841603e0402e40141c070144100c554280110a0240b0348c3c2c0d26102d048080e00100d04010700401c04180310f25001a1101c0c5100800008480c802507114406c020620014000c441c03c050010350402d002a0005600030400525014120481020518026070340d000700f482007800d10001a031180e83c00300281d81a04c02c500d0b00c0d01c82501030102c2d92603d10103c4409076041000944416803001444008212001e1040d14a18001540c490328640c9051032405140c0150000d640342c0310307080c4140202c502d1240c40c1060704070354001c56041e916504c2d01d500071400d155501445210528140a0001d0b001c940d055050324500001c1203051114242400d00004080e1801610b034a20b881c0e0001042846080c44a800a410955070386100c0d03841d1181c5100c1442c1030780724076a803280d2404485a400d92950088e2440010083c1d4079410780b1546011a0f40091100b6416034800341008014072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 982002032 1250 982000782 982000819
    0x151603121d010c0201051006031a0d06021201060f02030d0c110d0e212d010501090203060f010c0309063e011b0903030309140604050a0303063c0302 65
    0x100c000d10103180c000c11480510f224243e080b1142950301e01c000c9000307584200001407080d000251079002400b0b20070070711445000400c140c0d107000101120410740204030780524504020103240144500c0c5800d0203058400b40e030180d124482d01990a0300d1507240c40c01c048609009000c129840403644048952200b88482b008040710111440361b8411580c110f45408051107820700c0c50035010b07121001c0c1c030066050300c03c0d155444507030300401d0303298100c13940e0f1000e1803a40a201d298020f0580c0e4074096940d00d806002c000d0b1005102c203c0a050050050b40413000c2980014410141c94441c00c0003a004007035009040011004080024000031b0011f686a041004002100c050010010024450901c040141d80b84000310182504d0020341c0284007040424846c0c1c0068121034042c042c06450040803214450821008540c1999182c0c0601254010164103218000003800b11035554800c0001c0e00c1960409554098011000135071480d00c4601e207400c1c40c1c0b011030000c607030003040c5000440404200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 982003282 1250 982002032 982002071
    0x20c0307060506090a0b060909071e110d031a100519090306110306090f04150e0616080112030513082401050a031203090f12020304031115160312 64
    0x20f140030344c8400000c00e100000c20f000308400c82e0070042503a0300702041c2006000d0300b000020b00c04030402001941c13a130180068218003070280e184d142d842c1100034101c450010300d0003280302c2c042000c05181084e01c0c0d500d422007201180e614001250107420859940c00211002d00490b107000d030141c080c1c0ca01250b845a084183c050440e031044400380082c282d91400003216000803240c1c1074200d0040c5001900f0b1042601c0600d0740710f446030041110f080301307403000751044031391090382c94401c0e40c000028030048030400e18402030342082e01c1c600f21105605103003094046041e080001024820049500300340000007580304030180401070119034180b600400c6a9000360128041101c5041e0040000b0411b420b054400500340d03130300505294202014a20118005c1c00d0343c4000740d8010150200000009507150500d40220f04260b00442c0c40d2400e5060401c00d02000c2e00e01ca920905511038110401c050900c00d0320340200c0000304603d0810b00c00c1c10107079611102c40002c2d1070454500070307078403126a102104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 982004532 1250 982003282 982003291
    0x112230312011212080a09060c05071b08192103061e0f030b0c1e1b010e0a03140c06070c030914010c020405061302030f0f0726060103020c03070605 65
    0x3a89a90b642d500f0190007691100c03902511200010300762103451070040190507000b1141400020310314040e5101d8000f02c1c0e00001042d400034000141301010700060040b01072801250710b50307402d11503280c0f014a40d918040558420300780020404a14180045029080503082968824101c03103068424024014000d034054544a41c4540825500088944803024291800f50001251050854950082c9154000d0140e800444100101d0300c00a90820003075160304911101151202120010400661650118403586070315008500a0080000840c402c2291b01424140c2c200020350a0001892060071442c41181c4104020310101c1c5034000301070940f2074000da035003440090f00e0f61001403c3c2c80b60480c502d0700003100204910090310b0164040d680241e001401040c0d8202991b450340281e0704111000f20110ba000c0c420402c0083c00c0403101a801066460400e40c10001c4a141501c01c0c0d80313005407500303640c2180d000244640d000f58116032610421b8030817241c9030031080c940540600030031107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 982005782 1250 982004532 982004557
    0x1905041e061e081c18080f011a04020c1b0109050306070e01300f0e070905010f0605070305030c0717030115020c120706080a0b120f01051e01122303 65
    0xb038005034a06000c51081c04a40402c4e482c0000ea82c420b00040b5541401c4074914403802c00c030f00d00000741d0500304001c41c00004104a0020138044c01c2e48420720a07080041c62058016401005903a031f04003800b0070311211a02d085100701511a40c0c40004907402082c41d0007054140c450315050180d40c6401c4804007018000907a00e039407000000c0c1d00f035900954917800d1201c481c4081c0c1001c50b200100e41b40c0020000390303007481d00000d404060f50744051600e05290720030303c01c0c6a601d60044c0621581c0c0034101004e081c1d1824501c0c6003039001d035801041803100800d14001c2351001305a010400085018221080441082080c0c03256181d620342c8401c40c2104142c84050301c071380d0b801c051013400d0200300c8603d51420350000c1d002903894440309844100004018441e25a540c2810112990390050314200c0d01008500804515800000050860740050503d2004112034000604d285a40c4189030741034410341180c02c07a46161901c1c140e0050886002d04510100701800c49446c00c460000162085043c1007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 982007032 1250 982005782 982005839
    0x5010303081605120606090409060501151704020a05091515030702160807090f0e01020d0c140f0f1c0908090315040b161206090501050f1905041e06 65
    0x1102c05030740ca0310400f442200300020003000144140340c40809850440000342010841031803550344d001c1240c10980005465011042003409031a82c44411746203540d87d100c040c1c2c50b40b030034240c00003420301c80c40b481442d21604030400014042c0080c00c07809494804080d0541c000d820000c100510580c00440c3c503c0d005204421840524201c00e040400c03c48040c00083c0c50503078100100c40e8060900c030680e80c0800764881c841d0747e00c03e0300300344010b008407615024001401d940c0120001d00c1d007031104d0008c8824060030b2000c80c03071a00100e0200d8022490b5042a07580e03501805282c2c031440840700104056042c54012000c0038043d8000c000c21151720220140d504d105c1d03200401c1c500c100d2065070701900480c0d10000088809500406110400c1c1c580e0815015031158840001d055032030726041001207a4407100108254104010044001141100c08080342ca004100c9072008002920900e44079580322500e4440300307015011818a460243d0b00144802e58840701c03010040c01c407007070880f009488403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 982008282 1250 982007032 982007071
    0x1050a0f050c09010914010219080703090f180f06082401050a03110f280311100f1409060c0f0f191212050a05100510020a02220501030308 61
    0x301100c3c80800305844540103d400c1240c1c04600d01c020105140c150b200342c441c100560b0700b12540b101c0c03150707110369000c1d0395030794207850020300507910317a4015000040300301000e002d81c03002d18031494a140d20001001480030b19180310203000d0001c9500000b01805010b00085144100c0705803050f070a01e80c01d91106090766240700340101000b9922014000410040001c8c2d0720303140204004008020040040c10b01101c01c42500400c1a074081480304243c9641c1c0c0100108a401c0c0138038003c0305001c56000c0340046540750080c2a614543c2000300800100d000e811a003100108256201000d01525482d280d04607061140c2e0703150011080031605209142d9403000d0b0702d030002152003211940e4081d1604501550790303240e218a60000461081c81001270741c01004c10350920540b80316220740300c4041a2803d00030034070043d070051900654000c541031310140001c00d0300010b9454859034190b9070480c003411070b0814002500180c024a02415080000000c1810740c0300c180d03a40507000158500100425 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 982009532 1250 982008282 982008301
    0x50a0903090e0c160203072115050c1606060e0c1201080120030907050319110307050a0b09010e1201090b070e0d02040e010f060e1006090b1b030c01050a0f05 69
    0x102114403400b80315003040000005010486100c0c84c840c4090202e9280d2515810f00d660031000003850141e244040b10000b106105c82c1c0c0e86400c842081d031080810850401c100609032501c10950708078807010702048142d04000e0180d0280004001d429124013140c01c15110301e09040c1e001c1616195090094000803c1c0f240d010b01c00c8111664044011203900491541c21101540001701108950b0191140000b4240c80501c820000951800051480c0443c146002232804464801e1030340603900424003401182c84081300c05e4103503000c1d0380c0040d0701c6480010040b0341c204401c958140d0050480100049280415000169a10322880c6078cd034003503a85103c11a030781030803100041d40c4800d940b04040702504043d0b002101c02034001c0c0000c940403c100107000141c4460341d1010700000c41420030402d24441200e0400c0c040c024074500401c60506d8a81004168050800e152a01e01408200040340c40d4081048640141c1444000e100624002103944007e2174040d4003000d1060604000980c1d422 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 982010782 1250 982009532 982009559
    0x50a0f080f04120212030f0402100806030d0e03010905120316080412050d18050d0201110702030a061a0a06030b01030f14190e150105030c0406051021050a090309 71
    0x107520395000d1550340d0b02d45039101c00440845010003540a0354000040c202030b0280154441c00e14010300c031820b400e140c818043c0500400d0102810061400180861560089031081d080c10f403500c2c1c80042042c480001900405446030002c0c000e1080c01d010080421b208005980b141200c404d0180040780000001d0395a40d0341140c0003071001842c52031180d08940140e000d0541c4480d181c0300002c03010a040045082e1000700b1f02c0a45103544801c080651b40c50b424042c0a24a0f0071800d0010b051285030f5000c070380d030780359110300040ca81501ca800d14001c0c40c0f191500220802002041c14400645d24400980240400b24145001034207008072941038040364040c52402884514280d8955070310000520030382034222601042d1070ba12603100d81c0115101f08031081e050b003103000850886500d480c04040c58800c4805441d8080c2d030405c081040107a68290651303a282189041814655070075507200943c00c1c1070101c0030102d9602d003000b40b000991066201100c4144207488001c1600d48601c0d2603841c0300b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 982012032 1250 982010782 982010791
    0x11092d0108060d06020f041502030d0e0c0a05091902130e15130216022101060e0114100c12170a06030c05120c0406330206070e061207050a0f08 63
    0x10743c0c0881c4400000d1040d402400304001d43c1c480d4504168440480070a079041d90b0b1180d10050703201040100e211601c500c500c1040c2e10303c8000504005c03070079802151025086208681c0f00c2e060800000b10b11001050140c10000740b2400c00b1551480c00c00145107800946004800d40385a10b100014010301042c09004944040200b007110701400c0b401d003040281d80f00354885183c01c188601410010b0300c0c2c1710340d20055035160488031500505054a02070845807158040c10b0301040c824010040340c10501690350300b42c06c0c15a400440380e09640015504a0540c0d01d00402d584507481c1e03044901a0b001c90801484618084118016110031061006603103003404043c080c403030700711000c00482c50300c07040c90070f15280108107880083c09803100003404c0b035841340d000d000c20010b040502c0c5d10982e0408484501c0303007240062103003201c0007040025641d0741c0c002c00150920a03a440e1092003a941c1106a075480c2c00d00c42c0040c0c1045c982008010460f421120f540004180c0c01c001070828540259400da115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 982013282 1250 982012032 982012039
    0x3060c25110405060f121f05040804060509180108010603060b011809180f05030307080c040b090402070f0f120f0203040e0c030619090b0319030c0611092d010806 71
    0x40c010114100401408041c001617404103100d10b1a14a0752281340d411111441b00401a00100b20080c80000781c52000004588050381780608100010b041c2400341c4050322090302d01103440304a17400200e62036400d0b01d03291420844414000049a401c150030190660744610300502c42c2031164001501c80c07031400e0b24054000c50f0441030620003004594429588074058030383c000042d180c6a00c1d0340c0c1c198650190142c3e100d410010410505a82040ca580d40000700701c59200e140600e4505d034803440780108503d00d4031458002a030f00e0180403032503840019a542202d0310790350500407407401c205500384032035040d00400c100c0300440382c41c0c1d0700110941b01150f248480d9100b0740c1e903400c12240c400e903000401d000d5000e256120002100f4030b20300100c2000c2c007511000091003124400405103080e69030020440b0689a6149400019074401400c64806a2220f00400e1443da01d894040141c05001c0d0380d541c01400c0c440039103001c0500b00300580820002c510383d0522084a000c011107603882c084803111380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 982014388 1106 982013282 982013303
    0x90c0503040b061002030f0c012909060f03031803100903020d020f01020a0f050304030309060f020a0806030c01020604240515040e070810020708040503060c25 70
    0x200000210349000c403404c44200700956030f11590743d040b22644404507a02c80307540025086403901100004829105900c0e0101d14903540d605403140611502c800c0003c20314501b403628030300700c0b041e00160145152614014441c01191801d012403905031141000c200c0c04503c0034414081140d100ba03019202c13125141d0030080c031700301090f200d000140e40704000304541550004600782074094103081c12500c07543c0300c1c10140c2c01001480000741c8690308000c0010b010b045654020900315203103464070307440d6172548800c0c565182540030b1001d0141c0d004001203808202442c081820040c03190b0764402208504414075000e0b100280c4241c80310007510360702c58800d4501401841600403c1100402d111450480d85580c1ea103403401c0032800041d40040c150007400003110840780504005001c136803840c03d06000078034055210202050088880a071303405a4608030381c0e001164550414540e40 = true := by decide +kernel

theorem cover : BRFrame.Cov 981834532 982014388 := by
  have h0 := BRFrame.cov_init 981834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 981834532 ≤ n) (h2 : n < 982014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
