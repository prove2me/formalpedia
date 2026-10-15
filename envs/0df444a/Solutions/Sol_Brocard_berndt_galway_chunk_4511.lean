-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4511
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:51:34.471498+00:00
-- url     : https://prove2.me/submissions/f8d2db25-ec09-4680-9868-072c1a8104f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 811151079 ≤ n < 811330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 811152329 1250 811151079 811151087
    0xe030a02121614180a11031905330406050402030f090d09050d03030e03161202190c0509090a060612140a030e0105090301020d09060609150305060a09081207 69
    0x802d1011800302c1c03003240007054440406482d002c5400f8003c210b1045040a1841c2c1c0301042405408038000320340328000070844440e80401107006001e030b284001c1303821080e503500f80d0031604083c208662202d40c04006420081041c155402c8404100041d050340441d002c0004005040039408260040d00100800c0781c2c0b00c015401c200d100c3c0c54410140e0f04511803021003110702c100d0f54014554031511510221021900ca81d1010465087d4801142d2910ba0400554641c40d52441d20444008811007520242b06a042c082e46403912404d9035180340d804129074407480305802038000e00703000710485400503080d5801082111b00c140c0d00304c1d00400403552608621541d00507954410785500e5101410b0307500c5200d00007000c01c441c81d010358420f0307049105580111500e0b4402c0d410254159000d0206640c1e902141c460a21703214869000043e40900c2d19086e181600d10607407210b07510603000241040800d101046246c1d2103019690005404501c61810714218052100b50f50810642c46080194490308 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 811153579 1250 811152329 811152343
    0xa15020723030111090a06050c0a060209010323010303030c051e030c0f03010b07020a0605190c080d1109240412021503010801140a050105010f08040203010608060c0a0e09060a060e030a0212 83
    0x1c15992064087d84031941540e05d07108082d61601e555006844680c0403550702e5010b001080c030140741c0031500c0090b000150100d184880502c14504500c2d4004004060301481081c0380c1e41100c0c28280d003440b500d068408004000410310484035503000000518060107401140c44211209002a40307a50b10303030241c604a9085070500301d001390780342c24011601c9401001a1010b8214031100d403401c00e92400c030111110394806d84111100b850074090b04c88010b9040c040d03591a020448281c54948042c0001c0007403036000d403004810b48583e280100c80042151108039400e2312007004014030100c0d151720101e907048102c00342e0b04034150300c040008514424107401030a9400700075003541c1d0b490340394050041c0445000303100f4139001c01d80040c8503202842c0202a1981d005000400001d007540d6202c0445040003030071241b80214010005204041c0c40d04083c11816900096480c04418134000020613005241030050350140030701465407600b60340e804c024450030326501038038403100242c2040b40c841d50341d10303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 811154829 1250 811153579 811153597
    0x1b200f0304030f0606060813020d1103100b0f090105060403140a1e030f030b030c040b011412090706030c020c12030d090803060a05060310060302070203070e090303060a15020723030111 81
    0x10500a0029403940b01c1c5003e20300808c2c03480c036140c4900b091a0700b0040014142c0d2001c0b140c00d119210200019901441418403001150501149064002040001692861389002d00c500c844000602c0b65803a528150313000c1d240c4c0840c084448600c20040680ba09030b4640e00241014024074000f4080708403142842e00c15442512444d01815105500340c007540c07108030003240c16520001c15070405142a03007000100002c18140112a4900080720803c158080c044400d2184c00090500110207000c00440d070040c0005c2c038081101c052415002500c4040f0003003401d12501016440744000300e018000c440c50b000c035841c01002945140d02c2c015046800484075248251901072000400d81041c501303d80c880d86451a03402822410b095080d0000e4100c1d000580e0548104e030340c0400c01c102507158060003139001000854507494040c0401456071000d4000d0f80c5550741c05132480c000035800090040a85002240113846211482042c8a110300c44503034183c0c1c150b00705005400d003400044000c0c110a2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 811156079 1250 811154829 811154831
    0x6090d08010602061501082e03050c12100b06040b03270a2604120b0f0c0712110f07180b0d03120515090c0309011b200f0304030f06 58
    0x180e03842c038043e41c80f588115100c50540c49076401180d500c1d03100e81c443c1a4040c1540750302040380d10401e0024401d03146030b00505400451540390500c00e00004004d0540720180c100c445001207090500e5194551f1701c01c0c1c00405629451380b01040580c2e40b800c0070f903800f925028181075281e103001403110307603004c05031100c10042a1081401140c010b10105401c000181c015104240034810000d604e44000100052107229045c18000410501c2c030f685410041039000d40302143d250300b04102c1d054600c1030081e04800e50440100a250002219800180b405c0072040c100300c40180301961101e0304001460070b11500c1c80c02000404100c604800b1501c0f6044201c4800c10018071500c417091083c0700d43d5025014002c1020f0001c4070741014a150001544180b03000c0e070385032100c0044404038102250030380c1c45803219400842003000414091060602a100d02d240310b200d55226405c000c0c0000610a92200f2040000b810340c8581c078008004814000030140100ea03030715a41d0f410003810000c8504d00469280d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 811157329 1250 811156079 811156081
    0x40f15080d02030a08100902040b0c120405090606160b27030a140703020321041a040305090103091a10060f030c1d0118180e0102071515030506090d08 66
    0x511000a4200745a40441d002140707400803500050b26210b030f0082401c0703945801c218010601c5203660010300000c0c224543e038640c07507213000c440032030500050131422460b10009210412580c1d40d80091550406400d880c001d070780305454811a1070700e5040341000b0704000350180c140904a0321041660242d02058548210115800c000094881c0314040c510b0300010350303000b10b00907550202c00081a0640c130070b00480e8076001c24050b82c0c1042040704900c2130521680c900400c000d11100c0c024641f00202c7d0101c101100e8031382560b002d8640d000380801070341015074a0304803004016100600b81480d0720a0f0711940d045203400304100f0303049881c0d40186000240c1c0d8851282221b4081d001701410800640c4803000c02503005400060381100405880b810021003506500b4024030300d0030210054640c0100004a1510707100f404015590300c9044030410342e10401802c0041a03500ca008010f452110364042114990001d420307101441a81024203940600e40c103100103104006501c5d00300821507180c20306a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 811158579 1250 811157329 811157339
    0x10051314060a0b041b030b0109080f1605011704062d0501090c0c050c2413080c0a0f17120a0201140a180204091b08030d0506100c0809010e040f15 64
    0x6035482c55070f0048250024180305d40e030f9107010b0742201416507412300d014000c66660b03114403841c210004109117515080079003040d403d1030b0241502c01c06040c4c01e0900f0ba1034030f940d15600704409400204003501d00c664401d0808142400203142031540c4240001a42c240031a41d04e050700102420301c40c1215084c42c00114580c064018050601c8554001001d4600366403140180410200300100b20203401d03005040300781b030300700c1d00790064031200318000072981d07a4508240e011890500460501c038443c010341082088050411035901040d521030461503003841e41030050aa20f060589000109524808074518aa4542c150701901d05400242101c1c01140c4449060f07000311584458068002000184030b800942855008000c01d14410380c1104114096004404001080b42e0001c2445401c000f41903540c0f8003060203543d8100e501120200144456030714081e1843c154000001d0030160085541515030303008000b441c4031030501030b0040c010901c400d40704100030040402d403801c801442c08001b00d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 811159829 1250 811158579 811158581
    0x1d01060806060f031504170c01090203071e1403030903060c1c060f0303050c250305120307080105010c110a090603060518251503020a0212090310051314060a0b04 71
    0x201c0e00f50082d0150102c841c205c40462900f0000030b1080c3d4141c4070801d580104440e080004042e070340030900000030020070b0f80c810941070040da5402484041c0c07240d21f10514000b05a00300c4011502c0c0d038444440b00100690100781503001709803800780d06004410401004000c007400070880080c03a11403982c18100f07001d0b9610100c4000380120400c8142410b42800040c1c00f0381c0c0188002c6082804440084c00081b070360350412400c01304c0e50031107160750840800c20883c003001034402e442c060035002821490030f100010f042180c14440c0604010007405110144100101c0e280c140402c060100800c5684030007400d00640420700c0200d9041e846c1c070300001c0c0342800286016101041d0b42c0040d0008110b002c0100e50041041c101e48901e00421106c0040c4c170015402c0382e44200ba0107901d002d1b8866190040203800e180030420f01490543c0e00f0400c0201e00d40d40402e409072401424440000c1a45a0380043d1460a01407200100061403542c07034072102c40000140140b00b282020424449170710f4601c10300c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 811161079 1250 811159829 811159849
    0xb01052e050304080702130b030d03051608060d120f0e031f02090a0801330b090d080f03040309150c0206030f09240103060b010c081c1d0106080606 65
    0x32180e4980c086408002520800046802c03d00902c08682024181c3d000a400042c18820074240c0554039480c0c1c80890030107100c03d403911132003420104a14903040411a030b0760500c1d03c07070707040421200c0310024503556614444a98400d801240382101000100c0d0042c2001145040507404142001c030601314514000401ba590503056010070410320803107080d8240a50406190701368020042040452084000d208204502e000081140108003111080000c0d00a800390300841d4580e11550512139406c0480803104811026101c1c401c0340e1010707007001c641c10f01403c50001c184002c0001400305040d8040994002d403010907403290550b0003146400d4a0484071124003e4000405100003003c41c40140b406030341c000071031002c2d100000403406844101502200c4a181c1e400500b1005005000c01780c07007481d24402c02030804220011031601c1d0f0000707070b000352444001100704c04003c201d0340980c190051610004540c03201440c1c403000058880c0a00543e00400c000c0d40304050000707070744c1d1501c24004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 811162329 1250 811161079 811161139
    0xd2a0f080c0c2d01110414030303240d0f1a0106021612050a02150c061005090c09031501060906021002090a06082d160c02010801060e13090b0105 64
    0x144110f0b5000d150107041c6941003202680c1921410340b180107180c00038002d0303c000e1070019042d1a900e504000c2a903202540704005640280d006108100880c4c000e801c0c080c100c41d00300314025142c1000f500000701203201583c0010a0090901d440307808202404000c821207140d421168002aa26101c08980c3c40c4803030030000d040544032141c1040000201c0300c046600c0c5018805403052a2940d40104105c0d030010340d8080c0c008800040c1042e110102072068540102e00141c0600100b40760400180014102518801d81a0400150342c4a030740d40030000001c40c41514031001001d50782d40d20700941400b009210b46009409088165901c09007a8401c650074480018860300c4200c1c10220200c0b05400e000b0401c40070018000900d0562071041990b126400c205500a80c810b0700d01541d00c0201c0d00d1161003204103122240726000c005030b030403807201419281d80e0b2a100c0030164031b03074000a40040700e010b500c500b62850400a50140050201c0f054160740050350303041b81080c6e545000c0d00d04048200c0c0342d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 811163579 1250 811162329 811162333
    0x30708060d2001030204030b011707080d021513062d11040909080f030108030a09060e0112020a140d0504050f0321102403050604090203030d2a0f080c0c 67
    0x5060b100c44110107a420040061600504142d10b941e50078240300000e07085850352895483c204003000808210303ca014002d000f000d0603040d041014040e59411000d6012184c0312802000114824a800c404501d40c03900030005000b000c12604052107001495020710799000e00c0780c4c5600c1000c0070365001e01661511821070091500c0c1c030b0311030404000e002246080f01c0c841c0c8100f00c81c014004e0f9550107940a460f410740510f69400d11400040e02c0c2840c2c43d4031060501c040e015100c9182d03a000312a50031150154140583e0300e49581408555203d00000c0100c4590b60200d8290100746081e44030521491060040ba64450000301182e9034034095222500b0b40c841161801039401c60249025a41254004400720901911490705480d0305c14030085504001c0d0400c10003060455150080300c1d0082000e6404002880f01da4000c243c40303101c1c000311041c030580c031119801c1c5842c580720180103000f0f00e1048042d90307880c4040c40041c8405060382200001a600c28003280000100c103080340c0a081440380 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 811164829 1250 811163579 811163603
    0xa051e130b0105031f0b01021603050c030d09060e01030b0f0301020a0e040c0201020304020d110301090209041a010905091203130c0e070f021212090a1b0915030b060622030602030708060d 82
    0x103861005030048140c44c0341140500d903109d01d22010b8510581015500c40d1014001d62003c00b8249481c0210380e1905004204244408010140d08001a144007500a1070041000340f070303400200d00c9001041c2d820603019031000410182a41e401004072107418411101070000c0c01c064a8124281d0101f034070007079841130b00c5121140008400c040b99000c1c6c1d09000d00081503090807900004c1140e00c044805a91a11070100c241c440814054030290241040e07920801c21703030030321901255a41e40c034004200444100007002c51701d5064100005488030358400c84401009440d000203503211007090300e8944c082042080100c03055030000c00c03100c0d0f849205034102803c046000c6401060800042d102184e03074040c503034040707002c41c0324401e840401040c03460214104a00c0c04030f074070342101e004404806078400104070500004a100c03505507000035040303400030703102c14454480c00404030141e4102c1ca10118083d07000000c00080b40c01031445074070991194801c60703941005218001041c940000c0c00440b01c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 811166079 1250 811164829 811164883
    0x80114072c0301060e04060c0804030f110c03010e071e060815060c0f0c01020f150a0b06190210140f0c0c010213030506010e09070e0a051e130b010503 66
    0x80c5241d941c207a000d0341c6007038900380441c0100e4211201d6400031941100b044080005109003806049045e0115180080032842d1a0700c2c0104880c14110091041051100041c440700700e0400a043c2103200c014000c00c4010f0094480d41e82c1d5840c03d12640c000f4864140e95041030040032101502228a1901c1c0c5042070b5031342c5002ea00b0581d4400d01c074940e01003014005890340440420180703ca200c003504c002c0000d15001c1c07001902d0030200180307203051079001c0045600700c180c400036119040241c40d000032514003035020000720517003d20014011031408040d050700099070b0026130702400c10340005082107501a44456560000710032619202200b0000f80412086400c4000402804007841c00050034100400c15402400a043e40182d8a076880040180142001c000c05590001071000c02041c4691420440002d40d0100401011405948500103a0100440400c100100c41101c8600c011803801340410380b2104540641030741c0d0326520b00000300d03071800c001420450044003408400202c01d021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 811167329 1250 811166079 811166117
    0x90705040515030a151421100b0405090f1b030f06310f0f03140c0a021813060515120102120c130308300906060103020a080c3108011407 60
    0x160807802d25042000b4058580388800c3c401001000c85119009c43c3c0e1107a0001004107541c806040500e1300c1d000042d4680c00703220f00080d40c00c0d010504804890350060484002030500c011202201003d008174001c0140c04000c0714580c000c00302c985251a00200e044035488040c5110b0345c940200005561910400825148580100158440d1410340301141607280c144146801c12100c0d0804c0d64071030000f032421440c0403042400b0482c40125441518900701440078541441c004015201d0b543ea4004612480c0c2c1c12205042020300141034008520032500d10503000b035101002c046450100100480d0102c81140704484815590044050100d81561241e49240d423200040c160a440215107400c003840b400070913038805143c2d5180030000780c5044055141084001007100341007610400c100548160001081500034080724601c648a04120103071301106800354050a9091045e5042c202c5000b0981003030000f039440400003030040a810081510b481c2100f0b440b0b000202da04243c807a40c0039000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 811168579 1250 811167329 811167349
    0x3030809010e070803090111150609041505070c060c090501050a030e030403050d03060e0703090506070f0e0a0806070f0c17070309120809011e0e090705040515030a1514 74
    0x56800024000200c0d02d81c1c5450300c0107541c01414260000b040c412810368201d141014410900f00141403c514401461000c07520b0040001e4071810121021034240400c00c00400c02c0864812020030503400c02c01c8015041240c9032a046407054107068404110314402c8441d04200d42041c2c40305420050062000d50142c449502000e50b544420300c400001300304104a4008076283c6902c00088a0703052206090003ca00100a0700c00d1604203036820000450000e034040d07000d5801d250200030406084421541c4c5d20781c40c0d1500390300803441c40d07010642c1030000c195180651040d844004c4d03034158404c001d490342d40d503015019100010081481d5034030a2450020140140b01780b8260b00019100c0c00080d0201d60183c4051f20442c0000c10742c0c49803542c01a0145502508090032201c050042d110010721802010305103034080d50001c004140885d0061003036401810009180100b42003081d400d580441d00b007201d45004090810792503131454081e00c1d8440c03050b070700101c1801920221160510040d451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 811169829 1250 811168579 811168591
    0x201022a03060406090507050a03030905040902011b050115140a0e072607020106120209060d081b0307050c010908060c070312050c07051605130906060506030408070c1e030308 77
    0x800d05420030755003030210070321441c85036600140c3c109083c1411403401102d038200c18000c20a190003400400e401001010440710201d501240a50f030320310049807030b20409010708007070420b88400c4804007c010b42100c107002c4d01c19501c2d40e8480340c2e507102040c220003016003584e4000d0841c400502400407029640c40d88040a0b0500c0740d400b03030b840d030b440075040d10001e852007000103030f4541445005036082c02202c0041050140c2c0c2c1d81c03008190380004454901c05030446120750000d1543d501041944400e4030303240c514503295860b0055914075034035100e0703110b01c501300c819001c1c07540210880c1d03004041d40300507103154400400b42d9545003000030102e584000ca00386c0030f11844c8000c20240c0c0d507040c09000d2103442c1e080c5040303450304079900d1708610b800082c151404103000d4200b0140500c0d12030b0015505004440c034004030f07039607105040410082400d034010300d4019800204000074407580400808140744a0b1426030b8045507903006003454001010841900181300c1241000070910490107142c0103a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 811171079 1250 811169829 811169893
    0x509090411090c0c0616080720030c0c1311041203020f060a09030e012a03050d090b011a04031a0402040b040c1e1b0305071b06081006030207020102 65
    0x4501c800aa541d810840d90001c0b400c80020711000346900078458070750054544141c15907142820703d000750001c08014020400c000500c1150078100d1501814209400e58003400c1d03a036905152511940c54065414056006180f281a160b40f03156981c0704954004080489490400c0d051030014a40440070200980441c4200e0300c85108405082c00f10031700030356851a0000d08861a880d01401c4400c180501e00c1c1031100d04518240401182000342083d0a001c2c1101e00d4500340d40d15041c1c03054081c10310a10f01c49071601410300100701c02d01c0410340c140c0f141f040c0f01000c40e84103222500300510036400300400354145020440d600591043d203c641261004002049044002c00440c003128454140724000503605504010001000d034030008134222503207402c010045884000d05080301c52100000c1c100000000d01e0814005501d1030994040d41c4600c0200e10f4945d0303403c000b0070030311094500c04503013030016100050881c020b1080f141d94680c10380140c08204004d4840c55a0b00c9282c80080c11381c1c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 811172329 1250 811171079 811171103
    0x1e1009200414030a08130501110307020102060103030f0c1b050909210a0c0501020c010504061d0c0f151803011107050c1e03010914010b0405040203070306050c1c0b13060605090904 79
    0x140440042c00346c0080c41800744003443e1400000500080c008140d03881355030002c00649002d40d030702082290640341c141c1840c1504413403490044400f80810700f80a030608460028080404d5219a101c03000c42c3e104854500d850380f034241d82da0752244150300b66141c2d80c0403140c2c00c0c03041d01d410f0480a4070301c1c4100c5003054403041c5920344800f82684e0220820a160717035950303420441005060704c140300e4085211296801000c11414210366180781c030000c080d2090404807415001560754004a40c581d884031040030b5100e034101401071642d058015000c604c80d500300180d29640030a96010b4903102c5030080000c05203418100d0510614014a428210034114407224143d82d0742c501b402101052403103030001c0d90b10380b00702548042c2101c0841d0881c51185040009000240e60006001c00075244c00c00f80010700b03a00d075a103804202c0e11a840000604113004551800c251541d0b5000c010000002d0319175071084800000740d1001c0300c1c4140201008107005001d040e0450501045041c0d21a00c90580e01d02c0c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 811173579 1250 811172329 811172333
    0xc0307060e070f08210313020103051302100f0f05071205070309050a0f1a0c0c1507021005031e0105060a030902032103010f0e010303020a0602031e1009200414030a 72
    0x190010640060b13440394800050488541175030300749040c84071a840252402c504103458842124204007101904241d220000309003806810701b800340b8030f1513000305400d60502a0800c040c0080118103440e40115400c2ca0b112040c0e14060021a6100b6510044161070720800b00d0090700c01d60001c003016800c02440500215084d10b400c41080007030320300f20100a401c2ca01d0a9645412300302c105c5003c442580701400030710314414000805401981003107940380c4011255004040f16406120340183d4052110301301c070309180b82c00c9002903000d4102c2848030400040c005c0e008481c0040300307100302d6800a408200e40030174248203601c0b00b0700c2948014290303030218407101803070090101c44440340441c50400000411021000d40ca5070740c018042041031f89525031441d20007a45404031024084c0000e900003000858504040c3d0083c9410740301c1040c0100181004403400704804424010b03000a14580305020041200500d51b0501d60308441503803a14103400e18032480803410305607032600e814ac4102090000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 811174829 1250 811173579 811173599
    0x40f02092203021c020c091627090c1b08090303070503030c04050a1a0d09020d060c03050f15031c02010b062209140f0403141b060c0c0307060e07 64
    0x480324080c3d030013040041c0c0310507520820703803240c00c04403401c0d9400254242810b46417a51900c0d0711491402c1200700300e080101c0b0996001010080d0201083c000414000c59400a00341e010306550002b081006080e0300c0090507500d13125406807140001c8400242800040d44423001450390b00301c040d083d00c0c2010310617640c0516641054442d901140000b280074030842c01d046280c10000c0040011548051000d0016060144030705201c10400546a1045105540b20039a0b0f103c8059841201049069100c04004004002c1551000202040783e004a101c008102000c1d640500740113002d040d0f50780d802895a085404d40001d800190354903000342210595480c03024203920f01402065490200c2e038489844555122500408910791600303040341c05400b0307529071056101c491781e84900129101d03410b0640b11188140001d007240e080010b0403c150780c96024501c1145040c84044402c140c0350f0410800280c01035000001c0241d00071b1011201040f419000f450068400c1c409a40b5240c0e100c6403100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 811176079 1250 811174829 811174891
    0xc0a06240906030506060103330314060402040b104d0d03050106050306060c150c0403050709060b0f0a0c080301031406330315040f03021203040f0209 66
    0x100d003465582c1401c000307000c000d03c01507038802c10928013000986200d200508245803c1280741004400034004110b9210b03400041d038001d1a0800c0f061140c181d001c40103d035581000720340890040e81000d441050074241080002e07540c41503038803030180d01c10300c028585580907070395186111410002c440f0360518220a5000b40640c1e0750501030120000c0900001c1c61400ea2a041d00c030041601d400010008135030711400ba44c2e003010b070803a0003d58030b40c41e070a903840c54044001e409500450100081c0010014080c0003481260310500944400982d9207002e08215401ca2180414041013000b40d03004045280380108890b1000c0c0c00c2200d41c448040c1c84030403072904260821a6043c106081844100500300304080e031020031405016609164841d03a500d05030219200b400c45a103658140c84401d030307824400041c01030040c424100561400d424215016580c180e41030300907000f550040700c803141640040b030303100c1c1c3d8210a5600c0d80300c002d90300b84540b5070401004029000302c6402c1820002010500030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 811177329 1250 811176079 811176089
    0x12304051e04051e0f01050a14010c0b010906090e0a0203030d02030606040e150a05040903140f040503030f1e030417160602130905011401080f0a1104150f03020c0a0624 74
    0x4124410350f0600110a0b0002c01703499004c02c914140c0c010000c0c1c1e40c8040803041a00c068155007080b07190040016034202d0324004004000c0b010b15800070624501e00e03808402196680542486801c0c403c4500e15100c40c01840040d4054004000703411591441d6001940c000501510192a0560b5100340c071580350001e854030740507002540070041c1c040c680701d0203400103448115070402241410360784c040c1001880031010100410701007201825030b40c0003000d540c02004068152582c2e1190811010340543c4803050086454500c00c0030400c411302d1030003e8900c1260701c0300f0304015202001c0d0709001984c028513441e034150024141c000300022220f001a0207045c1900756040c2c06641800307085030545a05030044228070000c007190b000c80783c0c0c0c01011b49410903d05610407089480d001c000c50301900010304100340d40c4c60006070004501212000400906401d551081480c0003488800c506074803a9007455982d0f54468000d1501044683e4454114600c4a8580340d802c000070700c90042407007a03170b5440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 811178579 1250 811177329 811177351
    0x14060a020f1b0117090a0b04061b021e0106080304091812120506030c012f0712060b040207080403110a090e0d030e01050c0a0c080d020711012304051e0405 68
    0x103060b07003550700311011501100e840d00b24075455140070120a5940c0c00c00d40d01c094001a1004089014003820750310042c4120718400511940154044020355114181c1c1c00c0c0210350005a65441800c40040c0b01e807009880b000d40107145010310703042004001e046410b90004240412100f408001240c40200c00c00c031850079141e03450a40e00e68241c4008031000100304034001d401007010005584e0b4880f03080000110444800c3e40c2100d0b07800814403015000c1e10f0352004a1082c504080303407000d004204c1c1c00b902442508c0900c5841c000d20103020590140a10040059109000c1880041c0d020741940d400100b004d0418020300355240f032207206980d0007450b0108144c008810b4007079465071600812055440c0580240420306110178007a45521a98041e50208100c0840140c20021281c00300e072060501c0350800c0d521080d160805030103105582091a0109507007040024000080114081460021100d124207042c982000d03c8800011940c503101082401304144015584602c2014008c41140e81 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 811179829 1250 811178579 811178623
    0xf0405100c09060f0c0b060d050a0b01081c090f05060c15070909060803090d060b03030c0d02011d2e0e01230705070b0601050a05070f210914060a020f 66
    0x80161132074002038401c1041050003200b00e004181030403411508608140c1e00700d5810702e9142416820000c407000c00a0141c1810000058603040000e4800003030210103040600b6481c902105607141c0340c442c441e5812425031300c10200000d00d0142d01424102c4218429208800302003a01e400e038038102100c903400400c03080c090034014030046215036409010004000c5207000c0501d00042d085181d908801010207850300c000218545050066815919151048460514541d035020f4017818440d9440503810381c822045030480480015072002100d105074440d000c0040c0c0110071412010b503030741080e00071500d400001c1d004a00900c250600300108400503005950034040c404013504002d00200300b0000c003030208401003003100056523040402420328a13543c01e4180780664141c010b04101501065112401c0d0f024003500c00b101c1c00c500080d100d00790070704001c95041500c04030440c1c02801d0880190349000b401c81e06240000b050904901d0040305c504040c03038101d203494245142581048540000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 811181079 1250 811179829 811179839
    0x405031608060a200a03141920030a0905070b0a020106030b0117030d050603010902040f0207020f091909020609060304031e23070f0b090708060a140f0405100c09 71
    0x8840d80f0b400c000902414803016910700425250b051302143c81a00c1010001040b090301c3d030003984241c580d400b841410b500e00b49018002c0d60240760300a410303022254280b203429044102c89801c1d4409018401602c00d0464850159040c000c201510341111188522040030903000500c40162040d00c0442d03002080403801c52a0580401d00b06070320040d0900d00307020810011130b10210035500c03c0050741c20002490360340c210010340546040078019401034501251500c440c0c482c0d17002002c01500a40d5040740741242c1c9030902c01c2c40481103a003004400e85c0704e5101110385a2a400581c0301e1400100440d0801d20f0480c0040c034694010788085001c111040c0c080d5440700c00410703141d40001c0060400040e400c0c00407a803400d05610104071a5407881c0f0004400e030402c070410310b00045490b081100442c41d03152a00c18186d5515950060400300e01ca40070005500c859030703000300c42000100c601072903042e4940e00d041c0703440280c1c0684101c0b083c2c01140110380080c0380300d02c54a41a10b40940d541c088070344c508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 811182329 1250 811181079 811181083
    0x15031906090b030a0b07140d1407020c090a180510020304260409020a12060e01092007081b10060f0815010b0a0309050708160806070906080c0405031608 67
    0x158488404142081088102c965000c501190140d030081c0f07503101d8030350720003008075030219440d00c00720401c14020a20340060440ba034411106840080004c0d01c00303484a200603a5102081c00d485948030340da50300002c04200d40d541101021728508001207140c80c10b6aa207039420520f02e400104540c65000c000c01c010301c0181044000b4440c0041c065080b84590f200200c0417030304c1940107420700b0a03000201c840119100b0203ca10715852580070070462107480e10601d0061810070702c55505400e09180c07164446031600c004600c2000c9506403064500601c07584c4800641e0046101e910707030f15000160030018510240130f0802131440b00400003855a0402050403900c00194000191640c000030000c2211524050003d065030442c0c072a0540b04c507010442280640410071004000c2d00030100001000d803000030380811140c0c06010780c070196a80341c0b01210360710201101c0d103000240c1160000c100090140343e8054110150341c0f6524036154451020a1500d030300c9450005103056020f20801c003800d13003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 811183579 1250 811182329 811182341
    0x2e09110a05090708070e0d0210082a0711010e0a03060c02010f0903080a0b0f040207080c01180503040e101221090f03020118080d09090c050301030f11150319 69
    0x400c0b0b41c411028100090300404c2400e0041100303052261030601100d565940301c4040018650081c0442c510a8204100078143d00003030341c940200b00803604007a0800160204440b580e40400c041980c2014000d84402d403542440c041c44a05200e45038103504544d85403d15401e000c2c42c021070f00403518001c401e0001742142c5186a00e00c030440d00c3e1414410020b80d2210042d40c004514030130200d0a011150002404c54100ca40c003250b00a10001c1c0c0350042208603405084021160b0000b00958001500207524190310600010b1594000700404c1c400340e0b00c0ca01c0b1191300038501400800c211754680c1e00303107510300021400c2510012103005030b00fa4040c280321144a1000078929240240d01c1c500b599a40f040e0410780030007818001143c0201c9400b2140d0300b041c0c0002c191010494040c1211000083c0810810b40980c003c1e190400300a001110701a034210307812254401001c4002140d1500d607101c240da0000009030b030100015240241c86690080a14020500c041c1c0307080841035000800e03411610 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 811184829 1250 811183579 811183589
    0x10b0c070e01120b040302150a0e0c0f030d1209060612260d0e010b100c0c0b0304031e02030c060a020d0b040515040c020304080d0206010e090c032e09110a 68
    0x70708000140842c80c2c21900d1001c1040d400f601c42c0c50300344c6440c0b4081c3d09080e1103503014220074045000b0486c0540240d040420761480340d0342130301c00012140c800c0c00300c0396914601e00c0e6055071200d607400c00da20784101c4203103240140f0345000003502140d40c1c1c3e845054621542c44040030301540010441030105200905410601d5001a41000c105440786506c482c010406086280c50b034031802c04c007140400f0b4011011610b030041000d8200108104050314040c3d540c2c0042c0c402aa20400c007180b010807440440b8012034040e101d801016007031080c0e84101c03a4540301300000f180814021800c030034208204030381c020b0300e20060243e19500030100850441d01203280b03076442141403405014446450766000c00001d10140d4002c110094103034001d0345140302c0c82e480070a841c0701d034140d4000c1d4154041006816580244985061034440c0646135558040c071001c440e80c190400c42e407810034192000e80c2401a01c120300b4200103036880404281d4111584440c0a5a0341c104646240c4001c0c5041c5c5000f8002d04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 811186079 1250 811184829 811184849
    0x170a0203160302091309080a0801061404140f03010203190f0c21110c0f121207080714040602030306130903021b04020d061d010614090105071a010b0c07 67
    0x1240101c00340c00c8a0100c601e040080c0350340010000000e84840c60003101880c080c007400d0040030010300c2c0854050307110840c1c000000d00303550008035003107201c0e05440030204040c2d140d4074145800c0c00480e5007000000b00300694003805400543d8405e850a0014520070321024001d14a000400b070f14071000d980314210703801d100d6132507c1d1a080c1055007007400b03503011600900844440c08101102d100007415545028444010040f41c10b001103200000d040321031040c2c450641c1c2c011060290079001c58022281041501d035065030000e58540e11a0f0029a4043c4003898034000c000d410503806240782d403054200d030b030060700004200959070070040039500300b860100b5001c000b84050354500a40711040c0303158003c15812909a040c1e4660340382c3d016105c540300d0680081026550340d801045040000401e4000010480800018082d0041d552400140b660b160507601d00342c0e80c10011207083d40100001c070f0b640d00c08800190b903a502080c5405020f80b110100b26aa00e0003251082c526001d11603001280013 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 811187329 1250 811186079 811186081
    0xf0f0f0b01020c0a14030f010603050a061a0604030303020901030915230f0c160b190f060b040603020721050901080a0204180b0310050f1e0405120703110706170a0203 73
    0x44d481e41000c0804503030b58a01103151201291740000e0504031700e0900701d8000d41c00c082010091150114030040c49510690b802c0142c917010241800e580032500c800980d00c11f509100400110703009130000d003114041490000346c2c400c4282c2c0c42d1500c9803002c280e40350b9190380e129154041c1d0424601140c03002030b00142c40503040e15004511400c2d20500616825507a035020403183c542080345105c00a800e0750240f1300d0902440d018029048502e101260041d10038108034080c4004e102ca4800d10381a5008918446d00c8c043c20320a094000c1d40c04030600b10b40b82c03405020546c4a03007040424045e00c42030996500307680c070102c03140014400200548010340c841d10400080020500048038030060004641c4081911588400024201840c000942d002c490030502084942a400d922240c4607050580409440c1c010400c0200000901143c00400c02d03031100c8150b80409002002921000c1d10038501075076140c4a0700012070502d0b52540c0910085400c80d2028002d406030281c2c1e080e4000d401c04421411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 811188579 1250 811187329 811187353
    0x3060307050d0804320402070b06100509030a06090605100f1e23150405060f0705011104060c02030c09090c010f0203041e0504060b0304030507080903010f0f0f0b0102 73
    0x15241507210352445861a80b010004100b55201640d0042c81300d510840380200804100541c401c45e080d10b11810300103445e000b0406490140300380c9503c25088141500c1e55540c600030310803440c1c114000507041c04400c1c0080c0c04241d808101018543e032180c0000300c2c0c5100c041c60a8030680394017034220061203400d50f1040c0110a10b041c103842c215183c04034214000740c240568101414074a4001003151444e111010001c4031001803810151f44040c0e408260f1300040403032010103402540215580f12000304800c40c46040d60001403c040b41c0200300000311200783c0005820700e98803a50140c408922558144015860240300c43c1c00e41145c2664441c0c51860b04400e0f690b01c803100040814140014050b105104900c204161030140500418542c1292122040105412002d229017441039060100c04a0342d2000c88060b2800355a06880d001d041070419620081d80e5080b014000d50190f50301c85150121040e24003a1080c1d82000c2c80000907501040c2d9408015110440e1280b8190760040c0c8080c18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 811189829 1250 811188579 811188583
    0xa0e06090703020306060702060c0f1c09061404080105040b07170c040608040c08010e0a050f0114010b0d0908030c030a0b04060602100c110a03020f0f1902010c050a0c0f0614030603 79
    0x1901550510340140c2d242d40340b40c00206d01307020b03804020390050070104603007036034900004860204400d8101100c0603242e0000071041c01c0002c0440c0c5100242c1020310401c01c0c1401203400f50031181c590f61400f0308058031464502e0854030304440a90b4070b1084141849540744e02300300100b80007240c030360708210540303000c44c8175043c20b1042e8804c20701082540c800003024042400c04a40140094200a101910702c508403680e940314508010f94090081d0f221406800c08140300d51401103141401507500c9a1802c0c3c82c040b60b030340050300112607150300d034020000000e012000840c171a00c0c4c148907080e00c0b0305204001a0844001c0102a4095031070510f090249540002c0c0340c800042940c50b01180c0c1140d038030400c03141a014071502001034880c9c0b003046410180c0204014001c00540d000300c0300044a41c5140707681c2c1c6d07a540b00310034608245119000025500c5130b4040811a80134070129940c00c201c40d42d5070003540302903134481144498440000e1243c2c0b0361103200341a0591100c0040c50850501e200082c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 811191079 1250 811189829 811189831
    0x50a0e010503070e030708070603180c12080d150f090b0a212108060d0309062a120216030b150307171507050a080708060a0f060309020a0e0609 63
    0x54148000440050f000d1480360700c212000d07407005000d80c0ea502d981c42c0140f81d0b40c0d4006010300c802017420480403c00c803141c54044a6035064100d4414001d09103415140c805520100105071040c19080081c4c03a408015802000080c0c816500d11120091034800b00044400151f00302d80c085900700246c0d5106070b038648903904180c4d03201d4884825100151403030b03e040f176511024020103100903d400e103440a1004907220400c0307a1591520314440d9103800c100510660301800040203e030508200f030141910a02d01d000f4600c950300b01600001d06820b6415050705143c1100b1075a41401c3c604a0061a82c1030242c140380800c984c4400c02800e00b03694403c03805480060115090080314056001180c0c1c1c1000443c006102e0309290440f46440c0055540d21143d000290300d0740c01000ca404034480910403800c45d00810396035900d620385910b40140440d42e42d2000307804154400501440402c4200c0c4081c2810018803860310f00244802403071041c402041190740c030800134100c2510404c10035446040510b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 811192329 1250 811191079 811191107
    0x50709020304150f021c02130b040e0112080405150d06090e0a030c0602040911070507081b1c14070e06040219050703020304030804120204051303120e03040305010921050a 75
    0x80340d03140d00034001c00c0090152171b401420181d805000c081800d2683c1c1d0042c00d2a40d42c9214025544c0c0d110181d284251141e4428002e00445a0004008030600d18084040d250300c22101c45141960324000a82040300c480310704410b10500040308071800442d0b04c03c0400400411005102d401d205803510340e01c2d07c10420010b4103101d0040601d00422070035504031000382800300750802c08402040e18828581d082008110382910940502250710000042c403d001c070501d02c003250043c540d0400c00c0c45000401600c4411009106880c0d200005404c50782e207288030407002000b411168038003d503940b54000060040c5015034410804003030136481d21080d07450490303080e090056680f90585070072442c41c400c2e5800504400c0d4003050204494403510b801034500c4d402201e00340441e071141481c4500409540754020003084d414803216000c05103503081008192580015207080c00d59039103e242c2921144170b0101c035050a810b1002042c2da007120303241c4410364900d1911904146484c0700190882e4a040d100e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 811193579 1250 811192329 811192331
    0x150f051201140702010501050a0e090a030302090d170306031501080d0309080d061401080114011d01231b06040f2d060603030f05070c17010b12070305070902030415 72
    0x59080c00c25425005440d00b44880740090b006460305040c028000c10081c095144502180100001d110961030170781030080005e00d02900e15904295404d50082d801054400d4200c000e06035610082400c002030701a0707003c880608641d4907d4003004040c1025481075201460b4254500140015a070018014490b51074504001a01140754103048040d4011030842069150520901107440d03521b000c0c64106001c008e0302c40703129598841e042c5c04801c021940d445800500b442e51000407840c0700203501c170a042d506041801c000310b40001b40215404200303250703400c16600000c1c0711038991908907482903081c2901020f0720381030911fa030781c416240405820141000c0317030101200c0c3c481010055889010700355010f1621044110b441c0040241c40c140c4415000b00340d084202a0380d160151040301c2480758001d801441c60380c00c01202e6882c1906000c2d5a4480d50f41c0c031601d502e455110b24145200d80007908008080c080c0ca903240503442c245807a082000c406d4014414000010401344101001944103c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 811194829 1250 811193579 811193599
    0x501171f0b030a0b10030c0e01051e040f090c0e011205060f1e01061701051e04110714060a0501060507031b030e0915120a0305040b071104050118150f05 67
    0x30000b0f1030114540c1d40545071418a405010200c1e6152003200200c0740f191a070320144a41c0c40c00c0c87c1d8280d6109200d00341d008524652180d00c03020321600340d429800001000001c1d110560014602150902c010407100f210300f050b4140400d40040c2d80090050520904601300a02039541d400d44030f010141440081e90202804900340440700008101e540c190103246581c590307941c040c020005c0b001c110079240c0c0110643c00204d900c1c20f1125040300809040c1c0c41c0c108140ba81c17003061000030001c1c8440400e64080504c0010005001a10408054800c000051225003008017512085540681c011000e008080141c6000070b0380100d81502d502c14100c500c40046841424261585d14449100035403000340c090410a000030848041c01c18244182c800b881d07201c440d050312075610f200b601006004210244010131a01d039290b0001d0222500c40c403c0c0e81c01c214101c8010500741d0702e00703030800e0400300d41c580c0181d20041c4103427181000000c03208050344805460100400900c000a004460003006008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 811196079 1250 811194829 811194851
    0x50f0a11060f25080f09090901050606161103010204080124050d0f02010203211e010e01030b06010504120506240d030e040902090405010e0f03030c1903140a0501171f 73
    0x4100c0c1107950700189000d5840d0740417403400c00d881c0c2c0729900d01489070130401d01180456005211b075612030100034014901d0900d54840c1c0d504052038517a403c0f2141400101c0c205095202800500010203451001281a2400701e0124100d80724102000031010407001080046a8400d12401e1415811810b88483c2e04880c2c00100e0543c03050080b600a502c0c0e0f2007445004018140f074001d40308071b090000403508a054000180d15001080c0700f01440b1203184001840170888040b0295040700050406a1516644594242c40d07201000c400384c03943d802510420202c402c102d640f15854a00880d5038020714032420740050002000000c000d030800201d0100c0302141d0715190300c200403181e00200241e40a24180c54030030301800c62039007030310540d010301d1418180c0e0a8000060740e00800c1c407040d0940c100a0060070f081c0c64444115a610101a01e840b0304a032403445000c8804e004d207000c4034000c82d4540c1000d01d1440c184040ca02001001e51015000c0038110014402103852000900000300d100c10010f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 811197329 1250 811196079 811196137
    0x7020c041509051e0703110f0307210501030b0a1b080703060504141603091a0606090d0302030901080702030a0c0809150c150619120f050f0a11060f 65
    0x35812250300c5520f84000e1000c4400d40c00075600041400784d488a65560b9070800880c162075101e076101038050405d010b04000f14900070042c5500135220f1802c0b52a0030b000100100682d0014180604026525001442848040c0703918030380c403442080c4203020a0008c04802000d030700200d59140c0c00c101c4c4010203c0d80e00f610a07042030004000040017400b200b40764400f4001254003e40b5a040c05007009414410a00c4c0a03001e4480101c0d0003003200c90f80f080420380c410482860040065920000410406500d50381349581220402e02a90045845528685c0003400118000e0319803010341d03206002c0504c03002d6002c601c1d404510b50218502c0c1e11485c6510114602944454503c0700e8008089000c3c901e40400007140c2c01c1c462030b4448140d21a8031402c0c140721074607402c1d01c40c41d02103132800f19061041a80c0c8000c0c0202070341c42108003418491050700c0c0c6600b0304055051240c5c581d0401c2c0d544006020040c0a45442844225110391402c1d01005001c5040c0c03150145074000c640e46e11003840045101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 811198579 1250 811197329 811197371
    0xa0f1701152723042f01120903051b0a0501021201050306070206040c0b0c010204150f0f0c02030a0201031a03060106030614040203010b0a1416030801030c0b0a0e19050d0b010302040e030307020c04 86
    0x125500010800840340e03600e050041045c1c01c42e4001045d000400301420900c1c00340301c0705150951521450171000f0349420306840c40c45070070f60401c0d1185034251030010304248000d05440c10022102d8440c0d5043c1000c050a00d00054041b004640c0701d54140408689221944001c9075041c404440d03580715040302071806405a03901c001462007a00717074001d8215400100315090140980d07104510305802c420142d9204445c0400607400d0b5100d40704000c01540681c0c80302c1d034001b0801480e549200c0d441c500080c0b034141c098000c10002602c5600030007071958580820032005038100c40550840d8141308030041e00d8010040e0034820002ca0580401070100d01ccc81c220340692243d0141007200a1860070083c000d140284000c4440d2110000f0000f03100c0f90725019600401da45503a010440c0300c4010402040190030000621a00780c1c20b600011143e4407068148040c500c2403421780c91541c90b600402086941511014960303400400030002d6155004c1209a0151022100024011110314018002d116 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 811199829 1250 811198579 811198613
    0x1050705100c11120d2f0708040e090a020a091103060d0201180305010501180b01020c040b120708060103050d082a040b0a050304060b0a0f170115272304 67
    0x922070700c1807407901404c0c0041010f006004e20901895030701040d013000d4404007844100f002440d030303c0003502104540c0001c00707556009081441c2465103c4012581c0340c84103440d40f1102d588050003500444c107004e00c0420003045110f000300011201400710185611000386101d115402d8100100c046a00400c0303507400300c86021421021143d280e2801c076009080a01491b98481019940b00c40c1107e100e006581c00084181d01902c0c1d140e20804c10710001d4a03800c02400e83c0b1000c5000c2c800d078070301c10800450004024040007854507514509100e410100e04000304420040146c1c10400f002c0c003414542021520581d44400c8058065032600c2440d00664000044801d40001c40c64859680a4003460140340504000c1111441c2101004030500b01840380b1400000c000208101500400b81507408180c0d99000104150fa110100b02d01c507001c3c650011040c10108842c040b4107031003c41110300c901e8980c0403081141c0550703a521959030303804110542c040b9035020030008041005c40d1800031201a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 811201079 1250 811199829 811199833
    0x1510050f0d1a0414070b0a05032809020f06090607020105030c1201121208160c081308070f090204030803040204051e07122304081b07091a01050705100c11 68
    0x364110b0601000240103580540d1044140c0c129010a1000424640102e501603014607240c415100001d48090b00300400c00c0041c1e0441781a070f0407108420001540111160074000100d0000b10320410140151444c07249001d54400d1003000446d0300c40408545c010360b02400c207152a5926824420658801d0040307a4000030750f11000010111f0340380440126180c451400c002c4c54000c900c50803150303204200c66004010703961001004a090140d030800e01e80b1400346c0c42c02d92a050401040034020078140d881313000142c3c00003500304101c200f06191500030705a203407000e529051441d211050540005400030340314030741d294041000300d580210101140491011802054604003a000d4035141040340806200350070401804541010034501c2c00303101c04080c03010725681d100d0b9120455950458090390f044e005000c1031144076000e0801084004208580000c10f101009d407003d101d07015000c44945052000521803034000400104007611500c54103140002c01c140e410030201c540c80e4051030100b81078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 811202329 1250 811201079 811201103
    0x10050c040b0c160e0f0f15030f060702012a03020d0906050703060e09010603030c0b180601080d020114061e04020f040603090507120b1b0d020d020c1510050f0d 70
    0xc076001003440c070700c5040716122007102c00d0b40d6107900f81d80782e40048170001594510360300020550703d4500ca126801001400c1940280c0350030201292404030540904401c60b4400c104000882d40d0901901e61402000c6d20804244641080b01c0144903140e00304003000e00d600401c0c000d0300000c0c1031344080441500b02d00c01303202c02c1c20000c0f0080c000380228012414003409120002e0400b0b00140200380c21a54190740d80c0c1c40b64961900e4080f11307443d024140c000401e900650603215000e081000f0b078040e010203005060405940d1801a0031900201044800d070072000d4100840f95031030061480281c1e1450301c8501032a440d20000800a101e56107002c0030400002c100440c0480e403603400124801d03c660b00311601151507080f40340544500507001040240c407000060085202018803590f80381c1d03801002c030700340107100744060113a8000340f03000140a507011401001441080000304811000440400a00e0030700c0000c52944214074010580500c180d82400b00564480c4102c0139040c5400003c04144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 811203579 1250 811202329 811202347
    0xa0e0d120309060b1e13090506070924050912070302091501080a02092d0301140a1401140409140d05041a0405060a0c020102011e0203010f0f050310050c040b 69
    0x2c04585100341c3d1810329102d03482d0950b041074411249800c10010507035148100c0c8004010400c00c085914003002c0b9101c0b13184030f001400070401180501c4140e140c195000341407201c840303114906402c45004100d60700c01c489202c190040c003102d100030f01c06d0f1964091400504400c5103000e9841d48000c1d00b00755801c00700700000d00310510155160b5026a2007254540700c001046d01039000d102105a80030420000d81c202028600050708050020440e0b102a25203608001900710b521082e500314a075143c1d41c00700a03c05030b0621444607060400c14108101d941443c40010b03009039a204d00303601490307443c43e4003014440064a04003001c041d00040300e1452007034580041894000b4883e080c6605c41800c00c4464590003501a282521070180800b41400c614400465000008220a0303056541c0c1c3da9a602104200c1e0b01c0901e0b00c1c002400000d40d5075407404a0308294805a40c2c001c0c091aa03210a0500480c2e030045502d01c4580c00c83c22002c11282c440704000b00251186602c0018401000202c4a038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 811204829 1250 811203579 811203581
    0xd0501020a02070605120718080d0e0f040504030905010e0d06020c1b030312150d201c05060a15080304032618090a1b0509120708030a0e0d1203 63
    0x100032040e82c2501e001035940c91041c1e4060090010140005d042034002800e81d40c442c562410b0300c490b60302c0c0c1000301c1e561355034117950030310034403d100900240760b2005402d09801d001e888002c200c0c1081d0340030840392919460040007005540240342c100000c80e41802d405994944140142c0d6420030811580c411820f0440f0350b803498041054101c1280b03a4048005030300c0c0100c2959105000b14240e400d80f5a944110b0010064100c9011640b0104491150006c00c40242250f00c1e00c3c1841c21140300240301035800c10080360b420301c02980041c00c90001920019102058054018483c4400801c070310003078510705042030207035400c81c202a20022034000700b0301c582031075201182c048a4600812811003440c0c0858248107a0800c02204140c1700e44224a81c03e0040c0d6880d4040514000025205a0200d0103100c0360041084e84000a80208054007145004080d08440b41c282e10000e08056150900c01606d0b03014664034103080c007641c005070341c40540f02c60b0010411701d0f5100007891509d444c012000340c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 811206079 1250 811204829 811204837
    0xb071704061d15012c0f04020117160e090108102307080f15010e060d0b15120a020304031e09050913120207060219240506090a0b09011a07020d050102 66
    0xd868481103940310103e400c004045c03006001c4040010314503580e94644600b4144040c0c401c07410060081080f50083c054102c59074096010001da250082424080051852018000c0b05106002030001000803030340c0020b42044c5110b0075035011072000540b409881c1944100203042d949510000100300100307030700143c224810004602c8594054039034490314507480c4090310007540490401021084689441000303441c0280c4030250100b0b1244250020444500340303000b03605444000420310b14201d03508107580c00e40c4038220000440c10b519007510f0060410b0304111b100c0003000089120800f119120f000e03540003505000d000303030681c0c0c02e03c10180303210489980780c00d80b00140140d035150b44440c03021450104071125580208031012001024240380c0b41c0114048818182c88140b82c0401410054120203500c0724590006035854002e06001d29840d0040000030141c0c507101d0f00e5210ba07500d50504905503a490715014a070250340340d400441c94132400002a501c621088032080800505400070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 811207329 1250 811206079 811206089
    0x120f020607032006010f0512011b081b0702030727050106200c010824040908040302030d080f13060603062901050a02030304060b030102041505070b071704061d1501 72
    0x1400d00729140c40543d82e141e002c01e00455802c0ea941c08803c202c1d070704d0060220132002d0a968000074250407070900100c0058120784a440c0856102c008000b0b042080c09a030122181984018900e4990540d00080e21050180070b0f030080441648245038220322950165507100c04040c3d000c1150756106c503c0038010790705d045800200e4142000c0b02244866011078142c10178007040e1246201920390703040b58540c0721000c61140409049141d0b4030140c80d83c1d24010340315210b016014060b551070071401410b0420b81940016070900c040c442c07c1c00322200e600c003000da038002403010031a80c0e4194280b91020241c20241c1c00581aa81070001940115081400c1c0f01d42c2070103c03607144c01c03141c0d00741401510140030f80d050501c05078005000040200300244c20003a1075250040c001403402d522070400d608882100e40600d800900007180f861f0400825081c2c107034001c01c460410400813640103644001700b00b002400100001e8940081701890ba941c2a030400d414101c410640f014080410080f440600c0b0034494 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 811208579 1250 811207329 811207367
    0x1b060d150905060f060a0813020f0319050f1f090302030d0c0503061003110a0302250f0c12020a0512010f0f020909011d070c080712050903011d0304120f02060703 71
    0x7000030b450171400b180c0c60480707103403211446542c0d1010746a040780c404038801d980000406440618a50f818400e02e040d8a242d149900004c0406d810b002d460004c0402d0300c1411540b1007101e5603862840701c01d180c4031403404040702103902c410a140480c203602904c04078850160900c881ca0120039040f1002c1c40c82910b098507a940000c180400480586203504000391402034100000e0746100d219800078401020305040140354500d0885010440f2138280c001136403408034090003841081032030b0456000801031190400403000c0b0640024481c1c0c1d0052160314400d07038681201795082d801c03c3d0807040000030b13601c8040140e03400c81445c45010358881130311644100b600e00f0000c9280281d02080c0450807035840340700349580e50740c00c4c8161059050048280c481c1e41d428401540020300100c0c0000b4249503d41c0d882d512031041c80245420b41e6180503000c484202c0350344911015040000030354044480d1403ca018a801542c180f0080d000a11039020790400c03000102c40c01403542141c2c91103a08030101c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 811209829 1250 811208579 811208599
    0x160212070f0e010303021507201c0e130b030706032309010b0102151003080a051c0c03050c09010210050c2107080711070506030a0e0f0c121b060d15090506 68
    0x2941e001c020a040780c02101280f903407283c4d205503ca41284040300e440700c3c44101c401d0b0b00e0ac031210100b00c051940c000c901c0000c0d6000070030f034072600340814151900e09400e0020f00404800b1000291149024015202050f503548460070100700c0da120900801180e00407002030908158500c940640340c0481e0359070140c8a4052640050a1800e140138414410070f0003010805065680e003500b2640302c3c6a40c4410001d080c820441c0e040c0c41818614900804500e00080b0002c0d00035018068440003414202d8542050107100000d0f600071032240020b170485400002c86a4400c2d2503801e5a02840400114001c8609091406692035150090150400352030740e641d08d42e1607200443c3c00d900c00f1040c20f4901d42003010100400d04083c400f5540100307800c1c00c04501c815142003224503050036001244141c1e40407020696071420003684a51080d409000a003401c0030340c0c1420504004910340b0524060340c0c0006090032184525403061080c44030310355540c00d10b03554074220403001d00f0090342c0c040d2080d00450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 811211079 1250 811209829 811209853
    0x19031e12170c18041107020a060503010f0608010308160302070b070501021803060c0d0207031403280203070917030c030403030215010f05010c0b1803191202160212070f0e01030302 79
    0x1c1c2540d0a1240c44908030010501c0c21044c0005004205809403004506200302401a0780740030002e406403079541e45103900c075898400203107410400c035803000003400851001800401c0c0d01b8802c4844900032241402c110382150324049107041d105070311500d141c51011074030310100314040d0020425051000700410721201400f0406481e00019100c0384c0016104210306e440356140d41e00a4201c003030081c00e16902903103000c0769030034a99008030380407902080c40025802400450804031003040300ca5000031820f40c80c00030b030041c00608544c020b51485040801110907162410000c03164400c0300c44058945480e524900a5610390152a4000340b4407403880004c1003081c5028009030440704140e4620303241c5451f6888080341444080c02c0e00018105103000211842001c00052000d81c1c00c40c011948480700500004004840c0c800000b04403d0042040703043d8030940a441861258049034902c000d840054015840e119065100001c0e003400071030001f030400c20007220281201d01035000c2d2a9004088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 811212329 1250 811211079 811211101
    0xc10030c08011409060d06112b050c0322080a030c0f080f010e0624090117090307030e2115060d0c0b030606130f030c0519031e1217 58
    0x3d5642204041c0c00054561408030000c40c2c881c0c1c01036170001060080380810001c0baa00c9041c80880b2404c0b50001100d00d00016010b0303111010090700b0400c50350030802d240068601c4042e10301e084c0d98840c901d52510014a0500c106000c1e0351043c1d810340d64004e80d0740c014014240c0e02e207480000c5559408140c02d802d0207030f81c5040c850412080d00400683c03d085250300ca4400140c54140c00c0303584264100b0007400014506181074007600d0140b9128030345c0000040010381d41000780b030a40c401c404280409910000f00340c1b0103040c0e0505100340036140c6034000c2a103503000f100030b100c11070304038400181c081e035004200a0344581c445500030b4a256910010b010700c0a1241000030f08c80d401d41c01003000b00c2c507a410061500600300600c0245000c110500b01100000301c2e41024a984901d42b80410400242c0e21095004040642d400715040c280c2299610000d099440090160b40080d0301e001b0000c408014207024155000d000752807107000065005242c0c00c40c6050f824488000400451214001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 811213579 1250 811212329 811212359
    0x409050604051018020d0b100315080102093a080406021005040b041202030405063105010f050a0912060906052a070c0905010b1309060506040905090c10030c0801 71
    0xb00340c2d140341d40b00300304d041c62030000d512610881210f03079034400d100d034295600c40f50307500d86045080c1e03400700340328002c6881740c010801241d00552240c1c0c8100005284d80e02d40501011000940303131052404000d0201c050911000b6010510142070340703c0d24150700300140c01002c3c005450080e42112000956450032004840040e200a001e241044d40068001042141000c00e0300c0003500c10380707003070623528004135100343c001c07a4825042c18441070781c4c4071003072810300c007103190445d030002003045404e01d0840003820a6060344140c1c0c0401800007408212640550440d4009001068940291070400d0405400400302454200d40490500d0017217001040ba042c142c1810600c1041d420385149005490031003264414401142c802026040000d50030915100340b9009050102d02070707686400c410340b15034401086403c5400c40350b162103c1400386450f0071084c0c4040c2d03048031100250030f03141e8650f454a01003100e81016441000c4102e0800320590603041080081c41c1500c030380580e641c80303403035490304205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 811214829 1250 811213579 811213589
    0x120c080703200310050a0221010e16020f160e180c1c0506130201140a0503010e06190902091306030506070c0f050a1b291b010204090506040510 63
    0x121041c100342c000040030b1540400d00070001c0c11200c40b0f480400c11003080e03c00448580310b0f03490340482d42c0c001c0000c100b0b06190003055003071140c04035076040690300110103a0283c152203c0c190f01c4148411440e00130000701c0248002d490890b46400c0c1300001c035038200f18050080310600310340f0801107058401079845c0c0c0380050039400d0240618089100a1095040c8205450382075182e6051207900460001e01c0b0041c058402800441c0491409000260030009030210b01220180d04120310000c080e032110980303046d1103c07102005d0454490b03e0000c0c180401c003007071080030b8940590340002c0898680e401892811800e90b0484000c4001c48184001c4400520015049400c404005030b80c0702e102c0c1110510781e500c5503841c0501a040e079221240b81201c01c280840b10f101030605445510940ca1900c04020252024101442d0702e1281a054103280c00320300c00b11500c2c00104600d02640041d001010307080881702c000310b441c0c030ba4400c50840503007009e07a1a980203520f0440407038160181242c481003551 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 811216079 1250 811214829 811214843
    0x504030903020112060e04050106080c030303090624120609011a060711040908070302031e03070c170c19060e011503030809120304030c11010207050f090916120c080703 74
    0x1d2440e0019a804000340d401c40081a030784600114502c401840c5041c003c60044000240c0c4c81c6c01d01ca0020b181078940d0007041e21036072062080024000340000d07580d50206480641c29000c100c041406182e0074199502c40c1e81c041c00f02c81c440201c0b05000a810ba200342c403508001c0c03001e44124410408201100c00c500b5800034006c00100700441c0c509100d1007803101028000143c1050305480b460003d8000d000c0c02c0700107800000b050142c84005083c0250301d03603c294034484c03441c201010050b1694001d084000d00704203c0b045000c001c0c1c20820141c42c50088031600f07443d600c600002c0c0010b801d260a250440e02e0500d000e56008108805100b000f8141c20040e036108403290440e242900c00d600010507030702070307441000003000d407040070940610300403486074980d0a48440b083c5410200e02481c1c125850455000190030000c07551491180000d4020503030b505105900d0b55200241000034810010741c10203038030000081d0034006016050b070500e001d038540c03020784c80d1101c210513101c5880784000b078990 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 811217329 1250 811216079 811216097
    0xe0601051e0c03070b040c0608240d05030c070e0c2104210f110105040c060c020105091207080715020706030b040e060718060e13200d05010f050301050403 68
    0x6109010507a101078582442503092600050000345964880d070411100b0810380c1c420301007007165002c0e040f4050708450a12907640d103801d403400351000214000100e0f030030800f045c1c036003603540700c1d130424084103a00300007034943c0c8805d900d10340741e658502c03407292084004031400020f46080ca007005492840385144840000d486410079024645000030b04260f400c1d9070204c4500484551440c51083c3c15095900c0d04010f40021400242c001f004e503013203100c49641400304020000c0e4040c2c0500702522220308200032803070340341d000480702c0d4060020f800b0381190b64041080c0400740c00095000807922400d08550030203031519206c0c9022443c03140c9080150380300e19805d014140c02a0085409a00007902c00078290381c42c05d0340d6a180040954245000c114000071039200c40303540d052602c000c0c041c80d04202400c0d001d150301164080c0e996610800c0015994501d54000e803e0313a002c071428052100f4001a2201c840503869001804c0c00e100e068036030f41e40031100041c1c500303040c0200c2d48940d4141e2668521 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 811218579 1250 811217329 811217347
    0x806190e1c090b0c0105160e090103080a0504090207050304150504060c0f240501051c020a0e10030b010e060901061419090f0303050414030a150c0509041a0306010e060105 75
    0x4407580c0803400c8014080c00e0100803900310340e4840a04118544ea800206081c1410324941004000c04507400c41004155070b01d89440340c494680d0341d4111b0798800d01c041d60312007807880200d94500441c1c10000d46240002510414001c0000c007400660b00b8800c50074818448060081d40e19120b00d204240100d20065140c0c0701281402544402c02ca0041519151552110b001c0e40c00900c103c5072400c10b4143d60788014403450a0683e4085031560111905d0240e080042d0002030751205c4500c103010100da44a030000342c69030840c5c5c10043c0210f6111441c0002541c4820142181c0007089403000d0103641c031000002003113440344080c074220f5041d0600d054034111025144600b001c583c14501c8043c0b101c407070030025002e0401c0c004c04009600980e1056156810000030a02c0e6500426565100e81c0c051120721011519541201e445802000b0f000184c10010020540d094040c440031907500600e86041e0380c809212444070b403c81d21108509841c402e0fa25007100c48416601610480d00240741401000c0e2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 811219829 1250 811218579 811218613
    0xb07050703050f0307080f0603060106120506040b06120a11040317031e0c0403021201022809050a0303030b27130507030c060207170708030a05180a0806190e 69
    0x240d41402407510910b030052040c8515041c2c0d000341c66520000b011a0100401740d00404070154000f0401c402500d01945081d0000b48408080c9904a07030031541c1e2030100e407181c4e450342d02a000d802c4001d400140c0741c039044001000807503421500c1e603640e07a080c4031400d05d040c14068100c2d420ba96001c051090724800042c0c0004464100500c4080440c108500c0f100010181344a4544240c0b18040c20694075411441404aa58620105000d05a005004000011800c0880201000800711481e2002007a189080300c90100ca41e0100d50032045000003c4245030785038200412059090340c00b4084d403444c030320b03c1841c040c3d40c1c402d614094544180c0031441007150900c0f004402e6000383c0481c4c2e18140c0780d4444010500c111f610001c05680300000400070b0000340c0001d038642e440000060700b01d40d45003c2901d501c0340b080c00003200130010009581c5503406405240005615005055904110f0b100c02c40c140d603860069403002480c45440c080c50301450010301070b041c544d181510281207a00c1d80f90460034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 811221079 1250 811219829 811219837
    0x9280b0a0e0403030b0a03080c0c0402071106092b02100c02010c060f0e010f230c0703211d0106140618010201140c09010801140303070b27070503070504090b0705 71
    0x4042540703891459001d540c85101d903101642c01640c502741d0312040700b84c40350301e4418112a0240107030b0042c0410300204035200e4002d1882c49094a02d140d45104020000c0ca080c2140c40c014502400b100416000da4405040c1801c1894426120a0024180c0c03150680b218100340702c0c000d0005444258007000100560004080324903443c0c0c000c1030068500140c0c40c207580402411500c0345942d0072030036102082d0140c8404100b414041a2121810032003221043e40c40707680f1015092040894440a0718869151422a0242c00c03100030424129030303403440c0c450440c031681c81d20215801d14201250001e00d20090280c2400000c00c044c0c90000140f5071a00010307004119907055540e66070a0f510381340707401c0c80c45a11640022146030764a0320450009814103c1c181c008a84d480d251100d0710f102c82c0c4000084800d10368000b6500d071002c1c1d5595501d00b204224074910b0302c0140480440c10b60005c18001032017000c0d50710407000c6d140d241c0e840320144230403942c8080c8058000618000412003640c001d0b8000c4c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 811222329 1250 811221079 811221083
    0x12c0402130e1b0f0316090911031f0501020c120102040306020f0301090501090204030f390f120c230904110405150a050f060909280b0a0e04 62
    0x9410080051004604031080c1e511480000c0e01c0e2008011a90075884031401c07400ba41c3c85503803400e29074142c10250082c00000c3c0151800a2502c00100a0501924640000341140c51040c44800c1d241e81e140000d507002903980c0401c15002441a41c02440072800744400d89606034010310703421030702c1001c004211310400c2c2d000100323544c208000300200c0c115000805c14003040e1650640c0e42d500d400d40d05801c80d0350580c00101424410702051000030003c2e028040b0040d040185502084180d444004001038509400880310034501c01103400f4442050748882102c81d0324196040065030b6405004844c03100040080030094401c0341485418450b901d40c0c8040803001d60340007064054000031a08000c1d040c2c4050301c01c2c501c6661001c4070351a11703006030741e030280001c680170801e050101c000c0344005809001e900d01c10641a404c64429882c1c4c1e006446419900802d0700b407650030306035007801d90402030384090f81d80303025502d4080140200f24081e0000300c001c0508013404c00352910b00610707041b800141c41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 811223579 1250 811222329 811222331
    0x90f05092e090b07110708060c091e0a03150c020708071716230105070c05060336060c1c0c03061d191802091302032a012c04 55
    0x1124040b031043c9518a11802d036a071184a044a915420391785480070a50100e8940c1e40f080c2c0070005801c100300161620310b60159458003c425030070141d001c0b00a607003d07006d80c02841034000003061145220301c070711800c60341c40e40400600c808101d0803030b182c440314001ca02141c1c0c41210104101e001c10040188070400c0d000903030b0f5001c84006000b014141c1560f0007000b2852a034140c110703c03400e01d6200c1da1081c09003402c110313103450543da072502e6079036a49100f0b85100b4032001c4002400030703400d00d224090710510710030309000e0030012010703203915010303d0448207140d03108940001d5440f098800489010b041000103021044054500c08409024804501020182c40380000500e286281c1e09041c0c01d421110420105850866505490403080d0301750420164100001079941c21403004c0007102c0b1075010b03966540c003541d41b03285122039640400002505032003686c40c1d900c00c178841e141403080b0700c9902c894480d45850502c801100d58684803176100040e4112241740c01080e003c22070041c000c1400140c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 811224829 1250 811223579 811223591
    0x30206190519020607090b0406120f0b0411070512070201080c091c1208070f0c020d1106040b0d180206090d0309031202010b0301050a14041704030c090f05092e 70
    0x8156000c41a000e0b19015030710000c2404445600702000502809001c404c3c5ca040c28901074005115014255020702d40c1c980e511034142c50000d0b40d8100352010700001e00248900c22030300c0c401441e1a802030700b00b40c0d420700464190680121082040b5911a42c05940d4080243c0318245111842ea00800d81c0a62143d0b1110901621f000c1da4464109924001ca4503010600800d41000c0d00051005001400b00300d030851040c5401500030a2501c00150142d40c0511503110340d140082208080e03103c1c459001340c0224000540c8000c0342c0c0248150104c420341488440c0c84128444058103440b0002503200906000d00c030701c3c0c0c1c101075200385151030192030318500c030b290340381c80b2007400e01c0804c594900180d44403014504a820300b4000e080c1c2191000b4010095015202400c8000780303005030000b042c0c1640d000fa1008808203e400751005940c200c6640c0c640c06598015200080020a5617218180c1c1001c0002c0c000c02e4001c101c4420f0b450030b1140e01400034103a003000700058000207440b030111503030390a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 811226079 1250 811224829 811224847
    0xf2107050d030e010c020106031203020d14100501020f0c090114011205040804082107110a0b0c0a1109040f080a030e03030a050708010b030c0a0e2707090f0302061905 73
    0x2041c01200c403035036100016800c1c0c1d001c441500350386400d1051030a5a040140c10070000700000000c5070307200d510b4500140c4a40010255402a01100040414401306c0105128140d1215081e00040750740c26022964840103900480d52513030304060100b030340511b80d030004216540c000f0503940c14100c0145800301c030024901819000310743c0281c405640800d0b0201e024000d01c8000c2100d0b42030401d00e14003292a0380c808014489803803049020050000c9201c0b200390041751994814a80035060588072503841e8140700b541c4039941d8000c1c03001502c01c0010484200d21500f0101728041c0520b82104000400001c41d443e01c80295014128000806585e0a0710205441013070000d51b003e41809480841d96003080d20004100e82e2040c0c0007900b1001d42041800302c8001511701300c3e481080c0c2400c084851038188800070f40700100100c9035001e5188020000c8550798000b441c41ca22070071040d241e6078401c9482c1d140d42c1102c000e044c00000d40021080000d0000d100303003003000c1c01003240b403454264944128a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 811227329 1250 811226079 811226083
    0x7080907033905191a0d0e150703050f1501030b030709092001022805100609020903010e16030303091103150406140f04030e031606200f210705 63
    0x21452002c802036100c080c0070510302140b0701507811100c5a018103e00303040210100050840d1841d00c01d905d0b200294200c107410550308000a00b0108000703031b60007440b00e02c0580c59003803012222400083c0c50480021442c0003141d4100f4010020003c44501d0402c40e030006400401104401c0b6525108100d0300003107060b280c0c061503c049101c2e8902204084460a501d460002503081c070700d066411500182440410038841c000e059850400c000c403807280d49003802d905165040745404900d6040078000715107140542c004040f10030054008000030b00506810f651144a8005562410019a0410800700788070390005038100740554102c41010810380b00107840e00081c0c0c00c503800140b44900811090090710301c540d0140e45000e900c0951280340901f03103507210003030082004050000e000c03103a908684040000b02010751480e045241465200d43c4060b11064041307140644400d040c1004400c0e0020209130b182009418400500c0c4150010031003000c10703806040c103030303110f210300788650400b192003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 811228579 1250 811227329 811227413
    0xf030b1b03090c030c0d020609150d02030a020c15060109060f030209104b03140a06050a0603060e15130609020304210f0e030304030209040b010e0708090703 69
    0x40c10003449420301c68404e05043c48035002c0054070079034030300100401580f1084201d800c0000100c3d00c02c04001307050181d0240c00c1c0190120203144c1407020dc20001d840701140d00414085080782c0c115010745001000c45a410362084940798006041000100f200d03e00866800d040c180c001c1c00d003d410850400d02080a80b4500c081000000e001400080c4021020444070440c1445c280c42880010854006001c840c200b810f126481c20314012070102d04552080e131100320b04400b80040c1c5039586c20004041d502a0100b400b03110f10038540d101c0001036030303402881005c2c00c407581441200c0b21030340d6021b221014000400c10036a04900c0030840c0318444e030013510444c00580b80c8410016124100b1f800c00c0d02c06080030820b00c032980a00c0c0d038034410040d60060000441503a0b42e14000d0054805000440e0642c000e6a200941000150307041c0820030900300100b45c1620051001c0c1100ca98074090704075000c0304182d9824203141c1080409101180d04143c080b1140015a0201148809003810001038190 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 811229829 1250 811228579 811228591
    0x141e100e0d080307080705070302030708160b0a0608060a0b030618071d1b0a020a15020409020a0324210204060f23040b0f062203050d0206100f030b1b03 67
    0x2d0300004104410703800055071074200c0841d00e001414042d0f00e980203589d9108150000e003850b8000b040404200c044411586c6150740c0c041503031541d6080440c0e0308006003986000b0088507000351800101d030f0000c2845429406580140140080c1c1c80da100340b604050045103958102c3d000c1c4000100341c81d615000c902c04044203c040c1c50b4602c1ca095540d86007038420061040300c4000c820000c0c03414165001803041d1030741e43c00131003c240a60410b020070000744075603849001e40c98004151442201c0e0140e05c46e0034100c2c04001070110b600c0d92041d06c18400b000714010543c0c40141e0b00883c24005020b40c1103c03203d1840503100069460302e6080340c0b40720303c250790321001c01a01f848942c40440344e0600580101000c09440612045d11684000b503429040c00030454025480072900d101442c107008258550300d03000300c28881c42540c49041040d2501108a9128058490140850b258413103141030302003150044580000001c0c11560b9100703912401410a40b4103100e07840114044006107002140504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 811231079 1250 811229829 811229843
    0x3030f0313111918090204151409100e04030c050a24110405010c0201120207030c170304080a0c03020313060503060406140f0d140d09141e100e0d 64
    0x40841d1910b80145454900c0c2c16026074010358140000701c008400401c152011013001c2c4c089108075490300c2004000d100c8010b580306084c00b40041c02007041c102000b058400441078007502007025414040000030540b064000c0024900d41089446c00b5044c5c030036081442072030210581040c5480d560726280803814141c0340e8a0880c00c11411801d031042c02c09207901c04a00c000d000d0075400c581e4008042c0030f81c0c071885040c090498101c0e02103a102c0e0462030950a1850350071900c61340c8a0400030148104220211000c0d100d107048200c1c010152000d49105540c050142446c0c1824004215082d040d492400c8003944010b0240c04003004002c407910000e060a41c0d80c8645a107001020482603940c107511811121001030310f16016a160840c411501e400107a0704408800d0302e5191662140c40c4000940216000310352049200340d501204420446081808682a40a05a04001224014080141c55001010000347e660304007140421840d12190038012030441288002c51074403030326510700f154030b2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 811232329 1250 811231079 811231111
    0x10b09010917150601170f0a0b030f07031205040302090f1b12010e040f050304172b0311040902070b0a060f0e0c180a12172703030f03 59
    0x265a012040340018891500420700200d078404289440b03000d151080e406800380c0c0310000d000c1c2c0e409a00d0018140b0345000003a0241e1a15501d03960302c02d1402d84921a0860a1281010492400003205152400000e000e8400c091a41d0b0710710041031002c00e05e0328144002488008056958100041d00c9074031204403012151030300c488030200401418002c40e00305c40302400801420801240d203141540c20350318a4280940b04c40c109145001c0c62180c005180d44000280400d2070311404400c003110207912000c56446072105480b8124a2000e0101310f45100003d8002c1c83d01240710b0b4024451012007400e0039450151035031121800c5c0c1e8002d4000340e64004600052003200300c0144100c0c4010001000f81c40039143c01e003010700f00c3c061005081c4442c603010102d1052421512500310110003200103124000051b625490108900005441581d4140d42d80481c8000c040e5188104c5012611140360035901c80c1307030a6a0310b214805440b0b146500f500c41409182c0411000c90011400368031814503101c68 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 811233579 1250 811232329 811232347
    0x10608060328260d0f0f020c15010503011e05100503010c020706110c01050a11190b06010f02120405190e07030203060306100e040303020901021f0e0d090302100309051005010b 77
    0x10108a5850640c20003003140030204290f60038405031389580f80c1046001c50549400c1d5100c601400c2c9881e040410188009500c0c0c10340140050b50000540810003920030503030340c440c03c15003254403079100e4081c10031a4040c8a20310b010741d0f07800150320503913118a0b0264a038654000c24216541c8203120805640021818002c0da034110f00c09060402c0c60740000c0c15055965400244207005590300241407003590001002c01d0041800b582c1030781c003c01d604030141c071612402c20020340c150503103100d808030b21910300e0000f140d4401b0036070310342c0c100100307851130710b05403031300e800d0021440c4100c1c0d0318a0f010000d2500403410794003c210f00e60140c64103550240e01d0303062040416080200c042c0102c0c0202403009820044503c070003032465401600342c200162204000380060381002e607070f504582081310302c500c0d00d401f80d0032240d03018203096844c08044078015102c40c00f00380c2c0c104200c1d000195206047c03445082205110340c00103805203210b001500c0c0740381c01410400c010b5900070b80054442000100d80055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 811234829 1250 811233579 811233593
    0x20f0709060f0506160201080606070506090706030c0513030b0603011d01060306111201140406080303040f0b061002060c180d03051801210c020f100516020d08010608060328 76
    0x7030a0308841492a01240148010b500c5c07009a100078144082000040c0659442034151004541c119095541510785484103903242d000c0c41c082c4a0110785040c8001350010710580c02c0d1041c006880030000205411611144100440144000d0303056485100c81d240c91114401c500140032008030002c11000d00710301d4404160388103421a10b20f448400e00c2103e040030b4110b00c0341811659111000c0c08041054008500a09896080148a0300c000000e03c0100000d14501c0d40085000300300c03801c0307517403034180030441d0040c22011400c0050b88041c010421f0795951200400f0400c2c2a2120034600741210400304c1c1c00c84600240039400701e031010075180e00164540900c5c1d9038015007483d081e0130100030003a5129141c84003081c828956943d90b078108ca005402000072640c20b800c91421902d29500d035204180150004450f18480300c010307080702022a6000107031003010b0341916151407419030300b40301084991180050032254544a4605501da00c2402d118a040c1c1c05902804406142425810281 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 811236079 1250 811234829 811234859
    0x60f0e0a0e0616031d0d180b07110f0307081006060e0618010e091003150908120901110a08040b13030e010f200c090a0504021c03020f070906 62
    0x1105035428405a4446801e01182c01c650000085800c00050016081d0840003400311065603210558089680c03002c81d2000122250040d04590f21a14a56840411601c160b03805202da910700d01c0082c49102c0009084034480e004241c4050041c00265400600003450194198403010440d0014641c420101c0b0b014000c01d006403815003001c0c0c00c13181c0b0a42c0400c440d441407100000c07602c17142c0108000660b119824000c04a50000c1841d44103041403109103819a41c036100c04c64540040d0350f0783e50190030302c6000f410622030700290700f98201121214810384025008000ca0029582d502010425410843c0030341101c92007560f41000928051401c0380f00b107070001c0e111003039506104c03e07079000080d0301040c03000001c4020b03e44071400304104142691400e10a0300d2007803004498402c071040c02c82001641c0341d20008101d032440440e40742c00c10341070206c2d00d0031f840207134000d0700020901c440003005900100d100b40c1700e0702c1100c441c103070300400943c1401003e030045990a40c883c4010803400c624003000c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 811237329 1250 811236079 811236091
    0x609190e070f170c070b01090b13110a0c0f08040801090b0a093c060b0316061202130506121017063106060e0703111803030d060f0e 58
    0x81250058002c2000d03000b040c4036400b95500f1034407040016101d02c03040003560822640600106180d5071600615005040402101d80c0140d083c0352501c202240c003805150f4440c20b01d1a801c0d841c080d0641b5013115141c504800c25907002d42038200d02400241203d000b40020304c40b01c0000190010b40b85805140180090044103020b4141a0034101044a02451044070b4030130740340c906903400c100c40c00d8103520440c507179680810b40c003541810000c0c080d80750405000c124044041e03881d0750903410014207002c401801003400051001c3d240800c440c03e076030f00410345003122000c072120250751200000c40d613900c211464460003036070070107019056081d420054003030100460704201004c040b041860f500c5800a1606002c02c00c036415626002803001c03210a07102d250396403003918020080c1446005030100e4420030984821250018100c0c034441e1003880c0d80038280086461408491000c40c84298043d001c1055050104018040290103244141c900525644606410301c44c502080c0b880e40c28001403003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 811238579 1250 811237329 811237337
    0x3070314060102030a030f32010e160c06090f081206030102091302090a0b1308070519090b0102070f0f05030111030408070308040807080310080c101b020609190e07 72
    0x14007019030380120550b0034000303880c40e002409440303c0310b54402510800500b0748860100b014040f810f841c41c0b100c2a4510b142c54292040d143c2d07070380c1d162504030b90000c85003aa03a41a2403018000d0181c8140b04085501d8022a4007194803c215190100c10010001080703a0040c0001810f44495003846a0039a100000314001c40c2084080c1c0c01185004400302880d841c00c9074006030002c0113964541d00031300036040c62400e194607584001a0407001000c1030140090340d01c81d044001629203045d50b80c082011a01c1644040c02d2031038a503160000c1c20056070a02d0550240000104240340030882d400c00515142038001c000718a032200f0700d0700b12b9500003041c0c0800b103003c1041001140e0084c0072242480d50503c1c0403c07443d5200c1c1043c180341d001c2c03001c2c02411028000140046440d202da5624152601c1105a80300f00c241b00e001c1000350741501c10043e000c54000b03059550b1201240000000c0c01d4005400030b4504007a550001e408500c850390000707407035072841409000c40400804440c1d886056410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 811239829 1250 811238579 811238581
    0xd2006040b070c0602040305060c03040c0e010312030e0316060204092301121502070b040209181b0a050a0f03030e090c090607030318030c141b0f01140f03070314 71
    0xc40c00c0384628001c100b076042c0a0199558810410940c1c101c40003180c0041c260740f0b1508011003180c03015401954252000e040050020401d082c80e5001513040700d501103450103044007408400c0c1d01030240021b14460f030380002e000440c0c0d4400303601420240140b00b03020040e0ba85040c1082e200441d184a000946200c1613000d0035400c61000c50b822a0650308420300c06441201c1900d0007907080c00b141da41e100c280a0010404d501044a1545281d014620885240945540e0315040c3c12003050240303d01200d0354000240e07850300b1400e5400a4412290250012564075158004500c288012364001c41c0d405914120030030a056000c011485010801c0b284001c103030078a518800503234010702520f13074840d0100050000c1010f00a5011030b40c0c445050725000700c403050908019101c00c28004040c0c0e08144841301b46095000c0110724450200c050803020f81e40c1c441c00d0414080d1003050198800c1c14050010301c1e054000d0400c00c0a000a01c0c000c2008656a02d8191b030021b042c3c800000c0b0800310098000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 811241079 1250 811239829 811239833
    0xf0206070e0d0204110906120411102c1203030a050a230c070606031407060305190e0a02030106260304030f060506130608030405190302030a12030204080d200604 71
    0x20b031002001e01c2c1c040f100801d038255140f280050394820105410f5000d40002511400c280640104601c182c0c00752000030034031645481400310b48515000c005000500d40151a01c9104120518100c0303c0b14050342c42400f54040f501141c1d03000d6044541c80e405a0000c001c02613184038a01606521080340d11043c048001111600f2801c0e003001c007400c02c00031100c8000642000d16100a4890303441e00600240000c541e00d041c418081d506540d40345001c0d006040010440a0184c0107844c0984c149011813800301d030310301e4803180042c044000704013018061030340c1040269500f401010301902009100001d15941101045000302c001d04460b02d554000b03010400201c0c403000b04408105070440b001040b04c1c0d0310b04000603007100e004204000d81500d025004144500cac000701030030a4134000d98445800c080c440d26030000e8000c080c030000b98140d009400000005200b0b0b41c420020790070608015007010388824040d41004885c8480303c3c00140503180d241403441040721580e0185180320041c08080c1816 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 811242329 1250 811241079 811241089
    0x90c09190f110702120f010219230301050411040306020d050f07080403020d201506100804020303030411010c150c120c0207090e030f0301090b091e06040f0216030f0206070e 76
    0x3c2c800fa12448041d4250701513150217001e008801d90350b800086546603c0010501b0a2003e46018800002d0110786607840c000400c08032140b180d0720103000141140e191a040101809201000d024101d00038040000000e015002900014410f0f92003c01c0fa0700d00b01510404051000b4000c508001c05102800040f0350042940740018080f403404150380c44107403516034845007143d0b6038140d030ba2007a207080f00c1e046c41070f0174145802450125111b540c0003c000d80119071032003099a0195054000b000484c00003101040e94015801d03040c1000d86101c04a074070b500c00140300080002c6803a41d12104842c50507544054405400300c07c1e848100044103214a009641d0111030141c00d100386d64800025009120410a8881a1000c0c0c600d041d0341b580c550002c070014050400e0031900810f82c943c040f42c4441e9503481c058030160020b001410040e5961010071000c1d01da655401c403000c5900700500c03240011404550500c1c1400303600d603c060702c640801c00070f15080d0011316800420080e03d04516003581c030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811243579 1250 811242329 811242337
    0x60b011b0b0a091a16030903321b07050d05100c091e0503100c080f06010c060216030212040f12021305070f030b061809090c09190f11 59
    0xc0e020030080d40e5108a00006018018020b1318040d04980c0e0101554101822a880f519900001d07150052012205400350f0b1410900100813905441c1c041c11584087d103c030085140700d500412017904078400341d60486034018401c0aa00341c01a04c0a030950503001c211260003480700795420501d03040300d5211151240c08500f45200c11170744684070010420f2041400c8009000801c0203101e011080c1d43c98003165684501c5030b28028010031300500240043c0b0702c51205001145d880340e00882d66203040340184500d0041c0104d0500070030b10068800300b10305102428200f40342100800315043c0a0401030301e0301c02c1d910b0300c00300c05207003c01c01030102c01941001c2c58211924080d0040c519042480068a890544901508064900301c100810160f01000d0041d0481e0705460030403100c1802820b022541c40303022841c00e0b40c1b4182140c04c50990600f03c0c1117903480054002561042c920383e034005400303d42e042c3d503008030144440b0741c01140c4c80442d00c07580341c034080240780803c0342005000100c0800d0003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 811244829 1250 811243579 811243583
    0x24030a0b010e070e03061302010207080a030f110f0109030f1704111e0d0507030c0e0103030f0c14010c0806010909140103080f1209030406030509010e0a0618081303060b011b 76
    0x20782c0303010546140c00f480c40c58400c02e60081c161516131401d40b02900041c0d0300341400380e006214018001030381e48000b02d00c0d00d000030307059690002020711000d000d50b25581101407668151042e0f8005104042007841440c3c551403081c3d03201000901101002045003240d0702c80581190740300360a0000040e641004a038000c0c5c803d650b244043c911030030a03031000030388890106403c00d842e2450ba000304000401c0d0300085d20b200b030400000c556102d040f10b0b030316020309002c010040380304035080843c2c0600500d1700581042c40f5030f90b041c522091000c01e00382552004111100816400c1c014080e0319a00039051a001d0124814108000e02010f202d8140020061001501c0780000081c1c103018218060210f821070481007000c803205042c50760850b540c2c1e512074400c0d40c00007441d00000c01c0f0454030601812508583d5600100600f1125854500003043e5089a2075a00500d1000c401c0c00030309510041c241110307442c00c000000c01e2460a008085d10082d004060402c0818040a0f00c5074003d444023201c415 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 811246079 1250 811244829 811244849
    0x90307091107060603050f19120318020415061b05060a022d1e030708062e030605030c180c1614030703091a0f0c03040e24030a0b01 58
    0x760784441d00403010320401c500540b07074034109100482407200c00210000302c80126030456180c52051904115041c2d0380600c02010510190f540c0d00b501882904106444c60302821a00350014182d07000800b2280480ca0100b400d4000717803001c021464200d011111001c1c7d1000c0000040c5109590386516448020641100345a000c5003216240c0c016411240c1ca071046503210039019071700c0c108401046d0f0402503115181740c00c501c0d810030511514800340d07409154aa201c0c8907041c6c0328041009041f442e05480c0c2d01c0e468001d58440742103070303450300e65260400c0703003a8034001141803c12052608010b5014800c601400c02c00000040c100c04a00010740e02142100d481612107442c01c0840c8402028100050722583c82d51046108100e00840101100f034400c0e03d4140d8003690301e07020003084e001010701c01280d905040c48401e88001100c8014044c403260102500e2500d40c440036880103a92003a1108540485d014400445e542c03420101021012001c800911400c00746544a1810340d09c1400b07512446 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 811247329 1250 811246079 811246091
    0x100f08061002071a1608070506010504090809040f0e0303070f08180c0d050705180109140105130b01050417030406090f0e04030f02150403050c0106210206031b0a050403030905040209030709 83
    0x30700240342600d0805d250440c001d111a80f2074180a4905d4100c0041502c07a40100310002480c0d203014400d00300440e9003c410141030103e80c0e41040010300c003000e142040282c485404040080090001314070540c126198620190050a03004080450041050809058007070b21642151000140201d403400220388146183d41d0074038240307081540613407200e60021a00c03044180000f07416224203060742c0d040c4038200800e600302c04540028860030f00c50150030001452400f9030000181c1c010010104040c1001880c26554142010040c03082282c80d0394107810108091103c541e0107084000101410465003c0c000e0504025080000c0007500041c03d2050000070215614024080d16580b0720b120700c000103051415042c0034000364088505000e041d403074800041800c3d1038407402401034154100003681003100d15428000503500240140c01c4031100041d610b84040d582c0350081c401070502c0e550303640d1554990318028051000e190002c922450051045248a4a001030500200c0d41ca040b000308107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 811248579 1250 811247329 811247369
    0x6051c05040f050604060b0f01032904110403060906050906091f142401020304080c090a0b1302070b010e0c0316030605030d090e09010c0c08031005100f0806100207 72
    0x81800c00e02e001802c902503001040300b0720401d03600005084030280c07000745130560b80300c00450454008910744000e00d8000301094841c1c038000d080c0310000310000341c40040c0c082d41c085003c0301c07a500a503000312001038540788401d0810101d4080d09404c6902c100080c095810300b0b41d180780d12034070702d40310a00049011520381c3c1c110580703541140a5031a5a20041113050030010364084903150054152000900051018192544004125000c845109000e4000100c0c41010806425000790402601c0b03900d4107641165691407045806d00700301207240050303507500113285c02c1d0704e0b540c416444548515007035020071003540c0406085075030002c0c0c1045c012200c0847d40002f5001003203540c2049030584210048076000701e070001d20795815106825a404890754840b030307425081ea040ea2600e100098005a403201c001258800511b41203080814417601c140e8a51020405690300c00c680c400000300282900d0720301d03a4029603696000f400a84c1e11000000e41210080c0d9143c0c4603109504e40b002c510201c10039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 811249829 1250 811248579 811248593
    0x812031e1e0a02120420030d170408040503030408060711060609060d1b0b09040e030903070b0d0902040c1e03051501111f02070b07020304030c050d021c150606051c0504 74
    0x2c90403d104041095410541814801b61411203c814043c082a000c117100700d280000d28911907040b660b07504210189014080341a40740040c1c07048031400820320000c1a15a0148054809810884d0003042d40d4500404010011108010f8000258001c0030921240740c60300512a03034090401d451000700d80d0541d00d0910100c0c603940120750030236440c80c1030104142080e80c0003450b1603841190288080b03404c400a013600c9215500c1c0c540c2d8503500000b0100201c001017409802c1500d01220b00240452454010070f00381c410a090240000c1c2403503c4210010089215000105e40b89140400061030f2a6100030303000840c0300c0041c6c0c1409074034034003001500c10800455030a0500ca003011800c844110759200083e4010039030450b840400b8100141c04644004150750850f50801551240586007405004103150505401c0e078101468030400003004c00f214001e540ca183c40340590440c0c2004400d01c00003110320070381004041040812030342081c504d40a020300c1002400d000002926244c0f490980 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 811251079 1250 811249829 811249837
    0x10050412032142030f150f020301092406030b041104080f1c090e15030105130b070c02090105040b0a1214211b070812031e1e0a02 57
    0x19041e0b5060a14812804029000d0510030001190380444003403c19003510f059076029003001445401c880508001144000e035100900344e0044000031800e40e01d480d100e400343c4070032450341030400d41c0000040181c4182e511030b4040d010031101d10b8440d5040c0006102080003c40c4c820b0500700b684406400040742c0c5d8692080c03440100c540d90303d65455136111b030f480d9101c0300c40c13140c1c4d84000d0103500301800100c80c4d41c00c84001e81c04a207941e9034103403504040240012480c0604030068216200d0701607085518240704060242c8403103103071060500c00c680b82c41c00c81c660008040c642005900800314006803a030907080760551300119404140d000494001c270716003034a40e51080348400b01071850401440a241c00035500058001c0694030f501000e8176802d0004a280200c000200c2d40c02c02c210f00c01101c000d5625811b1070303500020340340c0217a84c40b0092454029020b003040e00c016000818800c40400d03a00c52444c00d41e140c0f88100d0924603041012181c13102d0b001c8131680c280c1c80c02c500052030702c004541c119 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 811252329 1250 811251079 811251137
    0x61d0c0f0a020a0b09060601050304200d0b040c141003020c15131709060702010e01140c0714030601080a1205161202101401060f0c0804060203091005041203 69
    0x85500c94041c20300003950786500302c2090310f054840c140811401d19000c2009407040f40103845442c40c60320b0f65a90403e1041b46d04000004200c0700780003c60740e5075118140100d4180c01074545008074102810020134070401035100b1107140c1c0964220964607212801845002a0a0b090058903210020034450501c00302030340614a0081000800564040e42c0c009004803d000384101c031801c00c03d003003065050b84280d01c000c41e4045000e01152006611800b900c4414405c18507207151185685a40b4000b650070000704000c407900241030900562030701d08021002c1c944100c000380055454244055154203a8010107010742000510702e41c045c0780950121240403070311015a03240300280d8107020006440302d02050300180581038261800090600070503031300c1d12000d42011010b91070110156004203142c4400014030401c8030045c8080382150010740000c0160f90050341d924480b40c0c041103480f1010a02050a226040c0414804000c501c1480400039071b01d0304064955924030000070142840004070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 811253579 1250 811252329 811252357
    0x121e08130f0b0a02031803030402061e0d0606200a0b0c0a050c160f0e0402130c030e01020c0c15040b04361e110d1d06150901050103061d0c 61
    0xd014030f9086603402180318044032106a07044010708081c031600c034070080d2406980140188000c610503106043c00071042440180030394500810003d5090903618154040d1000c21080c880c141c4074440801c40d896074224038070004d0000344240703a443c640600c001070000e03d00881e010500340c61550060003128410300058080f594103100384481a6103402c007030b00030b000350711601c4407000580b2220758001600490303004219825550790020114003c1c01c10700225000c2640781c0d003140d200d54a084c40100003108000d0701400c2c50203244000e000032039459000503075009004000c01c0100c0c80c0c510060328150365110000c0e6004c0e191504942191980600900d40c850410040b0310100480a6000801c01c00b50405010040c040e4541c01601712175561603001440d440c2013004020a40d450b6201d000d4082d510b130104190011a140e44a01e03180c0d04844904442c40100d5480d601032400704080c0d801401e00340303018002c09082c58804c1c0400d01e03400c400318000c1c40d081d4000c515a2003004044d24101070344044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 811254829 1250 811253579 811253581
    0x30121050a0c0812120601110313090209031b180406230702060606090d02120123041406040f020d03020c19090b0d0c0e0a0216121e08130f0b 62
    0x400030407864840c0304001c11441840a040d40181ca60016120a00c107800480705d0540d80f0000151504c0041c2240e80c10a80410404400c4541545c5c0a0f0070282940080045c2c4a40c01c0d43c0c00d140c54054602420f001e8103420f060404074a945020102e00c2240d0603882500c0592500c0c130b0940c02504015040406031807502e02c0b42c0030b4100b040c1c040148541590f03422a911500c41109000c1c0c0752084070352468000c1c410500303030005410700410404040c0a4080001904c0720080c040c840340c5140c00400c5240124007805100a014401ca01e424680c45c1d020302420483c1080d40e90f00c001000540402030062642483c0c9505241c001c1c0040444c5000142034400c00e466240b03a01c0e040ca60080c0610782189141040c1c0001c103080000030051560381c805801c044041c206441003034000f100a15007001140c0030410101e42c80103c83c50140114458220200704802e1208058509495051641044000300428036045540a903000e070f0803000c542215400341045041585a03082a00030203480021620 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 811256079 1250 811254829 811254833
    0x106080d1b061a1c080307110f12040312090b2718061c081806130b0703082a21040f020a0816061b1a0604050615030121050a 55
    0x1540c8200f10041225030350f54807202c62840e9070281450480281003010284005070400d030058440c0c40c00182c1801c1102c5061002220742450b020103031003420b2205402003420010040711381d4101c03011003424109442070714103011070800c0c180200029000d850040341c00384400e02502e40d01c0c03500c00711006061b0868604900051810000098901703900515002e801424080c119110041c80d281c2d0200045180217240c00c000c1c2104402104203540c485000c100c0d03403102c000042c1c0d9500c001c0440001d81741d201c03e07407401c014141031002002401c0042051400e40e40780c5c0120440034000d03201d081a166162000307083d03191840d0042c20035001d1141600d00032301090020307000140c90164421600ea07039038140c07200385031a250904200c402c255107007686410301050340118500d84c1501541904400c0d070040c1341d220100742e03440c600f440b94034841100050000c00e0406018490380307c0c10a641610301a081102e8000ba90300c41485040406684210703105500d0030081c1009002640220407540550a18 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 811257329 1250 811256079 811256111
    0x509010c0204061518061407080315060a1218051504080d060b0301090606031422020a14030c1c0204020f1605030406110c0f1314010b0d0b030106080d1b06 68
    0x11700000300311401e0b10100041c068450f030004154079409045490601004d07030b850341100d41010b42000600740341000550380c00d894070381c05888a66001c4e40c030f050076407a0500c4131804135180b90103c05040c2c00d041610f540400d00004520070a408100405586a0790341d040c002c1e0140603180c3c140003241c1c2442400540d40104201a50507903582e000e081050644d503000a404440402500c03158044055000401c1442a01c80707600380c074003400020540707174040c9500040c0840000c0d0480b4511142c1d07500240002d050401194107541c00944606011403004c181d08540d40d01100382c000d200d550009131255034541e0100555600070004040c2851980c0a480c0151b1650000d00428000903035107100303403a62243c001559918614050100b00c81c80800c1070a1000076042da043c2001050303199201501ca002d00d100210740213002c03404110703865100c00b40d0448195101041404c2c82603040203c10b0020b810b01084806020359241440f45d102ea91042d8490304182c507441b005442d8070f00d03160700011001e0390 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 811258579 1250 811257329 811257347
    0x90106020a1406060906060703030e0109030924022805070f06021b0d0611070c14010f02010228091208090a050306091209030703020301090812010b0a0509010c02040615 74
    0x21504050182003401c00c2d14543d50b00c012030b81d0f10751000c001004a44141401c500502ca0745001e46408102203140403502c1c1e09490020070101e0005004004c2001003000340c5119080701c561115411a14200e8004001e6440d00b40400010f640042e0f8040002000c2202c0100000d9591040036190071076900d41c15a41b6680c01c1d4451900075001d4100701030002d107152401c80c480c201f802061705000c03005c9501e402d00240300744140f40300034a03130801c500d20110340d4000161000709481c07032039801d982c0c03804000180107006824000301568014080031444102041203110000034100046045800b04103046410074001e5001d004124290049001808a618010304682500790307002002c1a03030b02c00501d6a240c204580340340c4160851601214450130501c01042603100060488454980340c1d00000e00312200040c1c03c0f1101d66002480d1100030b40640300450041008200301b40c200781600c00c0183c818850900014100885a2107038011503a0381e900c0f01014000c0e0980112203144400300140c54042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 811259829 1250 811258579 811258583
    0xb0306010b0a0f050c0a030e0d02042d0b031b01020a08040801020a02060601050c0d121e050a0b0102060603070303120f02041503110301061202030402060c060c0a08250518090106020a 80
    0x50310f082159040c025800c645001060200a110000305510100c0d518007954000550101000b1107140c00b5a803140144500122510041a100861250034250412a680c50f0310109030500801d05150382d004251502c2c2d6210301400d41100d01d81d1500102d0030030024502c02420b0303600214011582d000154058680300c00c003902204d03499110840103645501070f8000d0a031495003c0244988034600c240302c0e000101c0c011142c00305150540401b60520014001c03980724419644508001080503030740281401c0090078005441c0710306048011a031180300c3c0b80006020311904118131104000c05520038001941c204004540f926115503034824601c41001e800740c002810540500c48140c00308003101d04a420035110348005110b181d900303034040e40008005986c407030414415001c1d60350b400c0c0030f054490071251031251b5440c003811101900401c1d025000b0140c4d0603d545900340200c01d50541000d101110b030600741d846080506403114044800381ca240d0304a0010000060303026000039201c40214 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 811261079 1250 811259829 811259837
    0xd0914030a110607050424030603060f0b0405011403030313050c032b03140a150801020f1c060612090f0203010c020d0f03020c100c02030d091a060904240b0306010b0a 73
    0x44c407010021101c41c0181c0c0150f50401c4072400c0e0012403000d2141841c40400204c1c140461850394030b03105e010848095000903910704e5243c0101101614051040324090b11261410f00c1c05590300c2800700c3e07683e0000030002d1a403c00c12000350428400c082080e00c443c0080281101d54003d105100d0b41c600f41606644a120740044001d100d42480c00390042c011450701c00c9844aa00380c2d5640c218801030140340100301c80c0d20800201c00f1614580a00041c000c1d450000041a40c0395000803041100304811005041201e1501d00700380659584610503000462031008007044c501e02c142402060108901c000a45c50740c43d00418505103500894030500740c031955120140340301518a4150180c7c8102c94115095801071200514412125409044113841d940f040b242010038212a6900712000508155103425031001e85c82c42400d4880d000c0d6074045000d491550382418141d84000303129210061030500f000610105070b045543c29800702c0c002d41001070858400f541d403024907414550188500d14002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 811262329 1250 811261079 811261081
    0x200d08010509040f170d050c1209030a080105040b040605040f06090f18121701090615090503030315060904060315150b030a020a140c0c01020c0102010c050d0914030a1106 75
    0x40c645409103c0c441c64000d00c00300b0f141015590b40c3d69a19111842140010400340b14034141085680300d16807003410b000751006d90382c1c0055042802003400c000c0c942e2130703158400c10001810607403041010303045650a550102d410f010040018014010681029810a107010b092401c845071542000c0f0494103a55030800c40c2c100707841c9205081c0d4035540345a450850740c10030b49a0014803403101e9001c10b250b483c0f42c40078039500c0f600d0304915051001c0c0c0c0000324103911640117000061084080c84104211403c001d054945802d01007a1079000041000d0106e81e90007002d40c0031520b03aa0101c40e881203005200b0004c1603240d140103001241e80407410503240c2c0c0703000c0c08509095504040c0c50250307021200780600b19558020080041e60210300240200501c1c4005001103100a00141c00500c0401c4007238103a120707100000918252126100504683c10300126103d00c1e50030108a480030381c2500ea012500b038800b414081c0c0b041c40001910b143da03200c0010203000035540600c580312200307a44000c3c3c4a032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 811263579 1250 811262329 811262339
    0x4170109030305060427053906041d040611210f101e050301061203120606140c011b0915020309030c04050402011707110d05030c070210200d0801 64
    0x1b15400c01d0180c00c0400b902403903101c1040700071144218028030850469912a050320614000c83d0301d807640b20320900d86410704010441007200d4000701c00000680348a4202460145c0500c00e102c0002c214806030000100414240320890f0030280006601c200e0455543c10110b040b04166005002c250388130404400100d1150a410f040c103a0107024003540485086003041c554801007104d11500f0341d01c1c418495000103c5403820b000d241c0c010603090b020703000d50900505020300110240705040070080d107800404c0c0a11504070368008407247c3c6540b1040d44030034003904420700503c2d001700014540c400018443d400198480d0324901510000e80500d546a2806101a680c90140ca520309a154002d0500d0281a041c50350105501c180149000c843c0e80c0c6c0ca04082e6036107204141c92040c002581604810808081004005c0b8254020f2801d03900e50715103a040c8501c00d02407018001e12440d42c1c0d0195440c1325120769000741452501810500300c49960000d066a140c0c0c1c1603814102055210000042c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 811264829 1250 811263579 811263581
    0x19020a05061f1d0c0f07050106180b0d030c120c0b09061006020d081f030b07030e0d090f05040c03020903030c0124061b0503041205070e06030a051f02041701090303050604 75
    0x1d11800f0004060200b52261640c901a0703800140e00c03034245001c1400b4031808220240075801c0240090002004ca1460f80c141510644640b50010360180d40e10300c42003070010703034403240e8895401d4004c1400603080c503900b082140d4a1042c0e83c0c1c00340415002d0740c18010941004110903000300714620380c9403050b940ea0402641c90707911581049001c20400b20010740103d0300c61208030400450400940b550b152070341e50781e105100060320f8480009503641c4003404050b0b800c1028843d0141a4103065614624100c104000501203000e2903020343c1d114200c0d81060b5003c2c5e0183c0d4400000101a641c03104d889820b414028600e10288045198202d01d40a100300f4196034200182c43c80b50b2307030b88414500400680b12110080480442d1a44402c100014000d480043c0c1f4070025072041010748051031800f4104140882c010b00b0b054400e4102c01290000600005180c0310000001d0480f006242c0001d0311003c000e014a501130710200010803404806405c042d0701803150680319071801c0045440d00c0003404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 811266079 1250 811264829 811264859
    0xc0e060907050d0506010311040b0904050f06104401240c03020a06020a0306030b060303030705070f14060106030c0f020f0c01032004030506070219050319020a05061f 73
    0x100c040b0b5070400c00c1d1601d40660b9003086911003418113000c20328100d004000c213100d0340150700c50a200580070039070340c10500d0240249900005040e221001e40c2c2805000207a40d00c0e0841000400d00050a90090304081030300c020800031540c0e4406071503521040f14180c0180130744020421410f115810004c04d61001c01480c0040d0803e490300701d20039036411510f007500c2c00000450150103610518651400058440c002454184a6a80c0205c4c8035859031600d060b061a020b02200d120350014010080707155440815103000e41d4010903051002c40d444c1c101120006c184c0040c908041c01841d001151540e010340240d40218419580c0c180c2a55144004a803183c802400282030742d001281004619072013904440d220b2a0701300c4080d0030303141080300300040030350281d401141c6035085a002c00c000d180d014003802c40c00320f002100718001d44580395905903c038426018400b003009000a2140320b01e074400c204036461740764044112905400c01d4000009a1228495410208110b807038000c20b64000800030340c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 811267329 1250 811266079 811266091
    0xc27041101020f0d0e1005070b09030d0c0306120204150308040602011b020f07031b0801241d060607030504080f0f07080316080c011107060506010305070e0d020d15090c0e0609 77
    0x141030343d158a00410601121b880841010420240106c2000c25602401c140c011038114004550324580704211500341c03091002d0300d00a1500d0f044040280000341440400916811a00000c07407042540040c5240c0703909800140403420040740c0030903c1c603015800b1424100b0007140540c8007500503c4c089a03030b035a0026403d61290440001080000c240300c54520701034519440d24403680c0d859072601821911001d004040d10100445e205150b401242000d00c040c000c01d24031807030364810315a907519603103d0107400b0071b0103110005a11014144941c064902805800c0d050360016809020050317a90408460301c10001c0c06a80f0000401c100c00000719401040e00842508081915031946443d64002c590b030f0a4140d5214508a650803100d0001001214031604000034031b030600030300050483c1c500a100c10240000c548221034641d8070444011400f0754119614002c40340c0381c0c601804038200107100c10104900307010340030040151494800e426165040f0300d8654582e119001c201d8405420303254 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 811268579 1250 811267329 811267337
    0xa0f06060f0e01050c25080106050918030d06060509130c0e01120b0d0b100602010c090b03310204180b040b04170307030606020c03010e0c27041101020f0d 68
    0x19007903036a010701c50b404001041414803a08002c0500c2e000da0400d43c070080000440d11501c51300d010140b007080300000c00703000403000802c1040d0030030002c282481d202500d0710b42244606944040000e100304101d0f0131070541800140f000694805016020741c12804401d440340701c040007030420900d810b100b8462208005d41ea52008007550320010b5540d40d165900406009488900d03035880c9460b000c1503180c131a0320402c01d451031071500c203294082d01c281c82e8100348110790501d21414101c81c2c0c840c0c4540155161b0000a036500d40300c02c09107501900e40c00c1060b0828000074400040002c1a11b2801180c5038004d590a02c059072040101951641c048080142015002004100401c48121155600c140710b00e02421603003d0341e0031200340d683c00c1160154000781e00c41c503080c05119414481242d0140c07042c0c1c000e2100031014403041c0c3d200e00c0ca80c41032a0059240700c00c81303030015614124040800380e1000385a07000341004d042480340c11584800060240c41411040d40e49071900142d1290102840e6032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 811269829 1250 811268579 811268597
    0x5031e06010b0d0621050d0c0c091d070303030e070b12180f0a061a1c0b0601050906180a0b042301050d0e0a02010e010c110f030102070b0408030a0f0606 67
    0x10250010621010140e40e10400071404034941c200d56480c0d01070303005d501c1c070542c559480c01e45e2a001d100c2d0b0480d0204100d440d00240007829500d03000d01a08c884c91008030b10078003c0001403c5201c510680311006105256002040c1505503003c200104101d81c01c3d0341c440e507100d1903036100e107204200045484105a0300080c00c501030072491491083e003002d00fa02d000381001c440b40d524088616206840c00c0d50340d0442c0e41910101c111301c02072000d00544021010b03031400750508003030104800010784031408000000c2c00981c8298125440340c0303c01000d45403522640410320b03070105420141d0345d010340d250003800320303a642201c410303201200c6e5504502d00b11050048210b11904102c031050906000060000004480c124056404020f500000500001c580c60000404007174409200d039051169100761003011840841032491154416501c0035140c02d100b00c00709009104020010300380001075010b1100704143c58004500424440300c050102c01030840e5140300f2a02c1030701c640300200c0c00180c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 811271079 1250 811269829 811269839
    0x203040b0d09020603010303110c01030605102f06040b06060c030a030e01020702180405120f120402130908131d010302010318050f070302090a05130f290105031e0601 73
    0x4401400c800407030031000b003151001e40c3d02180d80c54000782c00481c04240c61028a0340544c004002c07818611b2000d203410f1008624006c08114101d402c90108000c000d0071400344024841b40d801c1c3c0040d40004910710800d00c0e150084642d1703c2d40001d4030101c0310705030342c000804c03150701d412001d8542c000c1d10385010350314100600e081640180107070f8041107040c1d50240502070159603501c10040c22485006040c680f585014a489420302040c502081c001d40d03400d101d002600425031098459000198515100a4a5500000302d1418a03040e05201403400c0c22615800c000d207840190004015480f40c2c003030913039191070180c00b8010311a0030000020010500400240d8130079044181c2201114000b0f00d40c20886880d06410810482140e0505a01c024401c000314180500c03c0307940141c1c888020403540c2000b10034010306480c00d00c8042c0c0044207262411003400074150016001c00d85008181001000c50b00256510103404d00c19288a401018440c158011441141c0030281c0d0403080070304000d80c245 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 811272329 1250 811271079 811271099
    0x2040e1e2404050d39060c0c03080a0c020a12050703230d050c0702030d05030916080304050111030f04060305071b030f110a0206040311040e07061e0507050114091c020304 75
    0x102100c2d42100303240e04502e0945c00420b4114603041004103c007502c00f140d9040500aa514143e40d000820842903442d2002c254420000c3c0d0f00800100000310340b21a0010040340303483c2c001da5000d04245541d030800c6660a400c40b004040b0f40d0322070b40316000300c00d40c0440088a03044054828001240d020030803101c0c0d0100b941e0010b9400003501c82c600d802c1580580109240030310110031400442d4001080c000106400c02604807410a130400c5c03000b4050810402e030762240101d110f02c5040c020701040c440e594034014401d485907500701880e460340302d5a542e0310050103000b06070380c00303c045021000503c20910b501404400155055141c860f48407440c1d17139049070f040c004103103c500c8030302039a01982c005a0329400100001d5004076180c004500c1c07031108100c101d40408090361301076841801e040101640100c080b1905801d24180c8090390700d80c41c00161142d2045000051555190030f0040b045a0320b044107490180c580348003101c090080c030340c0400e40400e407140021405a0300500080000c0388071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 811273579 1250 811272329 811272347
    0x130f1d0f091c0908060f011a0a05090f0a1a0a030609231009020a030f062702070206070209010b0c0c060414090a021318110a0c02040e1e2404050d 64
    0x4520749021041e541d0682d160500b0b00541b503141640c0c80440040140e60042000d040e100164009007501d0401540400740c50751244128071801707080c00c00c84030040d507650341c4207140045c155155000066800165802a81d40c06451560042490024040ba014810b841003201d07142c0e44810525010503076420000050200900b442a0500000d901041420560002d044e440311030340c0300810003142c3c000d6443c040e078595400102e81c00021040d1714203144c3d01c000c3e015203403841400c130040e40c5180c0c03030000c17440c10310420344003030b4012030810000039110454500400a591f103c80c26a400a40308008000c068452441031104110561103c00802c3c034020213034603002030010100515000002415005801081e8443d03201c0c602c0c50040000408024020700380c0ca1500590000c4c6442d004010250400b2044200039005030754510100c1d500800401c00c0b40030307002090130f00e0f1194250400501d03030342d940401d40f25040950040640c007e20b80c0c0c010441801a580600600300d02540ca49080300d082030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 811274829 1250 811273579 811273633
    0x40b04030f14010c0201020d1802153601030f0b10050c010f09060c0f0801030b160c1b14040902031c020a1406011706100308130f1d0f09 60
    0x42c019450782401c0109200d0003000c1981c0342c0000d601d40380008a510100c0301040130301034000c4481c80046005070740301154028601c1c3d28001c04c5440708400c0cc1031a0300c8944021501301c0390000d500000ca00e80c8400880448001c9003660103200000800300d840c1c0035103142128032a0802400270510940a0148015001c80040c8200004943d40b4480a44090f03907040f0900303a1302107079152103000700184c2c800c1c3c4860790503816091003d070952540e9038540840c80300a29061045105040111003140b087d400103468a070089a194411807000460b1149011140300b034100865a600821805080900902c1c00721a0014040c2c0036a540ca40c2c01500e000d010340603004114080d42d80f903100002c2d00000345104460300480145921740c180304140000c10341140325002240c2c0190104158000064106429a80e000741e8580d01c8681078000500901d038140c200b00800300c261000401c0013030040e0000707010b41c3c5400b1041080c980721041c0210910310701b0b54545810b5001441e5266216880040c881e41d051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 811276079 1250 811274829 811274843
    0xb0705070e1f121703040b07031104181506020a0c030221070609050108060f0306070c020103021b0a06060603050907120812071e0810230d14060c040b04030f 69
    0xd0310b40740e101c840e070107880d000f803101101603d80d403c00f8882d9044424400c3c680c0442054030358102078590340950140281a1000c250310f468044440508000640e0010708162003071802c41200e620700740d000b80c0a5a000d60280582100002502500c0000d000c016a9040314041c40e40b2803c503024008000c20300302510740ca92080714282e60103544d040000c1c81c000c2001e81d42d041e00c214101800140a4800501500d00c40d407040842c5886640d03002ca2202d80000b15410301c80184199880188c01900580107014003d0701640c01d1012103c81c08100300d80b060f0b210b500c04102240d10341030103600312003098510303605c3c5174030000080c0856914544104100c501682d003082c01d0440010281c100b41da82100d00000007050503400340a80c1e008242c51100740642800e181103a49041d007040103111060b8800c1049000301181c411305080b03c240b200b0122010702900e0b44803000c1441c1404840d44180104c0c1d00399a10941000032400c0c0d0011f0141ea045d1070400710241e18017451515010001010024169402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 811277329 1250 811276079 811276111
    0xe09061c060e010b0a030f05010605190603090609050f0a0b0c130b03151309060b100f0507060b09010e0615090f0d02060903070f08100204050904080c0a150f060b0705070e 75
    0x70350765800802c005500c554600702c5000303003d180c1103081d10304643c0321500955401402103010cc0031506400705503030340c03880c0c005030b8106203040c0880a0300306164040c200f402040e682c00320004020411040ca14000c28090049842c2c050300382940b803107104281070038092800014400582924010758000b41032009421340007400100048441c2e105070328800c082580c4a80710007c21249004400d000d1000301d612810700c031030710340b8003802c10700c0501503401c204840000c0c1c9070f08010465100000c00c04003e07041104541c3c68001c580400501512614403502e912940440452545e00032103002c60300151041104910711780c180000c0665000d001ca070301403010300080413152030030041d0f64002c0c8418440c042005250902541c00c00b0282509044842d0041109112030303125003807030540280c0c1c000159a41d45007002f000b0b505010051a0080500c0d18031040141c81e40f030346412085554910142c10494140c0d581800e426a104e5000024402e40182c0d000304141451403d820b0742c04109950032643d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 811278579 1250 811277329 811277351
    0x1140a0b0a02011a0402090d080a0c0b19150807062f1b03030a02030708030405031b0102030609070e130c03020408070f1a03040305160503090603070e09061c060e01 72
    0x9103070444802100182c1d0b4401c500ca81d91040e0001e080d181c10000d43d0110714000c81d00010038004000408081c00020001070031228040c401c512070726400c1d8000301014544c1c100084203030f0f070081807801800c0714641001c0306072807542224108107080711404030003030444515110080d00e00800d5060b0742d403107070000d6280c2225400080301c0841c1c50030030300b040689036203851854a04000445100420700990043c0711140c10b2613000822621070a811480707468490b0b40d107160203480c600c501c4600a0044a0880c0340303000038641500954018401214990555030794138030f088507135240e0074442d698401e00600ca0740d185a61740d6407114059400364580546840e444802040c41c000d001e134003241c01030115000c100810b0004c0c036040c2070340013800140700c1d25500701520014101d010b030f98040400194510440c3c01040420811180507031b5024082c191a40740880c400b41001d40b000b0206801481101e0006680b80b501c0303901c0c0140d42e00e0b5001c5944c4100d20035221200104402c0109417107a650b0348000d410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 811279829 1250 811278579 811278599
    0x1c1e120f11030f040f0f1202070b040b040e041b0e0708090613060b4c0504060f0306090f09121e0e0102070513051b03090a0206030a23010609061701140a 67
    0x4801c0c1e008200c421414247c0c840000e2601007a940b0410340c6900034401400b51480c41800c80c2c045440c04d0322103940b01c1d01c035400c2c160b00040200e02422000c000980300012102e8004500c02e114450a40710f400c2c84c3c5e941c2800803601c44200711020880024030580360b00c0040c2e030962040308107c0000c0e1540f0800303a04001c40502e4480034905403c1ca001200030090b2050361660021422250f492194590040101102070181d0246001d51014441e0180318030a000707119510080042042403c00c0c41545010080600100300d10f0802f80d400075030042030f400c001070007a82060b040701c2800b2074048180381010021a11024810031090450003021000581c80e55201825021195529000101c0e81000e541819003903c048a020814a009100b000040c200204100c030700c4030340645605a8a6513007001c1500200f000e03032800c00c030010008020241c00c0b18056619410384050b511100500390f00d5940c01c0da0f18465130041414100b8518005000303541414103030713003c041800703020b105103184c603000812 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 811281079 1250 811279829 811279853
    0x309030c02030d0324030b0c0705030d150303030b0102010b1005031305060a05070e180a0c031418160b0904200a0201020c07050a06021c1e120f11030f040f 68
    0x80019480c2c80100b04121840c4810000e005a00c802171401c1c1c81c91983d441030b0a040041c80401d1084e0042000414420288210750140718255030030010392000c0030300c0d071101d002c1501081c3c000a05e410544442540140300c0c8505012000b0660007401554001c1214250302c0100401c215560301091400045d208002c2c00d80607101552000c01c851505800003001c03c44020341843c8580d400c40b00320a400400c88541d00c0d00a0b849236000328007070f400c00310250302400380d003128071880c42031080c20440c201000c00542c0c0000c404a03401d980181681100c4401809564003c1540103041009849110b240c0790f4002845203028480c0030361481d40d01d01c03058859410145903000940d400088010134090241b100317001421044510441160030144000d40d1400180d110100b14910650100d582c5d03030142c03400980c184100d030340604080d040300c2002090410307080e01c5000310328103010102c040d02c00f0901440c9004419002c80504550303443d03049450303403100604255090513101259401042603603002e2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 811282329 1250 811281079 811281103
    0xb0306240706021e0721090e0903031602011a19030602120a0e0303150405070e03120d0b0a083301030c0e0a1109040c0e03030c06010f0b13060309030c0203 68
    0x41c0c4031107400100311107540b030440d041050603204001c01c02c0084c2146580791242c2c0840c00e2145401003a106d8280c03808090b41d00b001c41c0c0050160104150a04008001c61080c1c1842c2c05c4a50300165948007642601d01416000c001701d030002800c41c016003000c0c10115041c40030450400c050f0765690700da0800701e07030064003442a41800c1c032080240b0b0000c0c0d8018841d160909500841c658981740c0741c0b8000e080c00808480303103c0c0741c4072000302c0c0f03480f132240510860112009060f283c3c003e85040030107129074401501880581e043c12112003e601d8000c040b4012111002c01030210441d040901405039405041048034400c030380301c420217400340c226000901962141c0d4141401c241407954007038581800500d400b07c45424014920f401d1103c0e5010782c1d0003038209440120f58500503ea050740d22891703011556403d03200c0400c9400e0f8280d4001650360484035050500030720292110303c941810320550440c0c044c2d014914004020380e80c4254014068031b4000e00c0c00103800002640001e003081480010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 811283579 1250 811282329 811282331
    0x1031112060a080a020108060103020c24070917060601051b060405010614190b0f0403080d0b100c0b04030f050f16051b0a03020d1a0403180905010b0306240706 70
    0x1c201060070854210340c040d10460303006113110a955400288504c800030030581c1010b8000c1404007010340204a4403444058801e02415001803610205c07600c0d0390304580d000e0010340d40040003d2900441004043d07407040110180001d940ea560040d501ca9000844400c480312881d50281c0b1506401c1c01041d006911800c0041220703482d082280505450480c2454407403a8801d03440e08050020100c884203c41d00e2003002a10360111072043d047d43d015980c4043c0c5010342c00500122806042ea20134005d2003012245281c0800928031b044036031500c0301d0002001000f482010138003190080344c0c00d2001e40d0407840c2880c9021210501c03009250088c0c0c0c0710129440f581d00401040000501403040c100c2c06004801c07107200c0c01ea50000d501840343c0e22019000b041c100a180050141058900034403089068980c8014101450f0081400b50744880202d02200744c50404590b542550080504030348000507030358219114501041140d1005a2208103205500c118a200c00d10550f8003408603e401408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 811284829 1250 811283579 811283581
    0x70c0e09030423100c032309130b100305101701020c060115050a080406182006070b0105011d100306060905030706020d180f090914061b070201031112 66
    0x12032811030f2503680707081c000481d50380407400154550105080f03010400345404041c20105050036940701c2e108505820781c0342250380880000c0a1a44002d00d0005400d44800c0e0b8401d0000c049482111040d1750354136803110b0910300444100d4825000140c00c0f441c120541030750190764020b540d81c2000c88000c1a29165004a0124804041804110700610610344440700b89000340d80c0c01411803260031000e4092220040c046018003440c0d03031004d03040b540b040c1c203400300416080c1010301f1007075610000d83c00307036002c214148c40e5141081e10035201070340c1d030181d480d00403a4280001513508030145001812100400d803441c408035501c451080350f13a940d40780c400040c410305000e001003082c1d02b241c01450099114090030000e2075400500c4800608a529007840c402450003010b80c001000d544c0100444500d004000c201d4044540c4100c003a148150740100c40910304036019901d5500480f0300900503002c040c5262000003485008001103407051400050311804c0c01410030994000b84900724074500080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 811286079 1250 811284829 811284839
    0x513060507110304150201060f0308040e0903070c050d240b010e01050408060a021e0c0d032306060a02010f05160801051f0e06040902160204060b1e070c0e090304 71
    0x2115468108a4524200410301e60b41c088107a81d070702c2030744118202d02c007a5401110189100b980004090103103e420781c4207555032800d01e2000c2d0b030014010103c002c5225008524181000400c89901a5104a920444915010030014021080b02c4203503200c041c07484441c0300c201c09400007410380050700c0c00c0020301c0e0b00070400010000310b500e000b0301e410300108020900041c03500158482e8480b503040b0300580d031441d004918848051001c00104851100800d0900c004180801d02d81c4080c0c001d50303802c0250309401081d100d2503c565a8601e030751454500301142c0c80307061100062403000715a0001044200340040d00804480003111201c03440074940035060541a8041c00950040004030342071180b08001059040d0000740e4460100107100003207480ea445611034000b900c00070301145030304544039107a9031210100040780600c12440740c0c0c60124003084034102c840665084000c0071551070b1300c01c80c020100c654164407200060b540c4103040940090300e0651940075a226449580c05146c460f0b10348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 811287329 1250 811286079 811286081
    0x260412020304080a15112b020306010f0f09120c03060e0a120f0915020d020c3109061d0c031b010e010c200a05120607081009051306 58
    0x206001408541003084100007401000500c0f19545400c009141041c00c94442e40a00412400d102d522405401090741d100151107510b02910000b4104402e10449803200800300491104803146400720b01c14005012149116a0f0003500040090400754559612080c0d2050411031540040381d0421000c00b00340104616401a0080e40c048040200312a951170780e82e1442c2d00b039004c1c100008000d04c481d6141c10349171181707203004001c0c11b52010420300b080c00b80e50025250fa520fa403800300544103070b8030000340c1c5050040404800e90120002c0b940113043c000d51a1200002c50640510b80c5a11800c8820100c0d005c0e1140c3c2c83e010440b0032040c610317044101009800d00f40d030001264070a801424444c080116550307002c840040c0c0074a0030140c000240e00050b0b58200015001400480019000d03130700c5950310383c00400307100204a54001d81c49640b04d00b0010101140c8480071b415401c0007003c1030035039001e80c001c02c2c0c000140e941031002e001d8a85402ca8119141210214404485203440300e0600c07082d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 811288579 1250 811287329 811287353
    0x30906061a09130507080402130f0212220201022a1002030913050903120603011506022508100203071115060a0e040209040206031e0f0916060e01030209012604 70
    0xe40c02e00c002e24008002a0a86d5070007007019000300c5550a00e0b0740c800d4a40d512900620509050071074481c2480141081c03000c204890200641e40b0740c1280755681100d1001581d030079541640242040000301d204c01d142201e80f11301ca0032421440d064014017560710030002c1e250380080e9500441c0c95001c1a410403200030b640d120a005c0f680d103010240b000082010049605400f48441c000c403841e00e8400110b40100303032495440c04800f00030300e8081b80007503000c55000c8031384142441c80781050b0000400340c0c000c015503109042981e4001c1002020401d8181c016603480711031400e18901610242501310700342030118400e8510751060f0400c00105103000f0b403040300a441036005000c0280303001d50214a50f180c0103480a44140e45c044000f40b140c015443d01c1446a05100720b0183e820300306040086254007098501d84490701079480c54513501d543c241d00e44800c85501d07075201000510b85100650081d8482c1c00101c0c10020b00b00d00310340c0f4112201c1e46d243c40060f43c3e0180460603192904100d942c44007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 811289829 1250 811288579 811288609
    0xf0c06010e090a0201032711130b01091202121501050301110f07020121020d090b130b220c080a03110f0c01050f04030c08060412031b030906061a09 65
    0x7890a0000300c000024080140c20350a0030000748072040c0703031f8941c03130748000490680c0ba07900244c1304044100b0081080240d0004425140f20f544101e0220441007528100984035000403540072040040600507045081050b0028006040120030021001c2c2041c82402203c410113004000410807420244a480f0410700d005034002e0905140a052400c80e00c50100064108000390014118010903032452a08041040724110340c2d0742c960107444405411000320076030300b403481c0300d0005140d140000410360035103501c0803000c0c505a0b00c088000704408141a10401411a01c128410028682e50701c1e50380a005120000c103005801450001c10588d1507203225401780c2c00070030240c25903250010703081c1c1048030242070068a803105603e40c00350301d00a6038405030000c1c409000014452401184480c02580900c1c494802600602820b03411756512800002d44c00175600d1f82907203941d100307501001c011032280c0320100b2032540d07480c15000800d00d2403504195000f0002080d0078070340b400611042601c0303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 811291079 1250 811289829 811289849
    0x9081902060c120901060803040906050906090108060103030f02010908030406090506090d0915020115140111071202041802030a050c100305060f0121020a1d1e0f150f0c0601 76
    0x7290002070142e45005100c207001c284a52140842c0c5281400e400200240c50780c02e085a40312903564100300b0140506d8400d060103010040003151003070504000441c1644c8030360004000c0c1e40d20399035044500070401281c031f204555a6810601c00180c140000354016405000b010900d4620f904042e82000c0c0081e024181d554401c981e6210b00e070f40c1000d4404212001c04044040b00322032540282d014125100d45126040510840425583c490b2002d4081640c02a43d50040281500203030f11703a2000d41d8010140d14000c1141034078018035058120204020355040302a0b45556a617010a00d40410f100044a1940000f04a17528506124507008045002031a05000707a05295011a25402c3c1405840d410400000004294084041d04000010214081c21503907a03a41c141c00802074003003401c8081d02c9244103100280c0344c2c42c21284010350000103010362507003240d806003041f0402da081c1d2040c54214503480d501f011440001c4024103000b9082c518140d5450095981880c145503058209540217 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 811292329 1250 811291079 811291081
    0x4050109060215061c21031b0504030210120203090604110f18040303020f16050c0f1003050910020a05070b010f2105150a09020f030615061308010908190206 69
    0x6a000c0c488010781150090f02c0e1444008a100c5200c0792815225101420781d10401c40c09110700c0603a04290600703203100c0c0c1c2c0c0030400850484236100b4501079020844000950510003400503140050000b00092180d04102030840d03040c0f1014000d0360403c4a180d1a1500410104030505c04900001821740c4404c69410901c4030354107001841007030303040740c8250350300701c11900103270405010307030704a50703400d50000c10258a40d00c402404a1107500c013044111854050006000e00a080400040c070103030000800c1d41840f52030041c401c03401060300074801e02c074074414481d000e56102c106100502d070318152680c40c0d070307035034a200d0501c4038030390b181030b030041003284402c2c01e0410010458804150901584040500d2203600d941846858410030340441c848041c5250240316140240f68401c4140c01d2017a01e9a403c0d43e030302c1d14101030711100101c440b05154011b02c4420324443c9001c0004000c400703094800707002840c3e01c3d640340a00311406810204e6140c1d01c0010070483c030080c3c68088403003142461000f001c42d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 811293579 1250 811292329 811292353
    0x1090f031806050c100519060e07020c03281a0106092103020703030804080909010b0c0d020c0f01051e0409022203380901020a090509160c03050409020708040501090602 74
    0x198a03603070f05c1311284256850300400c24821f00001d42012007180704809200c56503c0b80ca01a6006600351942c40140c80340400c91402130901144404e018803101521440f14806142882d8070703100342d0901169090481140d03011112400e88490b40601340d2940c506008600b0a56400000400284060740c21030503504018000381c1c3c0042c004003a02c1d41886c00d41650f40355407414002d02e009000340594070121503400814064020720241424244070401c0b10031041ca80881a40c850421301c0071560090080c442020b299401180141600143d011080038510a45040f088140c2c201d40c001c50803158001401031860025020b214200180b54022130181918580e03030b0240c4029090a0032012111758140c040e030105941c1081500e54001451600c0c0600d0b2100c1190700030350251a0031030202d40c1c03070b190202e02410010301c1688101d4801c20501009800c1c44000d03103100484c14012000c00c64100b00105100310700b8005440710314071624859840301c1c10a40003402828843c0c2000c000c650000845c3e400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 811294829 1250 811293579 811293583
    0xd1101030e0f072705160f0507030e122b0201060602150f0604230631090602040f17010605040216240c05090405090a030206010603020c01090f031806050c 68
    0x489034001500c058213100307560300c0004001d0000d000441d01380350030100070b242480030300d0b03050381c004044e51f4801902c0000001952540106207010f030010320001040d6402d82407280803034101307802c20720490311400d10718800f01000c6204034080c4200384080b4698141c46507024018880501914000b4140d8400b0000740b290030401c0c01070213040f00100e000003040c1140c40d0f47d40055603070000e0a2000c200d1070710050010b4480d900c240d5055001d071001256540e0500c0c001e40a000030850306126442100c01d0440c01c1c400640b8021509541080d820000040c2d0318407040d48260007001d0214803000d08101c500c2885084400e00d9110740d00031401013107101d5406205050941e01e103540050450107a203944040d42e501300407280102040d2034a0601c14080340c5402001a0500100480d030074001943d9120889403a6a4651401409603101da001800300c0381c001d03005170128065210000400e5410758551402000c1d01450590100c1c5041200d0b10004040d0304d240d04c0602124100300389400f2885008903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 811296079 1250 811294829 811294843
    0x1d0d050a02060f130b0915091b04112206111f0f090203030406390f170a0302190c170d020d0e07051f120c0c020d1101030e0f 55
    0x428868549800140e0001440014400ca136410019044451915118041d80c50500762901280a640a4001203100d10009051801a40c5403030380f8211130039220040c0006024480041c1010503814404052140031089160a8008014940f80b06031460954042c000d16881200b141040c0c201d078000345046401002c0c90300031001140800511002140f0010740200509100258980800600054070a41c40180b0321600c2645001c0310095850700040c42e400c0806111700300345403204140c114008914500c407980501c6004042c07a86000c1c0741c40004516540c400ba03420000f00f9400b040f0700b0703900100b0b01035041d400b0400d414009080a00c0717481d043e0049682e07581560250000007400c0c07241c0d614540550340308000000c4103201e0981c03103c8055442c0c184c00d0040703a0182460300c184100741949800344800400041e2100020864026031581c0903000c2c18849009000310188210f006032210941d4030340c01402244141c1c64030140d0b40c001030a80380440c00514072580b001c2402045400c01081d08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 811297329 1250 811296079 811296091
    0x28021509030c0607051c110310080102071505060d0f060510060216090c090b032e0b2710030b0a08160b0c070b04080c09010608040807150b041d0d050a0206 68
    0x20640b1b51000300000303807035150311003000740350907081c0314041c1040000c10020394041d070301e103003448400940c90700782e0903080b40110000501501c41140d20448008441d5200c41c0c5c1022000c1c148039800f0a242d2200005048840e0040791029a901d003004096208500d400300507101c40e102500401141c98078008001131640200d070141e599454100d40e64602541c1004001c3c6407031480c00c5d480386070040d4840c03105034040007807201082e140c1c40029101c0c00f068070008103881c04400f40300e0505030018030050440d1900711244000401c00044040c2e1680c400c050b210602c05a55000b160035141942070003807002d0385c0d07485030025034030030011507104900d441d0801040c0c40303051041d00d81301c41507942034030702d4101558442c0805e1080041c0c00f0a5250303000c2a5241400001d4a035007000da41c0c2c0303000407166000215000741c23442c0c0046c03010323200017a00c54400c0940500c1029010507101c0d03446c0d0000381107806001c462003041c41300d0b0081074a0707040103208282401040d400d026040102d04203001c0e41300c036402400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 811298579 1250 811297329 811297337
    0x9030a110301230a0f0506030a1b0b120a0c09120f061503030f03060803090a05040203040f02061b070e070807110a0f03031d010c1428021509030c0607 66
    0x2481100341c409500c0085010070302007070250381c804106002580700d042903d01070750302e40c2062601c01d0815480e0269a00035400a001410503504a40310030341002420003008011001d000400200d0700296000360840031080016220981010b081d184112510f103800c42d82841200340040064020815007044042d4001810ba515440d840c5418001400c44031081005000b0541c8017109040d402130300c010007031203d03031004c000d000c0d210f030040c994a002d05000030b6880024407105001c2c60800760042c54000c1d204004941c1200c40c5a40010f07441d0700503108403000000206034bd045c01002c00c000c1200103041c87c11080695040c4424004c01400d0020b08442c144101051841e40c0d4a40400c44030f141c40380c20008501c02c444036803400070007a001d400c042d40c055001344c80104203104018441c4250350401510740c1d45110700505403032042ca8002074807100e030340d411024100c1e0743d2201509400b0b0901d64180d01900324070307072191840090254081c2078080030f54030900140108000010380c081d0054043c4c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 811299829 1250 811298579 811298603
    0xf0801050d0f0f0302030316080103150e100c0210060f050f22110712020303092e0e06010e070c1a0613020a090302030c12120309030c06011d0c09030a 66
    0x1442d141000740200010072115440c2401024140d000c40034500070342d82101d072000c00400c46141119016000e0002410001e45220764003c01c180a034000e455140700b80040c0c600c4503010b400080f040b41c068600800141e08400360341c001b2040c00344140d60240120000300702c030f0b1500344030120392240c0ca0987c2c0b5502403000341581c04080c01c2e401d045036441d800d500905018910b58880002c4c0d2a80004008854403100d04d84420f8000340040207507842846950000c103843c5960708203225400141d1214544801070300e0040c0012100c8a010360452020000c0c01003455503d060004400c50070018080801c00c04045a900c002403070041d240700403010320940800351038a0700400501008002c1d00c0420102d480001c2d11032486401070000c1046038022002d85000c0c450240c240704810f001c0a0440c00d030344d00006680030342ca1044c84051600035079080103c0307003403a011040c0d151070044283c015110494000e01e000d40314640d8110303240e910088840c046030a1040080200396111110000146034410309a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 811301079 1250 811299829 811299833
    0xd05031609030f0609050d050a0203122a031008010b0105040b0c070918050f010b0a030201080c04260c0d0f020108060409150c020f0f06071b0c0b030a0c0f0801050d 72
    0x42048001d907030080032400510899207801c0008240c090b1701212180101c0145a080364007070340660b00085025005107251408100300ca9004190080c80c01070807141117a545503610366020031052072050781c0a40070740ea034100b01d07146060307050007980850303a1a8142202e600060343d111084e41c040340d000c0026140c5034103544080710b00302034554002442003841c143c00b0147d0001480301c40c42182d8011000e690309030b01c5424040d400da44111403816002114003c0400040d407203002c00f15440b03942d201d0841d01f0302da100c625a04085160b0302d140c018943ca011440c07280c8040a00824500500890340184155200d82d20074010700c07001c080c081e042c0014540090755a071a2038109010159101d5290f106003004c20454000400ca2201840e00601c01e00e00e65417030810000500741c2e00064034800818040d40d03426811141440e0b5485060249a9207484810000d2251310b45100980401c0410545a04c2c14071070f44800c585102044034108400301d4040440c058000d2050740c1550015180481010703914 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 811302329 1250 811301079 811301087
    0x1090c05042c0715120c080c0f07020a0806070207050102120307120b120706050c07091509051e0103201f0e03150a02030703051b09011d180106020f0d050316 69
    0x11307801603400c554059400800c90743e10407802c00d4000c00520b02080302400300441100d11030001c0326528025003041191500c545a100c01038442203100402c03174100b554030780e0718081c00c000c410f03903404025a01420040c0995a0140700748101a0f8071200868198038000300f009003444a0940c5240c0140d688001071342503500c96002e40c01c0c0c4100800110360340c1c00e0b0f50305002841c5a010046402c02d40c000d00c080862000058000d6070046029005038080e903038180300400e402850007504441201d1820742c26001d141c0211444a0b008500640001c0026100d05103240780340305869071840c0c03103055a407213070740c42c00d81d8501d80312040d0349820311301460703620307401008245010301c0440700a4150020740108641d502998000314402c1c1301699040c4110f446000000420300b00c1e5020031540e030300d800c1c032581440b03510500700360011403070212031013103003042a04c089899000c8428240c0000380d121001807004a0301008061052104d11000341004501400014168040501b05040300c242c0441c507080043d102d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 811303579 1250 811302329 811302343
    0xb0709030209091c14070204150e040c03060b060c1c020f01021309060b0a0512070e060301081c0f1d04060306060f0303090501080601051614030a0201090c05042c 71
    0x1015200b14018240448015540c1030403440034070001c000b88001600e0307a48240382100200c892013100c01c3c02c0c81000e500b00310140100d01015050044500e40010307128403101d9103c4c0c001e5000d584482c9a19085003000320540b0510440315000324410081040340030000a504200700c2c178070900344403240c0c104038401c030300703158030308503400c1d0258008940e400045010741c0b02d00b021100c1040c820002265151118812409001244030210360203000481070a000410a99031080a514200d05454181c1f0006601500300f078110b01c803551f01c9a0900941c041050a01c111109031500344503032a55554040100700e52001050500d42040d204612a0203031220740150010b5640008144a01d0351110f2a4002541c01e0f44001c1d40011481071000555500600302a4040c18044e0348191910f142010b0111000c0c12055044662907403059601401400a00251544038034a5001040270402400d00a0344022141c2080e44990301d0585001825444c1072003030b040d00703042d5400381e500003091503440c5410088 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 811304829 1250 811303579 811303583
    0x605060c010608070503150c0c0a060906050403020123060411160308061c082b09050106060e09010b0a08070507060603030915030b010e0616150b15160b070903 70
    0x40100ea1090030010642205041d500d08104940740a5503442c10075666400d11300c01041c8210040e00440c42084041000303000c82c00300c04c0c0c1180e0f00d00c41c061799048101e4010200a46507a9610028130007015030a0203600e01a910122030b95204040030b00e0f4242c40e00744090304151066503a66800c04030b003040d01003590300c0403030b9540524030510382505000d0300350039040744c0b420310402c458504146400c24119003030051a4101030b603d0f04299140240c003000700b80b500d2098159503520120305440308064010702e01180c3c80342c0004191980b4052010b05180c103910b507403621445c000c100501902c1204801e45003c0b20007481e040109440d00c000940e86445283d502030043c03400c082d070101c241a0842c00080455428060189851001d01c4086044401c900841400954a800390311010302d020b10180c90301110607045107a4400e07a030799031120783d0003960300d1020a458a41b8510321480c0ba20b04c49812000d1240c1c44044c2c942907281c1c1010103a0040810014045801d503c00310303d150303104828860242da = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 811306079 1250 811304829 811304839
    0x609141e130219030608030f0306042007110f01170c0a090506040603050f0f0421050d021602030c0307062c0406030305121f0302060d0219110111070b1302040605 71
    0x410f6540300c20280359512650000801d0178900e000607458000402c4034418408810040d056441740020440540780d1706003542c09034100300e644c108441105400601e0b1540c407440b01195482014002d20600320341048178207040c003c0300740340d2004030491200d5642d8080304142c6440c3c2c0e039400e04030090304c407911640c0126030894030102c1c0c08a09240c1541c0076a0042c0c075100308441c4940e03100f540307612068200b100e0040c01c8070104003124450180d80c0060520f01040c0341003503030805030f00010110403a041000081c000101c401e02c80d0096050510143c8003845069000d408500c5c180100a004212940b109200f58814240d05e50300400820510401c0304200800a000845e0303070741001401e981207046000d800d04011070108a204880c0d0100c0c0c2552000000700c2d0510518640030008030f9000304c442940700320307000c01c14065180140c0043c0b814071007494070390104240d0066049400c40e00c046420504600080080d04007081e00194895407001049403c0c1248007014030200303020340f80682c40980c000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 811307329 1250 811306079 811306087
    0xc091d2205030421170c0a05010e010b0a0b030108150c1306030903170f0106050f130305030406020d0509030606060c0c090406022d0901200d0206010609141e1302 71
    0x3001000074401c0f681c030001c600c1c003d20704603c0c0075540d81c2203c0c14000d0500d82c40030404117801c180b80000e0300521011000341c42142d10282c07600d500751400c103194801c02d40d540f0101070383c031450004414002340c00800d854505542c14410300a607292103007031070791100444050015075042804001c40d00d420b08003400e500e088680e140e4016015081c008012804500f100001040000804500501c90401088620410703464400c09803100e500c43c4001c1030818408029400c6141170f4584001e0003144603d00450b81e440c5003402c000c1c10300c14007040c05809c120f000c00070800305580024400e0380044044403000d5880e0450311b0181d203070000c012002600400b041c010402805800c1e0b000d84800484410f2050402101000d642a86505d0389401d4048032414071081041c3c4d440f440306400440c07030321000c03031621280300761189203854010310000005034041401404401d6000b580c003002400c00900e803000011280001411541e8440200140c203801c1d98140302c0f5036918031070009101c4c03000740d00840d070b6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 811308579 1250 811307329 811307333
    0x8012c0d0309050a2f03010c080a1e1d060606120f1008010c020715020a08030112110a03050102070606060c11091b0c0a0b060a0302060315030a170d0c091d22 69
    0x140c0c0310900c030520601c41484005112501b418000c183c4008003660310b4501c0c503a21090f03500e0041a44401c1c4489104040355609000d4000b88500d880080a1aaa4010708c582d03901201d40780080c0240542d0198400f480002241c00501180640064030004c9407207043d5a1120140c103040c8507036100642940c242256400200e8000c1441c0d0240ca071010b003008000414000d050342c1c0d404140500400c5d890040004211a5050840c41031106118101c51111a402c0b5000200d001020341c10a6a0341e0354001803150400c4114814a0010801d42c1000000c0010781e4031050b5807040c00712182801707001d40c1400903041d0003242c0c014861602940a0451b2603e00902d13015070745e0780c0081007c2710f0004039040440d083d4903003406224122503000f40a14070b1b65031101d401910180d1803919868040c820602030070b000031500301451001c120411040d50329101c0d200700d00d134280d4608540400501420101c00d21050b101d400150800007064080e1303079040d1301d406401c1902042d001d0107145021000001e2101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 811309829 1250 811308579 811308623
    0x4060809060105031b01030930081f090b01021c12060b1e0c0f070608040605070e0622030507032105091c0204140108012c0d0309050a 59
    0x202500980088a4080c3c0e01d8078241a9a850350903d80da0040795417407841081c2d907200350440d9090b90311070440070020590045010083d000f07038134015050b8030500340c02c81c21840ea00031181a841700002c40b407408a0705140300590324401050040389070180d22100ca06400364001c06c0510455400c02141001b801e02038180200b000f04103064566019080480000d0009444c03c2a0b414014140c0c6544035a0b0101d48502c4000c0e0b0b0192440003003d025060f00481032040130321840380105030340d440d50b03440b514262401d40c0c101d03100184810284100006440d9244e01c07404261610700e44180c84948030801c0241020f820b000860348010000d1158000c00302c104045d0408450180024000c010012810700c1800c2d1102d0041b91030b041d4001342140540700020a0110b00d2079001800544001002480a0710501d8008000d07000800c483e9140c00303a120012010380f03041441500500b600e41030140350301c0110382d01c8041000004003019260b0203d00305110f0b0074800401d0056000d07005038011108c28400c06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 811311079 1250 811309829 811309831
    0x607020a0b01031245260a051c11150103080313210306050901030f0b0403050f18121216051c0215010f031203110d020c07030b100b04090c0e06040608 66
    0x3050300e517482c96542c04019070810b01e20585488038130b03802103803201401c01c0800c4586806940b90b00e20400d1820703008034106002064840424403030200d11040280c4018003018084480c00416901044061804000d00c41006040d25404140d880d40c0c0d0321241510200100e121a020305545410f400b0003401181d0306000c640c0790781d2103440c20b120350f969a0302000300043c0240300140c40070341c8621038500001c59482c419580079100e0f0a1032402d118804280950540101c07840e181d002c0096481d51042c0d26080f0072014070303001d01400801f050010644c00401600036842c1001900d01c00d0300001c41002070510000ca1402ca00c8260200c50703290b1000b00a61791601501001003030b0051030b0010910a90301300c81201a20703004014044140581c1c44c0c1180204068078194204500512034400150786070700007021061802001407180e9401e50405904101c0058211070001c2d5004000b04280100c1030140d030216800c03528001412166560300b560040d00006c0055480b00c40040d002c15140d40103150a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 811312329 1250 811311079 811311167
    0x10e060910030504140313061b12050c070b03010f030f06020d020a0801030b010602030406080609070207050a061d030a11060c0a0215070605070309030e10121a01020607020a0b010312 80
    0x2041c0110f8020303400c59200c4c03142c40da900d00f080758044401d00c5150300464040340000b2900e00100d0b54000c00d2b07190000d484840d0881c16001a80004014032101c60410000c1c01a00c43c044105145525040890490b0000c0344001010110a0010303d420f102d0240d0582d5001c04210800b5585c50f00c89800050015500340002c540d4001483c0001c08c055200200b070700c00b920b070035444509007900e92408000803031400411031001c40c45084800b16813500d0f07100c1c212000b4115500d03600b0003204002080210800e2030604203000c3da02c0004d86c540810440581d4002400b1f041d601c3c540d8820181d0741060800e026550302940011044a10b4001959014002c1c4480f034044c0c1810401034845400807004d5404880300900000c0300c2504020440c0b0b441c2142c226801c45a0800904101d44044940c1c00e0712004d46000c40d0482040c2403100c11560184400e55100c400c03071024021000c0c56a407052594881800050a042c030024083c140c0340e401b42a00030414050341c100740c2d41802808042000c801c45200007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 811313579 1250 811312329 811312343
    0x10531052a0901020a080c0f0d050d1a09060d05030c0a0813080307020a03060c0504030b0406060510051e0313080d0b132702040b1806010923010e060910030504 70
    0x18190035442201902c40e14641603016141031000b588072039119130848480b40e640c5001d6003490040080080182c01610030150b01c680d521850404c0601e0101e510290f100b09a10b60b4207640450740c2d59400317040c564003a10841d184003805241e410403510f180200e5440f2401441045862410300a504000d0311040c61910090500b80340c486040c00d450f4022040b0007500b14030012020310000c0c0580d008869a1480343c98a54103040e940d4661b800710320740940e401e46100340e0b254800d100c24100710041012008050a1040c0741c100105007001302059810040d444008000c4080b91038103140b4089100e0460304080c40c075440c0c008100590700101080064140714114411302c00c5040041c1d4081c220000600c08908280d940385200b00d840c2d81c0c0700c600800c07640300d981d44240d01600ea0301c8a01111020001c200c002e202494400d00140c00c614040d0004d100c00d007000c2d0781602e480100b080c80147c4445003864514401c034088400305034a4010f100010754000b250903400300c096035141d80018455805086 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 811314829 1250 811313579 811313641
    0x40203131b0312030c02061603020906040605030103120e0d060b04060f0306051e070f080603120f071101080402060306041d01110903070b091c151103071701053105 72
    0x105a0884402d1400f00000da00820300103410088d18844000710b58040381809803a14491000052855005410190103c1c80c084014400d205600c01ca242003c042c9082404420302c074640011864020b03200001c2025494010a20301c40d10b481d04048003c00c144004120f02d540c0700d02d00000641011a4043c851205030501004403001405146006081c543c440da405200301c04005c503180000280101d0309442640c69a1098009d001c0c010b240030204081d0150704c480541c40c0c19902c5600300040c40341003056210910015950301801c4a402c25011500000c884801444000031900a0034000c0010351030714a02441e40d520700c00c000c004243c2c04a06548400b51200b80300803d901812201540240700c2c039503020030031aa01c141c640e40740f42c01102c0c1480060301ca008910141d501da460510480e8001006001e800c0d5080038803030320b00010007030108440c0e40c10000440c03000401090031079552006e2414044c04030305003421003441501401814022468591000c0402000c180000215418001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 811316079 1250 811314829 811314863
    0x18060e0f07050a171c0f2c1e0904060605011b12050a2109020103050609090a0206090d0b09010c0e01170705180603072c01020c040203131b03 62
    0x1164000a55000810740b40700d003400c2c005a080741c1104c00c88135241d54440c07411002180040c2c03016503c201d02c2c05649401c404d510142c401080070580440d8200183c00b0106c40c60003161841d140c1d906070070000d50341b058030b40b030000491104031407040720255004050b01003072105020503900b0000517114281c8815000415003460801c206c202903801418460000d44100c01d0f0900c075800403c0810040e19101100c0013a1006039200e0800144050740d42541c5c035030b800000c41d6018081c8540c0102c049035114510301d0b0402115480d5003800e0802842010001480d840303a1b0750300b58100c0c854503008400110300e8544604c906009000c0341c1d1001c004566101c041070002e40c410080c00c1d68009404c1d51a40d505d0316070800556040e000002d00010890f803410041c001030305c0d0a009548690303160303a691a01219080a45500256516404030042900c44c2090300380c0d036000121045902d0b0292001030380d99484410301e0200d2000301400420001c48100000002c0c44103090103025a400354070704034012441c013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 811317329 1250 811316079 811316083
    0x180c040902074806021222180b040e0318010306090617070806060604030609151407030b03011a091f0303020f161505030901060308030115110109020a170118060e0f 72
    0x79100d2000103901c07800c0f007040a1442c000103841e8051a0602440715144908032000500321f0540141c0440c941072040095061564050340c03d046800b52800c10806181055070384d142c2c41001076880b81d004184001e01e10316407181e072000c0d0017442c40300000c12180780c503190702040042c10120040407074441c030100441e02c4000400c0076801804000c0615281c0703480c56071040068405244192400940789290307640d001441d00071000d45240d1441a0181840d04d00c0024048800220201307010b40c0c50319007004110018086880c0808008076030641d0b50356140c1000c4a03007040140c100a00c000c520001c000304264001035550301184405056400301e0900305d44410710140c2911880d03040b004410038005015004000440c0c1000c00c010002c12000e03103940345c80d01c00d9402a48203400511803141d001003e1070780005160103c1140e84024442e003401500010002019400b9030b4a011071881c0f10742151010035480103e8241601014001c1d06005080013001040090703440350443c0100800c030301500c980 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 811318579 1250 811317329 811317473
    0x2071707050f15070f0309030320030a050903010618150e060a15110604050c0307090504200109080d0201021e070b190902041a180c04090207 62
    0xd408049024140810040c3e01007601c0d14840c41c40034100068004102c0c1801c680401500a03119200542d2861900401024007166141c2814140009640010038003004407527551045203042921100b80c02e0010340100070590111641201d03050703804090161070b030050a400200c045001003000e0340c41c140b01e0034021003120519841051040d06010800c06030800303072640d016030701d401d03241029400b8006250640968065466501109110702245410801c44010b481c514606202a040c01e90f0b600960003500d03503212189081c100e5201317003540d1242600c000200402c4c0129007940c1c1d29000c02a000390300041484801c04210070350110030404d00000ca690850344614900f41d40e540f0119450741210110a441103038a46920888015075601d00640d4480d511140d6544100a09079040200d80900411544011507141c0d08108503900507105407401c8500046001d640c40c5407514210143c2c03200b2540f0131440c1c014150031101c0114210400040340e050ba075110706e0100c2c010318000c0f204440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 811319829 1250 811318579 811318589
    0x5070c06080403090e0a050a0608030702210309031203010501030c09050102100b04110417151017030418020712180b0c0705040516120504030504060309150203010602071707 76
    0x241008081010520607403140380d00501900d0161130f2a6140c0204006500040d64038050441d00c4105000c3d40704254882c60004125140040d8600611980442c05480c0d103240c015442c10711200103a0702c100c8090040714002180141a21810042c4ca1041c4074107410038020380d40001e20301417080842c1c5000c1c018860546d40144c00500e46400980c5001d000751248540c0603820070746608100b60743c001c146000d84060300e0184244a851283c2108942c582050b0303200044210312500203025504107103844080a403485003002c1c10b620300004e10401d24510459102c03001e841e40c658807801d540a00e540c05010824899000c08265908045003220030080300041c032524242210b404006011700c0400500764031134258141c5211a5a5800150807a2000c880c25070800c41200403420005a10801680b1140c2e1942e41c10401c0e0b08140d01c0060803405180151801c1c03556071b20703202e0b003807004950682d00302080c04841550390b50b840f000000d481e0041803040c0d0b0348481314030a07104042c0c1d1005ca508810b80d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 811321079 1250 811319829 811319843
    0x50f0121080d0f060906142407260315120a05100b0f040e0d0809060c12070201020909250305090307020103090212190b0106050307020a230f0d08070507 67
    0x34215058440102484861549961340c2d43c2000143c03044e4a004401c000c00803800c40d4030b5000314180030312502103000c01001c1500d040102101800c04011400d44500a4001c5042c0e02100c400743d0300d03904010995122203002050100c04c010030285112403521a102007a00c05914044550141d256565140b400040c449c1d00580c0c0106000c441d01d03400107103802002012464030a0a00c004542204d0f0302c92485c0d40c664000d15002e0300403e404c80602600002340100801c8907261203190007d003030103100714090816280c81c1c04190003520035015184448002000a4010b0031300002c00445005c100100f0030890b01c8410340003c040f802846240d1188140501451800f299640110300070450300108903440101203000080c602010000202d4030b640c03055000c603401446060075010030324140d1004042003010000c1250b915408950310300c5040e4040c101411496100428112003d10034208030351030701c0340c0404003002c41d00c000307040325580403591a8811103464500044440d40304681000c2c0c03190b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 811322329 1250 811321079 811321087
    0x120601030e0712050606030105010609030f08090427030216053f0714040e0c15040504090b19090302150916060c05150106121509050f012108 62
    0x1550098000d12007034410201a520031503125450030006802d000b0b41551181e11140070890182424482c0c1805400c9500b041d0b004546982d83d425405248664024084130300450519143d0f1600e402c00c00b00c040c41301d1880ca191900401500e404106a44020740051003110070b405020305500d41800159200034100c4a065403070250883c48203a880d604881910040006c0c941710140200c00310b0b0903641c000b0b4046c01f8103524240c5095106280b03041040e2003a4903060240c50381e0800050f03510540f000c02e40e1040d44041c1d0340e20019003140a15400700d0f820505103605002040421424584074410020201603c018501580c0c400c4074880139004026a01c0b5554503096403020304510769004441c04212900d00d60880c43c2d09200c6d131201c0d0701a03000300e142c007102101045428404103958490000c07a4020545c0b4203200108260a41c0d104200170a5694402c414000c1510034510082d24900c1c1c42444241801e06222401d84000d20989585000b42000844072600c02040c4020740d0703405c01c3e105414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 811323579 1250 811322329 811322341
    0x501030b15030603030909090d09061418010311040909140f0a080c01182f010e01030209010c0b07081b0f0f0c0f0a1202010b06041d09070e01090c030b040212 69
    0x30395030019001c070740d040c4030a000c0586c840e40d41b6440544030302103180c050285d2541c1d003400604440d42d9500007c0c140000700c0e8600d00740b042c22400b9070314800741e071903001d480072048000160000c00d00301c03c111140090029020034000d500e500100b081610031010b182da082401c01c890b41c1c40d01c04800791003510b07400c0454040c0109500700040c0402215a000007c1c2c100c0b002d601031502039515600c1114400c5032510024072000c0c1c0b60b104e60f2000d6417001e034000801e007404000201035100103403107541810f1f070100320000316922459080303079402d9100308112041e0903c0c041c054070042d0200c4070100c0780321281070341d42c074100c0c41070040e10101269680c81a04281d45004910a650012811880300f80319503451140705c07050400000c0050342c0900c003a008485100c1c10002e0030340d14568005809107508101c10064040e0341328111580052010203c4825180e11000d682804036985c0f051000582800010900003c0c40e4015480c42e03100d91030400c0f0000c444000d020581c010525814000f454100000301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 811324829 1250 811323579 811323619
    0xd062007020906150c19110d03020705060a030e0111031501140702011d06121005030712080d0219030608072c0403140c160812070311010207150c0201060501030b 71
    0x305451380c82d44500f031032402c081040c0341c90f290b0f04d800d00a102c0041004818019052014a14454107541941c624407168030065640c0740305105d0a4001c08000405810141c030a030f001c60b410444410080c4120751007041207105a0700b041c0ca560031141d480324400d030095030280500c0010080550403160400e04540c006480030020444400500c8640404404803071b503541e4000c1400c03182c0b1781c20749866410244080500907510b6003100d4060340c0720750420f106042003602c00c29140c1c0e900c400c8445e60341500c034400c000039004141040001401d10b8803004c0080780c05800180c1550f08103821a1181b5a6842e11091390010031840c86c506480e900c8802c2c3d103641c0d41c240744503a2080c02810010020100c0302c0c40848207620800e2000e07556040401c80e040200c5185200d000200324441c001c2c04800d143d0441481c203403003061002014428850400c446540d002e40503149040d410622040d101025000c0300ca000d4001403003c1c41c01540b07410310200703096020344280d1003109d00c05850b80201c81d1058442e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 811326079 1250 811324829 811324849
    0x5100f1e0207030f0f15061a030c1317010e0c0d1104060308031302030615031e070e041505060a030c050f01030b04110a02101b0f0c020d062007020906 66
    0x2045000b02e030310203c0450416200320102d18030468030001207084e50309013001c81380c01c1d02901c00251400e1450402402032070b010458004110303080d00300e070341c5c0d10b610703084045a210341c120350000c550329042c0c00501804154854000c4440642c001c0c840590303980d039080d490309070140d5031590040000781000c0200e554407481e205941d00141c0000b0300b440e01e075128010709400c00c4900403212524420307c4030440c00c0c02d20085810500c2080107040d240c0f00500000c0d1600b940e00301c01025089017a1158038180001c1003d0001004c440a00481505181c184400c0c0c008030243d600d80c070b40b410704002ca6840d05112281c241180e4001030300b0f4140c1c03400c1400b0006103050241e01541016142c58003001c035035903903104146a00e00510f250941e1695085000f030704042243c04450807840ca0306400c0f009080100b0012006031000d407500364145c009506068402d003092410103900100000184810445640d000301211001c2303040300381140d109024050302d6445001c071300a4201c00c000c40829458240f0721300213 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 811327329 1250 811326079 811326137
    0xe10030b0f13120309210e0a0b040e220308041a06030705040e0f06160e0d03121e0903080a0e07050a09050612030c01020a0e041406010c05010e0d03050105100f 70
    0x1300300c84e0642d4940300030103802800d1032025002404410124281c101601f4070700007070281c4d0b1041c559441d200003076039070380901c6c440c2d41c0d14041c40000162404050504844584612000d00c1c1c0502d00b1303a0070024070552080f1000c580c1da84120240c030b441c2200d803064a901ca0034008000f00041d07030030201800003070302d003070f44404080d0f2103500e24181204806124aa20030382c200000b042021014800c000d0040140019060003111380c4540080425807000c0ba40c1424600d01d5008610f40301c07528076035803480d59413181d414011403030040900105a0310a52550052030318140038050714100405003901d840c0640715499000188000c02c00020045800c000d920100040860543c134003d1a800d605591102d154403c0b165400250440b1903500329001000620080d03404029060205500d00160240606202c4c14400c81640c03660802009401c4103104142c80c0068690f100c04021000d4041c0c1000e009081c400c103800c0c4c29501c12603116000307144102929035030742103220740e03d00d45180c0104100c900e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 811328579 1250 811327329 811327331
    0xa080706062c18100c020a0b150d080a0905060d02090a080f1e0f0d020d02070f0302100819021809340e190806072d03060e10030b0f131203 61
    0x101c4e0305008861140c1c400000182d000781030b440d280c2d0300e1710452040c0010159400400c0440c00c05080b034481c0c0c5441292550b2104005d0740d1440c540d2015203007050f4503800141c2c815400200141440300c02d0300680b40c880c00a40c1c8140360251554030060325840c4d030880d510007135401001ca504800300f17102c50703000254540702c0c00d4500c801046411641410301491028016900440441c018658100003800041c4183c41072400203d00b5640041c0310560250b51000c1002000300c040f64120070702d00443c540c1d4003140e8008550f41c421490213107100100c11071320640b04901803c0001e0b40110707144075000c00d540442600612a4003d030050807814005441d08a04001800411071110740324601001402c41c60040c0d14170600e4a070108861800c0b600034540c3c0704000403144c8080703100035062010720101260100e2010b400d0b0040d01c0407001850a50f00c91104e002040c81409550107003074031100c064034060b00e0321a00982d9a0002111240c2c81560219000c2d0b0001c00420042412442c401c1d18250451030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 811329829 1250 811328579 811328593
    0xf0b01050327030a02010b0901231225050f030a020a0b130b031f120c1701020c03070804050f1912060e030a020f160305100506030a080706062c18 64
    0x240d5843c58001d9036610700581e644083e00c2e0b0700341c9840c01109005103401c881c90030301001c0c00b052080a655142c060580101c010080c0e602d2448001e1084250502d0551501c80d00400036025071810042d0900c070310760140d0049918100c0500b000b16600c4000c030b03000341c034802016280c402031216540c03050f21003a03141c0c00c40e03940100b14032002600450048140202c1d0403120703001c50000d52090002c603480000c3d070340c0000030800006028101e0120440740c03a8400b0580c1b0360303d81000540603109515642015020020b00f6004010b1554003800540708191200c02d0412482c00901c0071002c0c96a0500c07041d50141c1c1e604000b07020203810341044061081c42d01090541c0b49112062641d0000108440035030004a50550611b804005015200d01242c1c0c80e0308200b4510b4507000c0d11072068200484846442c0d40008039a0345040143c408242c1e0703c044a160b48030090308000e40200601e02850058180d43c0d40341a240403a40382c2d4040c0030f0260803140b10603d441e8900601c10110f1118501019800b40c48 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 811330935 1106 811329829 811329901
    0x3061c022211040f030501050a0b060403110f0a152a03030b15070b010f06091a0d06080d030204080c0d030212030c1e0d0f0b010503 58
    0x1d52003401d42503441c0803500034009865203480311090015002922025252480003141d0082c0001c1001c4d40741d2810542c262107400c084164000344c144030030b00104041c0c08042840000007032286c504003600101003200001258000c05a00080e61005443c080d0400d40b595092156411081207016008281889a14909101400309a901c098012082d103850320302c0000c400d0010030081d181d50052070201900e0346d0074081c15000449200300054203a004590307860071340f00b1248005a040400001c0e04080381c00004603200c1c00d580b16a8005299001880440b80661148e0b030b003da96907003072040461038680490005805181c180300c03d08003182e40494050549540202484e940b606d81d413110310818001d24441d4401d0584a8101c5031408c2810341c0104086403d400d007d01805410340e060034221040c0201d00ca0118404100050038440d2409007502146043c0340040c842409034 = true := by decide +kernel

theorem cover : BRFrame.Cov 811151079 811330935 := by
  have h0 := BRFrame.cov_init 811151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 811151079 ≤ n) (h2 : n < 811330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
