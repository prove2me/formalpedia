-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0482
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:01:57.4667+00:00
-- url     : https://prove2.me/submissions/5933cf49-6628-4863-9a24-bd76be7f3fdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 86510792 ≤ n < 86690648 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 86512042 1250 86510792 86510813
    0xf0303110304080d031d0a08090d080909070903050607030501060e0d02010302070f0c051507021e030708030c0a0614090a06050a0209040e0a140609060f070c0501020705060612010204050108041209050d 88
    0x7266040c81c801b8102d40410800300300d00400030741044500341061050410009200b900c0c0d4000c50b603502c0c0800c00702c1121744900c5100c500c40c500980b10a1651441c50400e0341c10b1000c0202031004042c031301001800b10641005d56882d04841c269040540e20340e2030300c010b80c028407601d00301404500c00c1c45151805c001c88414040184d07902591402882003000b01201180e004030100203620440c0d2403901303121103e042e21595520381004045501d0582d0f640e450606582c4262820804c940050302c01e40d0521200c0d00600070386203444140c0400c80e1900c801603940720401c40100070152511400030840061098065560407800140100203030094200c0300d940d103081c0031104480314003d209034110103140215800d885011140080c0045a03100d0700180d0041304000d00a405104561045e000450130901c040d011503449200206540e04140d01008410302230549130031801d80c0100b02c01d01059a2280d0740c290000c1d88031040101e80d01c0141030030b85607011250410346d00081e00c0440c610900410342034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 86513292 1250 86512042 86512061
    0x303041b080318040b0307050a06050c060105220b03010f020c010509070503010510170a0c08160906061713060c090306050606040302010906050c01110a050a02070504060f0303110304080d03 83
    0x484414a07949000d400d480740601c0401c5404185803540780001ea007030075080304020302c4006060b00c208588410000300801b03025000880007420115841326a80d40030005d09001d4101101c0040210180503c580b078140d04817511281801e8441c00308900c15142508810341c2c11003110301c1076440308a0f00d8041d9009040c1207906914a114103d0001030301d08041c4030350303405500590000d400d2141016034009000c140f003800031059200d070960701e00100b119083d00c0805404d440d0301500742c001c0d5980341480c201d00c681d040049403e203808020003c403900303e1228240c101200b0042503481ea40c4108000b074065506a01403c01c9080264002c41d140e844913605050b42d110300c50400140d1188030a220144c002c500000b80400c2080300705200240c0610050101301074100004034401c0402c005240581d0094002d1030007080c404502040c2e41601440920702400099034204000384c40c1415500024026101c090140b2084241070b050018047c821580500140421038850344116a070081c02800070381c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 86514542 1250 86513292 86513333
    0xd0c03060b030711241303020712060209010305090c1014040801110c060c07020904230d02061005180c0903120301030804030b061c120c020306090c01020105011502060c0702040608030304 82
    0x80e240d0311740100440c1120340071102894440015a40c0d01155400d40e880e9020070b030f056104254000031481e0100741810b84451180c000941c8072820f00c000503065540c040c0c494107144d0840d140c0c0941e03684964443d10314030740c0c00749401c910505004140143d144036640006905509007901c0245a842d100c004200c2281c0503000c558295440c0e0360108514004c03108001d41c825210400704001c104507034054504e4504800d15580d03a10840700c1110301e0815641141c10240c4c05c030714200a201c0c400010703c41300600301510780c09151820301c403031403202620040c64000b090102003418207054030100310900c0b0400ca203c01c426a25612400c048055802a2100b00e0713506914000151a038181122440001400805480380450301d9079620301c0c00768690100b000c2081010324403207025990400a0a003e040400007030609100035100090a449050b00031110240c01c806010411a0303000400d80d900c41c1800501e181c580040c0d10010f4080c15007548084402d02c0040b00340014000c10660100320001800c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 86515792 1250 86514542 86514553
    0x905070801080a08071b09090c0806090a020105071709100206090c0609010e0103090303020903010606083907020a17100608010b1309110405090a050d0309080d0c03060b030711 77
    0x80321083e54684100c403005052400a2007402c0009a03203006a9600c00c00745108603400c507131211046011074452003015203094817104002c005440c410f100c0c0c03d8100b1440005441400c6d03007500040e200e0311074142c0c000c003021040001d0124a8500030706455841c1c038000d01c8408008070492000750341e00703010784164001e80242d01542043e442c3ca4401c443e403480041e1200508141c0c0b020041d0000c00d0380036803c1c0c00b4941c00300a121443d9400b803141601501458407044d03440d0821070b1003100c51580c4024481510a40ca00e030001a0706802010300010360500c0110b0317580c84020384040b03400f00b1101d80c00002524129000b0820103140071808624440031176108001555480c22a1400c1c0c1d2038100780d840e000000d051801c480b20185800030000b850054029401310341464000c6011a102156240c0d001e0300b040c44c2142c10000107004010075011145003e00c0041d40646074421a0722030100500c11250751060110700440c084c0d0000740c01010f030741d5203558803841c12810241040001e03429400700750168 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 86517042 1250 86515792 86515799
    0x20607090605030421110316030216030c030b180106120203160f12030203070c0b070311030304020a05040203040615260111070201030908070c060302040312020109021302220905070801 81
    0x900c0680b4070640c2c1158a02400400b5400e4491540d00925903245c10046410755020201d081040104040f08040c03044111042403030078000d082c034081c007218010b09491900104040380e1540006030039280c21a00706411030301d40c114100d402110031041d52000c2c0d420410700049400d0b040420329540c1b8001c0c2c055a00003103582d40c0301c200801080c05410000d041021060010410b41407101c54580d200f40102c0e0310704200354492050806252340100e910601c00102e01d810558010500c070032001000004508500b0264001030a6503443e00031701d40940c4d80480014103000a54100450886000207105407a07511454403205a0380d250701d450070614050340d0f2885c000320051040b0307102e18044404240c100411540114040e01c0d82d040c00352140c000a020100c0400c00101d402d100400542d100113946625501d8115190b8010301c0d540004e6902d401440d10241e10344c221001e07500e6001e03180041e6103030010f04003480880c1000400004640300d0110100703140c00c460340b1642c003545003607d0b50071051b0f0740c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 86518292 1250 86517042 86517047
    0x60f0f0b01030207052d06010e01051002030408060a0b0105070803160813050615010302040e0702010203070e040902100305062205090601080604080f0708121303180501090e06120d0206070906 84
    0x41c6000c0142254850402e00800a8a240d4400d040f080100f41071b06011401c00c001e540b401101380c205046c1c00c00103e004000c3c91034a1400c400c0507184a0024600389803030208843d07140c6000420344281c00d44c8846240049a200e03800f101ea0181c0c1c0070020030346908026451103030713421030101c2c1c00d004540c29801285910143c10b00d11181c035030303000004003c580d84103001c4150310301c500300c0d54505254080c031011a40d20082c070f010381d2054001d42e000580fa49030100e03005005007042d20540d1b02852400b22081c002da241c0003048405d41200d800d001c94a501c0e410082800305150301c1d83c2009000510a9015449180750002c5009221880442d030709662100e09103601c03504181c5004021420401011f404005100003500d00280501c01c164201015003021288200b02111801c142c10a400c6000081680110081c0b08204000100c00c0c507140c103100000c0d01320711490040031402b258840c00641155622540c080700c43e482101030351070404508001940e10041600c0c076001040780000b0210340e051 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 86519542 1250 86518292 86518297
    0x2030d0305060f011b0f03020d1202070c0b090307090203070302130f050603010608040c0f03030c1505071b02040609021b0607080403020a020d021f0203130e090a020f0a03060f0f0b010302 82
    0x5200070901c8406904541c015641e45c00b00514204d40000310000340c0c0c000c160450400040c4134002d4003c2e00b010380f00c8070402049600d040e810703401c030103105000d05008108040550030070348550b20445991600001c001030703d800d045034480c843c2680000200030846078950040c1420201600e00071140395101d14000002d05501d00480350000e1003400100802846821040d80060007030700012060313038440e4568125810660000c1d0f02003103000c0740240802c02d032600340e640100c04081c81048503040400c4c000b04001c83d015058064607000c00003045c155602c0b640101c00a01666004558608500c003c40390b8512030209020014024400018030340d900884a091081e40c0c140d0152954428660030044919100e0300266000003e41500301c000323440e13061040104544540055480c1c0c0c40a469013040700c2c081d90032440b4840e08880034031485140000b100060298101c0e505051014440c3c041620b10034640c0c4003402940c02d0000d040744204040d440766a216804810510042d04588010740507031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 86520792 1250 86519542 86519551
    0x13050604080d0e0d050303040320152a16020f060418050411130b0306060a14210303070f02060f01181a130e0c120312131202030702030d0305 62
    0x5030455800521500e01c01e00443c10b80000052408020740e00b503484040c40c54104035021000305103116041481d20030190391624084480342d0050240c06020380010310480000307400301840d02c0340e8904003140c420540004294911043c907101d511088039240d0200108040501a401201a2501c1641d03e040c041d0864056485000101c01e20001d0001600c0050400800c15034500c01881260381082e9190825044401c406c0b41020400e5220141090704115003d02081c0c407a0038807010400c40c1107081d02c8003107030340a01241d44c807500100c45026a05084130750911148113000001c00c02c44200d4100c5c5211418000b5603003200e04070742e1000810f017000c00082c015412051104004440e0700101c0c1c0c0c000134805604810640e0561650300007040c02d800c8a11010080c2a403a03035008403000f42c0400070300d6200d2904aa85440034066171101a4481c401e410703800985402020028440355400b441d034040141c0d101400c4041c0c015001c0000391642c2000e01c040744a4000e05042c2085941f207402414003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 86522042 1250 86520792 86520809
    0x60b030c03100e070804020a050405010f121407030b010603050705090904020d0c1e0504110a08060d0615090f1503110f030106050d0f0302060903070f03030513050a060213050604 78
    0x216140c001490100d41c000411250b07044889400c0451280030044a040c0200e5480e142c0f03480c2400c1078810480d100d0342c00c0e04071030300484ca0b0030010480c00000c4c000180071603c0f00c0380d026448075040d04040d2044214505450342920070800b000003000800802070307049418594040290340c483d00c2c0c1c100d420b440b48048030b5502c05c0500c80407901502d40280031030807061007002042c00041d594030454066a10090407810041c004070020007403810b00340180780200c248191402d01d000714003003001c3e0074002d0180000380911071140e1160204441daa2000046400c04d680842c040c594480c184400b40003060380e40301c455030800032040e00c0581400e0359041580d40c00881d40d50b80300c041c241407008407242070b800c01d54107649800d00020162100d01070741030001d0040300d08815100050401914041e00034140c954194020412400030a00100e40d05407080d5140c6000304e015150040c1c10000c840305c4180180c46801040d40c101c040225982c01064034070700b80900c00d10140d41d80c001300603ca000d5442014403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 86523292 1250 86522042 86522047
    0x204080c06030603030705120406020f06010815060a030807060507030606110c040f110318070e011d0403091e210503120601031d0f060a02030105100807030e010906050609010801060b 80
    0x2880c1071006540c0c0a100036040381d0909034180c8a0711714013084520303c80b0316035500081c284210390f03050248884054030400102441c0d45801017066540391031107207403941205001e01180403581d640d0f005000a42d0031158240c0c444440d400d11800510094400c0c1e40841d140400025000d4040c0341d0f0144d5400c0d21a018006101d0b080f0f0170300c00903008003921000c20741da5850901c0450150400554002c02e8451000c0c0700c2d0786102468a4a00541d540181400c1c0c208500104410b160502408201c04500d82c00603006807070b50703e8140c0d084c0120ba00150281c099440c500c0c0b000488a680c800111803a44480c09001412407041c42c000c1481c500029000e60404c000c00c03131801c220040f0540e0014418540024103102d565940071179200710b200900c4554000082c04400390300c041080c15004000441d00b18515407510002516480c5041c2416050201742c200107207403d8000e621000d00b54406500a000c1c0805925007240204012280130344198090340002c103007100c0520406040d02c040316105071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 86524542 1250 86523292 86523313
    0x6091404030305040201051912050714030a020a05040e0403080610050c0c040b0d0c0b03041109070c03030902190f1706040308040f05190809281512090507060206070201020408 77
    0xb80030b40720040c41607052140801041242c2e001c0c114048034000b60039035a140104141c0601b64003a12406800c4034100f2807080200420b10382c1c5c0c80c04598000d00591001650798045803000d94241c09150300c0081044050300820017410741292180d44186011070b1040007440d10124191203034043e81a40b0303030669000c2d00000c600c500b00766006500e11000107004010007142543c6403d071824003500503080f000404000e20041003001d030a9900d00080032540c99902d483c11400c0144401844d80000d0304154640d0480000c0d074542d03c5080080320180311100c1c2c49192103144000e25030381107100364038290001d811403082081d00070030707418001c0d580b5980d602d40d1a02c072625207100c0c9813080441601da9000700007118031820610082410210720030741643d51034003d07000412204106400820b15410400c00202c0200c101e4103030210280c611600d0010f084071003040003200c100d0290f003a85502c080c175202c088000d0045c002012821a5016800c4542c4d50ba03407540120700380d000754803d080640e8800039440307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 86525792 1250 86524542 86524547
    0x10501060203040512011d031201170a0206032a0405011404030b0a020c030c030313140a02090a05090c04060803030f06010507110105070f080a0f020606010302040303081902040806090705040609140403 88
    0x41c001c4503015400810420314143da0000c88200c07c54954a166100040c14001030f904030a199006100da40040740c1c55112585050381c651030030744c100910401d0000001014500325010b6020b03100b00d00c0c2c0d00c2c40b07403250b00c02403014020fa11a024844c0401c060441071003e40e08100c045405680d40f00c03001942030b441c0c4200d8103001c0d4100c904540a0b9000610401800f08810409036203d0349240d41104d00c64445410301d0700ca81d00e00c5800303808290b00201244405a1a08001240c000040c4180040c065031030250150400d8203401035554400e081120003c2d820030000044c5010300101185000700381c40d1280156010f21510b00001d094040c0b011200e03000358064000b6118a07402091000b80400203a40c940c500c0394000345400001c500c00301d00910103903a0402869911001c02e0a08518041c01c41e1005005001c4c000c283e4088a0301407480c2080da615260161002444181c5c210307a5141059180240ca410a502a050159283c2580054601c60034000c0e0700d100c590241c0071842c03648954804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 86527042 1250 86525792 86525809
    0xb0f041502010207081201180c0512150d0f05060c0a0c06020723100506040c020c22020f180406060813030c050d111509150702070e07030606110105010602030405 71
    0x31000d55500303004001c04558908010321440641080c098159814062120300280410f03280c082420301c2c00b80f0004030603804c0b004840816180c4031954409a035031200002003803600e0010250041011b4400d04200030308640c925039100c0c07140041e114160b0f0384003100909401000a041c0000b24841c0c0b10b9804294a0340c01044054050b0210341e90004040c5100c0d200c66100001001099100d000305184040c1107100b400d4000d5070407030701407009101c040002580e80703000110142c8107050001c1030048120007028011000409400e065444803403840440c5a03030b410803040368803806441c20703100705189402c0c0f0a0700140c800b03e440e8502c030358036480030180c80c001c0c5100e821420301c07070351842c0307a00840d0b003c0001a404440c02e56540084640440340141003003986255204990018030512404413004038492101d11501c1a11880d540c0c2e031207504903d000601d6021882d60400501401079090f4550041d41c01d4071266241d07208040c0200c242c1c507080301c401b44116401a04144000d01061078100c05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 86528292 1250 86527042 86527079
    0x5060f1c0501200406080601090e0109020f09040c05040f080d02030f2a060a0b010809030901050c03160b15010c11060906041805040311030c06070e01050d0c0807090b0f04 75
    0x402c000c0004240d0010b09480c3c03002825124003007001c10900d41d001d480c0b41c2e40f0071400c3c42c0814109141103480340c0c002d001809602a2585c0220310129400d00b0f5800703562041c41c0c001c10074400d9240390200030b0010703406800342e4582c400d40000c010a840b1000900300400d82210740c010340c60540803030321080458000c844801d80c00505a50300420000990400103002c2c0c0e200c0c0054800c034107080500004403402c2c05407680c18846424201b00320190080290361601c42d0a007052513a075000c0380e80482c2180300340f140f0b00e80d42d01d0017414208140600c514080b445544240c0131801ca100d070344001540c220342550002840036040c0040612242002030103486244400b038101800d054460301d40314001c541e001c141030580c81d503070010401416440129641d280f003030040503500d000d0021499640b0b43c1c000600e0481845031a45590078264450f03400c441c0c20850440d010408162190401041c41e1029204080000c00e000800301304480301c1d908403281501c251110b01d20b020b20f4140003409042d034250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 86529542 1250 86528292 86528303
    0x20904020406080307030807120606091202030705120c01030f090503030604090c08010609021e0702090703050408090d0b15060a020c092a040f0801050601120e0c1201020d05060f1c 79
    0x502c006181002040908400791103512110760918042d02c004189440f86c00f5500b4895003410710400c01150403024031015148000c3c0c030501c0c55040c60000c21310b00645640308641042020740c001c848228041001002c280090780d062101541c1084c02405544449a024005070410800f007000e501d029070005040c58400c0d11040b00e211340ea003806908460841c0d204900325a00041c0040c00307031540142e096283e0201040950400700340f1780200f07001d040d0043c060420306640381c0210302449041000d948101c4001009200c40060900d03081c2c4880c1819900d206441c2e1040b420181640b82c01d506590400d138603035000f40400d8416200300200f00402410742c49645003014080e0b04410850304c0743c0c000c50b42c0c03007859040da545d280c000203048222160f44515003d900d8441484007980e0310669404544070400404a070b002c02c10782c5520705012809003004e500c1004003c00c964400da0640142500c204e80200810143d5156400c2c804509004294160310901c448540c651101ca0420704010701e80c0a031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 86530792 1250 86529542 86529551
    0x1302010210021b070509040b0103030f05070f03120f0e06061c021206090d03020304030f0c0615030c1403030f0406031d0a0c0e0a20090105090406030602340209040204 73
    0x5800078040741d000c0c0034120143d03909403034800c22001080010a0003000196800039882c80c054403440711140060100030100b100c60b0b044155914400c805943c1041c0d0001c078100b110100f14a0701414040c1e02d0301446100509014405c0e24040e000e02c00c14600341c00d641d01401b907554641003084904013004008411460030080041c01603118000d0f40403d040c980c500400090400d400800e10b8000381030751201c02c040c010000c102c00680c0c851120245401c9501b01240c00c08032900e00040504101245485107218085000003804145141c60088400009801d01c1104030802850740701c2c4518140c5128080e810003003000000c0c807a500061020fa81002440c8000d0007556641e4103103141140c003900c040712001d40c2030000d01300790851250001103501c02048080042c07407400c0c010000c0103940090f8080045480b5085074040c80440d00440c030010700802c507103500c03403078241c00a412070815516603000900d403142c2102c8240341521421292030459030000e0f0b0003035003048440c4d0f0340104102c0cbc00c1602c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 86532042 1250 86530792 86530813
    0x5091e01060b0c0a060b0d030203070f0f0b0a0b01080a0905300a0509040b0a060c03180f12110f0105030c09040f05010605030901050601081302061806040305030c0c0108070813020102 80
    0x4440150080010800c013410541e806030410106542182810074130425070300d080c00b000260000300700e41d24a42c0c070908410900001d814030107500c40d010480070b002c10b07200d9400c0041244180c1e100c03007981d11090b20b64a540d5165401c4800443e900028002c240d54080c0810781c5011070840007a820701c42241cec0340014021400d64192180383c0007840c619010440c04100c040240c5028055419020000c3e900b150740b0f04d02d08100103001d480881d1003e0140a8001030f9032021001ca070703440001901004190b4440c0ea607441c4810000254440400d07605050b010544521520300a02c007542c07a0700c0d0580d102821600e501460041039030101013920fa1080c4c5d101001e8850705c545001d40303402040e1545415860f440c0541926003550001080e080c10001c10324100404014005550640d2036015240c0710786502d0b808515462a44840015a6115030045000010084004010102d0080c118203855400040b0700064680160903a0000f0200c1c1302c0b000012000c07180f082e00c00951074014811079030400603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 86533292 1250 86532042 86532059
    0x311030d0204031a0703020f09040504030e03071401090f140105030901090b0103030c020f04060501050d1a150901020f0d051905120708010f0503150412090e090703140105091e0106 79
    0xd580110398039202159400c0689a540700d80fa07a11017001d0a0035841c1000208410499200d82e032141c911075542c50300030a007418480c1d0882404010042e04071194907464050584460031040c18060004100356408105442223002c5003040741c2805440300c5048603940010340c1c0c0ca82000b00400303c559a0f42c481d40d07000c6920f140c03015000350300a44410710341c00c407030b8010b01214404000358a800b840c10648100720030f980c0501182c2d1000403441c40002c864011040d010340d800c82440c4640c1e03000010040c81c1c0b00c0e443e0010000d00002c0c4090b000c403000440f00305131541e25040180c0c1802c0120382c023809415900c080104441c50801c1c211700e000f520348070390600e805141001c00c1e5a07000000e40410010b004030024080c00c2405884210010039024448041800080f94001c10040c103070008140b01c0f0224901a158100203000341601d03010359440c04102c4141d560580d84015144000c00d500f4081e0700c1d40e01071060368001d08424003d0b103044d03195845100200e821045244c0201c0d0f40e9030000150800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 86534542 1250 86533292 86533297
    0x30912100507090f1e0902030a0e01091406100f05061b010219141e07050f0703032105070804061a060703031e0c080a050601050714010e0f0c0a030311030d02 69
    0x340c058070760900d02801d1a059803131001041d001311103032200124103041034003800301c101c004a07101c2410250b603070342c0c44964120140160521600300b41d820701007a0300c2008060088060360b2171800003110081d40d100504015903950320f100781c5001909010081c08107040a000030040c01e01403442c4130400b4140303880000c0c01caa2140045c1c00c0c015420100c10040580c0c0306103034920760100120040d00340b03c82e009921010707220074864128107410004c0d101003000030034419091079601d0350f42a180c440e9603d090140c03c151400d40d140c4c2001c401d40c40c00904d407410310310036240180c0265031240404c0d5100e545e90030082091013104030201404080380c0c20966140002030003950f1017a40c01160180d186107141e44400c0c01c007441e0700600b5007056000900d169000d118503910081d0701c100440e00e07481d8000182c820b0301c550701015100300d0b40b015240d50001301c1500180106a024802c82c0c000d0900c0c1c2141c03030784031081040002d80c00558880200b02191286010721542c81215040c1c81c905504400200101d0b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 86535792 1250 86534542 86534551
    0x110903071d13080a050f091e01080c0c0d0e030c03240901050103030e010f030605040c210b030307200402030109091b05060a0c02010921140f0c060c0c1302090a0504020702030309121005 81
    0x30708c0800c05c41805940d1007036509030099104003003642402d88114000c1c1e00c41034422104420000d4806103002d00e03540400503a084c80702e028003651440000c03801310368907082c01c075405d66507404805004030324428030510500381226019501d40d0a41f034000f000459118110000310410162141000700343c56850b449158880c0c402600e4500e10032029400d00b4800080c003c0c0720314409481d0050000c00d83d200402120101a4414152921109940480e904c02c01008068540041c404000400e010001c5e40c000e1425a0103003602c0075107031001c4c03480e00e41c00c8500f0b8018245c1101e0140f28803007125000d0728002c07035220300c141000400f858031030034801a440c17041d40720f500b0003600480034070061144c4040e1003c0d050b00701802400818a140f01c0c0c143d0b45110312030101d40602c0d00002c0800301040144800324111200821341c1e0031186a85a80350042d4002103c828852028000d001070355180c20b100b21680d8544c0a8017035420f041e504000c203c401648541511040d01404140c06400f120922030780340708 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 86537042 1250 86535792 86535829
    0xa1e0509010e150f06060304020a03050102030906010f0e06031e03090310020d0e070f03120e120d0f030903120c03020c0d05070501110319110903071d13080a050f09 72
    0x70008036100d600c1c50203000b014005943e4507140b00344000d0b000004000e0fa403241003501c451359039480f14400708c1e285005691002d8019403000c000c1c004000c1011400c503040314800c01c006040c003511406c0c148113101d010f503030460b895030240c01c01d56015800512200c1070034411005403800e1000b4480800c1c01c08130900c44040205034002424180700c6080c0c40303001a00084100108502400e0040350703510401355010280481179101c40d60381182d403080c080c07030040480140c0f11050074000c4503006a510002d103580c0c0c1c40401e800f100c603454031901c13070b224030201c103a0541e0700d40840c0800c2541e000d0040801619003400c158080001c803111432820030040e504e01030b455407071541d600042d081c410708640c00c50380769444010081081c4003e0079540460001018201a00045c3c903100c01020071540344208440e6076014080d2040028080c00350359042d40038038108a884ac2c91b50358031075212000d07660201000621a00c010b100c0508854031403405418481051401640382240316800142c928580e100c10741403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 86538292 1250 86537042 86537051
    0x1a1012020706022208070605070501150b070b070807021011070c0e01030c0e06091602011506030c170c0a140d060909060c111009050a020409060605010807020c0102060a1e050901 78
    0x1c855650b00700b44c0052140518011041070424440d07944400452060038204140401c980303013404001e40c4064181d0807440782140c0e0050755246c0703240083d0800c44050390646028400111303102d0044456900c039103250b0740a4050614007880b290020104542032615501080c040503000584200510002d80406202c401842d0315500e45412115200e4100c2082581110213000041e101d40c0c0071550040001d0021640412003000102d00500c0b8000c880300d10071451800001c3e4040c0c055202d071945d02c506550b44ad40a00080c61400c407010800d171502c608200041200a003602d10600074040050000c20b002840d001c0c2c5401c0030816101c05800c0070312180d03940c0680e2800c1004521414100740c0e2241050411000140883c60710384a0050861403000c0e104d074541010000244480c000503640244104103aa41c40e04012000b0310150180c0342c003044140c00401e4495000155191001350141d0007081c031035484202a030050180303212681215906800c105000051500405116001c400300014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 86539542 1250 86538292 86538307
    0x120f0507080c0f210a0516020d111e100f020709061805010501020d0c0b0703020c0604080703030b0a15030f090f030f0e0f09010e04020312030f191a101202070602 71
    0x14100043c038000c03030981d04c0c51480e0300300d1110300b000c060303c17aa103242c0c0c102140c442603c803481020355001c0340c074004d5108544075000c0c1c0401c035841c03003260079800341614440080204605580303c0110b400720139603407003d1481d00790b0380c46910803a2841441da8081c030503204a00d81d9518840c0a44089402a0603078031060303011403003100054454640109000d1000b0000d002c80110068080d00c2030309000b9011491540002c0c0b02140a80c0447d0b070741942107030443d0303044d2500341090000d07504007100403400a070074080d20051920b480c1020106540d00180d484488044281040d001445030310410701527592500601300109003100d8841c49040d01130380b078651046c02e8450700140300c4603034040014402c40003040c01114684400c46900e06443c81c00010b03103034546407400040d02d00020544c42007905c900000401c4100752615800034024450459000007500d4000c0461742901c0314205c110f1285410350180d40400d2524040040c45200b550800c1c441c1c05d80900031000c2a64007d240c180c98040d000910403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 86540792 1250 86539542 86539573
    0x101b0e1207150903051b060304150e0a0f02090108070b0d050601020a1203150501050f1e04050901080d030e010b0603040b07090e0c090a0f0302061603090e0f010302031603120f0507080c 81
    0x75100380021060a0060070180c00000c01c81e001c040c002801c100c038400cac0c136060061802d500c26803406540310121038000c400c0d840c1c13000c1c1d64020420102c1c000c04c10003000288030480020340000707072001c01d0941030070f060a13000120000c080040c1a6030442c8240050040412030344801d98092650540e40850008204a0003000a000c690311107030400c00c040060011229904083d15040380d6108882200040000034480381405203800580e48200c07903c000103001900000c000302460f11584040c807981011002075401c8608042405400440806c00180082c00b6042c4c100e90250190030042c4003552180100240c4501c1120018285c110010f81100d1610b0084600e0009200038210f0000007800c40d404507c0714029a800d503548446800d40c940101406485040b0240c9551a1201c0071490309000b400f01c01c1e0401c2c03205034000d01809103c0c83c850206185080166500314118140000021404944080701342d4240b4080120074000c0200050680c0003d007030b5205527400808107042d140340c21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 86542042 1250 86540792 86540803
    0x4150b06042418170c04050c040f090b06070204110c0105181509101808070302010207060f02031b16021f0206060307030309090c0c02030d02101b0e120715090305 71
    0x351800d00002194208442c81a022100199091000c940c0144d041c0c48505500d443c2c01510681e90103402c120810240181610180c07084420010a56400c00d40d50901d817012502040602e5402840400214000d82069088800c20f24031480c1c14600c0c000e2401c5403142115015600341d241ea41030360b05000c2c0c2c02402003011200d0301a003481ca103a55070078034120030b95030791002030b0700c1460b60b50f01c0b103d41080340318556031001c826030342121005507510110b1600900079403000008031041490890000d514806038401e4901c40c2031584008041d0019020070415079402c6445428844045050a03400580301c08200c841440300c0c8001400503803a21020190074068001c040030302a40c09100100040f0342d0041c0030104840f407416001410440b01241100d0401884802035054464014648840d641c00280b84821150b4800100000d040003007544810440e04603680d4009845a0501c0016141c1030200200815640d801c5038603883e580d2140220401182100d0404a00c0011040040c008207108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 86543292 1250 86542042 86542109
    0x6070c090e01021804090c030807080301030506151c1e080405130203070f030e0717030a09170703110604081203070806010201020306150309010f020d0c11030406020604150b0604 78
    0xf941041c0646072481600c1440c1039400e0311442e158601d000901840c40d4140000e5504101c425942c0c0a580c280044d00d0760003840201c42d01d104002c00030340d080800b51003a091041000b040c2d10b104050314101c65048100805040d100042c08411890301030280c01002004144182000e903202e034a00820014442e46214207147c07010300420401405682c4400e03039407241c130303100c0c10005812060306003070600e0b00d807040d081400040b2102007126403110001000e8994580156943c4413845e44500b8120100e4038456035040349039200071030a20000d06403020b5000501c0c00074101d9803c0980d02c1002c1e83c40d03c01010301c03c80869400206000c0c405a2110146600500038002540b650508030041021041c014040d10203900000c00402c1c038604081d0001c0840d03800b5106d042d03444070b40410280b0018401c0b480290003040b1241280c1400d540080151012101d058015000b15900c5480e01d03000943c41c2240041120b07510f442130400ca9590b840138101401703600345440103001140ca1540c160580454 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 86544542 1250 86543292 86543321
    0xa020301030b0612030f070803040219380d050601020d0c0203031611040507090f0911030a0c05070f05060105010305010e0f040201180324140c09100c0206070c09 71
    0x6001180300581c485810074010303510a100d9132411480b20741540034800c0d107420341110001d15101402050b801660045000300c03482418907400c0014805110ba00b0b20a55a48100b900000d0700700120802c011005080e60450b01d0a24061030340018003190312149070b890405941c0c0060001650381081284903584403030a042074240101d030000780e900d0081d0411001040042d4400c0e100700000501c40d412102d9015200340b1403400c0c07204001e02482424040c1141e0710020301c000280b401c0c0a4055400817030a15590309107551902107c10000c0c10189000c0310605c002040301c42d00251890360300327080d81401503020303140310350400c0c0c00102545c03010f902000044448506101d40c880c144080503030050340c2404c1c15190752140000f0307200203150aa202810740f840d136003520340e0350720010f41004500001160040090103107a42c4a8204d600d0142c0d00f520113618140075018860500c1069030708010b000d800c20100340403c0b9400140141d00c0390400b29502044202c08000d21111703405010b1a001060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 86545792 1250 86544542 86544547
    0x10219081305030f190303020f1207020c0612130f0f06020a0201051312080411060417060705040303080106050702040f110c10020406051e070204110703080906040b0a0203040c0503100b0103050a02 86
    0x1c3c440740d0340d80c0b000b00d10842d100a03560745070305d410140694112100c0386150540d29848a5490100650021040340d005015000d03011180c252440c0c14400c550684404600d002d5031902d0305a020035040040c06001c0b106403000d0140480414005004c8900d05481850056a2072070001c00081c01c3d244003421a0a11200c109100030008a020100528580192420140341c0e42c7d51b040140c1c00d00150349a207504a03000140114400f4911030030080c0036414001190301c3c585a1030700413200317031080b032202030001200e041c018040750b071159004240e4680020408203820491411110440354032862030340351018006840c3d0301003e0144130b640035041c071104045044c1850020040c105210300c8811030340c00c0c000b030102c940090003200c040c1e0b050a0b03000390040084c0300100c20398038041d03400382c83e040d40441e07140000550104400220148038591000400070140c4450016074065000030b4012502c80180f81c2004c81c1e0340e02c04000c0c1982801c085980880c0f6010040d0014007140c10190000044a004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 86547042 1250 86545792 86545813
    0xc010203030708010902160c0f030c170c0d050a120e090a0e0627060c0301030201090b030105030703060c051e0409060b13030f020114031e060102010e0d080601021908130503 76
    0x2003550181103401100026a496101c95807c4c0c0c5110a80a00141311100401e00840d4800c8250000d030147e07841521080206a12102041090680c1000140d400d50180c01001100d0902e24201c00e109403086040300c140101c5607460740a9480c2054054001941c03180d40104180b414a400981002000c181080141201202c0e0303506c602004080c04a908510724014102110b02d116058000340c800040c2c0c1c50f107003801e00c002c0b2002d52080c40203a000039001c1c4804a140000c89045034121803004009200035031035951128017500c000c0e1581d0040c850184202c0c040850000c2ca1000303c121a00f12850303641d410254484201ca05c19000420b050350103025195815000c41c0000f0709407600a030160540303029901c01260244804642c1c03c241403004018000ca6008800342d071030714444030f81c04040c42552540300490880344038803016a165884526240000340c01807142c0f07030b004403044c03041d15000410114108106100000101c4811800051006a40041d04880300161004501528a038005c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 86548292 1250 86547042 86547047
    0x80106051801031104030f060c0e030304120b040c17010906050a06080606091b04060c031e0e010c0c051206060306060a030c090f0b0d060e0d14040e1918050c0102030307 74
    0x59480710181030680d11070340d80700c0e083e44031000d0301c0066510103002c1000c80703414074004020301824902080441d13002c00c4c01940c2c5140100681d02503c4407071a0b10f820021442d00c0b10f5034420381c041c00680300301c00460000310ba05094818080c069071020310003c60300a8091910008540d0b005044102442c90100c0601c135160011031255000b00381100c1451803070710344068001071040c0b109004290701c0130009000075400c2e0042d03180b07220b050003a260341200d00c000340c3c141e1006001d52030350b2000007007005020218542c01090303044526030140604c00001510340c2c02240424280d01005400b60b48404100205ca21f810080d40e81d1040041c1c0700f000d0301a2a50382c41d54648042405007405054a440303a80c0c004400941c803860844c0001001d83c0120541810800024020500016014041c2001c1c050405004003828240300c518000340c07501d0f1910b095850380b40c040000c2e00c0800d2562401c03016004ca200240640c812000042002110f007002c9460240d240c41c40100c8814190340050042001c1140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 86549542 1250 86548292 86548327
    0xa0e160305060f06040305070602070801020f0d1a0a0f05041b090b070609120527010f0e150a080906070903020d111f050a141c0e10060b03060108010605 67
    0x214941000304954465000042c3c0c52441401220380041d00440d0020500000050310030480701c454080c0c50b00c490300c0d666000c3c01d0340b140c1c03145003507691000c1241608844d243c0c2e00c2078442081c018101d00c00c0f581ca140010b02001096403021616014100f010f102518251160351710740b03450303214800307622007040c90042d2a0714414070030300a105002040960900440350420aa0705500070100721101035140c00161030380e004145407440c3d05210500c0b040f00380511055030301c00607105031140c081c0e412603408215002d041e580e80315a0813a480c82c1411035818440c0c0040c208282d51911400704505d0114a0186400310090100041005032201040540c4510316a01c550b55008000c410300c44440d6408642819403a6004d091455100c282c040c8030f05922a0150088441590b1200d001942401c81c09989000b2003a5805544003c5551140b100010384c2c44041422524001e54480103803609840c2e046510079842111142400401c0000030341e07120103c01d001d440a41010f90602c02203040c03248402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 86550792 1250 86549542 86549581
    0x901080309030d26062407120c0203061603060b04180b06030c0301090f0204030f050d08090c011707020f161409010e040f020a1a0d0b0303030925090c0206060a0e 71
    0x44da40808a034013501c400450721045400620b103640d2012820000382c005070711000c1d00b96100b183d41d100c110300301d038410000034400c42d80050051081e80c0b1355a030b40101d10703900014070b0380501d650791400055142ca0200a40000c160010380680c5401c0d18261102c02c0d0b806140303100d849010101301300014140da04c1d040c0d07419641e80d650002103003e403490f60680244516000501003d020820f20020000d0008a481c258041035581058540300d55206070354072250810030347e003c0366043c5800403005000600c4254003032154412507204401600c03c50b0b0411b0429030811181402d949824081c040e40d610704160014415501100c2540c5050890140224080d00060a50f00464404403c3d9620129440060191a0420102094250a200c04a90100041100c0c40341090300140051801002383d0348100506000380101100300e002e10809000440d0a03500b041d0219500418000b016124401c0c6440031600200b03ca42410020842c0301101c5901417688c0080090821481401c40007020207103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 86552042 1250 86550792 86550857
    0x108060115180308120a0b0301050c07170405041d0f060c0405010c060902130204090e01060b07081308030d060e090105010501120c02010f02031f17030304030e030c0901080309030d 79
    0x140c40c1e2a4030080e180c0b81035548040c04c259404200402c1d102c00c500300050055004180c00c0004500d00c8050500380c034811034140c0c03150f0405020100110300c1c0300c0340c0820b501d1020045285469281c00001d0122401c1c0d01d00440c1308902404840c014010402413805c00c1c40401004200a1074401e030300c0100ea11481c099281081580a016001c106d0250000e2840c954000d14110031109800d0900009410910070300a030139003040d0004150480c181702d0a000c0c0c2e000302002030b02c0e202c255114070099a0000c444d5a00c2d140c028100007074800e400b80b014092285030200046202880c008140007030b000d0191a500c80b60f45044010081d9a80001c80584002c03469000415a089960804c1c0c2c010700d0b080d40c0e007040c4103000108101d042c1c4030745004803000345501c50401390003a4845400d0414910b001e010034485a100300041808079000340c0007422100d80c003d04603803406e05017401141300c0c64004e900c248800c0d44081007840c0c0728501400203030942c240c140340c8000c05400e40111403e2808100e200b001d079 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 86553292 1250 86552042 86552057
    0x30b1002240411010e061b01020c0c06070803010b0c0a120203121e0a05091203010f03020913080403170405030d03060501090501020f030d0c18030c1e05030604062705070e0108060115 80
    0x50711540c01fa90780141c0807010115841c0e80c5401140e002c1c3d840051900d8282c094079505030407600d40b460030307a00c031a034105640b0740c2181c0c200040c0c08415130004442002034440c0c0d0400200161401e40510000200d950117181c40c0d4911031043c4a502c44081d00a14150070080c256104442c0b001404581c072106801e0041040e40700c8611581c103261155843c054803220010000c074403441c4441144045134420f50b4076a04a0350344070400030301002c80140007403a81d241044208041100110046554424140c030146040c0d41e03071707001a103480d03410f00404000c01d171148800c000707640c0c000b103040c4024003081c0082c292a8036000d080c10b1300d034071458040d00280c5954400c5094541d02c20800317105040ca0101c840d82c151502c80c10300c1c0c003054509201c1d4442c0c0d982a04401100105044414011200c0140080c0480d403035594500b4044c00c2c030b90004000c41c0703041582407401c1d808485800d058150148014115050400c1480c21040f041600000c1c0caa40c042e100400403c09100d8485410512610707203400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 86554542 1250 86553292 86553317
    0xa0201080c040807030302070e0903040f030f15090b090c0a060c0206130f03080304060c0e0a060f121b030b04052203050c011103071d0105030c0703030b100224041101 73
    0x7580c1c0a25040311045124182c408010103800040c0441520100010140c0594601e2601da540e4880c80c003d0340d0500110080403c0028014944000505d100341800b01d500c80b14403044204236008407100b600c041400d135090054210040c0030b103440040003600d400f41ea5500f042005800c64610040c000e015a50002d4080c455038144500c5102070101c100901c0c920319924188104180c00a031000e590383c0b0304d80341444182d0340c010b152a40e50102e003e042c480481c0d00c0c100c3d0036503804506410010030700502014400007070340540705030b14805130700e0281e241d000c6c4c240040007012207804560950165184c2028401e154800d4040b0b054419809040070011048138641100e06001d401030300300d8151b00b0900d8803050440304002035407007900e0039034500c0c00086031800445000b0400600107404590100045100c01c4425002821910f020341008500300001e038012803030450071018060016040501603140b040010264036500860088044000e070815071900c490795049246058103102d00300c03a103035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 86555792 1250 86554542 86554561
    0x1031b1d1c03021608010501031a18010609020d0b0123160515010905060306040209010b03060402040515030906100b040509061807080115020d090905070207030f0c0306050f090a020108 81
    0x3076001d010140403881409203290207982d1310645082500703260071040b4003140929051080314107c070780150304040801c1210b40c2108111402411850700c45061420710b190340301e400d004040c01008049401030348e030400d464046086074400081103040000001d40051196907541080d441212444000c035982c0e000000713a2501c03414120300c020018041e040c442c10221403004504e038101c5da2001410301850f52000c0406468031000c960081d030140410005008201d005070140d5803200d0050001031800e51110005820034a04415104e04190b0000811a96420038000d103900144010303c0f40c1301c6c460616000e00b0317981c00345000d41070103014664006247d581d0703903070965001e85aa9282054990a20000060190100b401a0300800902242c8003a001e480051407022414259136030502003030030329524001030040509602d01318450000040003086140000c07407281403140c9150441c0c5d91451802c0429a4030051241b484040782e5420042e17036081c08034001d00030541c2440e2a091655422802 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 86557042 1250 86555792 86555809
    0x60a020a02150a020c06010603090812060a120f0510092a03080706020909010501020607051206060705060108061614160f0b01060509040b040e0a03080702031908010501031b1d 77
    0x14a9002e1080300188150b00500398001c0440b0700d203e00942c0c00c01d031703210401502a44e1801d81c00a081e84001c0042c2860a80f10507a00c0d500810f0003803100c1c1340b082d40c49030100c03484103100384140c5460075140d8103441042000c0003450500c4203480d505101c000c00e691240c003c00306104d4165801c40d5110300c00c50b105402d2807140707440615801300301c7d00d80304c0360701d424110001d40000d18000c6c0983c80d000c0010074198000540103206900981e101071074502201c60010710420090f00e80364010106100e041e0004134140845806841e6450040081d4a0079a200008003041541c1d60800e10511101410343c030501b0904403141da030025071a041c61181c0c140f41a25034000c140c000580031105480010078200d85c003000810042d6011641800000901800c110840d55000f40782501e550210500c1e0300003c0c0201d221a80c4010140103681c10704200003048840b102001001c64002407107800140550b61b014818201c1d00c1c2d8805907003000185070300303401178100403948030520400b42c032401d19026903540d50260f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 86558292 1250 86557042 86557063
    0x5040204030c140406050f060a0e03011406030d0e01140a0c051b01020705040b060315011407060501030314030412050d020c01090503030604050f131106070f0506040c08030408060a020a02 82
    0x10465859a480c2002400100302d8000c0003114810020449000e207070500407002030b01d4005001240016040003000200d44c0701200c001c0500100710203501d05d6a80c28032408070301ca002c0c0442504a40303481c0702014180410090064203100c0790b55100041a684441c0c1d800200a1005425540361680c4805680b60040b1200041040c4180404049038400b1705a400c14280303001e80844810603140c408000644820001240c0c0040c0b0900004aa903c0b03603080c2c400b80d100c4181050503806103604a040102d611001c029200c40391585d004100705903000604510380714150040b9400c600707080d5512116071a4a5081d103013000030108400140d44803650444408520302d0000b045a54043e14005440345c1040f119203115900c0c01c40050300c001000c042d69480380d810902440d000702c0d100c0d52040018600c0703a0585800010a2080c8400925080396803403100c2d005000604051429140180080c0d240f80c00c86101a0010700c002c00440200003112a001545803001680b2000b40c2c4a00302e00c2d000c3c0322903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 86559542 1250 86558292 86558299
    0x51c0210031b020a05010c0e130b04020f0d0603150c0509010305150303040e09070501090e220f080d0b01020c0d08031e0c031603020906030105010302090406030b07020d110105040201170702010605 86
    0xb41c00400c00e40d0001100b07040039124400034880448019400c0d10008441580b00b508151504d0000b401c00d986a8001014207000903c011b0403c2d40440d40e130f2900d40c00c5178103235140301c5940b6101403060002800a0030b080740c1d02e2000c24085410b96050040043c018841c0d02d030b05050710342021440a9a9543d52480c0284028003103a07169542c03000798040140d1305036444442400785030008121544940342c1c83c021f4940c00c1142140030340f6201c03803500380c0b16020700d19103903441030200d40c00b40040c81045010030301c14054448152941d840515010031101205042ca0542d1301a07400101140c8845008084c1e598010404a80b680d032101c0341d0141c4a00e0800341c40c5441000c0c107042000a401c40000b950080c400c8041648010400c280c1c268100d00c1040c0c1d205611030f2043c070040010f0340c400d400074419500e0160000c030f0070f143c1d680c0d20310081400c250f6803540941c00c2505414945c542c04007201d580c03102018001d100e10706150300040c20b83e08003440e264850b2520301000802c218004d40102c4000d02025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 86560792 1250 86559542 86559581
    0x80c0703060203150910120311010615090e070905100c1502161a0c090402030903070c03060c110304050901030f080c0708060601080906060906040c03090c1806051c021003 75
    0x50f4550051043d4801040c0c85515260b001c43d82c5104000f40d02004d4170b00300f64947e500000c0c20b44090b43c40494403c4401403641d2565004140c40d644203400f503198503c04d40700c400c0c400c0c0c1005201c0c0319090000300000100600180200304590311500302c040607001c6818040003803155420f0020220045030036828000380005012542d80d4010b101300c0a20601403802480f1201c0d5940d05619441c80c15215076861314010300c6007801900e8a070b802160005540d10489142440d265a000e00c0240b031940203598065640c1000020b103074000c241c0c4000300318401d000c1e5103001e0074403001984008040c0005042c1c02c414000c020204880c403c12034203481d0303602c03007203038102694ac020341aa900c00c01c481c1180011003002c0071800c04c031000035015004180080020744c15954000c01c5c0001400b0f10200207003059200d005600100c4d40a040c2c000c040e19005507180c0e0026800c0038500143c0d9056400903010328641d410080000040a6040d840d072541184c19280c1e8500e051070031009072802c00700e60307103409814 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 86562042 1250 86560792 86560801
    0xf0611070b0f0f010e0906010e061309060605150903060a020d020903030714120304050a030f03201b06010302220f050c03040501060501110d030e0304210b0a0605010c080c0703060203 80
    0x1561a03a84100344001c3c00820903078840804546000060740c8400e410743c0482e0040c00300c00d0400645940c0104041d200788000158285000d00f07590245a05466141d61001d00388124109085400d40e01c100c03483c0e04520701400310000c0b980c1c61400614040764960b0200d4280005d08064044a90006009080741c0d01c0e609030741003d904000f0044501100f07481038003030803000e114012081e03d1040b50000d01034003040240b5201503440c803000b0700b242c404040c3d5492a190300744c1c00141818012008800302180c8072070008100e541c1c45c40040b030701c85100da03004800400042c0c2c1da180321007080da040030801c0511070384404100307000b4045544400302e0050908040100c030f4620f10000d50700c124045c80007800000d54500040d034600c5489240c1544a411038114024940c5c000d0700060300c41c0555008807840d0036650322214032407020081381c1810b0380c088a04100188000c0c50344640c1c00103a15541009034030719240020f0682000300e000181004170110b142c150110043c4440b10003190131032000d55030380c81d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 86563292 1250 86562042 86562061
    0x3060b040b311b11100509070824070c080d05010b0d0b040c050306040b0310090b1009021c0c02030705060c1c0920030a0c180501120f0611070b 63
    0x34600c00b800012940486100b40145402030003d4100303c0c20019820111140c0200e494625503500030890380b00b10382903250f142c4828860a0f2141800c8400380907094104401c0030b007480c0e0100f88003d0310096041e100c0040d0825082180d03040002c03400d143c0018811494507400fa801070f0908100304501d407200005044200000801131218001410031220442e501000111402501045c001800c06d0002800500701580049818800142225819140c42c400c01c8140c801400046800c41218010301410030303003185110b8098040e01c8000d609216699004141407240c68184042a94540c0424000180280700f1604083d40000c150398503854034440c2c241d01d96000c1a00851900c54007450040800d004d4030070000b01d1548101e0110507001c414800e078014249000b8442d915004502080d4000380b20442c20384001c0405200000341843d004010740210740059112200c00c240440090000400c0c0c0c81c0c00701e00c1198840c0b00025070aa403000c22030320318024070800425401990f41809000c2a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 86564542 1250 86563292 86563339
    0x1020709020931020307120b03010e0a111816030b010203030103030816050c16150302040b0301050420031305010506011b14070b0c0102040510051e030408070f0f0203010c0807050403060b040b 84
    0xb087c040c10b001d00d896450600d4201d904400000d80c507500604201400200c4403c1801e10f482e1000384401100b41c00d800a07101d110b03100f611020710f025101e0002210581d014010198000d0090018504561446d10301801e04c0074010300b1074213812080c510f8104502d006a06841c0ca0b0b6480c2c2d07084074640d1903000e12280c50003455000e0f8800000601702845075071442802210241d030a5481c1c1141964a40f4040c070000d031440352a11030f41103003499141c091200394400558071590400b4580d2540381e200c0d0400c9421204050119410882858190154401c504088040305070340a418542e40c04401140d06040010b0b6030003952100c2c0700082c0c07401c60044150080c1c011b8960480342d035103644d0701c40e0800380c4841c869003042c180c2d10050180c58102c1241e418014580c080d00424030300b07160405a81c0c0c0c8004000303001c00300711440c69074551110190309007440340c600b0f040310900340a04141807041002d080350140740300040c01c890701c5815040c0a6241e64110394025040036101c2c0844c07c3d072034a030290021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 86565792 1250 86564542 86564567
    0x305010506150a0e010e03070905040318140a05010503150306090705130c0f18030215042301020616020c0306090a14060103031b06091505010501020709020931020307 73
    0x55180e0700003400400c01c640d04035090f6076032a80301e0110791200e04005441125038030200c258140030300d07500015142e699009941c8a02d110b541c5420030800558070800316000d580d04242003512841c0b030f414485444031072100081e141c1c01d082080d2280c2d2072403114035610004451054150140c3d000b803089145000400c60709454003103515030032a04001542c0012502d414414500140c0300d800b40546090080e200300710302c0540786010074566504c940100f041c00b00c1081d50315250071030009040003d0724044607605180300d54048c0241e8030740540030000350341e00d0020304001c009104820002010a0080005240725070f40601510103d2900080c2075460b012220829180816101c01710901410f0205005050741d07810303203508031a03894400001084ca101c207a0704031081c0c1d64452144000c80ea0203458000c0d121500c180c040703900d60401000904020707990384070035401c0b0300603c00294a50b4030300d03000c010341c50780ba041d00480102c45080000610041e000220f4205803000051115041d0b22440c1b02d403e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 86567042 1250 86565792 86565799
    0x6020d180501060611030705060105060c070306020412200d030806040f050a0e0d080708070c150504140c060406090e0405010605122107050d110c0301060603060e0f19051308040305010506 82
    0x32100701178030701d41c8912410100a010750015030060100e8900800686003481e400310071183c0b030a459989003412a4081d410030940c28600300e044038204440d001500704020700d1a84501c4070640c1203400310318489143d800003000d2080107800160325490701d80c0544100360721140c043c00f190411554000051402c4120203019000c1d0500300082d040c014002d05018034516602d01c44035641b00c26044440384c95010046410200501c0000011041ca00070640100d004254024500e0b0401c500b03186824200460740b4040c031020300c0308006168000705000304550504180c20665034071031402500400254010319030004a414004144003000585070711058803296802c0c2010302c071200d1104103801281d600501c968819801c10380182c0c4142071880b5070340e0041040303c1743e0b4024040001d003940c083d500001d0003e56101400c02544503c01c400c10b800040307503480f00e801410302001040c0d0b4091982c080684054481c00800c010700300010118820b103401c84141c3d511541c80c0e28007140686010b03500a4072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 86568292 1250 86567042 86567057
    0x304030318050a05062521080703050108030702060705030f040e0f06032b021203190f0c0509100c021314060f130e03090409050f060703020a050706020d1805010606 72
    0x1031030f007000c05503403003610001406141005224800720303160440540d1503000500b101c001210008518644204100c280d01242c2103600c001c0a000a152080041080c4205403d1000410079188048101c541a580640d421075488502e824400c1c034510546803441140c0310b00040008040040340c03103803402034a110440c25401e854400c20156075500e04002d03810350580540340018101d091090b4513001d56443d00664603a64408a00c079010364004070741480c503005102e60900b00c0025240321309404000302180801c43d028180340024610301590505c1405403c94080105100707010f980340c0121142d005012550030340d0314110460150002440c0c0c0308050365488007180c000d1030201030714a17120101500050a602d50035203800043d04044151991a0000f004030420305e459500030780702c00c203014100400d075008181d00070a20b886001007140d410584140101801c0680c81411a1415508031034056100c121a90440f0b0041c40040c18606810300c102a10341d0810806404c80021141c2035182d070003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 86569542 1250 86568292 86568299
    0x10060315020a0503061309020405040302031c060b040302040e100203010801140604091a070c0605040f020a052e120e0d0f18030b0901140a091203020406170604020c0304030318 77
    0xc103074014864180003282090000401c14180403401d840429096040800c40400c690085011100103490507001a040000c20103001d200390045d50241d82c440c02d0713040051a1404400240a0060707000080c402e0707898031042003c45004008030404400303211411035603540e40d4004036000300724245591000c0691030300086d20030300d440d103e2000300302e41208000702e01d14403200610b030709650000c144109103c40300d41c180d004a8101e208640c400e40c4544005d807440d0030280104171070184c0c6548051f10454001b08442caa0820840110031a868200c8444400360400c1205403400314181d115840300c0f0740340034103003520700c2c20019060026843e2500c5040c0701e00d10900d0102c9800c03240480b180541040300c08104001000781304060b5000c10010300020300060003640b0420451011740758800c00940301c8982c4000c1c000000c00454001d2894141103103880d241410180c20000e0002c5d00d1000140900300040480d1a650121140171b00c184090325980c90312031031b000d0300c2500d00070603003a0352804060011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 86570792 1250 86569542 86569583
    0x60f010c14070503011506120c1125171002030901060e0403080f010b0a0207050d02130905030307030b0d0b01090504050a0203070612051501080f04080f1207020609070f120311100603 80
    0x406864044c1d54038238140d00303103080d424040c040144141e420001c603485490316048080c0041c5148004800440d502111070724070344002503105400240a0320000e0900200342d000c0007a5080031074011100140c0c0725958000c0c9903006101075881808805c2e0101c3c10003080503402035000c0c0c40b0303624070117481a1691b201e0500e10201c1c0210b481e40c2000d607002c0c180620261400e09000d0040510050085990910f0110881c041e6140910101e840d5807010091182142c2c00d4054107110100581300c0d00780061450f10766500307070f81061103801203003130343c6030f0106003400428805060b5241d005011206a030780d58200003410b00c090303003601d540124a010f0101d464448000266074184405948400641e118800f100d1400c07100644200d40c6e00104000d01207030002e092000d0120401007404882191402c0480a81030843c002c103400c03480d42004800384180500301000c90b0544481e041700780c00454a40ca41518010319105050543e84603444512240518035000a003e80b40704100e034a02644200c80f10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 86572042 1250 86570792 86570831
    0xe0a08031308040f0603020c0f1506090703140f0106200d050a02030c1002040504140405101a040e0601081903080f070e060a02010c03050105120303060f010c1407050301 74
    0x4081200030030201e4014031015074800c1c000c03030040d103603549001d546610341111000d02d41e2121010940104000d032a440c014040800102c0e4a40050322600c51a2850310704d03030000040c0007074800c07808035021800440c4254880181c1300c0a12201643d5800d00420106104009104007000240c040840074070340c030031000c050b19190190100803c0e08000c42e12003561796401402c05070341144818003411051443c20014034400200440340141e44506140610064a10360030000d10010075950038400050301c0090041c0440d04141e0700080e90003501007680c0d02006480100b95030050400c08081c246c5200030510318101c0c4d04d000700302c51501130120142a0292010302c000b0780030510b040c00040d11000b00c548010340c0140d05152040c43c103440c44002072499040307000d0400043c2e661700003513546a40c0501c40c440c05054100c90050320b0308800e0400c0c0e03035030348001400726010321080203820314680d0190b1711500380075512005600d8850001c2d002030355185468072482e4820340c24607600c000b111035200700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 86573292 1250 86572042 86572063
    0x80d0801030c17060402060702120601030b0f162c0d060b040b01141e0712020105160e06090d0606030605071112070308010311031e030406090f0e0402240a080405010e 73
    0x71303180c595516001c00000d07801800e000e1fa08850000036002240c00d081c0010b80c040c610500c2191818200500302e0340c01d025008224507414030b844483c400c0c1c0d064108009039010408444000003c3d440c5030409002d880c64803122540107099244000100b240c503400070000c1280580c1c040101c1b9141d103004580c0545158540352000074208023096a0044580c8046032500319030f0f92480c544006c5503103640541c149000e502d070050b5515001d2007083c9841104080a048243c60891402d4402e80006002c610948403558030680c25003914408103c1d15400403001544c00160805c0946001c5201504184440042c008140900700903185008105800c0e80c014942594540032160f003141e03906255180e000341341070740c54803030f02c0700c46522400c2c0340840800c01c41c2c06a010f55142c0d0f2428001400e0042030382c105041e0b80d0800d039404e218030300138500e890740c4c011340488094000074140c078803505803c0c22034858150000c50006110075816000040c150140d40700c2d90080000c0d842002e100c135207410718680d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 86574542 1250 86573292 86573339
    0x21002090d121b120201140105061909080703050706170f0402010806030a152004081024030602070314090a0522180203010e0303070e041104080d0801030c 68
    0x6208008501000780c0700c6241071041c10b051034a1a2240314544401c0403106003182c0300c4c21100d00b0f00384400d0b420f00401e40c000300b204075040d0055040800003502c7d40920030381000100d15100c90214285d21030072006000b00300e00010740343c48a4881c100b81d511900d5600a41010800342c104100c2000b0000c12090310881c88440c1a00060301e4960046540a03006001c1c41d40c1407080072070100c0490500b409081544100150015086100e01041e401c1c0803032480c90180c0d1280207000c00c00140402041d0595000f0107071100103801c03a00422140c15180c800c00100c070f00304551900100c20019140e0040c08000d00a450f182c02c045929501d0340d04912030900b1003074000306031450412141c1010706086080d20040c10000f00b042c0b21a001810844515103c038000c18100d5850b0308003982820301c5400c02d5007580c6005180395280c10080644028034014426000d50f503980072034030407900e401040d40c02400080081d226614244040280600402e0006840c928030f40ea00020f00001c0340400ca510810485 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 86575792 1250 86574542 86574559
    0x60f0c07020904230609010501080102271c0b091002091f0e120606040c050304030c08030403050f122502070506070501020d050f070f09051804050106150309020102100209 75
    0x203509215120300003030f0003110160b40300801c280e1a0048010004c1014103220f000f40b0542c5090b0f800582500e0060384160240e91041044000784e02401d0f01ca000302d54001c0c404000d02d00100008525551031202c1101078a0300365034603810030030509440c601d0042501d0400c60b41081103e094950481c4182c140c0c01d44d000c0d260400100400341803980240340c107a040d08140e22040144008180e943d0028000200f0035013000e41008264501489488030042003803400302e003140342c1a50041e11071520818081e1030030401000145c101841442150802850280495114103042c021071202e0941a240c5080010350340454240142d0305c0395001c41d15441543c0108600391411080c081140d0200c03074240c500f550200b00c80160380140e40a098001c240447c40b250303031440c14070703001883c01100312112010081011000c000560300d4a04040c068928680301003032549407071401500514441d440380c41299003821409900175059030244203605c0c000c0e02640c4190800c2c00c00c26089108101c9299409040d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 86577042 1250 86575792 86575807
    0x60b030f0f15100e0f15040f0c02060109050114010c21080403080604110d0906060306060602031c090201050301060e030307050a111816030c0203040e01092c0d05030a0b0a080609060f0c 81
    0x645c0c440540202001d4428070036107a0f51800324060b1200c6000108606888520304003685604000c0180140303c2c040081113a5410100829000d14100500078100050002c0050034002011800000c6072030105904500d100c006601416071007085030181c002c02c00740c00c005206810703e0f01034000002941c0c10030500d04409100b1980041804040660741155140c2d0040006201c61160720042c0c15240c000b181c07201c030051030400110551000600195007014070885c0140d8000c0140c038151074060400304101d004181c04240366000b000406407892048011240601254414141c1100000c0c4e0794490450350090f212943c0a40a42d240d108510784080680ca801c3c0c804c0e40454600c02180c0f05413460150b03258010001d074a030a13003060541a603506c024104c0803072003604c00f0f400010388580c01c1d08070b00c0e6408844d44e194442d052010b0705000000001034002c012a83c854407140500508803800307180c60356502c40d62040c08071007081c11482140c0105162031500150303280324100402026192210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 86578292 1250 86577042 86577061
    0xa09020c0d120b18150402120f0606040e04060b120a0f0506060415030b0601170106020d0e0f010507060b0a0b04141212040b0a090b0315100e0d060b030f0f15100e 71
    0x418000d600100f01700100b8641d40c1d00c4c00103008540030042c103520b00c0c2c20f18007080a8861350262405200e42401c200400210b40c040760507503449604110000f0300a402d90000c82d018481081d01c040e418000d0300b1411042185489404d4402d501410440e5090765582e4144011162f00c0032001e80c000c441c403e070400c0018880041b90b984118180b408990300003121900762005130080c0c0011026030030a118075220380341d0201d030245e803201e01190850100b8860b074001818610420401400890711008540c1c0941c503140c0048004091304000740391740320f0780c400c2004011407202d5491489040c41c03e07100108000006844500c1c880c41c1c25095261a00e800300503801a403150504e0400c0c05000b21000600c00b2014001d10310034a5a20700b00ca050040c403408004c04002050204000d0120894124410381c8079003003210308107640000005041025800000d18002348000c0d5914103229039140710000c00c00200d0007280c1c10315040c4a4a02c00c1c1ca80e6040c0d035850903814018090344001503400101c1c10702 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 86579542 1250 86578292 86578339
    0x5010525020d0606030b090d0305010321090b0406030c1101020405030715090302100503180607050a0c0503070c0b090a0603060e0a0c111501140405040f030507020a09020c0d120b 78
    0x184000c1aa5088044656440e0140e801960042e902c010401b8100134814100b4404402c40008901d4100301640c11542c03904446007100312802c44017540a80070459041c01078100401800d118920103480d03554419006001d0040410071000207203803540102e071142c07070500a03203058441c000c000c0e040031030514000c01c500050280c1800b040001d0004000b01580b14030469509403450b60f52207965074908183c00c1c014188150005101a52007081007145003940002070b9141d0040a1501107514010307404d0261950090810140c1206a2010000b0f100e4100070010224420161000b01e600b581e40c5400345c0489590380720354161183c0300380c0000c04082465100c0c1420450030708201143c3e582468450345010000000c1c0481c4880440040c000c081c7c490036201c41c0b4100c2164180100c2c07030666116034a6404141004091140121380c14045580d80200140a811214011920707202c81e0b17005265141844030b54403000c201004c05a2800c20350b41c1c0103c401901000d046040d22aa4034000b490444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 86580792 1250 86579542 86579617
    0xf010804030507080403080405010806030a030c080306030304170304030201110601030506040609080c241f030807061b030c08070306032307091112010e090604120c0f0807050106050105 81
    0x40b03000c22030400050307000070140c00614001c180d02d40c0c80e0350400d00003420300100500414425440140103400003940304c11000c45050340700f8800754503516a50f000c00c2c5103000341d800c04c0c11443e004012500445100101a0041b6030007640c0d10040581d8440d12140c07900001e00000e0716607001200004c002c22040d412102c3d01501c6100c0c2c86203080e040395030040c140041c031080340200c0c1092290194000c0c1e40b2802c0c02e90003140d44006030018081c0400d9400c00342e0b48510004114500c0071410f20140099076100a030816100c03000307600110a100001002042004076043c0031552400c04105001c0c4a8414407041c0c3e1b620142c2203840c3c1000b160307145144d801003901591144250900402c8220160140002020511264540380d0305803500e54620a0016044194003c04040800003003000005805400c0780e000008610300c0410010704540c1d0201e58040030f025102055450420849624002c00000d80120004c00000d0b84440044501d840380802c103182d180c05128000018050351882e030b1494 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 86582042 1250 86580792 86580797
    0xa060f1b1a0109090c080102030c1e1b030418020f18031018060e030f0a0f0e18010603051302060f0c0a020414060111010c0207120206120f071d0f01080403 68
    0x14071050048074440e01000741c224015498a8018003020402d030030b072480f005000914025030644c6051080c2d080720b400340c41500300c2d503294401c500084200e82071041701d20000914800d00c0021140d42c030419560362052040b041c406a48503504083c9550500c02ea403031442c0b213102c8241c40c003001c07821059102d82400c42c0d01c43d07041c010006411011039413442207040d40c01c005601610b03107030f241c0c2c1448400c659503020000c0e52500100902e0040d802c0b00e40845144d0407050406040250014000301d4032001c428034100c0d00705040d0300c00070078030400d00030460303040714560b030303400d0000d0f42c0d6925025550014800b0001d4000c04180315441c14801c9040181c410303040c51000b140d549141c0c9400080945114000f044010390b9070009011155a00c0080b00c5800780c00540280914001124021756a00c0030b0f1203a5500e00110b112000c0c210741d208011116900c9a41c034442a0604087c428840c0140080e1040c0020660407107030001d40d100742000d00480800d00404d0613500050240054880c580000e004504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 86583292 1250 86582042 86582063
    0x102030c070801200408030703080c04030c0315180203060708071b0f020102010e07120813030b090708011a01091e150c0309060504050603240607110a060f1b 69
    0x280da54100000001019580c001181300307018200e501c3d00c00079400c0101c900041c0104014090741000104650a0720362604d421a8280d075143c1002006000e070745c10007400d028400e0400014041d445000b0b01c01a80c003407400700400c00d0405203030710444080312030003501904018005024603000f85140340e8460141c0c01d10142c454101c42c1b80c1a00c07103c40300411503d4404d0705442e00700b0b40d40d0902c151941002c4080040000c1410090548104020010000e141060000d1342c14145448020781400450307020f01c02c03014a04107000c14a03158182401281d400750b10b4072130740b40c217141031000203410328440c1a1903010010b400d1515801d827040d4801201e840200d010840043c1946403910000602440e9a40f249032030540c0345001080d0364100c0d40300c4d8040040500c8144880d0751602d04a90b000310305984403031201c2400031310701403041103e54500c0d41c0c008004202c138001d102d8503d143c10540401141d06030f02c2c403a16040155200c8078103c1c010000203401c1c0303505420500c03190045503011406500d0108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 86584542 1250 86583292 86583307
    0x309140106121a01180c020c0d030c14061b030405011b080702060705070816051f06050418030206060d050316060b03010b0406030b150a0807080604020306070305071d010203 76
    0x80c01e490050b4400303121800542034800912400c185941c0303030103403c40c060070324075450500d140d01c602c4054035090b00003030303507520345011881d000b0401c10800041c0540104401c071840d09000d0688128504291800d08220081c080c80e201c1c007060807446401c1071210009908040401c01406030001442203070b01b0340d41c41d8040c2c00c010448000d5941030510076075a4003058500746400900300f41000d002d840c180305003480750f000040c190f001070358280b841e04442104d58050701c2c1080c1d843d00b440540711141d03001c040118690000d60702d80020080c9d074000c0e01c06000d120318110000d91041420034020700141c0003034011500b145440c5250150f80ca016404490514501c03004196032020300b000200c804554401ca9809581000c0c020850325800032503041141d10310b140c49524462200510340d040c01204d407900c250322a655503104c072001c0d0035007404843c461030b120024155a01401c0e5003ea100707100300000a0a16403180c003440d44900c45035920104407550010b0781d88903162512513440c4c1540800d00011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 86585792 1250 86584542 86584583
    0x20c0a05010e03031f030309030f060b04060b04060219150506060705030309031b0c0a0e1305100b0f12100911130b0a08010212180304080303010b130e01050d02010309 73
    0xb0b58a10403a0303809503039a428015407801d40709031032110881c0002118241000801e403ca6503c4044a80040f01d0441c5a1307010703d0298010508803800300da00510b000008120380b0104006032003902c2d59a022509600800c480c1d64114442c1c00d0001414418180d40b42440414550070850308190080d080700d003002a2680d81da41160011200c030440c0d940301141c2d01391129816000403007011040000f8080c0141c048012420068060040502501065010410110403070311001c55058002e0b042e100d803502c094400e1800780080100344d80c401d0a0080c50070010b841c0044500d118003070280000e02e0f202c0300b00c804d900060001ca040552b0b04603420f200405460307c0d03002c0c04442c841140354000814220b61402c0084921260b0000130b010b0380705000050040ba034820700035403c0541d0001c180020307401061071910b5071055401150050101200018405010502400b540150100000c00170f94541a0500400409101c1e0b02e038850390301d44a1102650090784841c0b00300b8001d880ba40c004444004a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 86587042 1250 86585792 86585801
    0x60a0c05030a050c070f060813020a05120304031b080d180b03090105090106061418031c18050607020604090906090507060f0215040201080f100e010b0408010c0311030703020c0a0501 80
    0x402c0401c00000e8100541c07607007404640003406104211000d03c9003400c40003030400300000c1411a240358442030314070035075031201c0c2c02400400d002001c0c50410348044405079141c7e04144403c0301e40410411800288800300d5801c4000d55242c070005000c0001455400c540e52612000d008491407140324011842102075802148a40c1c090070003c200e0381010001c031800c44450b50300807010040190748400b191078401c401c6402c5c90360410ba04000004000300042c1c28510300c1584ca0350a40600700c2501305503a00f10300201140c00c0d80010007003a90b075440c806e0002903c6a500000c2d4080010032050014005590194a04900588000844402d5660340620384260b03504008041420a54070303200b40ca50411124042c04151207450300d66080c9940040c1002102620341480216410000340305400d0584c9420010b003290100488556513510701c0d0038190f40705004581041d401d2a44c4032040c10700900580e00c0d80c00ca900004d502d559117640c001c80094114601c4070081c0d000e000000c50124509002c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 86588292 1250 86587042 86587057
    0x2210f0a030c0f0c111207120f170702030d03020a0509030106170c0406120308130f0f02211b030f060c04140d0c05152203141b060a0c0503 61
    0x10000b0741c0d19841d081c0542211014411442040242ca900d180020004140d0015910381074525510b0150610b541310305045068200114441400680c4414040354840c03019005003e400c08424140644170285018454108040d4150b40031511500c1d100d442503004120203103041c5801814030885e03c0c00a030941d065a400aa030037517800d146241d08100a11103c2c0020004860130815186441d22042c5103140504001c0e050100a00001c0c2c6440d010b0040215603660190403061092080d1501d26040d280007a802e0f0702070003200485411009000c0d918280c1030800200401c1120b00101640c5032150581c1b5895406004001c00a420300c030040001d2400350221208041c0ca460910040380200305514421511503541540c8500201b00d80b605080e0561b030b41902e540e804c07203089050380d400c00d00c5940790201080d0304480c03a1034054031800c40300c0425a0b101d4109203210000b0f0044099444426180541080500750149503641c50300030003c180120480c01c040300000b9907511200c3c00d641100340b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 86589542 1250 86588292 86588297
    0x18050913050f0a0201120209010c02060409020d061208160305040f0b0409110403080301090b0a03020907080403030506040522020d0606060f0207090203010f030b0901090203030a1d09040302210f0a 86
    0xc603036000c000081c04010100c1500ea0001c100460450300001c1440302911819507a0a900180c244166441104040101600500002c0d038882c1c1c2c6800e110700950041c0000c030308030b03403510401280d0f2601c000c0c411020070380c200a1403420000e26100710b0484503130441e4201c0078000c04010004108035a26080001046003409240e01e4524213400c500c1a40d00c3d040c02035620701800c010a03c0094200b10640381555801c400004641c038604000c1040c000c2c1981001c0c0d8810a05400c2009140c0e0203a8075522540c0320755810302c1240c41300301c24482a14019109c0140e800e0301011704100c00718801300c41029040c0000c1c00343c40598075584449049030420b801201c0080d4201946400894041080b400105244c443c214907540c503040c44004c003172030540001000d001c101403718a02d10425004034280c960010305a0b89c1c3c506090300042c0c0103425540d10b4120410356000b5800381c514060110a00c80e540580182001414014403010510b10030b1082c205400403d012003440c1c1044007024003141001e54 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 86590792 1250 86589542 86589571
    0x90515150a022503030f0c060207060b031501030506070e0112050f010302090f0906011203120e0309010306080a05070e060a030f0b0601140a0212090d0b0a0617060115180509 76
    0x104000f410f10780480001e14028118000101800451541e00c8080702d40616100104c1203910f40210380c4a40c20b190003516260004c100103050041035800314402c40e1007203045901c10700c1b44142028000000f4403021303000707070069400148c006005a603241c200c0e400c14035000b409410651510300489000307031000000881c80000500450602c0702c01d294100c43c540110b41414035011110301c0c1d48820501803c0d0900d849500010101801480000e0b8070030300c0580244850007040040540c0c0e50024050540081e0600d8800110752101254245660b60810040c1c0760b00c81c1072403e002500341d005001306070091810817000001c1050302c0d4040030307000d20500c60381100d802d00000048c46030f00e1000c50007074580410131036102415000100c4051521004407150b88900300040000e203000e00c04070002d8441c100d440200403160f0020340c010300503140c0c1d005200002d40703a0082103d540349401d00807190440f542176028088640111140e122003408a9558502251030300081190b40006445118828052 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 86592042 1250 86590792 86590807
    0xb090a0501032603040f020a05030d0e0103060603180b15061801030b103c02060a06080109030c081303081803060601110c0409081201030c140306060a09051515 70
    0x2584100407400203109103580e07540f40f0104101424400907200400445014810300210748a40646038003c210084c140c8000b0880003c1c042d05520900411b00d0010b45000750200e442d9010381b00f07440c82c1c905020444102003a580c2d0b502c010b00342c00680001c880d418880280e440696488004003040c600c460345034805661540001350941d40c40d0704080e44901d03441ca815014882d403103000320032041841b504000d81c050403000d44914601040c20352409401075a0300c800c410b5500050264011341000b0420001ea40d604d404407400ca60341e200000780014103944100000c203507035030301034841e01341192105201143e5a541e1740d0400d9103d0610740200c000e603024072681600e0180040780e4066000c0c2410320b101240500e10640707455144000612941d0394030f55005c144041c0e001a500d016046654007461544c60741400e1030561264481c0f43c01c00d5440641850041c14042080c60041001400c40001c007400c0204800190100800001004100e145520360542e03884120118440350765803c2c0b591402e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 86593292 1250 86592042 86592053
    0x80d0f0906230a030f02041706160206180114011203030b040b210304051c12020f1902040212250206010803070b090f030409020a0806121509010b090a050103 69
    0xc0d50104042c00039107071a61400062503081e26805030540c059039692925082820f078001e00c2001c0d5403089151011802043c40c14440c0c02100c144400d09080f03403403d03038036811548940036280e100e80c40107820210100e1800b0002d50395001c0030a00d0000042100351845230160880174090b405901c1d441103401e8071205040e058407a1000a081c19501171241e03181d80d40124078448804020840741c42c0072041600d40c044000e00a070b8001e048010f00710070000300240712111038806010700558011400441d0b480002d4000280340908441001c082c007044211202c8042c001041e07204103a03007040e000c11000148108403000f0610030507895030512408000000c05e411020307000182c80c403d55100c1001030080794000019281c841e6401305032008942c4da258006402c0440940700e80c2d141344800314000c01d0918554020303000c0480c0035501c40d4059a601c2003042141d180301100000541c02965841251050110400782e01603142c4001180720700100021844507241102d003881c440c1d07601c01c018002c020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 86594542 1250 86593292 86593307
    0x908010e0303071209050601030b0c0f041203020d050406080f0a0912080106020c01020a02090a050a090507030311011a01200c03031b120703050f0702011709030706270602090a080d0f 80
    0x10b00c901c4c00b041964500d507141a560003060002034000c1c200800000e800886903c204c8a01c100441011a2100d689070b2581e80098900e460031405030050b50701d203900c402c3c0700d0400d80c0c0440780075559409060310b4140180300c6602003d05600c10094841a0b10808101c8120050000030b005079500b1400f5031410000904000d1541c2c00e9034115007003010300e000541d68156003a0380020016400041a40312402d9a000820000364000c0050207a0400041816008800386c1e9080810200130b0250040841072203a1a074000803101d40072905030302c0b030320400242d00840e1560a10803881191041c01c108400079103160060b908900240900c1d03420440307400740a0042007291206490040c5c14141c3c2550040d0030b6002c1c03c00902030054001c203011056a01c20000e1481e40c003504009030405003041100c9030703280c0c0d20020055031643d007001608041d154003984540c8041580001a02880c007903a621800654080001e131a402040280c001c54402d4041c044001e8140554503584441f0783d01c000c002e0202e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 86595792 1250 86594542 86594567
    0x90a0209090601060212030a02040f2c040807030503070c0204061202180106051b15130209070c110112110a0206010f0b0403080a0e010309140303010f080102160b0402010908010e030307 81
    0xb608400c0c0100304040d0006490710300c290592500a03102d079a40c2901c2ea00a00903079105020140004030001414054800480c0001c0620121076400300c01d11036001a00c1c5806a4000300501c0081004801292182e000303035801c80c1291512040c090415000075003600c12540011504904402c445e00131460002820310180194070349007100c540c50100060010b00840105c842c10b050329204e804120a000c1c4015110005208500e099070308052402e260300c0c0ca0030f5102213004070150b0340803503000b60180e4684805182d002c17100e407960a85034001107420704a14071802520b1a02c42c1490106420503001900e514501c0e13900801c41503142c4040d03101d129846602403200c030f000c104424402300c2c511504a90b8404000d003844c0c114a10307a003004900070440c4000c050f041c19200b40d0f10403880311011000798102d8024504450741c0c1d41c0c9452045080340724100300340c40101480040040010344e050281940240141040f100030750341d401080b070a503000b007010300000d0b800002c03c1041160b01b002c06603164 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86597042 1250 86595792 86595811
    0x501020c010f090b010510050c151518060103020f0903030412030206100b0a1d090406090c060e0108010510050f0c0709060605030f07030e0c1003061d0402030a06091a090a0209 77
    0x8840c890301c40684001303060003094041c0f000315080301c000900071000c9030321160840c01100c0ba040340c40b00d40811510b4081e2650480c20001c003c42101e41c0c50301d1110a040d411401c101c410301034a580300158000d6100d50540500400700303010a80341a9010720180c0300403c1411030030300100c0c09a1034002d080900060010b4402c0728002da0a01844582105035904110719080820350318950b84403000c1c40003018040390b5807100406040104114079034202080c0da601c0341e00403546880d2a048140c0300640c26404c0940000c8c1041d004120a00d0b1107a50300c1c0555005041052a00b0001240704034284d2010075641c07055840140f0030064100c45228100041c02c1c0392801d5419130900c41140451450054024010503495040e90310910302c00b0322a55106040003402140d214400110140140c41c0720700c101035101043d0500e0000c1d03a40882081842140d008000d02715851940d40c94400a11010000f07840304020381e44114404008050600e010345064401403404401c188100824020000c2c0034100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 86598292 1250 86597042 86597051
    0x70f050409030914210c010816020a06021c090804030c0803090112021e13080c09090309010c06140406050103051041040303020c060901020403021c110a030501020c010f 74
    0xc60b610258020540342c0c0c4e0282400d4490300700c80012030503042040660071a141c01070581402860000305040e5600302030300c4040496039028000448428001142ca02503040034606000254040d030050030748802c00071404c0c0c40c4404441d19002294101d00003100e09450014040c0305000580b55030000914807a0004c3d4a00988000000c003d9605c01140c0102d01d41c012492a91082500100c06911442d48bd89140c440102c940f40b02c42e400000d1140ca4054021907502e50070383c1c241000040e20800400340107500e041c01b01c200441e0015050704090b292269100c29080240704a500c02c1e038006c82c040c1002049075419420400d040014076900c249406180110321446420007200f40c1022030000e0308403180700c010070003000702c90194008403040800b082008010825801d580544494000c4404032200750b502c044c6014201e103c3c900001c1d50200c0303030219070200100d01c02444d90740d1b140324100c161048030780c41011030440051f50b0400c4485940102e0b280f51203e10074841c19408119207030f010712 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 86599542 1250 86598292 86598311
    0x90a0507090509070b030c0904050c1903062d0b070303090204050702150105100903020409080c0f191104060801021209010b0f130207060902030d02060103020a0f03031706030f010e070f0504 83
    0x35a00d184505c0f44402c021004000203006028440a80300c1900c005401889589000b032102d0400380d02004144003a450100d0021410b14400d01c0383d24295034003065040030010700180c1c0c000d920048125030746a0103002d084007140000444e000380032010310944021407100c1a601c1088107940009201d20115440000c2d070900c00c1c00c821040a0441e03000380d03480d264001e0a0b20080311a00c1141e000a0740060420f03420100b0050b400c001043c04805483c142d420401038100d02d980c444420030804d415412120900030086030a03002902c40001000340f0000303c5603507507900a426600544002d010a02a850400407510400e001e40380c101c100840741480f4580205001034402d10102640080301c940c04074401e0f0411841e64803009260350000d044031862509450020758500e001d01040f40283c61001c0e0020b0381c5c03254400e85c0401d132541510b650200c0030000c6640402040300410b42d99141c8600500d104041000707200b420b82d8520090301500110b4100b840d840109180d50348040d00492070f00c050346 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 86600792 1250 86599542 86599561
    0x1020114060906011d030d08060f01080601020307060b0f090412030608030309070e0c090603090304090f18030807170109021201050f0a0b1b01020d02180d121b0b090a05070905 77
    0x100d50050003401c0140e040c000c5c0d0140e10f00140b820100f426010b108000c041040720b5082042c0c1c85c460102150403840d841c0c1e80a004540c144016903889004d41d20601100c00014a542c00034566444064080c012103004007001a0610905230b60a0310402c10031854081c034164103000d81c1000d0000e09006610b9410040052540d0704202d02c16400c01040c8000801c281918100480314100001401d01d91a4140302c20760316100e50081c4075201105152132460b1541c1881402180705681450a44e0000b03510192820703a0404402443d42080040e0303840c0f1036604c6035509081c14060a03029000584a2109100c004224071068201c2485424106025030326607503840d4081054402901e00e894841026523000410a140f0700c2c0d202032154000b01d81c101c030034400b47d8050b040c080303400c80788080400041e4003400408402d8440c05040300d424401407004c1d0300e001d5a988082d012031101003803c11411a21514180c4505494069194000010346828010104400400b81003051000c22580c00e100030003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 86602042 1250 86600792 86600809
    0xb10080604020a050904020414101815200d0201140405120f16060b04060b070b06090601110105090a0b07020d2102091306030606090212010b13051206060102011406 72
    0xd051066030009500528070b84290b05031016604090030554440d6126902c14146464090b08070b03000303403640941c010980b841244102c0314400c100d10f8103000c981c141080082140c0811203141c051107001d2a00b5840c080c040360b100d10301d0700c0101e405400c408081000003420346a050154103c40080c0c042404042003021a00701085c040c1850306940e84c081c030042d4500b8074040d00b907680304400c0410411500b400320541006400303038070864040100035246e01c0414054000c10101038031400b5140300161007801d154034090303080030050510072440c5403500c80d0103007500e0045456142642024003881c0400c20004102504902640007610080034020b00c0101410705854401e04503849101d0315811040320390b030440c1c100940c041c00320f210a402030744910001d801c152204032226490188006041c607803610035101d0030031501c0d076005000e07460490404002e41200c0554030b40310b01c020038005000d986000b2182e06d20031148016200b14a000000a4219080008000c11510390303007013040360b1680d95901 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 86603292 1250 86602042 86602051
    0x601081b0f01030b030a030305010617041e021302070503040f150f0c0215041401230403060504020f0319031e09060f200a0615060801030b2503050a0b1008 68
    0x18070305800401400120042c1000c1841150580a414030003c141903042c0c11880c140c51068036500e0710004d1021401c070a00f0002c0310301402c405140c4020b5016440360803480701010340014005c84034081c40c00c2c4c0fa041260702944044446031700001d010001000140713031490061007004141400b0250840d13014207404441c0b000c0c0010803140300321400840d44e846d0306d1003446459003000561110385a82500e014607040340907190200d43e45031078040d03850141c055400f401ea00c6043e010f82c10146155290000386c24082e10481e40f040304109046440d4408200b03180c40100c0118800c00c85031054100507058072069030b85440d0041c0c1d21031400702c0c030503045044102110458580025034021640c021907003100c0140e0710081800090f4918500f2410000740d801c811402420100300c0602c8151811001840c18452007000c2f030b001d1300040000c41d51500003c0c0d403081000100d10604020614113020600159a240e00426519001e1200005c03191180c0c44041d0016a50b60038640d01e42c80014010500050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 86604542 1250 86603292 86603299
    0x219050f090a11130503010e0c012c06070503070201120506030307151e0c1407050d0c050312070504030c09090f020f1309081207051813110a0804050601081b 69
    0x1004150b850340d49030310880c201d030064050107449080180102c1341e00c1445115442c80307036007080740040310b41c0320206180704150016102c3d224041c0070000c8000754445c54a5512014202d0804122015181d52004000003481240959966000c03031001408180d1070301c40b5100101e15041c1040342c507071000403c581d0520f802010340d41c2d40440000d9a00c0c05081c203281c03140800755920089100b0394400e6084800e809140741c80e01c54000d450080400c5036401244400b602c1c82d400303202400b4015000d030503501e03003080c01135040c0c81ca0800c05a0002c08040020f84c0c4000003d040003030200b040c0000300c0f44500107002c42030018440300129440f880300894140d00085d104410f540c01540c100c0da1a9072040c0c04003141d501302071002204600f020746043e0800c070881e4000c0002d40c03002030016807007801102c154021840c501801e00491300144080d0f200e01b0ba546100341c036034500c010b0031740d102500080d0903140c0707041d510b004042ca000e1410b030b4101481a40001129800060301c0301249121001039410340b0401e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 86605792 1250 86604542 86604559
    0xf0a08030c0906070b01060801080a020a050f0a0f0b040e06010507030503042a060519030506030a11060f0d0203040221100f060f03050f06011401050a030c0207150207030219050f 78
    0x20060404a20520b85400e03800400050004200440c01030403604907000c60702d40d0039007aa60ba84600e5241d00708400700035030004198509002ca890607801205421401501802000340c03540c480c41852001c039003000140100100b010400180700005107607100c0e00c28030382136081090b5580d001d0040d02020344020f00d110f1500c2050750b80040000c0600a030800c008500e28002c640d180405045a80501c3c92050022640d034240d4040c1d034064040d2a00504000d0300401d14645151550b400620200607081e5100c00e04000b8100e02c0d04001c00030384691000d05000594a003420b20400c02c403c80c2d100e40048a44070709a000540c41003021402144864200c1e0000c11a000c18648240040c81c540e0054008945c0e400400f00034048002202645010324074200c1c0c0469032900c0d83c40e400b9212000e030782400034100304080400c0078803030340080342c808080b4012240829100c942c803100c0150f5030310460300103910018003001549000720880082d056107035034020100b03050a001c5850349560200d1a4000c0c2000b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 86607042 1250 86605792 86605801
    0xb210907050a090b0f04230c0304051908120a0c021006080c04090c0b0705010c081e130503070b01030b09010f150302041503150209040b030319030c021204090f06080f0a0803 76
    0x340c007028a54200d005000b00111105404d402c0710b80b2601c07d0014445000d0800040c0000340d000084034045d0303800400601e22503203a10104100c0c2e4001c0070b03044407140b0046c4018454280d440c02160b010360303501c540100e00701e840044000e2178180c44c0c01c6820030090034004100201140841c16007040c03681660081014841400d01060540280c0c0c8104c2003504001111028088190b2100c007101d0003654486005803280074034100d211025400460b400030344000071440628481d000915110301c20000e90b41487c50a803104041e0035003d901c00d85105000400304095410b080c4120010000c1c210410030007050412180c414498603400024083d6940c0c001e02c0000b4000181a80c0082d9805a40c84a89082c1c40d00c00b18007a410903003480303005070700380009205649408000e8030000110380c2c41200c829014520f00304e0203008400700c1981940a00148080704415072030040015010002c4007042c0700c0480640384044400c503a200300c60f00d0b0040e003448940a0300204080c1481e907040191642c5a80720b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 86608292 1250 86607042 86607049
    0x10c0f021e0310150b1305100e060327010207110603130b0702010209010f09030503030f061309060b0a0501030504030f0503040c051e040606050301050114130b210907050a090b 77
    0x92000c8250307410f216654084200ba0030030f41080c10345144094031480540d6650400900c24045c281c1d140c0701400c1810018400d50030140018240c01c101c0e031506801c070305e00d0340700801c44651098134203881084012103500340070389188041907154250781008504e40903141e01d8980003540c0b1041680c0c4130310780000102d051148181c1803042c0765500264182881d0618400c064001c2d4000303c24240814000300f41c40364228040c1000404507a000405145142c0c1d40240549042030010040ca602c00d11f44416010205100d21440c55240c0c4100e0303002031038050100410038200b0b015401181010304003010040040c0d8445410300498819091503030f101c0c0c9661600410361180d03600084d401046044040000c40000c01d03105150400980f0308000564031400112110703c024005da0b4040f4000d042400d02c001181c80050082912000305d200a0b0307929000300c1e00c4140d010350300924084030030000310750f802c1c0b05000701c25070040c071a5230042c002c1529201c003064041c2080d1007070081103959a485880e8648 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 86609542 1250 86608292 86608339
    0x8040c050a0b0a0311130806040b060d11010c060f0e1e0703120c03022107140d050a0f0c06050f0603060c041d0604150303030203090c0102030c07030215041208090f010c0f02 76
    0x800ca5886d07070811907210b0520551300c850444042c0e404c01d01c500c01080031400e0400d0f21210700340e0404a403014001510b070040d01c0313a4400d003000703c1c0c48a949500400c102c2402d40f095134615002640548038400b84030b8203c04054048590660650700090f004100042020080c18030480c4c50782420304540207a130138141d0034106a80740c454101452a2460010036a4000081c03404a03c90308098007a008403042941d0b855030f10300c40f0324000c94401c001d4100300c5406102140c01c104262b10f003401081d109981e410381a1001562040744090b40c2c4070501505217000e10801d94001d11030f0030110b0a1600e0146a4881524499440d00164000368042000703a01c441d001021145155460340380180e9132407400a000703500483d1480c13014002d4542001d015880482200c00c24901d1600a00700c05080d9001c1280810f9000c002d000120402c10001852a05004850402c14015001e80e40c58600d0070040c1301030111491030b05410412118010f02c0003611040035181842d405070358000105a100207042d4656 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 86610792 1250 86609542 86609557
    0x702100507050f0606150a08191d010510050907050a1407080c0a150e03031924060f05040e041203060816051c0201140a0e06070308040c050a0b0a0311 66
    0x9024800103084000c0380001e032a8050300f0b059504841d21280c40c840c0d8400e50080ca07c2810000e070802021800030000c0001c000c08180c3e140000040003580d8207000d10031390107903581203241c80e5181d800300702d840040300f410035009000583d032000b00751804d140001c280e84514040710041c0542101481d02840904043d52445584000340359600d418480c0440c0d03485070300c82c1e011a50001c004c2c4100e41b0542070381c040c000d141c00261000310b0035070701c8020020307441103540401100e00955a410550314a08100110340031100c0203001c1c0c81031030b42090001050354407801c0c0048140042000104480e80e0011612a4000d030400e0031044040c8134110100e003d0010b6900600142c41448152261301c0300c004c11030011114200e880b007942c14005021051031107902e00000c0c4c00f045400c00003004050f40c1900134090614189801c201a0b5042800a0907540041400b07030001140c0c40b040104001d071241c80d8601070b100861301005d0162038a49001d4007403044a90130b504044d110b81150001e03d0061007580d070360 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 86612042 1250 86610792 86610803
    0xb03070309200f1f050711090c0d0606031808090112050109020c070905040506040f06140a020c0d09230f0405010806090d03050c250515010602010b010e060702100507 73
    0x30280d25081c8030100c101c45180a92080f001403800306500c1c078240340c0740c1d4050302c03035508040d6107215045029503003030300b00d03c40a4071100c0e000c0d2041c2503141e07506602c0a100f8043c0c00c0000351901409085d08044603000c1c9c01c95000c1c103252160b260a81c42c4910212070345a580700c400b41d5034816204004a0308100401a032071141350902002080000d0350f5005402d40030745040454002d9a5241c694000340c90307003500e000c3c0c035940081022401103400e00040c0d000050107a640481c04c0e402690542412403800c5821101e200d40c00b06814117410303001d00442c50b04078010300e80018010700749180103401d41134020404008500c01c2072991030b182c0b01d01c0d4500240c01c074000c2c000c100c15a9a40c51060b1616421921640d5134014175804003e114001d206103030103001d80312182820610400c0b94114900c0074156400414440305440781c0000320100b1240c7c0010f024104080400d5150100c06401c2d00d10ba140e0a50600954030030341e08041c0c9881d0252102541c041740c402a40a1079407506545504c40c0c40e102600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 86613292 1250 86612042 86612063
    0xc02060112060f06090f0f060302060703030e030f070b062e08090118060c0201110406080c0306040b031b01110a0515061c03020a1109011202040504050102090a0e060f060a0203040b03070309 83
    0x10b4178800c9622802c134142040c101802a20307040c000b54001c58a040c0802540220188540c1c000304c0e101e540458200c580080c01c0300d01d050120f03410705290341c004007801c0f03800c000e0010800020382017440040a2180e00c0030f0000003c9201c00c0644c214028031a059181006071040004403480801d420501d48000ea01e010002d10304a14107150700601840d0408502640c00c102e01c100902d81c3d03000031a002c0329880e90350425162030305006030700c03183d1015112aa00980341c9070441c0450350140652212881559008441151000300240488412520342d000700d80100c009d02012030f030702081c0c284140982c5680d101c5c260780d0361000a510003c110710701059916101510710704160300002c0e405841400b410b2803e146141003030030400080002d001c1c13280401d00e030b5103c59005003840e401003604140f18800250410a00a0120300c040f5880e5001d52135001440017070006609000c254000d42c02002c1d161740703142c84075802010f50349100358814040b00c1d810020018902da4405c0d403040351104e9100102c01e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 86614542 1250 86613292 86613299
    0x909230a23010504061502120c0709021204020909070605070602090d0c08070e0a05040309030605090106030206031504050604050c07030f05070501020d0b01030b190b0a0509030601090e060a0c02060112060f06 91
    0x2101c440090007054043ca191079004607000002100714011144c195004010360203c03807007605116081423440798420310800030040f07140b29441c0090712001869090300383c00d51425004000c60a030707000d000411180c02c052814003d080d8481c089806641d0081030140e51000c885000c546101400c0350040d10080000c030740482d07100030114900d01124070821f007281d1286c50781840d0b03104485003600d0050219041480400006509400865000384101c00024101c1d580381c000c03464690007106c030303204840c1c4403001d1650189401e104890304004242c60400c000c0c54141100304082c40b803140043c3c01c2c000549a111245480362045a85165000e00250b49403850b0780100e0b0f02400f11f51001a01090920350b54018504120202e540451b0100c41d02c1d02816103049200c0405910020001342080000c200445064404000c424001c100542e000a0000f0500070554242100500a0a000d07418401001d010795030001d1494191040c66481c5c58210445181c0240180120b02608080c03c1c107004001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 86615792 1250 86614542 86614601
    0x405060415080711152203020d110a0b0c07080c0a03030204150e0117060102030c070e0f070c0b0412030e010e1507020307031b0602090d0c060909230a 66
    0x101001c071141d807251429034440c92000e89440103011070b04025035104003c401d40b0642000ca803980c01540508100451481c0d1024a00c10046502e074140e0250b8801034031141100e9002d0030340c021051804010384900030b803982d41c0ba040c400000d06030010714800446e418051102801c120358a4450f16012901040c24034600075029400921400d81c0340141e0441081080d409000500c01882050b5256030000b560380703524030320005015062604511090100d5101d5460801c42e0324003030329051385240307500e10b442d100c00c1400c008021700b10800c0214200768070000401402c0007d412540c4550100511806418210003d02213801444029070900c4200c0020040104049078520b040c4201e200f103581c4d03081f00590fa24810b1500090002c4e4031006110200d42c1e621413241d01d8944564409850300203400000b0f0b103201a01e00c03041d501100200010801190030401a5000382010b41d006d11001c140d44c4e1a4156003021100b60030780140740c1500048070700b5010b1780059103103112900d0094a117403401d0301c1c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 86617042 1250 86615792 86615819
    0x2070b130e0a090501050105041a0909070f09051006030902060f09040f06030b150306070207060e030a050a08040e011208041215060902120618060111160b09031005060307050d0804050604 82
    0x191255446d1a002140e5414240210705c0311000002c8140c26028505003071200200c801440c40805025418011a0802e0700c0f86d0000f001f403504003004900360410140c8003201c00440e0340309809051a00244d1001610b41e0801d6a50387c0b000c0c4000f150b200c41c484000328000d03084070440d41f02c00501c1c1c9000401040341ea8031040f0b001e420b1b0049280c501140f004141540d404050350000701503400440104000c61282c80f0110717500101070240c420807803a80d603d1743c1c034012010504445a41780400c080c041500c2c4284104e0041080f50441d142c1d6003202c0d03c41c0c044501c41d90064605040b00e80120100313000c0000142086003540e040108106075640364524001c0d006040381007684484440414000c6c5012007490f00d080200002d09103247d1603100040d41c8565003456041103900601e860500d45c80c1c0212550b03030050012283d141d40e074000440826040c800c050840303814052614040c401c4035140095a60280c8009441100310384490b0700700710699000f950b0000368898000a001701e00c4c000643c070b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 86618292 1250 86617042 86617061
    0x70305071406071209050102070203030f09090c0703080a05070c02030a08090f06040302060a2706090e16020601090c050f03100501091a0a03020f040302030109050a050f03040602070b130e0a 83
    0x20000e101885160065032903000a881440004d1030098500d04010302c1540030b18010f0303210b1400140b811005030701090842e00318408658549001107031905290415001050b44411030500c401c2c036140c4144e801404201c4050581120306548000080107039020b00c80103203260790000c044840307400310b41c82c245045500ac0e402a42c0141003550001001e0300300b03041948c0507230b580288140e09001c80d149086450240381c42451400d4404951100000d801c41003801010740066620910101c0c109001580c000030003900b00b040950341c09400c50902c5d5030210f482c3d41960201d02010a944001030000ca0b114010109540318010002051024100803125444202c400c2a00d452000307e82d54030318046082584000d11801d40c1c0c0070020300345007611039801400200d41e04103959003450b8403500440c6c01c5520400303089400f9030041d140c2c5400d01104102c2801840d40c120021450241840301c02505c0340344ac1e2003174100041c404169044c424021001840c05440d003171000902a14184414001030034951740c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 86619542 1250 86618292 86618303
    0xf07200a03030e1b0d0c0b070503270102030d050702030c010e060115020a020603070f090306020a05071a01050a03110303040902032502030a0509091003021018050d0f080304150207030507 82
    0x10303105075034400215035207501c0c010020040c0450004d28090188061140c04125401403481d0804640503140700060040b850140004640300c0a5002e1048200086031900f18510b4800205e41ea00d16a80082261582c014902022800741c07580700b4160700c0c502400000702565400c1c228800c3c1c0880e0000340c0b49040384c0c80201004000740b41444103903280c101c00c403000713900b103602080055601030040e44070b80154412450b1a480150307890f00e03844100c5e08030502c980006100058140c0c1444024018016241d8211043c0c05003549460300050242c01d0030302c8001c08448004442500700e590034001d8600a0000010555692908140030f1a54400300410900c1d042071003240b4a00e11440002a00c1d4160116220706103001d41c20800c001c501c010080003584034040c03000f008401601c80c141c60310000c1030141c6802110448840c2500a06a2550010b5005507221200340b0080740418030303060000e070740044e0520350320344403420718844c80c4602c0040850740314000203401c001c0541c41030040c0403031400350 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 86620792 1250 86619542 86619551
    0x3160e04050702010c02070b090a0308180a030b0708240d15090c030209090a050d0305040203010f110d0e03071101030c05071b0e010801140403050d09050115030501060611060f07200a0303 82
    0x30fa230140a0303405003c00c2c1c00e0700107100340000d000060110b002003140d80145501e4410120841000510480c081d405c00c84011890806014400f9044102c00c0c2d0001c0316582041030320300c440340300c81c01c1c2550310200451003855600a4030050041807483c0324650f440304402400f1502490624100410b09440104d000365800300010700e403e80003045c00d041c010b500c00094049050b04407000c8000c1d000182c02682d0555960000c03160104062042107440c440110050b0b854010000c0600d048600745015480d03907820400c8100000744c042000e801000b0000d0070001500e059040c821105809030460007070400007044807040c04006030381240b0b000c0b204a000030300b80301ea803a45205800d9900c00b00c1843d02100952004c140002c0c0200094134140d905000000780c00c00c080d40b00d8030300f0b40e08152100c80c5242c2d100c08081c014040d00380114030141056051070103800000d446842da8414004101c420700001d45d2000c607843c24813541008450998400d500101d00c0060cc2003191210503a240850109280 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 86622042 1250 86620792 86620799
    0xa151401080f04030c0f02060903061008010b01020703020306013803061306050f01120e1204090f0209010801120c03120f09080d0c0b04050c03010203090708010513020603160e04050702010c0207 85
    0x103402d401e5109a503d560788140070380d40d507a103014001c11100740803640814103100408541d101000200c0c0300d000b01030ae42156013490000401e0841d0780300d020071811504030403014005600c000480030b04403440c3e150601404441040407159030303460000d55403034401c1d064501c0904100307420082c3d0b024210132a0380200c04800103400d40d04030340b00c1d84621900465115000305041d800b85400e4080c43c1200362010845080e514041c1d402d010303001405404102000c1001e001d00442441800800801e072a03085242001044c0081d020301c07014400d4078000000614032804201d50403103008000c45d03004c041c00c0c100300c00300e000c0940700c040852035110014126100008480ea0000360001c101c0f000c90b1507102c861006500d42d40c0480e00001c0040d07402e885042e0031044543c03400d00c0150703c40c40040c0003a010481c2841040740c291200540720361000e82001b031030309025958410849070012169104140300703990100301034900900c12410540d100b490642009040e0380c042d040b6001c243d00642c2070314400d685 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 86623292 1250 86622042 86622061
    0x907030c1d100f0b0a0e0901060f020c0901030816060207080f030103031d01120e03190f020d030606050405040b030c090703020c070e090607050a140301031203050a02210a15140108 79
    0x22948560f4030080c028240801415a481c40201003640ca07070701d45505001d440038045030b00d14800ba403042001441400c0c0600e601907051008002e046030071a000800344d40746854055041c0034401840d420400c418040d10100400c0b43d0495003225849a04030362035608080341540c0542003484103802050b000484402c12071013010181812401c16111300780c0142401140030014032002c100d5200c5480204a04a80c0c0c41d198500708092406503503a5922100801e04001d04100d840800c6806040c1081c0e014000715400c00180e9040d1030b42520001806e40080000910b03140c02884145e400108100a010105515400400e408000b00088800d010380c1c0e20318030106c138002252105070580205001c548a40c2c49a00180b110f0740b454030b030460603804941c03128003684d80203034000c45079291b50140300c10066405019040d40003d0044085082c800551040100c41c491582da10b0030200346000000c61004241d4005503c0310308100312820400c0d11b0301e9459800e12948188580490115030009513400d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 86624542 1250 86623292 86623321
    0xc0503060108011e0b031009060305010902040b030303071b1703090604120c050a0206030a11041e06030905030d090305040b040609051206012303030f030403080a0b060a0c0b0907030c1d 81
    0x3d844e18040034406280040c804041e40001e050454010904c0f90001180900c81c080c0c0400356000700700009a15445204010171240707804c00840c007a0b0400e008004942d60003d0100081611500000403150420b29003c0c50018182141c04a0700001000340008840d002507400d11862103200d02100b0391070904400c1e03506030304190b402400c0f075102501c18401420040b000e5600080c1c12180890010790410a105040d00315800000d0200880054803103101e0f1101c1b00e010080071141800c000c52030783c4e91a1030780c80f445860903c0c030005486101c40f030304252040e000c850041c89014000e9807910384885c0000d020700c0307c46c460140b15400c0310403200320f083c03c08100b0710b0480d0400b184881e0f00115003140054000c242c0d00c03105606020a00c81a500d5400c001c0003144071394480c0e80e8a04851406030340c407400f01c3e5a6110f2503409403100340220250b10340c0058a1041c003941043e0703100c40740da1f10140e0052401b0300580008201884a41c00016200c40b0000c2e00c40e0344105076010f0034182c1d92440340b0145d600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 86625792 1250 86624542 86624579
    0x90c020d030219050c100912080604050103020913030905120307030909110301060c1103060c03010509090601150c0f0f0b100603110a050c030706140a0b010206040209060909100c050306010801 84
    0x1645283c540220010a162006802034850360b0301281400001c0b50824181501d10405000140131003d40c0001215807100084404000030750650300810003201004148044500e00442c911041c10300581c1b00000a00004103880f8440c4101203c568917a048102c0c100e002c141c000c035012410381100d01030442c0301d8030280c40e820f085a01c0d0000481c4c0070410312505903248000c3d415501900d0b18140700191003410440b0720182d89500d03210034040007007401000e1080c281c100384018010070008038503491b50070000c0c1c0361034083c18889041c000030549107882d0041204084003000b0342004003080701184103034215101080001d80c0d0b00c405505580015200c0f180300c0604221a1072070030302440290694900c440201d034103000031943c950080315043c000d0b503083c9030414020400105540e025071009603000384003811041c24203a0214540050142c20039101e40c4100d000610920000c001704003004451340c4003030103440e20540002d401507000741c4050307000901840022418201810785070700c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 86627042 1250 86625792 86625817
    0x3020c060411012a0b07090f0e011a0703020601030b0603031c0507021509060a020d0605060a1106070504060801090c0c0b0c090f150d0b0f10030506030118051002070807020a090c020d0302 82
    0x214a1545d8802c68070300010950001d10030b10183c0032846c021060b00010141c008400d000d600303941088007007910a40b1038061010441c400f0445440025070100310b890440740d016080402940362a80000d080d0b020300c0404005110102e420401c0003800d81e085a07000e545960251441d050042c0010780028500300c83d0b01903594000004548405525402001003851035400000c844d41c4a5000400c664030140c261000201071600d9206005400c0c001290885030701d04085141501e0014042c0c00c5220520409c9022035941a200e15458024241401d0704d0740c1c0b2206240552070705440c0b5800e250442020036014420107076145010341060800c28443d000b904034107030f040913042c0c01c45c400a0248110b01d00d8011416000c41031140e268480108000c400ca03440c08201441e1210030b050842da0450000782c5a008c4c03000365071000c1440800d41360141d6200800141e90352005003400c160754404c01c02c00030b40242075103100082c0c06105610504c00001c0a9080e107019400c0002c084007a401112421000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 86628292 1250 86627042 86627117
    0x3030206010303080402011e2309030c0d060204050a0303120501090513120903020a08010f2007031103070b0f04120c0507230607030201020909090a0f06050703020c06041101 76
    0x1290060f80e880f80c0c8107105141234003144200308140c60104424030740341004502d08505100d0002c0224100c07107101a4804105070410b010540003950346c941000b0303501e0040001a141c00c0078401d20781c04070380240074054a9124025501c0c9402005c1099042e03540f02d21501c0d000020821512600806004601e0f4035892560b515140e100d6400e908000f42c204401d000c180d2400100680302c2086c7d0100038149080005003070012142440e0554031000018410390909243c002c64841e4600191400c03149c040c07500301c80c861a08200c151451103610703406408420f01904011402c0c402c140f889100f140f0031180c4185100018900340c03254044918010b14540140009000c244070000c1c1035641003108120785108079040030045519680a22800d4005075000580402903050090105401c03c2d00040101040700c1661a0b03031889881180005080c2d9444501050290703109405542058042e40c0980c2c0b0a403c1525100901042d900000350102d5031b408000d00e2481c00060104a14080142001c00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 86629542 1250 86628292 86628299
    0x1e030606040e010e060405010506010201140603121c050405010929011802090d060c030b0a06080106051303050d020d030605010302071a0402060c1014060405070e011409060d02041a03010303020601 86
    0x9480c6040c0590302e159a5511202c0f00d03074400300705e500c0c001c5000d5800050030781030400009081d207495403100041c0308002c10910486440010300365403204a5000e0180e03c07160100c134040301d200d40c9840501101801c4c4010f1000344081941311500f600e02c22952481a2781c41442002c004401d944d540c1c001c00a40c2c82c00401c280c0c580c2d0140b245040f0340c0d0000041c940a40500090380c107410500301511000d41d90501c49807000c3c1c044c414a164501e08a407846180f5107080e400034080034050150388204130011600d010151110040c1320003031984103055a0011303105490081d0b03600c44800d50400081c3c1464000141e43d40a0300c03c440d40b4982009510148062040010500d00030141c4101d821000402100c01d9084080c040f02c104840d0100022824124000480800d1342c009800184a49c6ca0102805126a0408401e4030031a10030b08210380700c3c1030600e009800340e00440c11246c0d0000344c002402c00800089034020416140f1445081400301a03014907d00d007408240401009680a10010b2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 86630792 1250 86629542 86629549
    0x70f080f060d1410022b050f070c050a021302030403020c0a080a020607080d0e031b031201030b060d02191a07030e01080c040b0d09030e09041e02120d05091e030606 72
    0x500e800e4481d800c8510b28410480300100300e901c204148401800c9440d040120004c916804c03000840b02a5400e001f11305060040b071b200600068084001e0062402c2103008000060000101050300242a50380381214101c0c260081c1d84211001c4005004a03240020545170801c4400700341c032100e20040181c00b0080d400d20141d50b004040a6811100030b00000e0420b180b14007411003040400d83c05140c4031403644075901560340c55100c0921058006104018000d005c0d1540c0f281166040550054503456040200b0302202c90701c1c0c2c020350007802e41c90004407200f441c1d207200300480b8a500c8002141c41100c548040040c000e156004001a141d4814240070750300c1400000e40108000d51424901390769100381d034100383d2180c0d060060b01c40e100d1500400340764204041658210080c2c1d150b000381d15081da59808602c001d41c03d0964031200066074103040d916103020700d44851404500702c44180000c20809011138100405003440384280c0720382c0c05201219a20500301c42807000c3c00030f0215480301002c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 86632042 1250 86630792 86630813
    0x2070609050112140c040e0708010b0702041805060a02040512060c030a0b01051b1f0e12030c1614060106050a02070e0a0f02030a05060f0d020a0b090102030909070f080f060d 76
    0x401e140c5607140c0d0f03036003590b90704c0f03000b131190081e202d85c500140c0d1145403561040313429030018225020b000890004110b031003500d0f001c94801950413a4001903100c452440d4150246500ba00a0030a210300c1040117140c1c0403544c010003c0d00c204440c4140101c18100d066683d8003401c84585d00b00d00400d00218017004420781107a5007140050400d907040c0443c40c0d07240090010143c0380c0c2403ca41c0880681e044d418130711190841281044070087c400690902d01d40340d61010004a91007031410000b001901c420f900000380c400585100e03c0f4080c0281e09410884070f481105200441d00b4020b40000003031850151080302c8035090742e500613116062800d4000c8100c420020880c190f8a03850740d005020003a81d07480254401d40a90300001010300b44442070040004c1900c81041c060705031115258056951604000106c506118031240e50b6070310140100d003980180a807164000714079905020b10643c00545c60b0b80040047d68070352200756a000c030344090420065440c990040c1503440c1c80030116030903514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 86633292 1250 86632042 86632067
    0x90507050d150911031002030406050a020307050901080901060f0b09090106020c0102190f02180a06050f061204110306090304031209050a0b13030503040609080c04090809011b170306040c020706090501 88
    0x36006201e1301c1011070f0605142a44001a0302d50000800c010410300e8414580c01201e146811170440c90110000340c030602c18034820905100380c200028001010942001015151240207050071a0f0b03111000504c0e42c02c41504540b10304605000403490901c001395990b0000c00c16030091000c2c5000c0e07181040b80504100059404120080351400540c4481d4003038201070f8028048040c540c81d0000368035044428940002e0301c0b40e1880341d000d4025648510507601c103050740103d02c43c42500c0300c0c9049504841c486940d40c0d058002c9030104a20410044080c0c400c42e8003910700038440706200c0314100c40900d010300030603600042500050114a18441c090000028424884910a034030f0707440c2d2a00d96001035000d400010340c013580070710080c0024040001e04410540b03090021001c15074400b410b502803504218100218100305644c3c886080a0001c02d9540104204503641c00c20552070074a5030044034540c0c00b0710300306880c0700c030950710000301d040c125411640c4040c2900e00b00001112900388061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 86634542 1250 86633292 86633303
    0xe0c0f0a09090915380301150f03020102061003020a030b06031e0105010602070e04150c0203070c030308040209090604050a060b030a060513020405090f0d0e0103020c0102030703090507050d1509 85
    0x12008102401584600e11101340a64604054541c10350f0560098501006040700e0b40306201c2d1354452030506805c9110905492500c0e800000074221000c00e0041203d1091400202000240045d0b034100038003040c0f09980c001c4c0c2c01e40d18160380740c50700c05ca41181c05100c002e4028490140420100d080202a0b940000008042d42c407800440c1c004c55000c0c282c8099988002d95441004014450b01080908005c1c004201c5000b0381d480e2603201c001d010311400164005140d200e400040e41c541c4248211180140d00c051840469516030400400c80303202101c08900608070140400d810210000300d080c860b50744072000b007070429426603c03540a04101e01145415111302d00d2208002003041c0074191040708852140c081e030107a580108402e546001d406844103030403e1303036214101ca034003007204201a10f0078141100e01e000100c004030002c2c0308034000145d003544040148035503903515821590000c1d0007407003100c0712a52180204004000000c000034828040c85070b0240c801032441d0000b0746801d000e40e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 86635792 1250 86634542 86634557
    0x51c0f020105121005010f0f0206040f0c0509090601151418060d0f020c010b0909070618030b0112020111030a02031209010e0601030308040c08060c0d0906060801060f050301060e0c0f0a 81
    0x42800c20203c02920312094424100105209950b07201c00110041c40b65803070300e004003a98403440a0348840c0050800f901184004002c5028068209000d40041c000640481618941800e88170744860303080c06294050fa002c1c44d801c840c035900c1003140d00c02c400070281c00980b900c121502901e101e50b44005d0207a400c00030034040c01c0c07500d0f00584504680102c1c048005680c036082c0c00c1074282100c0c17118161f00c1c4245802d5041c44200750000910100b511081d08007035503000d480301d8280b50600c0c0c881e80b00074840d4030002e00104004a4100d046940782d03200b80c880002171462514010303181c1c010564132030010f038014400a25202c00401205810001c07440c00000e0f080700c0e107103200303080070800d800503004200d10310144800c1162a0340c80d000100040000341c40309083c18500803543d44144801e06078000e84030344485003440503a41c130440040000b88000c110b12503032400c6044818500e446001d21a510303010000609040e4102c60502c40c10b03000c84e201d803074240401d1420a607904417402a40800121 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 86637042 1250 86635792 86635807
    0x6080d120e010906020412020316080c09071206140f041b03090c03020405070302030f0c03040308010303050306130e0f0f03090a05100c0f0303020304060e030910030216081c06051c0f020105 83
    0x91780f000b000640490b40d02a94a41c0d00740c018180b41291074440503000c0081e10104019048010a1100c040c1100710b801c81c00d5616110f600301e80300c180c0c0314584c03d042880d0041c0006c4001d8076904c90080300b401074030b5243d09a80c8510400c811680e8840305800d145815444410342c8034072135401030000318450f01d14014003039202e40100e801c440701241c0d01c40119500005108070420500303201039020b065640f9051561419690007081c4580610005040c440c1c080702007101c50340c0f0342c0c0300207108040b04071341000040300304080d007a03840c083c041a0301c45600410103070640420022084a4a2070800362001525928041c01e2101d500641340b0100100004802000700159880e5803001c40a030003580c1c00340c1c4a06040c100f02d0110b50820101400319030080185183d01d0301c80c6111001c032104582401030b118513600786180d180316044a030090580000082d05618170500b18254080b0540e550760402031151240f00348900d680360505584004003219015500183c7c0c2d00d030113194100d206140043c10800c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 86638292 1250 86637042 86637053
    0xc0108060d0611030a05240607020f0409050d1407170a020f1903020721030e0613080a0b01050406080601030602070c12030f0e010302130515040b1c06080d120e0109 72
    0xf030300503808080a800020b0188145641c022650000c400c03040c0003403180c181400c0000d4440d82036242c1800340801081c000e0540d91070f01401130442c68090030500111000340381c015181c3c004d01680601150702c0082d8410030070580d0f42039030f040680c4039070302850311140d116800c078040d08005425021071203403034105c1c0e00b42501407100380d59007002c08448030101c40d01441c010b81805800e80200355150000b0080381e180584029003441000d81505116109a406e10007180a600c280c01809540901c00400007480e1080007606440c0035004c3d070300340d01c81a40c07120b0402050300c0052240940c41d07070004d001400841c58640c02009480d203e0030b041086142c3e5a00c0a04210b201140c0a0b4080380711100c400070129040407820120341e40074641145031407020044944204030500030340c1d000d40707071301080c000b0403030410b00846000d0501e80d5540c98440d803824400140c0d00040d81405422941082c5000824800000701802040d05a8907010491030303100d00c1c024007c010040141d1000e648640b141b001190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 86639542 1250 86638292 86638301
    0xd05010b04021b152e05030f0a020a08030414100512160206070206060a15090305031201030c0b0909070f020a0f1211030408030a18180f0501060c050c0108060d06 71
    0x1c4010001061200348a030444e05040c40400c1e18039510340e801c0d0800000000c2d41d8107407403210040e180800c0300500c4902503030304101c40d16042182c0500c5082003807444442c00003000c0700350310300c02c441c54020b45031188112501d0b40504d21611904401d4441c2c01d9503580b501244e0021604e16038981142001002c4a0740f4418100c1a00c008070b40c27441c080304450940b0b605200c140d600900f1070000307040700c0c00c0c42d40210300074032200e10585027100141890b403184c3c2c511440701100255046021681c0701c0e0210414a10020401c3c1300c1200c0303c800801000681c4100c03007040c0c50300d02d071009001d88241c0da640340c01a50825040766483c81103001c0e00720030b64005440000006100b80c000d0351201042061a0700c0030345002e50401409403e0780c400c4c48204642e5400100300c0307440ca03800349080312041c6581d0070a50942b41098000c203c80918605811010141c5540074509105940c401030040d40d0380c484003a03c80d0700c02e404014040750001c0404c880c065028051080e0041e40c0030b0001404000551585070445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 86640792 1250 86639542 86639557
    0x9010c022704031b0c03030f0309140f07050909060402010503060d0212150a110304061d060405010c080f070c020907020705121c020c0603040b25020607020d090b090d05010b0402 78
    0x15a855000d01c4141680710441c42211181452410204d405686964150095502c0000d081100500c003400010b40300e6040200516400f41c0f20358441c80d0000360058981003002c4500030107200300c0100003454940401c00c5800354612401400c078a44454004680300d610013010075402c44d001d0040d00300181c48460b09080b0f076581c01e401601481065481209003660040c00204000b81409620f202048141040300c1d001607009400003501c401991f02c4604501407005550b0321030294104102c00d010064000c0e041299043d078038440581c0d22448407000711001036a94800082c8481c81c1000181404501d041d0040400c0c0100c1c0c101c80e98a80016000444420706902c860b00520a600c001006c07244501c0c1c400c07000f60000d0f02c5d000c0c1075280403d13000c0c04001c101520700440308012540b6100c040340c4402009807040101d0164110b00309005c0d603078086c19500740f0014880d6052404506110341c2c3c076030040d07500c10f1808516101c5140304000c0e0198524809503242d5507101c480c0c1030196114402403115 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 86642042 1250 86640792 86640859
    0x40f0303030c080a020310170a050a0b0103030909110f220b0702041404030c0f0611040603020406020f01090210030f021605010501030c0e0910050c0c0624030c0609010c02 75
    0x300e40480a000b48043c0003d01072a200a00600510920b440020760040544078140d803070a882c1d032140600c45107082428540a4068002c1446903400e0000404900b41601d0103605c488181c655a003094404613614070904800400062004150702c950303c80040042010211250aa54100788401e06994465501050151500040c0d0300708504050040d52102441141c0ca4240c1c1d1805403405411600e03074000040c04852030100040402550790711118104241ca082c49807250f07200d07000175000351302c24006c00d00988218094182c0350001402482007440d400740000e5480e0340c10140030b0b0064041c4050f4410b080d0b40a0001d00325000000c81d80103c0580200000304640d40745040c507440030b000702e80040140780100810808003540000d41c0d00070460f900385c8005182d548204100c03215020300410b40351035029540511070f11003140c50b11785a0601c0c0e0100c0d10541407000c5020159034400d809041e54000209003c040c0b4558041d00d03200e5441800a04030703801c041790400000584010010800c2017 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 86643292 1250 86642042 86642051
    0xc020708010c020705030c01050f16050c010e1f140d020f13050319021003060306020a080405070501170a0c0201111902070b070b0f07050c07080c100819050c040f030303 74
    0x200c00090240207509507850001d0301c0614100b038007080c1ca0342e1034815081c0c148040020a04000416407040726920b440802044890030b04c1860030903103681e003000704240082c2011840913200c0c0b078110f402074038004107a01c03034280b00003100d202524542e440c5101c0d0b100006007400342058090983c0002c040b46074620112984d01c0b50121815041241140c20040c0a680104d8010750740d28860306000020784e40448010f01e203040100d100310050a110b0700010145030011a24092150b08111440d0060f441441500c14903a03c035401110100104e041d01403014031a41d01040341f40038254405241882c0a2002081a1054049a803416405009001509542407010a004c56414040200508078803442c0390b141c9080d64035044078002010f865104c0e003a801c00c1c041142c0c5030050003151070004580042d030301c05654800d200c03900c030241860034601600508444c03041e944d105294062245488001002c2e41409183e804d40c01402d00901008024200304004070322502030750300000095110b82e80214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 86644542 1250 86643292 86643299
    0xc0a060c0b0703020c03040306090203010603240606050910081b040803070312090c0306050720011e02090d1b05040f0b1306031e02010e04060602030c0d020304061407080d0c0207 78
    0x79801c05000340788108151040c007042d2814030000c011641100d07000070f00070401c07011720300000740100100d5000820680c0074001c0c0c46200c0801d009401200f00307102c04200a010350b50703034094541d03204d800d05859000280007040712100c0d01402c101c41d04500e11503070030360b000c003011000062a80d000d90045050b43e800441c500b0105a40070030100c0103030a02d00d070700b4068040160b4855507210018000101460744940000724254030402241244e44580d54005084043d840000350007090400d01890302c540d03010003600e02080c900c0c003c032100b240c00605110352500641d2600700c038450240d40050200813541000149503038a40c0a86044280d40c58400610105134404001030644c07503a4501c6043c40c01c108081020a58840f050040004c100b1140e02c1c00c10724610040f00c180344203070b56103940035181c4840401d10a50001c060004144604110754070720100d040160f036240100d215a1001803a210b5080482c8005c56000e042c8062103502d0a60400078040030000645400d200c1001c0160710401c802c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 86645792 1250 86644542 86644553
    0x30c14090a06080a0b040311061611010519090206040914010e090a020d0b0601051b0601050918060c0a0c0203011b14040e06060c0a02130b01090e0c03040b090c0a060c 73
    0x2150400c00c40d0000b041054a01100103842e8010f1213400b80004889000007805c1c1806454044000e050300400d03203009151003144810704640a000c80e00000c1d80d100c000b90300344c0700148070361405000c0d50b510403009075840f07032032800103030540d58801c9802880078080003845005a014404080c001c100040e40d0300d60418000340b5900000510410701c0d070303121900240258807210042e403400358022a04008540c2c0c0c540c0141d609205240303400702115001c3e4190f15201c0c8010071494181c42084940700c0941c1c403110001410050440c0100f005a00980d0109905030117031030040c0072807042410310310b00c40203141e00068210b40000c80003441c14041d0500440b655540302603040b61002c1c0d9a0b141a003049c0c28031000c03510044009191a02401d400a80c5a2070b0000400c41c14003900e0b8010f00c40214038203014a914094004c140070140401e2200d0008151810914141c5110b42a031302c51440c11660350783c032180c81c91076010701211a24000c0c0c00340c40141c1d0703c82000440150080b9140c4c003c80e10454a001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 86647042 1250 86645792 86645809
    0x301090210030b0f01091d0612030d1b020606060d020a020709090b151219050a020301020c070e1302010e010509040f0c0c0302060a0c020a1b0915090c021f1104030c14 73
    0x614108403464100b403207c2442e0701048095008200e0f883c12483c3c0c0c6910202e41c0d000d046051000091101154210181c4040d810004074040c6d502c110400894001100381ea440806403800d80d40303c8400d0048204489907a1b01501c4003407814030460307d40341d60315041030f01110310703040c800d0319070301c44c004100800c20302034401c2c801e180801070304c401c0811317190641c0054440a998880a0401e024005200705001003000b54400158005008554440b03854040d165164031520070aa4112034000000e1410881038101c489165010384a440c0480c004000440b00ca6001498059000b0b0749d41d042a200030080d44580361500341243c55120040b2090305000c0c3c584131000f06200c1c410b60030305101d003480aa011515680c40d507402130725005411004818558148501c1e00702d081c440e403800c0d1000041100100c124002c42d0b041220800210b6511101283c9407139207030111412540181b000150941d49a602504525011000060030942c899642800c010140d40c040481b259400194155510b0030400c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 86648292 1250 86647042 86647069
    0x507080405060a350a0b0111060703090b070e0d080d2018060c100c0c06050f0f06031c08100306060b03040b010e131106040302031516020309060906090301090210030b 73
    0xd0340c1c03262010000e5139000300d900a100030202911020244410703401401881d008071502c4041e2078440c41c00080017002403901e0715058910f0744501020829482c05101d4078101d044028001300c96044040e11094003a0b0311040240030350940e614180082010038001c3c0803000124015000d5a803c0a440b09402c14407580003454882c400400605030324401c000b9005002061414021402c034982c180d0960f4034400c0c80001a00e82030603e400c22032508440e07241c8520902140a6003c6241c4540042c9591400c082e00154402e2103400030300c814260040b003009a000320382e426198441070302c907914803058070400e0f0700c1040c0d420804414001001047e0300036034050724020040302078034079211103d01c81800039003001030030186030780007a05501d8480d4405c40c0c000d190041d044850028a280c16004000d0046441c07014650041a108a81e14404011120b6a6038010000d5080c401e0075010418241d202048059156688900c0307180141c40701c065400c400141901d000032944992800d00c040e44100b40b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 86649542 1250 86648292 86648357
    0x821010b0f07150b0d0609021e06070605100b040303020c0901090b01080103030c0317130605070504350f0307110316090504050a14030c071a03070507080405060a 71
    0x1080e8024042804103540b03585400640505031407005404107001001152220394014803184040c00a019140e04102c8916200390386039486403040071662420035203408035803036019004001c02004606950807e5822403503244a08000c2a81c0780134040c06a400303644100c02582008926402d1840c000c403c203030041c030722800f092001840300000240300c0c801c1404000e0510104090780400c1c10711440c909200c00780c410351013031007600f00701a4010b103500c0c01d946c0c100d5a0600701000120040d01c90416201150b9241d08400841c09110000c0d500c6d40e20480503035a8080c44041554500200401c03000d201c9081c1440596510341ca10304020350350749401a101d9001c0c0d800403011210401d006280c490480d00300748d40010302e0351100d2501d682040403000020b00a81c000840364442c00001100501103865003000f101c1c6070030b58034085400042500d94003600110801e01c00501c566000b00e00812030580320302c000910b89526180060240c1d00021204c00024001562800031448010780d200100941034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 86650792 1250 86649542 86649547
    0xc030e06100b030c0a0201150e04020f120316021302160201140301030b010b0a050d0c12060807030206220801090c05040606110a02010e0411030112050105010b03090303130f0821010b 80
    0x1044002d0244400f81001482120004107500518401e500081c1d0160200781d0000d0305660b51400708a6030001600d080e403055168065041ca04e00d403030440c200c8ac0b511079002850801c106000e081c0011240210242d801802c498202459001d2740d00c01020321025881c40d02d00c1c5080a070000401c081103022001203140800c00041c80854035942d0700034110b9010506082c0c0d81c10f0403000488260080080c05005507041c0720343c1703102e00d541090010040b0f8500d414100f24066440241540d90552480040d401c04420401d549003920f007a4400b00d10500c501e0f1b00085000e40e80c48080c2e08403039074030724251500c0a2986050029280c00e0244a000305114601480b0411070301407155140c802005009043c008403002d47d0700b803070b2500e42014040c0c10f081030b0015265a51501c250791000c20ba2002101e940d46003030004900c60246100f624000c1310024000c42c115940d2990081e98011200c409640c9910403900080c001101d90000b468950380225074640c60030418240c04035511010781100b501110305 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 86652042 1250 86650792 86650799
    0x90c06190327060c0e10030c0e030a11042301060201050106021605090612072607080f1b060415051810050703200a1415010605040e07030b03010c030e0610 68
    0xe001c03001c82e6800c400c0000b403072500071200b40c07000d002d6501d120381c0040300c1a100080150b0154004d0589107120780b190031020310b20804058a07180e085400074048030114180344502c0c20150310032482e850202501e0400c00400c5045074003030400c00d910000060f0f441d2300041c4045641400711802000e0b526400b600304505060001e1075400009100a0140403da40e21402d5403108000c554020804050030b5002c411b800d8410340f007481030702c00090782103101d15800001d496400064200400c401d01000c0d0403c0f01201d1451980080c405204642c800c0c0188404950306001301300c906c1c00c10425031245a55508503200d85941428401d001501c6500e68001140c1010b41000455094990615003900c61000c51007404c0e0460b8420303056170240d40700d03080c11031003040034100b92030002d03041c000103c0f070048407100c00700e03900c00d80240668800501e0900c0104241c452051010360000d03114100402d050700b0343d00119007100c2090700204002034440040b00c0320000c051102a400a2092035450021401c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 86653292 1250 86652042 86652101
    0x306060b090f092707030c0f081c030225260313082104051c0c0f05030c1203150105190503100b04080106030c0803030601021005090c061903 62
    0x10b2092180118082c00018840a0b8040c10014402c0449050482c40c08060816143e89010030701049400a44c19080401d040ca40c104140f02100c614400030400310366183c5081080c50707200e503404018542c092201c2c005c2d0b00b01e1864041d003400b0f42903400d48017001c0c03141446502c4401c841000f40703030b9912500503000e00040c1c3c031040300e030b212000c1030440110005070324081400b0320610600d804070034020a43d540c805800034050a000300c0c012400ca0340682e1403103454100103000035200c01d011548501c50180010074800070444902d0242c0190303810000890f080c5070800e540e0081121220300004100034082000c00e4281d50000000c1c81d041d414030685241016800c0c19615040d4144440030000444034410000e090300a405112861612903075500d0645000e485d460001f250f030450b2100010660104c000f040d03d00c1000143e0050217110402403800c03000381006007560f4400e015010301c035885230700c4800c0100301101085103555410000410000c0c229002c013904002200404d4240301c01003c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 86654542 1250 86653292 86653309
    0x6030b010c060b010c0204021803011508060610171305070902070f020603060a0305030f0901090914070f1b030509150a0507110319060212061005071b1703040306060b09 74
    0x690280b0002680c401c03200050b58030b1113095100942c03290001692400b0030b0103000c070801400b802940203000020300e1510391b40115802d0b0180d54030b15401580003502c20f240036001425127140c641030030540e540510501010000d0119080401d40c2d07400d0084001b002002c102c150000e0003006400c6003017030226614940d00c411a410007a1154501101044c0940e0341c19103035000035a807100c00c0f640c1e0303100c001c65001034640000900d940070812042001402e401c0350f0141c14484410304528071002d070384101d400da4050500420b10001c00c41ca6070500c48800c00c1007403c0c00b03115406a19100d45880b148c0d010041c400c1c01c11800400c80580a00c616449240c206080c1d035202c65002d0f0440c6224119100401c0c60400d000c0d280715080e084900d00d09040c002c131a40182148204c03081d0b004866550031090010030000f09036040005541000f01001045905c05900702d03801303074103170410320650b5902c0018541d5040151440c0380e030b8000140c100308102c000d100d6840100413822b521800d00302e01c0000988004c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 86655792 1250 86654542 86654567
    0x9100f0b030a0f0203091006080105070c0303020a091a04080f011503080714060114040c0801151b080301031a13050309100203070b01030c0f050d02030706140d05091606030b01 77
    0x3200301001049101089810101010106a204540328941681d03c203a482000710040d00001e07240c0b0302d01251a240602a851244103e9150f683d80c846050707600b10000e41c050300341c0d1070070800004030203d2a0305400f182d1078856405040c60b0ba03280c41c24012410f00344025100203403240c2e0f2400181c4503000d8070301005039040301d81025100341c64000a0170148040929440d1a040071f010360b130000b003041a00410442c40b064816a0100040203c1d001c003500d00700c2d0280a40d607006600e0102c103008041c400d01c070020034400060503105e1011071503a02d46026800070707003045499105c419800e82c07110b41d46000850f802004608000850300c1107440c0e003501d910800e42c0c00d60040000c40f50626049000f007007154905640020320900c19a500e04003117090614070b01554045484e003d02c00036861038202900451540c004018019461030080300742c0d07400c00c01b1148401ca00500703214224880160b803080301c0c0706440042c0504803800240040180203240d40c0c100c80c041c580b5081c00180c49990150404045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 86657042 1250 86655792 86655809
    0x102130618031b090c0c02011d030c09090109110307150c030504080d020f070602122d070f06060e160e060913020d06050d02031c050f030406090209100f 67
    0x400441c04841ca01040107402c0600403a50619144640c84002e480c26401c441c412a4100400b105901007142e0306031983c03030040d000402c02c00c05102d00c0030809000e41180007004089421011034100400c0c01c4000c1200d00c1801651368046d0305050100c002c001485000f4110050306909081014542c81d00c80001c00b0142000040710b00101014000c5c0c044402404030070003240d80d01000303610000d6541d840c50700f030440c2c9800303105c030000b84140c0002a0f492100300c0c14210a41020010b130302c035107507072244980100480d2004008440d20344075020020000d40d8000c006001007144941401401d49505501c122280b82c400020450445a40b200b120403102c3c2e1072800780c000c6440071000030418010000c595074010b080c030101740d1a104441d07004140400040764140500c1d0f540304204101c41604560113901030f089810800d5440700031141d0b8a1040726242405420240c101c0366403d0b0312b410840f011965156500120340540c40c20200c2668800031154150040381d08103281c2244890491140d1600d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 86658292 1250 86657042 86657057
    0x6080d050c03130e09070605090f060f0706110c0111160311070b0a0f0e0901050a0b0a050d0f020319051510020c03010203090c1201020a05030f1503101b0201021306 72
    0x305644180121181141540112103c1030b440380b840b424044010740d481034052281880003da024000c0e4207a400c400c00003040149103240340d00a201c01c0e03174000c600c3d1140c80d0700104480000200c0c240318010040300150960781d21040310307038202401c558002c4105032440b41c083c828003402c0c1e14400ea200d0030309a4549000102a114580c0f030603c0c180c4560030a491582c0081040a45503511a0004280003640d0383c0b2440c102c081c00d0184140c2d00001c0c0141a00000021024000290300700c00900341d0354004d00c0c0031032400d00e1154045007100c1240c2e5541c03100360b400105002c280305400c0c111859040e0aa4030030000c40c10140c54124910003640c12050050707650000c283d040500a01205d0348800b0058000c3d9a030b49002c06965482d0141c054001e4881c094203129410311070303070502c00d842c070464581d11024035549035034120400501006040f101d04a40c81060100951414448114034500440000c2943d140c071008141449000c0343c002c1c1c04581c070601c8a000d001c508008944100c0f22603051144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 86659542 1250 86658292 86658307
    0x11109040b030313091a01091208030c0c0a0503070b150a0915080f0d0f050c030d02130801090501090302011a09040605090124030c05040614040e07080a0b040c0906080d05 75
    0x307055008136028040c0c1d00054880000795035000d0b40100e500140007032000c2c00e040e580480155a61000750144e542143d05041e07180c0c2c005440000210341000705130012034100a00d05010314580190038204581940000c41c8090401c841d49605503003043e210810800d104c0004004180d21001038071820441a4070b4003000410b1109400e001c0025001d003005440072543c0380c902181c0d50710780324103d85000035840d11008810314070034015200d6005052020318079241581c9a000d011390062464294060280500090450024414405e840e81300fa00003250148a0381070285c216100180c1c04071107071540c1400030406984603d04540d1055100c1c030000b403244c440c0c0300c0c2d1600610960100e00046400342290361504001031200030116882201000c200035210000d000903100140304d00003d5038032100c01c0010514054005481111246080381e804d82d65403624289081c889000650b180000001840f05105008400c0d00242c4905203007404841e1901a10542c1d4480c01c0004c0700800c40b0126a12 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 86660792 1250 86659542 86659549
    0x50907140c0a0602030f0c090603070f03060512060709090b0f041104030f0f050118020619140301090209040506030c0607080310030503070b01050909160b07030207090c0e01090602011109040b 84
    0x40c0c59241d00760301101d0711901c02c1c0c0382c403000079842a40c00e40c110b40640400501e00f10704400c2201c01c3c490000d07048a0550726800816215801d040c0105018941c841002150a444011004c0300240213440100800c1c00c01c030b040036103840c00303540004881c1400c002140c0340075191440400d4180c0d0043e90002200c1c40c2100784640c1d0f5000b00d0304000d121420485241040c40841c0d01102c201034000c00082003504200303408400c10340d8140748025003040c4140020050294685205542c0460f00e0a1040103079881113044a0590b100f41c010b0043c4c1c0b03501083e02109414184151548200240c000784041502000060301d103001c0c0c0c41c001016150000002041880083c8415000b50f52200443e86c80c1c1640385052543e00034240511400390685d4000204504400545074800c90f9030040e59100c8141040603142c155804910190103500c1420303c0002d08064510482d42d03820f13140d80c0c071040e410310048001070448070150302603011681890070f038152986440c0d04984c0803020031140003448003041c4020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 86662042 1250 86660792 86660797
    0x7060806060a03022205130501030b1302040f0c08090c0a030c0902030c0412050105010501030f02070b041412032409090601050607020a09052701021305130608070312021605090714 79
    0x3442070003001c00c90b20300c2c480030005175041d041d40c1c0c2c00c80d4002101485803c09008803a82480301400d507490003000f103018038030504c00d01c4030410700181010800006500900082c0c0d11904000d50004441c0b0b410001506800c0c00004c0020b0800c40d41c828556103540c03102e0280105038000c4101065000001c2000385680d2000c8a0040207225003080e101e04650601d03500030107091107041e0110f410038000d00e140c0449442111070855100341c007200140c40d183c803045100860070340105024403c120000701d80e601d0361800796104407421108034402c00346001409001030f00702002c003030003a000001400341c0800d001c03c100d07040d2801611207980303600c86030000900c0e038980380d03006c29500c518182c03e04c80d0848050034441c1d0147d0300b1446020b040208040e40a08030f1081c19525445040025024012031404240d04c41e0300c0e0f00d01c00030200e1311548495135241044080d906c112046c501c00c04032222695014041c0007180c004114115081515280100d450306200030118010003042c04001d2041d102d64109 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 86663292 1250 86662042 86662057
    0x90a020f181f030e060105010c081801120204030b1b0c0d0c02010e060403061a1c02010503040c15110f2803120507050c0c04020307020c090406061203050a0e0307060806060a0302 78
    0x2c8055400b9494081d0080919098420a50094400103e001e50080980c5661701d41d208400920705031018040c009402403000100c0e040142041207604907010368005800690301801e0542c02c42c0c01c050b503010809000311894809100401e0050b280394140101c2c80b400c00050074140b45201d16020701c01203c3c0101c82d844440d0b0711003400300b408014808241e1081e20140a4861309954055075142080f00d110818090540825800c00309003005510072800b131900544a038000d488065244c0a000d921701c40071194074800030303042c040c024200302c508000c844810060180500201e9004415402d4104000d0103413120700548504042d0825201310901d1055900b081010000f03418038102c02081a8800c01842d403141c0304084a140161500388200d074001c00d0303550014500c034250b0605104602e98014020380700540e45040018001205182c601c1442c0d100e40e403000c1c3da9110654000d0440e00030345060394002c2d40604001e00606400c48011508108202c0f9644c0c0c65602e0708404401911400c1e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 86664542 1250 86663292 86663329
    0x3020f030f07020d0207030803071b02060d09020a0609080d030903020f0105100f090e0309011b080c031e1303060b0a170a0b2a07060204150905090a020f18 68
    0x40208800c20120642d00a42c0541c0c261450b148204004030703941d000900000e0904030041010800d00c3d4003501e81541802c0d80307500d90b07901e030401030b03000920b40e5000300c910b4000b07194980f02a1170841c84d00d00300308030150403d400c04007100383c1000b8a0680d54000013400500345076440c840201414002c1001d001104100f4000340440d152041c0d070303034140d6840751003100d10400000001080c44140d41c01107842c48240d80d00254107101c020001111080c84240d03805162035503070403050021802050080c800d1070b1ba06002165104803e002c0c2510f000403002030104200020701c12102c581c030140500504580d004031000c600b8641741b4001950b2801c02d039001a68810441d031848034030702400f06101c410309004910241a075905c080302c049880320449c140fa070224180c00d503010142c40391903000c0e105d0180181c2c40181071586a0140200f42c100c001c0d0034a01090700403000300480e25140c00c0d2207030b2101c6d4924066090020003020071001d8014142561002030000b00789040548501d0580303041c07502d500f1b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 86665792 1250 86664542 86664547
    0x70c030609020604180903120908120c13060e0f0a030201080a110f1215060c060106080403090f0b0d06080c1507020f09041208060102010b0a1e0807080d1205040305040b030703020f 79
    0x10105e07000a1000d241c040b40070500800c00900e000b0100d1003054400380e004114103107000c10101800701040c00003407024a03400401c1c4040b0309007442014401014045035141c8910912340c080030005400080301c041c0b882600c09900500c010703607110400540040d0f001c900480c030640c585500808034040c1c0301081102400204d203405040d256900003038015050480001c94904000041c0544ca00c60740710b00400340da200f03600400c550340c0704224a59006000e803901e40c540d0350310b800c00302521003103591051f044041d0115428180500300e10030380c0001d006240080031aa80c0100c0401c100c2c408100100ca100900447c0081c1551101903d1a8245200902c000103500d41460101c0e01c000081003070b0700000380321000140f0f00d54014440d412019600a1806240914051800c0c9411520400f0b034815450031117800604050104004030144c03038071801500a4040d410310040c0360110300340c01084064101414000803036000021a030544414640d465030301e50705c0d40c8040c0c0113441221302e1000c0700e9000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 86667042 1250 86665792 86665829
    0x8030a060320090c030903040e280c0807180501050f120405010914161403190308010914060d08070201020a050d0801050411030708160207170d030b06070c030609020604 74
    0x88040081e4030b0a4129240030003601c40300c20390f100d00d000072181d07040e0551007044180860010100111340c8140002000344500340c44640c1c80c0d4406002410030454261214160000c0540011050742d01c02c0d020f140c800c0c440c44d40740c10690b81d000c00302e10415042c0300c0000740c043e0b800454681241d96038850784c004030446003005e01d0b00c2e90080c2103a072401e903401c180900c1516050500410451141c0c00548510700001e400c100703007c0c0c07400c0e082c0c5a0103903140c03050003180d000b1600f5841e009604c40703000c0d807a0b10300c0780e624294585003516200c4483c0d041c040c2115040042e03503a510f070724000c0000d070407601240c0c4959117807006074940311382c20002078010310495424440f01d40e031201c0c015042e290113035030a100321240300031801200e002c16100d20010801c21400142c007141c00c40d011080303000c030307503c11a100355541d60a089a041680110740c4550303000903c184030500d81601650300d526200b5241300380760841d2030711900004002800014800d54a410080c0305650741d01d425100070b058501c44201d0075144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 86668292 1250 86667042 86667083
    0xe0601120b060c0a110a0602031306140c011406040f09230708030d0606120506030606010c0203010b040c02160509160f050d0f0902010905090c07080702030102190c0b0609060a0308030a0603 83
    0x1707a000103114202c0510085812807021050310b2510090380007003190705003031a00a0381c06825003651000e005006019640304440c09002e5000c1c01c2c07400001c0340101d814410140420740d0500d0026400700c5081164410000b2802a0703026440800001d520111201c12003110b41088181d1f40100250f100114049154481c1a80440301b12030803915800804824104140196041100c0340d992580016001030125400b822401c14a10301c0140000307074000d2000000750450310020700000040e8800050003442d0611040d200c0082c06088400701d0f19458014804402c0d00040464041005109004800c0303aa00502c00d43d89030307002d81101031220100340c00b103c8008003680041640043c500b190005260305062603604c3c09900c1c000256480c00d80980c44803c1d05500800c000ca0b0559401c0000510803440664407964030b81f0030345e84007218003100d420440c540c160083c00c0c1501c1410346906000c8640d441c80d030b10b8800c49510642d8a83c5070364a501e800c100070722581e400640300c1e00900d04880342e410b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 86669542 1250 86668292 86668313
    0x40503120403021b0904120507060b060c070e06040e0705011206120b06090f01060e1c15020903062d070e030f100c0503100b09150c010b09010e0601120b060c0a 70
    0x21508424881d00400c0c44c0401251003820b031400340c0160301c0b0401c40894184614024440d081c041e040104842801c840415125032001303d0300c04007600200307c01c0c0400403042404640200c0c0840701404688000650151110a0747c031400e030501c80e20303100300c003106e0250350070010040c5200951181c0002c80c508003041c0590080303450703e204400e45400170b2407440350003590f50b046e56496a280003405541ca000d10244008100c00c05d222040482400e2001541404880392034401240700507031142070960034180b6182c405005605d44003450241c40070401c6015451110320030812244039429103401d407090b02d1754038034941001c1d01405078149410304643c0c001405400300001c481c0400c00925a014100c916000a40b0340d203d581c11951000c1100041c6003000d411045401801c4080c007000030001003103294025004a01d02e81d440d10f03200c0c2400e00d011501d0a0050002c1524880c031841d000c40000d2480c4010102c1d003012540e035200d440042c1c0c44201c181d4040c1a60081103581d98030142c18a2030200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 86670792 1250 86669542 86669563
    0x40c1a07061b0906050a0522090b0102061303051318090209060d020303090415170f150103230102190315120b0703051909080a030606030509070b0304050312040302 72
    0x541050b000c50004030440480c00101c0300c40b551007907607140c20690100c0e207690100700c44c08100034081c0b2000c000f81c100140c01c0317a042d07c0344035640345075585050500b9040d00d039500a540d044d50814410070404402c40ea00a6007603030350510b08243c0d076085a064110640c240c6401c281130b4111005900c0000d01b200703a010301e05440c000c440e02c981136a181001c2000d01c1040c044000c0d0550420710404100341056040385690010485064082544803009482105100c02190000750301ca9000240706990500c0030607010790f91003200d842035605540311600c0c000c4003049995001501d651100900c01003e5042d107404034024090400d101c01c82241c000d02034162108030b160740030008103000030740c00fa08482c4001c100354080d00c1c0401995079402d042d801408000c1c03000650350621002400850160300c40c0660385071003105815100d4400b224000c0c00c40380c29402c52402d15103007074140b10701010002561400c4917804d440c55940e036681d501d8050f045018051400c520f000c80c00040c00200742d004140403044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 86672042 1250 86670792 86670803
    0x9040509010605030a0206070c080a050706091a03070c0303140114040b04050402010806130b060301032d0c140d0b0c0403050f0c0604050f030a02030a050708010c020102120a05040c1a07 81
    0x261a14003400d82250b5407031044a6040c0e1114107503000500301a80688000e030300600228511550300c0002d40d0620702079542c22a02600600424006d0580004105d0041c1801218440e288070001c06c0c040d08902c809401e86041c4150046c2a000309842900301080041c002c8035140b0a551352803207002d0003d0202040c3c1480b13241031102d4507509051603c60140300f039405948210710750b1142400e02c025480c2c1c3e81811404240c0701c6110b080541c440e440154025841402a10002c2c1c5c070b00a0102e01c01020a4103140150400c010200048cd0b11a40f1660076211703a1540c0034005c03540305c00000c801c9401460002c0c08004844104440801d10030041d01c01c42e0301034400e40d0003290004101c0c035201d101031400e40d07500c08824081070115042005070200c0e40c00000e400c8a5424895400103403904900c0c5204840036032101d60309118070b8600703000303011910009000079410200760944c107082c0580000c10070711419594000241c00c0c4005100c0540050014038241c0d4a20f640b07503844030aa550102038140c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 86673292 1250 86672042 86672051
    0x30102131e09050c040303082a0702040516020607050f04050a1401080705040303140a031404050c0a06140d050c0906040320010e031b060c07060e03060901020a050301060f0201090602030106050904 86
    0x20105030b54000d0318820b401c404d910600d0325043d5582640d100401402a00e000544420300340c0054886070227003107404004030106600c803426441040140c807401000301105803030303a0044074480c82c4c0008000d5000805410074545424503200b508829000315800282c0c407050505001950b14002410000700d40d50a0b43c0f420103c0d6103c01d41070760507109a10008000801c0a01804550780b0904054907404101c0d00d008036070f480c0c1040786070740129801d640650742a0810440350300c0c00e1030045445401044581019a0b1040107540502514081c80d52910029904da100186004001c2c10845622080080c1a562130319128140710015101e00c4100c105000a808201e60342580540c890070b41200303005004103032180300d10580c002c4051000d10080e0300501c040c000c00c0840c3c2010710818002d86490740d0b6103401c407551034080601c4c00001915007101a441040180340e01640801180e0558a15061840388802804030403401002c4000c80900a113202200109000358824005c04074076000300d03010700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 86674542 1250 86673292 86673299
    0x3010c05041e08030a0518040504061a010305010602100f0908040303110c041107080901020709060b0d05060907020c2110020306040c09060219031101060e010608090c0d11030102131e 80
    0x1040d1003150b0143c001142d009014000303a00340304400809440b00c28605810801150a01084c26264250f600701c0c1c009807141c0d441c4151200c407256401000009280600c000d501d415000f80d102c00c44e000326031007111340711045000fa40c602500407a858540c81070803540d0707541e921300700148005102c5004403240d01901c1d110b40c1152505004404070584c4180a80c0e10340889503413031640c0e541c0203000d13050550059000009038040c5502c610b800a10310303480010740c0ca1007004004411510014005d901c94458034060040b955800581010203d8090321605981010011881c1c800302e50240d07a00202d1081c1c050701c030380e2002d60780c010718083c0409076401d104050310513609403600080f9004a5005a20010b107510300c01282c2901499428000d00b00a801d500c54485024203580b216006640152058001041143d621a0a443d40700c8d5804010f0414400ca9000050310145410700140c0000c4240c1d8410b00c85642c20b504840580107000c03038801142c0c1d69095412003100b0003e0380707001c0100340f101000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 86675792 1250 86674542 86674589
    0x803010306021917010b0d0e07060f0210140a02030402010c080c011506050703140d0b0316080c0108010b09011214040c0512030a0206180c0a0605030406110a0804060b04020903010c0504 81
    0x181413851511546010380c2001c5900c4516041004400100c40d2146044550010306000358805001c640d960358807911040e18001c1c2c6009148c40390709100c035150412403900221384641b42c43d0402149400945e032500c980c0012140c0b0700c040303040500f0301000002c4420400e00154090854403507600c8607039001d503a44513003c0d1014025050b0140102e11400320b000c40b03d013681002000032101c0e403007000401c809a000806d2400b5240040000c111403800000d002d1084104a910b50094091a05d01515070403d0540d480a00481d40307080d0606c414200c0720841404036070403402030100303410300c0c4441901d45420040821000c9108076409000c80d1b12002612000120031182d050301c180d0001d02107a102c0340003144c40c61454690192840c080c042c42c6c2c1031980e0ba500c1c0f00000900346681d07955124241402c061045641d10071403c0c444d51410421018420b4002440c2e0390700c1500282e00190404c40000400c019216102c00194154a032149050b541e61300030380504196603c24420500300f0305d900000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 86677042 1250 86675792 86675807
    0x40f020c15010929040e01180f06110a021504030e040e010207060e0303061e030c09040b07020c01030209010e0105090a1703071103070302011b03120f05061806090c0d060308030103060219 82
    0x543c00300d000c2180c100001405d15801c0b0320b4080320b0040000452007500c0002a9400e642002e040740c04c5c0075000c2c2610f05001c084d0040c00b0040001c1b220092034280000c101941c0c0f6501c41920401e03000403500000c090500428084030711a40c094800c0c0a0500084542c50003544424000c0386d42c1868444881400103000081e02d1181e03030003404079441000085882042c1030030080e403003681407003105842c0045880d03591089001d01d00c0b400302d0f018581410309002e0b09200c4ac0b02c1840d030425205001900c4c00e40e80c080b81d500c0c112082070070030990b21429030002c504803103003c2d0443c2c100b0080101110201c918000010130b03625004418103a039042c040030030517880d07120622010740000c81e44070411807040c41a0380704503c91032003418584928001c950000b41560407012414010325595400c0150a04104007504c08800c6103403046115441c01c140020107180002d0402c00801d0300105840c8403180f030a500044c007031070308200295141c1d03950746441d02c069884550390502442499440715100350007000c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 86678292 1250 86677042 86677091
    0xa0e100c081807080f071505160803070c05120c1e0706080c0705060103030305010e0703020c1b030a050601030c090b0915010e040216110102010606051206040f020c150109 75
    0xd4041582d00c03103020028034440e44480c0c5036268058210000344c41401040108054886000502510303803031302088002e0420800d41070401c1c40001c00c494004140f004c5004a80d09a021070b005440392a1403208030f90078402070b10010071760b200d0024180300d1681460041c059480c69407048071085000c004d020319000072400079030411540301c3e080901510780a4030f240d44e4081320070420300e41070510700c4d00c410b4074014003a8800e82c082903171100144146c3d110200d00590044581c2011751610311100d20303a40d59000300904108613070320041c028442996041c094004a181c01900712189175031603051a404141d0a8819482d24500e8011411041c0c104410342078070440c04126482402c940040040d2400369600d000d181d0f00c154200320040000c01d0300c00200700f189001d4140c42c03814080f00800642107a04c5504004140034091140000309030400ca8403942c041c0c815180800c102031040103d40c041c0c000d0042041150142405550f0f101f116101910f04840c00b1100c24015002c1441c0710440c0c8480300c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 86679542 1250 86678292 86678297
    0x60108010605101409060f03160807050c0a12020c030f03030a050612120a03020d1a042906070c030507170c0105030c03060d021203040b090a0f060801170708060a0e100c 74
    0x294901c04040150005d000c03000c0000e086580340803c0f084d0480c10300d9000303c8117030420300c51031741d413441800ba480305089a21200d01d080880c50a5402ca54965560890b103400401c008100c00c1c030043c45910034090710301c0c04100070302101d2a00e4034400380c140e101e4204032400d6100901e4880002c0d19880c0c80c2d030804218090460240c200921886c9500c5400e07030045000100303040d000c010322201c4501e03038816071028500d50b19032901581c6400c0200010745030018814012591200f10816603030254800d540d10000c1c0c01c4038500e554424614114014844c56400680b050080c4240044c022800c0403034600710604a130240ca103001c1e00c3d400151454001034420516a80d4140000f840c1c5040c45400d85042d2400100074400c1201110300040c51940301e5040345004410100d40580c6a09000328844003030500c0012910083d400e2181c001c0c2002c00c140329480c00103025480a00050741e0500c07020019010900a451f61803a1900812004d05064020450184140840b88000361405d00c2113040105291707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 86680792 1250 86679542 86679557
    0x201020f03071703072a02010206060d110d03031b0804030809060103120c0206070b010f050f091603110d141006030219201009020f1509061602090906010801060510 72
    0x301d660b2504e030002044c190a000d05140980c107228903100020144284514400340d00c101d8a200090a066014010600a501d10030340c440c00241c800c000400c440d20143c03000003520302107040480c00343c850304044450a00310158420003260b440f0386150b00c554026261940c0503101c042a40360b03242c00901c006000a900442c00c002000e20402c81c00c0315050000f80b40d5401c002d000d0300c42024240c0283e10110040018031010031203420856095030744c001c1e00f22000c076a54035004c0e41c0b0041c0f8240f8000c00360100b590303840e01e0b91810915001170384c401d40c80e440001c100074400c07500380941d0600300f07599060725041854000903100344680202e8a01c5040510700000854241d401a07501100d101c002007124203840c00c4413410300703204010140300348210245c01305541c4040d0042c44031000001e054140185610300315520b407804d20b90200d82c9207610030354040e0707500c8001c84403215000001003070095000d401e84c03082c000250300004806058416140080000958480070000c1880c1c2402d203240104000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 86682042 1250 86680792 86680823
    0x1d070303091a030a1a040e0601060908010902030c0907031b090618241110020d110412300201050703060602061302041104090c05042103170603010f050907030201020f0307 75
    0x1e8100081070b01c00120019842074003403000500f075810780650700095230302040040009030341c484100c5004110380702c001c10100f26160042030b22610503828040c0115400404111118481c5e80008881d581000b0700958600803d4001003071040e051050340002a03680c0d00f951121101110014203c904d0000c10030f83c54010314028202100c40c04402409200c08000035440382c260034840b081905a541c100103a40d9040c41540303104488241d02c2c000311441c0b041c0400d0001640701905000e090390011850340005d4403c0966010540f00980c030321908201c80710b10441d10079015008076000c2c803541d4a09121880d01e9480c200e1756401c04440f910038000180783c052000d82441d82c02200b40303203520340d40c10b440c140d02c400c21039081e101d43e10b000c500000c80c000380402c0042c80c1c850b00a01c40001000d2041da600e00143c900800e803c401c154541049510701300840e01e03640d82503000c0e65030900030b03034030901840c1703060303243c1035252619488143e000d07004100d190708000c100071041310080b541c00030b03485011050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 86683292 1250 86682042 86682061
    0x80307260610030e070609050a0b070302070608130602040e012102060901180905131208060604051e10030b13050105100503041e051605100c060e011d070303091a03 72
    0x40150b0101816070314011510115000d00002000d00309031b440314260305151206121060100ba446603603807420501c440400079a0101f01c0d6800c0700c90900c1c000d00d5036147e205c212400e03600c00c3c0340002e04135480020002007414100003068121a501403d080e045005000e500c150034045000007036000404008500f4207600070321286001d143e444203407007440380c0c9a644110440d030007a1740240070306031340c600d004c3c0800c90050310741c08060720b4600e405d010038140203004c20802d0156000d814422039484500003041d060328611092880b20007804000c04d070400c02c202500420440d11068060b011401800e040d0340814090141260000341005040c0454131400315190f802c0584101d40321111808a484801b00022400c0141801400a001406004e40e844144580d455006501560201c0425415280c100d0078412400d81c02060210b1045250540180140071410314046e088084481a24007150005042025244031340c84002d60151600c0484c440500190082d08008804000198080b103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 86684542 1250 86683292 86683309
    0x50f07180608031309020310080a05010b150a0905012010091e0206090f06090607050303100e040b040f0503160623040803040f060b040e0a0201030506010f0f03020c190803072606 78
    0x1401150070040340791100800ad0400c09410425513480e034580020b542c807403400000100c03a010f0303d102003514114008001505d0750f2200d20426050140514010113141018000700010760034120541d07101040d2510303140300500407280e05840c40644000c60341c510890030811855400c0e0010700890800311a1020001103a1913041e040340c10050a100b1400d040d1102c81c09440f01520500c042d54483c904015803081c8010161711801036005408248004076456200042c0c0040d00162015101d154508202785144550151141858200c10314502032103002ea1140b00c0400b410b4854546070242d800e00c03804804002c2c0c501810301c010400110f000185444c9600700410b2041002046060345200060110f0380d4484c40e40c2c905801241761001103603851b125166000b0002d0a0024a107141840c0041010f40490300060515a0010740003040c00404c101c100221103145020440084c0c0d946013820b8250000c0e141c280c0407507403040d9192070645509010400314110076a110704107981d020308000105 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 86685792 1250 86684542 86684551
    0x2102010203151905092d060913030c1e0b0a020c0303010618120317090604170706090206030916141c032705030d02010e060112050f071806080313090203 67
    0x1081c00860000b0940c80c0c91110501c90100720906d11001800201080728003502010b20701d00b400c10243c10400c0c1551044c800c41d420207040580300740c40b100540381c1500c4111524001802e030214a84507440c807001d180c024440c0103803007006030006070f48410380d602c002e0303020740000c1d401250414401070000d45e210f03000c10307240740850742c0010054691f01d55a0152180004900b64002003210111001c0d1031502c03401740341c2001c0b190005144504d8036072036012880040e40300f580c110341f200148600c00e00c05543c100c50010341c0c006148030350300c2c145500b107242d444000700700760f11a41042c248009003006c3d6201c10700c03551400c0908040c0215090781a200080e0070058001c9040c081d8554405205400c040f40100e00451301003940b00c1050f0a010030586000551120721045a06040c1d540400b1500803621a044543c8500d00000300b402503c1c05d5410000b40314101e0400340310301c100018041d0340f060b5020b04024520f5204010843d200c1c00e019440b48940d500e90303440d40c0305854040041b99800c1c0d00070b40c0d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 86687042 1250 86685792 86685829
    0x705060c030d0608010b0f0904020306010501051e0d090c0e0405100504030302041502070501140906120403031107050a03030b0603090a1104020d1a0307060305040b010902030903070f210201020315 86
    0xb4214088101000c03200c003900181081e03035480e11111114244107841d002451802c40d9408807500e8958002940d545050003020704000010960b0750800c2000d001c00d00d01c5082c20750110b40c4564511400000900812009843c440750a0b040000c1641c2e10b0f60300c0a0140b604400507180c405ca0301c041910180001800807003c2581c01c00c00000c05428103801c001588072980e010f080c5592400000500c095031140e070f140c0760102c0400014115985144c221000b0351002c0e01c0d01c0c01982d40d182420390043c0f184c3c4500c42041034000660204100e800310b28000707c00e102e07032820040601d80c0014810640021140c05105620410200e4081042c103051808405402400980b40000300d440301c0b42a2a29042d980b01075000d12186140c041c80e050103044e0241109180820040c54a900d03159074216042c400c41080c0350380000420b1000b03005004403181c06400021540da072381440d2030848800d10300b04150381c0c83c01031680c0120702c0c001d10600849018001552490040101c0c1d0343c100140502948080c40c074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 86688292 1250 86687042 86687047
    0x1501050304111306170f19020d0204020f0708120106080417030a11040b0c060124120609112104110f01020a02090f0105010f0207060207061202090a0b0c0f0a050705060c03 75
    0x40f2103003030700071480036019210a0b03048404d00201c040f45069441c1243c1d4180e50082c811041c030b4000d0814800038003030740450b1602440000303400810020311071148548000e9500050480030b1120800041072100d224003944c4035181c1c0d0300e4200311242c07141911300508480840d0001c188504944003d1a0031403211140090583c44000c651200740d0712903804803001c1080414040289841444000d0040c4200e03d01013000580c0e41165010a001020241c001d21410340140541c0601c02d40c406800741120710400c0103551041d5103010aa90810490944c000c121046e405091000d000c0890703011710b40c08048000c00b60604401c12410f070505400700380c110b02ca54828000541d840420045c06240c020a034a4040c4d4180300c0014803001e040340c080b0065611294003088499030005405044640c5480c20188130042c00c54490040d219040080d42c1c4078905120210b0b200000c64002c0202c0700c001004c980380b800d000d50340984c03584502c1401030300c070b40c10030102002141450760060440013000030581e231 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 86689542 1250 86688292 86688319
    0x7080309150f12040318090b0609041e05040602040311040b090606090409050111030702010c0504030f060c0c05010212090106050a1a030717010603090c0506040b030a0903090f060e09150105030411 86
    0xc03480048070141e0001ba62080008149080151401c001e0010303003006110f66030602c2c0c0414114860b04a055004a58075113038050790307050b40c011800d042030348041d06108a040c0b5042c0b40d400794009000545440c491800302501918051280201c0c2c2d0701d014100e022181c4e503580800c00b26411000c00c80350059215141301c40007403030a210783c0c51070b440c6c000f8075035849003081e020081c2102c0c9e0000340d000c2031241c20041400485c0c00b00c0070604034590300001c046079034100403804650040001000034019030003c981d03031000185514029100d15000070081009640d03e600308100d2510601c181c606c22034000281074080b030071260056074411054140b0420180d06022a0248903409070300110010707035200126020081031490010080200300c4211b801c260170300d00006c4880c030010b403184890596895101c4209400754400c14010b124040301c0c0c1c1040c503603d850240c001064051010b118102403070029140416603203202000715410b80d41d03181141d445a45c0c1c80f0084180360071460f03024540c001d096 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 86690648 1106 86689542 86689567
    0x1806070206190311040b03150405060d0f17120f06060a0504052107080c011206030b0105100908030a0f081e151807030204060207080309150f 62
    0x2c0c804100e80842030f40140030f510303841000044081000203050528a001c3c600c1940400c81000700701441200f004100c6404a56159210241c00002d1011400ea0b150319440e1034030409100d204110090140b070080e4000c1e080422407110040200540203e2845006030091802d0703034860b0070300340201d070302529500480c01a20302072610080304051540c041150402c0c044005000c0d01c90554985070015126455080b4003070110351000c000500c1d600403481200100ca07001499059141d00b0001000400c00c8400303910f5080100050020600100a00041c0741810985d01c0705084510f01c00005002688000c1010b802e69048407804140c3c3c425101070242c0c040318095080d17004029002c00540d0b9450071200c42d120081d09142040361007501540140b003602d8164007260340003541da4400603901c0c801d0450b42900705c201140c0d40c00d1242603240281040d031030880e0742581001c01a0700d89 = true := by decide +kernel

theorem cover : BRFrame.Cov 86510792 86690648 := by
  have h0 := BRFrame.cov_init 86510792
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86510792 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 86510792 ≤ n) (h2 : n < 86690648) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
