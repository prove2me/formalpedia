-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0683
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:08:07.634026+00:00
-- url     : https://prove2.me/submissions/bcfc5af9-e1fc-4310-af7b-d53cc9aa978c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 122661870 ≤ n < 122841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 122663120 1250 122661870 122661881
    0x103080903101503080f0f0d0204060306080f0c0405190516090f0b0d050403030b030a050d030501060318121106090c0f060307170903091309050606060f040e060402070f0303 76
    0x64400d0250080282e52100c940c8502c0c4403c48008007441022490754860701e00c03a8122014011261004100b10304002c0039000c005d25480107400030050322142001002000c6900d541c02600080d4004107451021314000658003d000d13000300c5022505546001c05818401c82c0c0703c0b400301d900c50a02c0300b440520104681d01010701d0096076149a1050b6413021109550360442c418040c40d0300c000c001d1009030b03100f40e8100660040c041e0902040d000c04410100b440c0850001c0242c030f80c0d81003002401d040540c1409520300500302807400f400420114070300201044100203004003c10450059070500700d016401480401d0180c2054403042e1800010098440e400e905005100b0900c034100610340345070003016203009009a0352550041d42080c407800350a200060800d1136144070030711080f24071369034085044070311060910000c80c0c440b00c0c0c0d2801d91b01d080343c0a046207110306402c4c1700c603900903110305d000d5404845051540b90195190380002c038000303100c0d481000e0004074520351910149601508070703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 122664370 1250 122663120 122663137
    0x627120b0105040e060c0f090307031e0b1005030709020c0106080303070503090607140d05130206310518221112011e0905030f0a02010b031e0c060d020c06010308 71
    0x1813005004c01c02503251200001c690350240d04c078051180d42686003c44018103038145010b011100700d5500d0f61224501c821510407202c801c440500441d000b0400021000b903048120621200b0310a420580000e459040500800c020240d010510746082e90003500321900078a03188050341d40e82e060421008016900450351440244030b940c0c04654801c3c440c501d0181c0002921440b5800c2a15454000c0c010705005024a0350104080d030030304000d42e503040c00419500484410950f0380001c2c070058015580c00c80200240164405003081000e5218880055842e070f400b0b000c640201d0b9075040e5102d6031030103c120380c4000a9013012520303040120488801032254000c42c1c80340c240d1412048594241c40d42401d840300e13482c3c148101c203c0030484039001040021b02c6101aa41000714a0702201000d410011405c00181e4580d283c00080e801c7c05c0c0900301440b50850720140c840368140380c80e940c1d104040031015004030740000d0418802d9072164160b500e50b2002d001903440551792420003480c01d400c000e61 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 122665620 1250 122664370 122664379
    0x1501050d06031e1403070b01060509041514012c0d0c09060603140a0207210201060810050105090912040e0601030f09030f02060606040807030209040f0c031209060503010627120b0105 80
    0x8042c4d4000c9000001c0d5441903074841e103003c045a090910889503074220100480d00b080e180c1503084a20042603c2000c09002c0499002c034040130014001803582e103141c030500d00b5000b42c40c2e8080e942c04400d48000c80b11001e050740c40c5034500342185480c3e50042c21039844203a082385032002c0407441c590b00d500100e0020400e41d0010b08240c42c0c240814003284141070300141118094410182075500340500c2c840903111900000a09680e10b459850030828034000c8540401d80d2040180290725020301c40503085110480205600205903d14456600c81c40c00f52040355a07000b00095041e82c030a070400c800b03841c00d00906215420076490f02400d02048249400054018003000445604000c07083c0c0741150b0300c050080500724915000d100d2003aa01400a441d6005ca185a41e4041804040d01e0700046100300300c080a05040c039135000f4004106a00f0070410040100010000c031a07001010308288030f040e880d1030103043e6500010344014000c0d03502089a0419181c01c44060141003060107040ba441500d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 122666870 1250 122665620 122665643
    0x3111501030231150b12010302100302040602030d020c0115030807060b030313050603150a1203020c04020f0405010e0a080f01020d050603030f03010608040f1a0106171501050d06031e 80
    0x94444506a10f241203c504008041074110000c08640d000320705400c41e021841552181c446100740c00d40e6211140002032100c412004204500745051603588605c1103180440c185130410000940f00d1280f0204501400e402003203464001c5029840b00f0110044841103600c010f0b0380e4500b541d40c03600407072010740d00b03a843d22010120301d080c00310031240c8000d00f1880c0a020282014100320035a04090700c50f5480000300c032020062901c0f13100c1e00d80090024403440d05448815803900919208004840a0069005001487c40b0419200039913050318000d0a00404004008000c03480c1d01d40030390b01c25002846225010040b0080c10b500401c142900440244410758420003803550b640310b01e00030050040400c200402c800d0f48038080341c2c0d0b0454414003541603018126251a604054102d1080c0d0000c1102001000400d0f0040c840850b00550101312b41c260b8030340122140003080c1c5a061030350511100091054000d2a01e034030903806164444162601414a115841211240400d08036074542011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 122668120 1250 122666870 122666899
    0x150d0e010906240311150d020406110712080d0506010509031006090c0219061d030a0302041814150126040311072d05030d0e010e0f03120304031115010302 68
    0x400648094030707017000c10b40c1301001d40d54081c000800c0c651021100354100c240715030760b2500d10500040006000541d0381140c800c043d0428035003880e880798403840020a10380080340001d44803009490003000940c0d00050709540340c000580d813921420050b140e01d40a80040346c4c2185c40c2c558402403e441040b50200b0190f10312036402c8e80d803000003420010703c211100f1904d500040e03403a04901d0b81140e00b030030142064175030742c5800d900e19040010b9240c0801c0c2c020605220890b24000000b1110541d030754107000c0210348245107481da10b03000d44050030034500c8013503100c46c0c0c1c6d00560b81d02126041a03591515080711140c10810614002d82d011000a0610798003c14003045c001500c00681d842c0400d900c1c4540461255025060f1030142946204440c40f5400240c030358017801521540d8503540c41c0c1c60035a511410004007443c0c800d04403544207684c00d041c01885a100081c0c5600841c100c0f804140c0c0d02e8445040964441c4421080c0d81c24510408a59200c8103140c1d2030100d040300d00c02e0360752034101c000f038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 122669370 1250 122668120 122668181
    0x12010302010c0c09181b060503060409061103040503040806160c15060b0d0b03070e04050d0f0c0b0712150b09010e0609040c0906080c0403110609242106150d0e010906 73
    0x1b01e2140c140000d50078000324903545030652000181310310800002440d11041c11004030642c1040b94283d9203500003140c200302862040c40381591018140512149664803004007420080c400f0300d0241515140b01c010100710641907118802410840111a40740e191728140c88014001002205010740140c04000504e0356910f9400c86c011517004024040d68202c03a03608680c0324400078000010441003041d0751020501c405c08440c003e400325a104a00510881501070a40d04684817003841000070348410008c4c2000e00003039801c140d1013480c01d41d039154598000140035018100300240e00500e03205103081481e802403600d0044a0b0240c1b5061590754502031100c1030f600503032001a01200640700000d0321483c0c100010b118080c0000c212862500146090004d00e4441c401c400041102c0010340c07032040266904082884625661031020030716152010410a1800040405860714082450b40f945601d5402c07401d01d081d070101c000c00c0106118244400039013010040e1702ca0000c0c1e01361301c1100c070300b19 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 122670620 1250 122669370 122669423
    0x507090f03030305100905131415010e040f0b070804031704020109140301020c03040611060106051c05190504060b0f0d11041e0203040605040c080c01080f131e03090b12010302010c0c0918 82
    0x7103181d404000740c1ccc03070300f08991511786c8000c00072609420401690b400140c02001803a01400c0c807669107002c9803500703150141400251488110041c4864010003006030b900c00342d0002980c1c0c260720ac041660b902580441d000e4000c04191361000e010115000c60312551000315031590020310b1044542c1c5998468098502d48124402200c02034000c28038111020090340201350852204075140358501c0100c040c0404817801034504450309a19050115200e25208081d2941c0c031204590340e4402800b42d44e55003100c1c0300fa51138454011501c584600c900c80300e84009010070300700582030965030f074a02458510300400e8101d80488040e50045804074524400003030720064010181c440c4204c980b07901c90321005040b401026503400c0d904650001c8001400900820544601141d451242005c2443c014081012030742002c6882c150502000d00500182502d46045030b40a09003a500001c0e41e00b0700c6804000c40707420a0340d2403802c02c1040a24400d92200e0454403a0040c080000701d5444049900e50b1b401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 122671870 1250 122670620 122670643
    0x906010b13030f0305090409061a0301231b040303120606050f16020f120703060f14011505120705030a0605092a0c010e030c010507090f030303051009051314 69
    0x5406060502c00500d40b042e40014460003070402c0e5007000c200c84005415a80c005c203088030307001c0e1038991501c4400c15284444140d014114000d0001c00400301085040c6100c0154891200800d900441d2602044801c01f07503102c2007840b0740c0c81d61a074403810068811407001010241c000d1401c07200180700fa110780d040c0c0e155103108107030061a0511f2144004001d207030400040e6404031069921274980c1c2e43d400900103001e81c49002401406103541000700890f0100162003408505001c524004002c0c030010890550750006140e0850400801d006c452601444188503a010344e1101805000c40d0000c2c0914400c031144001403280c29118014080241816552035040111103500c2d0340c0140c3e40120811281500056510b003000c0359840568292103002c4071a80321500009105211010203009182d40540701d4103000140c5447d044403207a280340d051102504041c0e039500805d403455642c002c0b0000500c0c11507014445030802c0c040512001021410445401c40c6910580c145014003081100759117 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 122673120 1250 122671870 122671897
    0xb07030503040b0907080712060506091b030c09040203010e271f0f02040f0303170105030a03030b040209030105010e160e10031805011e18051b0d08070503030906010b 73
    0x1a251507480c440000f4010f0500602c50080507008141c1c039104000820052840c280d801141e22038505180d021150080d100d58054031511003046040202249802c40d098200d00c1d01e950790b642c0d40880000c0e43e0007500d441592182c000400028058001200c06002d461060070004d1500090400b00000080710340806140390401015182c17a980701c40b000390303202020480301140007490f03c4040c030101d034080c0e0010801181440f0b01442407580c4049040c0010301100c070300b1749081d410200042c4d42c0302c8009400508140e1500060105500c45805484000b00040c0080c00702d540c45240100d0340c003800300c0307120203400c1802d81c41d5416039100b8980c81c03038441000790011201c000280011005060720380782c0c071440c00c6090210b280000390248514000610452050450302c03040140c1c090a03594040940c12a816801c001c0e040824408680c1c018100a2080503480103c004c501003400d10b8a00d0700e000d0039200c0040780100c00e010020004511401c0c101040d41c3c816a00c81403102d549018138080c40010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 122674370 1250 122673120 122673127
    0x2031302010315050301151502070b07170f070515070201020a170624090103060f050f01030f0605060408060906060901150804051c0507030815010e09060a03021f090b070305 76
    0x35501940c00b50440068002c0c2180c88143c450340841c2c25500d5010710310400d80152170082003400310034044c20700b00900303500c05004024500700312525140261000940120804400c071443ca501e881c0c01c0f6101e03c1c44214265031a801141001c544032389501c04408041900c0c14001480188184201c510b400320035110341034402c3d1414410300c030070003006244640000d2882c0303810045111700303003281c0303041300c8011030003a99a045100010262007041d0b20042d9409003200e42409203644941030b01c2d0698a003840e000855589417450302002e03201d40c0d4001600082c0c0000c010400002c04a002407090510074200d4525403980e40a11950100034804c0382d1290084010403469a4410140b0503003090060b400c648041003a00504a44000c900c071814011540c00122401003640040d00d49621940650089a1010308140044c0c07000c020400e80c01d108030780d00000520559241d0003d07401840d009880500148404805855010451038412000c00e11640c00081c04048040171103111590540d9040c5c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 122675620 1250 122674370 122674373
    0x30c0b130f12030e040b030a140c03010c05180f15040501090e2203123b100f06090203010b03100b070f0f02010e090f01181a010813140a02040b0103020313 68
    0x1a040d007007130300740e0341d1080d15140d240203650303000c00011010a0150312440746a002030540c0514100b04441220b00a9050074035401403150003070140d409690720700b0104551022940d000074062000c0c11403950b4010300a85002a5640c0d00c0d001803c01c3d40c10a072214003107188c03584412aa038090403074088410781c00c5803240c10081d20480c241c55401d544031b070401d61890700341c0c1c00741507080d0707802d6001317455419031140d13540340041489290201e03406043c554041030740c203400856680c81c1c1c0040d101c1000789540b504030711405985698000d41c0100560038046403656101e903085030851b80140c0724881011082c07680070074669840c0d070460701c0c040e0344802c0c0e1149070b29aa9440345034911424209906002c0581e441c1f03c3e040d1203c02c2598841e1b9412810002a0760500c40000d505a0003075180754101d41ca0022440c000c9241e4600203a1441d00900703080c000f0350307102007101c5280941e8a10003400c5007ca003a98000481000070f0b05501248201c9042c4801002000110100d000460342d2101030b40d010000e080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 122676870 1250 122675620 122675627
    0x12060506090a060e0a12060b0108130b0402060a090f0b07050d082e09090501050a0f0605092a070c14010327140a050705030105062e030204030c0b130f1203 68
    0x10f1010060400d1782031541d07a0078441180705400c0303001c0d108640c585031103203041e6071301404a41d030200c2e500c0d09504c110509a1200510307204010002402000c0010b02c0302107581c041d981000060000310515130031a40c2300c08011459401a810403a00c03481403041044c1c402d809084200d1049522800492103d1120302140440c03151042011024407082500880d120602e4010354100a00810001c5424244003a01904580c1c164030800740503440c0500c240724641c0c646038030075000101d0468954030101c0c8184a01c0f03100742c60414101e820710300002c0341001c100341e162088044582c0e0552031000341607102c005405036440380000b528170402881c0c11080d4186807114080e0f049000e049840c5005440f0900c00b881d044d04008165000d5201000800c10751a007401400e034030141c1580c2d291104042400210000800c0c010001e5955038614146440144683e0585d0010f68102400544030344d55547e00f0500383d0f00416032220000240d081c0892040580c4c05114200c0f640e041c014400c0c8803007903d00704d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 122678120 1250 122676870 122676887
    0x61a040b0a03090213020a02160e010b09090402061204120306060203040f12050109080310090612050a0201082d07020609071a0a03020424020f06040533010612060506090a06 76
    0x40380d000c01100007008580f45c0c05d10203001581d80341d8008012084810401e030b000007038154030182019140c0c0c801402901040803d442940c4000c1d102030240741c86610000320903024995141004040c20001c03c800d10070910000c00c130000180c2c40c208846a100c040413601d074071450048100328061054100207046034840c2404800e4028000000c0340d1005a8502c1c0c95607205440c02000b2031840282030092001038800c2d1402064005c001c0d0710009007030b07660561a55004200a810311010200180880c00b0050442034000002e0003198508620101d40844151742940c11500600c111800030303003908000aa120240c820000804c0d004c8079100940301c481ea84a202c5003410140c00344000550143c00c041d103840c0300c4880d00d41420700c201c15000b0003441c0104122407044d09a100340184800f042c00461101014040b9811440b10b05001c0d0446540c1c4811031f00071003d08200351400025019805545d11740941030801040c0407490b80d4104200c40341c0900540d29070b000b000c840c0d00300401402420030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 122679370 1250 122678120 122678123
    0x1e04031d01020f01050a0b0118030c03030e03100204060203030411040c091a0f030c1902060103080d051b130609050a0602150a090c03050307110d0b060103091113061a040b0a0309 78
    0x40b80c49003225400d00c682558401d1b12485c15051b02d03074080700304540e00315100001211003840d403003000f2840c6840341a0940c11505c0098113000b0f00c02e0403452540c805101e840d03120031100c28150740c0c680e9500c0b0000c0d13a035802200c0c103640311204028031080e00d00e00340c02424000c0c0c200e0794070f10050a04150700030183c0c042032041c00300d03c00c6003000351000c002401405180714002d100300d10b44c0c0716140c0e14203c07007810203180440307000c540001c4014000604140c1c180e40045891420020343c0790795207425510629000b030070412940e0700c04100c0015103201c64207008166600343c2c0d1040d81031541c03502030010b254020301032030000d0382100e46040c0300c1740082c240311030f88039000020100c0c0340f450030740701c030390202d19140c006a445810000318042403001a9420031b1901400f521071030f241c074107151035020f500310b40900b0030341c10107860b950071606100a071b00200d0312a050007000c0011560201c003940000b4041446406920b80c030310910324444946010986086500e01c01c10a071070001e42c010110300401c4640340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 122680620 1250 122679370 122679373
    0x130e1b04150e040213080a06110301050603040305090f0a0e0402040b01030507020c0f2103070b0c090f040203130618140a0f021210020a170a20090a080a0602031e04031d0102 76
    0x10b01c0080c141c2c048005c4004007074807405804461100e09120055400f1143c183c05022010801008661298401c0f80e034080e4061400a8480382c3d06000200640034845455502452200c07002c031314004a40240d9005901c00c0b10304101ea01552001501030b10021520000560402103200303003181031040040c07800d110300400c070060b07800f044a200d8030002c80f4010085240e50003c14004200006000c102e50400c180101250400c2240c20004480f100003100b42070003103070084046108140c040c6070000300990700410900004660881e869120040302405503110003103000851200c4d800410304d806c605401c00606000700e00941c0a102521003244a801d950384101c070405a20b001041c07014200c1035116540350203c20320441c80d90000780001038003007002585000b40c0208000c100c112402841c103100031000d130b180c503c040005400302d540d0358040350160240701c5090f010841158020351280e5005500400414114000800103001c201c4e4020003007424694070141c0e86210301903000324000c0510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 122681870 1250 122680620 122680627
    0xe1509030f01050f0f0103020901121e060e0d030203042a03080f041d090d0e0d140703020108130b040206090d050a0f02150c0c0402030a02130e1b04150e0402 69
    0x40400c0c640000000e800481c1d96560040c0724081c007140c0d41c110b40084201c0d0142d0081d504640000d80744180600c286680f229182401c141081107070002d10b0a1102c400c2c40d54091840d00f404e0a10140400d114244140e00480000c201480e029100781ca01a60300007081d00881c00c10908440e072001c0744451007450b00c04405100000040c0202d0003001c90f0500314000b030f0740311407030090412981c20081d01486020f030801802c001003000c000441d03401010300c51402c0c1141940d86c00200700d10f0f103404d040180022010b174002d1407481d2400926070040700d2003070740c40c8900b50360f40d00304182c1309030015000141100b110601107405441c0120181c01251402419081c5005956a0303907464503484e031008032800b101060140055160034401440c4114401c84018078102ca207030340480d00d030714201d48150711940c0c0c048080b401c840034541c10f860520441304407221039591070f1410044248801c41e04043c1244101c201807031021000c8090f03508440360403441c5c4111180016040d620b109001c1e482d190032030750a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 122683120 1250 122681870 122681887
    0x302073002060f040b070605070c11010c1106040605040f08010603030215060a0b0403060b01030c0e010210180c03050f1011040b03190203070504050909010b1018030506010b09100f0e15 81
    0x3d60081004042c00c8602a40c1e820303582c0340440c190385000700040188100e0f141814049060342810b850031480910308240d010b1310710f242503000c80c6055150303140c0100300401e0105600c2c1e0000c0040c01a40c0b010031408400c030360b40f214000c3c03d8a1840c080100141c21045480340c1c2d0284640045d0380002e4020004d058054484402e49400c1d003099000f6612030f03444107280341c61941c040c0b2a02003908594a09203001801500000c0e5540102d07002c1909841d645050034101000c48030036525049910541c0398060315642d0802c940c0d02e4040da03444000b40d0007000450350904206100c2e0900e0344607c00c40803170901e07142815010700745d0402003003c19504103082c500c0e54118903d1004500c110714035101c05031194180400d10101000081c003030f00d0390b0381c907084901200781d56030492024412130510309400000c0c41d12107040344041056000400078424640086980381c402c40c00752070750b0202558003004020031100220341062545e845540440e0980e104409181420744c1d0944100719403544507840c1442c3d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 122684370 1250 122683120 122683147
    0x519030e0613060b032e0f11043803070c050111030702070506030405030301050609060c0a061b03020723010204030206030c0a0311070c0915090c020a030207300206 72
    0xc680151002c03410194070420490320748241607100e9016001044607030341d031000011440d034035116400804080013070003850b070014035041303c00c1d002040c000601000d1000201001c543e006401407000040c82007805c1c07592900704060b813080e40003601d4100038101040e0120349207150b1008d4554000c20890410442c040390003401074aa0013070a40b035940e9507c3c0350204009050411b650840c51140f40100103003c0413a900000341c81c1994000c499040d60b030070000001988a11a00c00e05e004070303008240b1200c081c400c00390312000044140400410800f5151103089040b480381c107600605442c04418070404441203141c00c2d209021b15140018a0140c50350001807543e00112031001c024400000d50294141c1d00d4001c01105a90455001741081201c1c0e941001982060007041c030255039485c0c0d00303600c1900304c146400003480e03908000c0140034415030000351078100726a002d0b0058403600704e0005041741314907015074507442c46003100300c561004007034624201402041d090f64061011320018609804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 122685620 1250 122684370 122684383
    0x1a0601050712083111030109170a09050901080105010e0112050d080c0f070606140102070308123106050609011a030a0207050601080a05010c0c0308070e04060807090c031802010519030e 81
    0x144c00041c00034000b80c5400d07250501e500440d68001e905040c080d000091000550142d1884520211625841e070004100c40311911580a036038040c2d40c0c1c40002504a80c10352180341038580010b0644c09a07a204c43d10a62803810317080e00103046501155a000302c50344942601c40d001804c445007503180c8640d006420360345170025442601c0207940c44800b0003c00710040e841880c0c85030280040c204070b900d9920b0340c850901803035024407695850000041d0090140c0484107604520743c08000b000720300d041122200040001c1000ca03070301171800010a00c1ca190201d1040d04030b9500380c084010030400826101c065410141507148069001d02260300016824040c0701d000c3c014141c002c1c100000541031690960320603060800500070003101c12000300c0c0c0e00c003401030360129050030515140b00f80080410010501a4010f0000e0b0080d030030045066003480d002450183c05c0c50382d0034400d0407968220700c1003881024038000c3c08600300300302c0b00d000c501072181080e600321400d0400080c0c8041d0098543e08266 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 122686870 1250 122685620 122685691
    0xa0903050d050a0206091204060807020a050a08040806240d02011106070f0906050403230f0106080c1203040b04141305100906060509010207230303071a060105071208 73
    0x50000c5450f2104603030401005520411500041110b18001003090000d13120303500400007000b08140006940718020008650600d1340401100c85076a6681040340240d0494041c24405014100120b0344c1c00d054210b20380940c0400c4840d60780303c0d081007002c00003100107105089051010180c998000b01e101444074510482c0591511702c1610007c00009103101c0b1550014020303c00103110a1000c40c2c00001e883c10343c10030b101c00050314089030700200c529060f03645540020075800c0c010007080700d4002103161204000203441c3c0b842c01006180c04140c803030007180500c44a14034103000400100755801c00205106101800800300c0240d1100c0c1181618401c60700740000112103101040740641c640b1604c00101719900d89281450b031460f0000b502c9401c0ca11510901c4490341450340000902d04154200440c401000c0303d95940e89894084c40125204401040304000d50000400c41d5014208031000d0311340c00341e8004c014008202e426580d800001c2d00103482c40c01001c19080c1c0c06100b411800c229038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 122688120 1250 122686870 122686877
    0x20a09050409060609050105120307060921020c0916080c0d020c0d02070812030106081302031f060f1a0703110304030b010303032c1e19140d051206060a0903050d 71
    0x49040005d40c40c1582c906130f010034085e840500c40c104001d140441a55000c9a22000106000340513051901c034600026586140298090016030500f44d00004c6409a21401740d078030301c64035925581103001e03280048140070040b0303550301d00040c00c0d084200014113040c440514010f0401c90420307240c1d0720f00803038404a20096845240c090021500802030560100116200750b8550340c1441c5005080a10152101c4103031031044804200715078041c40f4a402c4070a2a900040c0c4401202e800140a41828414898181c402030804215000c007401040064261624024504840c59a04079142c1002e40c1e0603162174003061101100081c0203008a0f8000e5000390b401040b04039101e251003121411a0302d2010002c50180f0340032400c14400b04009485281500c070b900200010054141c0c20700311041c1d0120b60001c0100b60040c10403019607945581c8018220407240c140c01c030741c00140c46a00c100c8015050046510700080c465140000080040d24518a040c80e2000da480d5101c2d85800310110800020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 122689370 1250 122688120 122688131
    0x50f1209010c020610090f1112071205010b07020607021318020a170304051003020f030a051906051e030724110102041a0d0906050a061703120a020903070308030a1a1f03020a0905040906 81
    0x142c0d9002f04c5000103580005d400300059454412000130301d201e0071600038040c0c040411508103564401018003614050070905004c05010b04414444d48100628128401c60b9459070100d003c940781ca4201581c001c01500079403410303052008010004c904407085d0b900b0150200300d440e402c019a0405075001c0d03030b40c00d030001c122410030300d03c004004021082e035032032100d2804a04001c039590343c8018000003c3d0103082081200c071200003190400400d03410040600c188124550102503218000881300920366407450920380a8008050a034803492140b4100d01585241c2e401c0d40c1080140104000b007440c13540003075005400d9850100b596000ca030240e2640c1da4070341d405c100c20802e840404101641d51b1000d1803a00e000a03070780042100c0041c01c0b040c282c0f1741c0411540b040d03031410401100a150010b880e1074981c606107000d076015100c0003c1c100e110080e03002d800c4c0418204001d000c6560301d5a103541c2c0c2c0840c494002c0481c0250040c81c420810418604030014658980e40304201c4614041c0c04003080c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 122690620 1250 122689370 122689381
    0x20306040518060703150801050f0402031c08010e060a17010b0a0b07050604080c15090d0210060b0712021608100c080c0301030b07050f1209010c020610090f1112 71
    0x49a60040040e00c5418085000720038810001c0f0f456035010015080000d9114a130444005c00800b0070b80040c40d481d80b8041c18024041c48038190584954801c40444280c0103200c051703541d40092180d0714002259401c00103210540480d854a070740008041c0c50040a05d1fa035003149000c40440640c40e01d06079640d0341c1344c0790710781c03d00150032405441442010780c50301e5103541d0b446079070b400c0c000d101400300d0001141c400c008040070301c07868044050244481031607003032812030241c40715460000d0f07401603c07865624060f4030403140614421141d074518100d0a01860351101242c2e0054000700b1001c600400d044054000b40c03050981c4040c0051000809103c2c400031114000c4401c5486680e0034402d400342040303200040c800460781520f038001000b4880e034540171000d5406009041d0015102e100c003182e11500001c034042120b1045000100a0003505d035651380036611524152502c0d5841c0500003018042d904144c2c20690034088014400114402c3c0d41001c01d8840e0030040d00e40300c101f0819000d012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 122691870 1250 122690620 122690629
    0x11b081509070207050613080106030b150f010e0d1103060705090301140f0103030c170304030e041503120507050c131e020a09050108060607060912030c08090a021903060f020306 78
    0x3402000152854501402e0280b4003950790444c0f8450540301d010005004842409820341c124001d1284200902c24543c480c64502c071840f408491454903101208031a680c00d2400d07014034102c112042c0c43d44000c2071720f00c2090002151460b075041c0c500751400c1100d000b058504000700361161415544254850103d94205800d450302c610740a014991503000b03004100460440980c1102d6140c1082414540c007480d104000324205555400c110780d0120800c400e141d0000b221114503001160100100c0b5410401c454811016000140c06200300103c0b41c08414050802410b0203401041141c1c07006404030002100000c0314a1446034040e100c5c0c04843c810034000403d20350b60020404158203114447c48000e0900b00309100d610304020340000440c400ea00e0300402c81d0030700d50b082a814000000340e4140300c40d003c414211203100192a041c0101e0040d071040b44038a00444040b005003044070708903000c000c003181c1c071080300300c04006180e800040090355511416041400c254005601c03840d0030300802 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 122693120 1250 122691870 122691901
    0x409020a0b03060f0108011401110f01020a020307060e060720030d05090a0b07020d0203030c1305030303070216051c02040f0608150114010509060a18081f0507170103060e011b08 78
    0x745c140510034006002c0805281c8408030784d82000e01c1c03c5054403280005162400d000445008501e510005011000613800302c01003000700d00a800c2480901280c0461a596650468009000440c00004020030141d4240e174550307841c031081c048070306160503401840215002500c060003194441d941c801c04000d14901540ea200405d4000751150403105c40d0069100e1100401d002c91410700050032142d26001300b003500000e000c1c05401c898591a00ba400070b50b6032003c1424801c20400414000225413404900d10144100c951480071b403204000d9080c40054a01e11010460701612407401003400c1c00100040e504241d008460984654034110030302130182d01c0070380c0490401c00d04000c8a071aa8a034030003180c0ca240c0003480e080074100701c041d40210b0030b8505c5400048040c0101d01d109801d041303071541003148001d180c40041000b61282c10b0140c541c941d4070710302890302d0080100101302040060344501a048440c40010501e81030f503089140b4004220040000031850036014096614a0780508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 122694370 1250 122693120 122693149
    0x90b0f0a050604060809010609140414070602030a05090303040308132102090f0a09050303130c0f0501020d050a02030f0f0c06071814010905030f0327011d0409020a0b0306 75
    0x414008a0420020803210f2140e40240414007400703030085001d986007540710310b0082c80700b0802001034130f8005c202c00201100030b07034095840c89620500e0b05103144020070310740b00b01c88554008510380704600d00252416040411400c1e8107004c181300010105206000602400081d01d01e401d50441c02c000828001038403003400154982ca40307041500040c1c41e02e20015401111045140b69140d80c0e1084010240002940040031800040300b40035034881ca0081a20b091071107140c40c000015211500c0c0c03410440248143c900507444900d00c0c0e10a20702a00043c03a00748013900c1501d00c2c101810090f031083d9400600600c48140c400203810724510014000c054010030b00b49010204505440754428440344580610001c1c0f46d610200000c00d60b0141c035a0100424000e826212064040003410b612178200ca0402c003610004401840842009940900700c13940d016114042d8006440504440000c4030300303145a0010354421800b0096074a9820441c0100500000c0303c0c1c0e00d152203018401282c198a51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 122695620 1250 122694370 122694379
    0x15090203060312030c091f030b12060408130f03110901080c010903080a020c150406020601060c170a1202130519031106030601051c1b091d090f07090b0f 67
    0x7031190a0ba0701003100c0020720080c00b055501d03521890502c2c1c4461180c100e07240ea016000a10a10380744480c10b1000b21802030320b03181082620416400d1200765105040044d031182c01000004000400090181c503032000d03440b5a51a55075111540c0341034812054109a0300c890914500c40b15070326001d140366000d4410000a041ca00c1d0505001802d52603050000400b209004650407503440d208001182c0c0d0380c90010107035402c5440e0480c948001303030f0240c01a01c0041c09404000300e07413a07004801d000c1c41d155001c011080700929000907a12203420880e16001000702c00c600140c0e0458003400501071219441d140c41c0403140c688000c010f441601141c01c2e00ea210103001c000c0022450340380c1503568010b000e59501d48e5030343e180f0004803080d201d0030741e6001d00d0712940a0712400d084c08a500c5260381822600c003020414266070342c142e54115003803040ba540401c80350701c0c0c1f64228031f4444040b80c004030224101d6040c00780a01b80c05040c80002c0d000b581d40c907a500c41141ca200d242425549441071002e1f00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 122696870 1250 122695620 122695627
    0xe0a090209070507021014070213022a0c0105040303050a08040f02150309060105030d021009050705060f04060e010201050c03071b150f0b0a050105120c0706051003030e01082502100f150902 83
    0x46401c03607e4000c4000c003074401c10300c1c00101c503961070042d01119400302e25154803800b400720100e0481e0f1001c5043c4440380c1c40c1d102d2246404181e5003e0b4040b5420303207415448041c2408500307a0100c820303990060044484d04000050480182c07140704035000c003000300e0042140c40303152010b065807800030140e01c483d10035400b01c005462086c0d004500e0240302500c2400104070b99a0b44e04103903240003020b9200640103c1e00140201e610b005400141081d0741d60f6550f1107208003210ba004900381c41c803d031040b0717041180820110700490f001c1d0356030100d44030f010404240f407524980c4400501300c0c1828039280c240340e254414034422104600c510040030408454a02816041c100020482c0c011500740e10410b52052000c00c20b036013007960540b9440c1c3d51008041c8641d262902c2c01c4520382d192444120080348881342c00c2c040940c01031050500c076014001911650506509400c6025000130345040198020701c4d410820740c2e0f0040c0120400e00a03e17060104103074440450185030f103945617000c40b541c0d03031051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 122698120 1250 122696870 122696897
    0x60708100501110c0a06020304030b07050406120b0301090212030a0906090b03180a08070503070c05120c060d0b0a09141b0901030b0a0506030f0a050c0c070e0a0902090705070210 78
    0x806090a952007840c0040c820360088640c5450041042c141c139501c58005100040e181c1c1d800402401074034807482840015448426051310b1a00590064030081250102005110300d02a4448a016400140003050401c820380109580740844078005005800000c0d82da8006034022809400424461500c4901d0a19183c0001c0040c08007901c218101d00f149003e03800507134420451141c50b1034110030f00c2550382007246040c55403580021070844190106030380c002903d2405110030081c2001c1c02001d891710100d81d50030088682d0000c1c011034034040d0b8500c8801c4007910350f0019000a8100c203100010103914041000101800040407003c1d040816040000e500d00c00754240c4205080a080c0810b6000320080000d84208681e042513400c56004010050400f290070103150007644060000c01060301d030908208260301c0786281c0e010459201581c20007081d1401602280c3c010059200086c82c8281c0d0341c0012144030090ba0f0b1580024400301381c50b0154a4000300302e0042c00d9032401d2050000315030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 122699370 1250 122698120 122698141
    0x30702090a0c020a080408071802091c0201140d091502130e070c080307031b02010b01020a02010e061324020307030f0e0d050f01020a090905040b13050c03030f0a02060708 75
    0x30881c144080e00d598403980c41600810030410704641c420f0450380c40d42d8403899683da44269611660902d850b078880a030305845400c2c82156405040130b06440b0161103101a8400a10f000d403004034104500c0d2012040f8808043c005003070740c00e03007100000c00c0c403644a0420070b005040d6650581105481000b00c0c0c00341881800d01c840c2122100c203001d03003096451000030f0320440c01c00840071700040ba00008000405515500007d2286c02c1d01c0da4001d81174a0380103040742210102902c280c09170340b042d00140c01542c000c40d4031030041440100100d00e81490303a04c4000030041239a100c603007400c40c0e0700705030365810b440304d1052a8007416900c011030038403a060f20001c0000d044040b580081c01504ca4501081ea254051020700d403d03000022203101e480664040d500035405100d003000003805800e4007003024040c03401114080c80d04203803210780d035480d9415904607240c40342a0407034480c86801034244103624188050840c0d494604682512a071000d0310203810030b00018468170420003400104524aa003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 122700620 1250 122699370 122699389
    0x1315110f0d0804120201060302040903030e150601050d02130b120103020109060e03070902160506072105090303070e18100e010801020306090a0f091b09060b18010c0201030f150302040c02030702 85
    0x10860307410f481c50003113564260300405035a04065001070800d1510b00506d501600b10581200401c8210380c2c056421402d60368240200707444150004004000454121400e5009445c4141c0c0907510040361551f42d20050702c40e64060b2420b5000e18488000420039036030800c440e0303c01004941046034074204079000198480009010340b14101da07000c145011041d050100007190b042e030001c125052420610030290a8840201c4c4444289044680358801c000081c01450302a2480400031419921056001d0341c1002c0701019468004021100d503032441480e01d03521901402c0141c591038122801c0000e0b901e401c0074160003580c4541c1c010814042240c0341c000341242e01c5484204000b07054600c2151400c09490fa0354000303403081c0268070f030064007030980f140ca00c811903800d20400c000c0107541d00c800d03100a0107585046149070500c8651041035502a0982d8048180b0514000400f030384a107400d07504442c0700c01c0c00300611400600092046003054851450712800d507000071403c0500c1c40d80010319101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 122701870 1250 122700620 122700623
    0x6060806070f0c0312090506100501050c1c0c050d031b090b090d06020f18040e0703170f0d05010602030703021005090703020d05030904360f081315110f0d0804 70
    0x3c0c0070603070030506102d0b83d480e803107a00054200380200c0302a814a287c2c3c4146c00d4a40300011050844002480e60280040f0390880e00c100c1c1c007404c7d03201c06a03032102600c001800d4000007403041d107440100c001003050040840000b001c3d140003641c42c043c1c00240c0000d28900740e400d81407143c080d1060050903481000d60355092000c8403e180000e18a2414401900440c499001c504c4c0c804100342c4402d0507032551a90510030b00b030768204507000d081c042e2903603110480d00c005030000c410440a0400100c00c04000c2c4001e17944140e40764a0203c0980c50002103a000742d00c62001a00081217240030035505001401c08414008400e1044d4200620620389814039444020301c501f440c00d400c2c808210003403060b10200d94000380100a90015251000740d55020520940203400c820b109210000290800d81400c49800c0040e601d00001c040d41d40c00c072154821490502c000440b00da0018801c0b592800886030300b429541c1d0005503685408080d0f03d00400904010020b400003481d4502c0a03900100c5290b009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 122703120 1250 122701870 122701877
    0x20a030311030708190f0e07050301051509010303121b090314010c0503011e080601030605073209120106031b0e0c0a050a050c01050406050103020a1502150612070f0306060806070f 79
    0x1315255682d0f00c020852111070281c12030900c40070320107424001c141c8c0c40469405070b009220307555401c546500c0b086003205225501072030480c0188046031042c0d46034012408820000075000405000701481001c001c007103500000c0072040107104110b8120407291807038010030024030045ea510200a480c1e4001401450aa030f0b03003034903400c8111180b40c507440b03004080280a0703d6480d612801c1032009024110f800101098030340d42200c600c0c01900300c500c84461030b80503c56880707511051408aa0380d20200b0543d0340050b030100c00e440000d80a00c41d0328021440741d1105100747c01d0901c1c1200b420035942d070001d22500d10100801440d4132250741200c00306101d914005d41d4030300d10004191000d01664618012940c070301002c000c100038850f406a03041c0e034000c0b200b40d407040c3d640c1c1808640c103443ca1591240160842c1580e2040c4965014406402c050018143d0a9500111000038070301251a070054041d038481d52410000c0c06112b200b01c8010300440d0000c4d02c041c0c540340c200075100301107440040042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 122704370 1250 122703120 122703151
    0x304020a140d020a080303010504110a0503010b03060109170a060c0306060e060706090c0e01080c060913150803070b15030a0b04080f0412060f0e010618020903030712020a030311030708 81
    0x440d642c012000c05801d0b4010800d00300c1c0c6440300f8415560350424081c03140500d2800d00c084480001da40c068409070200c690354146140c0c00c0010081d00c5410240125050140d0360b0004a50810081c13541308030340603010300500c42d10000d42003203019a0710b0500311100b411300c0c100d1b041c40019403110000240c0501590310594618a616000c4000d00307002c5009084000c0302e40f0301081001d00101342c00d04940c0070748211608068648100300e01440345144459005a45c0d2080344100c181a8000c29207181e008400c40c0801d0b80d84109035405c5610002086404e0607183c020000d1881d0004c20483c1141002d80080c5100040da949520040002520240c80030038041003d09494025000721000f80986032004520300f031861901c2000340101c0409064101e0611702c10860f0b0400510480c000c403410480e44184025075400d105000350712444200741c060000f000014007003450440060381c02c068603401000c880380b440c01d00a044820032008003020280c1002070000c620340c400c40c000d40224401031741100c07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 122705620 1250 122704370 122704409
    0xc08060f06071a09070e0105031b0d03020f010204150314090a030507081603080106110f060105010e04090f031e0302041404020c011e0c020c010206010323070e0a02030412050304020a 80
    0x341c1804280c00c039580f0402c040c040181050001c120401150314540c116441640c0301d008142c3c540401d090141d0407409000d404000d2843c141c0c00e152240c60003070050382c6032400f0645c4c6185c04ea03030064002c020349080d920b5403020442e0381840750394084892401e412900e402c00b84070340c0d901e0341e02d0500b01804000c000704200080c01019011038604880ea1401800001020318003c1c1034544248103610104070400c4000b20742c501d00cc61200c091340012000b5200c142c1c01c210040d00c0742c1e4400a0255003203541c4a0310600000d9040000d071648a0190b214400e0b0b050402111204502c21944800c04250040c0010030041e8036100202811b550211000341c2c0325101c140510340141b10f0800ca003c81c15002e9029000500d140e40e10415058905900f590710000c180030059035149804c3c4001445404d10189824030145051244e00110200e0000ea07001103075990a05999440c0960300551441e9001080c041004405281c2074242000c506000742140b609400090740d1440d0703032181703400f2103605080100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 122706870 1250 122705620 122705633
    0x1103070221030c060412080601170c0408060f09010e0708030405010c0807051c02070801180b04060605060c0706080114010e090405250e07140415050f1207030c08060f0607 75
    0x86a100201c1202d403a01c00082815680e5038090b41c00703486e0b00b09200103079540e0b54850300110b841000107845415002a070503525004e103210042c0741c184e41000501020483c1401400b60340e000360344005c4103100c00c2c2041301059007100e9a020b003104160348030000030024410080241e40031510700342400e2044c00c1850904d01464490070900500c24012620845440c0c49100703081c001c5924142c2c2103031402d40c2c6680c801801c03944403c1456207803902d41c8010100044100094a9000340308902c0820f14550f101e01040f259044103c01c941550480c0c001480001da2089002c2c1c01000190b14101140300000700103003018410b030102e01d021700360680019003800b504201040c041d1250b0015200c4d4515481c1c0140382c10089030088541c0c4007801030105541e14462148656140d07004d14066182602c4c06c944940540c088041d000b05000c821b000783e140d019142c40182c10116944407020301a4504030f5801412034080049120511130b40d10240a80f5071184054072110359000c0d00ca0f2941c5156504101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 122708120 1250 122706870 122706919
    0xf0911190905040c0e070201050f0f060a05120a0b07120f02090d0f0302070f1404050a200d06050904030305070f0c03021917071b0806060102031614010603080a0f11030702 75
    0x5c000c1d1440803082c810031940c154007141c03107003001640c0c980007034548180418000ba400d903032282d401903c12600344803d10f04001d02c01150380104044038051003c40e03030740c00101002242c403003000c2188400701080b1800c0c24010401c08000e1080218a4210030f24000b500300303090400003805203001c4a1344501014000c01601010b0702903103814081365503403801001d6144400000d103d0140d8181000300b040c40d1818050b041c0c000c400746040117405040c403080d005032600142104280c940e1030380c60004441d01c030302c48030a0145000350b0b80401c1d5898160b5010b003407031a6990342c0c9410004c101307042d240401c1d0302141e003513111120074031040c01c595405e0900f1454a10a215080f0346098001020420481d4451409490800d840c1b08001543d690b1640a91601c2c0110b4545000d82c100301700400c0c000040d0669844030b10321030074912070031401c01d10a817402c586141e00100c0b00079200085024607113411120001013090350b0701d00f0255044003001c03181c1e201d0003000b100078014002a0800601240d100c1c009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 122709370 1250 122708120 122708129
    0x3060f0108070630020405010e03150a0e1006060c0605011d010b030a0608100209040e06070c020f06070f060e060603030408071e1a030f010b0405180901020d0f0911190905040c 77
    0x40c2c01c13403114101068402588544120350100c0d1100d481c013480da090104a10811032060184400c80e0b50310841500d001d481e00c01d1003070348140185003614012030001d104220162180b9600c0004000007840c08208485068004e0340d201720f222800103122200d4490b8a505690b000224035449840d1b00d070404018002035000001301c0e025001030010020305613805000d01c001c0884060000ca11819011034540805076903020000381908290400b508048032003840c100c4019060310300c0c00d1020380b00c0741080d80717500c4421a88162200d0400159110810045801c00400c81c05107203460314015125a82d2940c510903080081c1050703c0503070030385003800700c03880042055101207c41c41150041c80f5949030300403a441c0007815801800810307841c1020007520141d45010b4014074101f2590646000700e004020130112003136401f0001041442c00c54040c100400712180000305881203180350195901c0034010100e0300034001d5900d020b03a801ca111082004580d444100010203445d0350800811280082c0c02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 122710620 1250 122709370 122709437
    0x23040b04090f0c06210209061309020d05011a07110f090403050703091a04030206070203100e070305060f100e040f020901060e01030507020d140d140c040503060f01080706 75
    0x8036414024000080107105109a40c8641c815413900d906444000960011050b0702c443d400364020450f00c55401007200703550040100781405201101e03840d00f2115908800c030490b8000c18a100412030074018a8050104200c0c41080d000d1744403040b003a203000300c0d08080c02d0100100080005c0d61500303022071302c40082c0500300b10060b11300b0381000380140d8040c0004500244080b080010390320100d605620001144501030307032500d840c6030200700380794001da0b8085e6494051060b60038410320f00c0703100d00386840e45c1d50303809001000d00d942401030600800511503090000d00e402000b40008a20380b140e41981d041c1d847c03e49c0c003a111802c215500300c2560301c0094010f4564000820180c0d00000c21001806003641e0a04ca01e980d012001c036166107c11264101045040032074626500c905d5000d011039070405940054070355042400b410340c0c0076050740d51003501c0b980000c00380154242400b100380c0c8084041c2c000c2c0c0d502c0d49040001c56641070b8501c100c90400541110f44404403811040c1e80152010004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 122711870 1250 122710620 122710631
    0x1002091801060206090706080712020a02030c1b100516020402070312050709150c0506010b0a12112a1b12060405010606020f0109170307030902060304052523040b04 72
    0x58060750302c0c6001d8170000828410000c002440c244203040c1103108188a43d034000b800d0081083c041e0294009c10401c1007580014802800300c80403c1010113401032100c00c401c950030042609201c5000200c12080b004c01004101808107203200140140800754140c3c1c00580d01e00b1241400c039141d416184074462040e06140034400c0b01c0307a00803544420340d083c4000003401c0c88034400054541120000e4010a240c2140f00104103080341710016000b0031400742801154840540c0c071210440d0360400c00440001c40200e951a82c0ba01c0c05014010580c28480282c8071002010700081c1e903e0300e4010003648200070f6101c112803240c981482e03040807122030804807540c0b42030519000d800791800e401007a0040c460500340c4a043c040500501e074455030800810554020f000c110004241e000a041e84141901d0300d034500e0058491200a51285024001815070302401d000c0800c4450310484000c0c846407842c1c0c8042c0021516546400444000460b0740da180340c1740000883c001c0c114001c43e495100c0e2400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 122713120 1250 122711870 122711879
    0x5180307111c060f06171f15060801080106050609010c060c020c0402030108010509010509010b0d03030504110307081b1e09060f13020d0e150408450a0302031002091801 74
    0x180c2040394201600c4006000c2d950711802800b1042030692000c041903445400040d051000c042c070083d601f0b80081c1c4003c120b121402c0d120001e03c2059500c80c000089044004001e898401c0c80740a019003000c603944c614000c0c501000a180a002110252109641d03901400415008000e0342e4181030f800342040d03440391b9442d400ba500a11080718140f00950030900001d04110041c4540103070000010b100b8802c859654070120001c01c00208101c505030701410f1003070180e43d81080402c0082c03848000900c40e03481d08138001022108082039090140700c0880500b2200d0200070007000c2225801d503900310b66980da11000481c0309807407101c080e8110409005001d1f031194590020000b6008428007800485040940070b0381d10301099505a01082c0c90303002190009903000010890700c85180c14003800a02e042450680300210351514160846605141c88495010b00c001d40101080488040c3c00036441e5401107600d610321403503030701d072081d6001403440c0303895407611a04521741c035043c0c1c6810070a45c0c45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 122714370 1250 122713120 122713133
    0x4050c07060e0c0105030a020c0106050301050a090c06020a0302030304240608010c020106050f0a03020907260711011b05030a02120c0912031c020703090305061003020405180307111c 80
    0xc10251119401c042c450480c2000000300c00c00402070603540c840c030390354840c0b41d00e10080d0001018410705549440380000c41d642c090003500c1c0030f04103000001498034000c0c40d180c801629664451019900407441e0079004c00d03004416a43d03c40e4000e14502403609109a03540020109c1880003020f49140030130124080c1415480200c0100d904d400821080b41c40701c2c2006204881800901d40c84120b41c2010701c0142403c840041d0842e01c9400d10074010204c0c182c3c40d8441c2c2d2040c82c0c110411003040340030421a99030110302c298020003c07030f0003044420204001d81484040246144061000000100d07088221a034101c0e00c10800c180b0103c415401c0209010000340c4c441444948103803945c40e039220034203001108881141b952842d0703203443d0f41f1300491144080c0d002090241c052280c1e0540c00004507009100342841105151000d000030390442c8100001c4400142c6103289a103103411001c81d58480020855110381e1f0011414804001c5480c00900c00c01d6005000907070002c862040300c0204010f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 122715620 1250 122714370 122714377
    0x616080d05010e07030e0a02041107150c0207120209070e01021606050409050606040608011202040f0608030318030316080a0615021609050609011404110c0c19080c1201020904050c 79
    0x80030b0f0030b80c560b01e88815500310196001e4550341c24164118024002c014a0a5840051180000241d06040c28450b4890043e5691a910101c610302c0c1c569004100c02035040c4501005460400c0d207525007052244c02145005200800000a01c031111f0040b12140c3c3c001c0001500324280a00340016054441c50010aa80c10600c2246007007420035000c21507904c3c10f58143d81c00d40d501d0703507110040c83e032904546c045100e4603201d050341c0150352910b40d29450f2900e80940c0e00031b0807440c00150369a0400210b0196054511400020359810a0082c009002c1030544003030f030345032154940103680b9201e40f54014020045c170b910109071054426840880d8a401082442031401c0207000844860b950b00740b54000e40d04221400e81d4002e09403c014001c24420034441141c0041c00352000482c4007002210683c1d030740c4140c107101e80c10740c48800c540703c00c1e140010011602590f00b44140646130300e400300a903914942642010b10490f8151980ea01c000d000354142e03506214000c0c014030843c14007210480c01d5a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 122716870 1250 122715620 122715629
    0x11030c070606050919140402060a141306081e061c080d05010f1e06090504050c19081009061d060111011103070906030203070f030e07080604140c0d0b060616080d0501 73
    0x203007049480805121b1141c0c0c0e07144556005043c00b4500101050101d4840c180e102c0c862003400c4090051040e00c0c441c004000014242c1c0792284529401e0182c00044103405994044203a106041c0c104000c80d140c03c0810f800c81401c402c2c0414401409240c80d4880d4080c229800c5101898607000040002d00101e202040702c000c1c409040e40407d019050b00d4010141f4010100403900180d81040740d402e1941c1b295502c442c40020080c01e10001c07084a1203500064050790380050406018440003ca072525a00001e00400e01e04000481c50801c030440101202ea1207018104035400000b0820317400307020440c2000c1d40d20002040415100c4410100c141c009880502c0003810321100486c8460091007203d00503204c86d00c5941414518000450180101c11407484850003107210015414030208075150017a4811103c01d10340e0f11007841c1d0f445c540b0b002e141029200d500c1e10950800810260341140e600301006540c500d90b10b030120410280b8000414074003c14403140000d03581c03a01c5078154081c0c1d060b00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 122718120 1250 122716870 122716921
    0x9040603061b111203011e080105040c0905060d110409030c051c080f061c050708150108010f06050a090f0b0603070f02010605040b031509010b100513060311030c0706060509 76
    0x10340300b610460b604d900000d139102998408100502907420002c0201c100b55004400303051090380c85859050a6400a840c12604079070820018000507031350780207107948003c00356600380224049032121548000c00403121409070750f664440000341446100381441a50f000ba0072544000e012040d02d0500300a030081c02400a00740b0000b0441d482a00c2c000c140c01148010000491a07014010740341c2c550386814030841d0f10744100140050300d11418851680700c0b442e5950010400d42c07400001700c2c02c0d14400703000d185101e850100140059581c08c2d80003001c0c1d500000300000e00d080380d00ada0f90000c2c000c1c103800c6540060080108000075500800340004c210480d4002e100c01e41c0d544051000380e400d030740440d0740d15402c14059500424508200c0641c003000250002c41e009000341c01040c0400c0484400200041d00011900340c000d07048003410008040601d010001311040c0c0f4040c0c0a50301003e0460480c040300050f4070301c28010160000340290400a000740c8090410f80b6845200109010204050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 122719370 1250 122718120 122718137
    0xd05180a121b050a0303030b0d020a0f06020c060406050f1c06030606060e040506090c0d06050d0804051906120c0e041104050a0807080303070f020f060103030f0e030a031409040603061b 81
    0x520b03040b20080202c5801609100a56083d0351713050b00501907203400190811241d4803060056502d0811860050000f801e908559030300b04403000b414150a43c072410301840c4104020403155501000b140c4654807408100768980e409020000c11104141400e8101c0d9400c09401105000b6541d200b64101c40b020317241e02c44000c281c08144810b907042244c1c015841100907001403440b172146801000380e600c2e0014001441c030f0302d6400040b140f0559200030345107048003140502103805c10030b00c8100300c881d4080c0d909945614181000f072080003e1f465000d542a280c80d944000705000b03204e580c1440c0030080003403140d214030b125800794981191003000c0c0702d00c0444034001566100404c620f0305485984003d54a150b03503444050310b0051a10800204510610022410345001401000d002e103201c0c1d6541e156050040b840105001d18071b000c401c0c400c1d0010515000081d4000d0800100b084103001440e44661a420001d401030425510151040e030901844202a0703070304074092600c011840d00d4a118 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 122720620 1250 122719370 122719403
    0x504060b040506041e0506150c060901180f080d06090f05060f010504050325050607060c1d1309031b050c04051303080c0903030f18090106020d020d05180a12 69
    0x203907002d0341c0341c0075030390010400c2e00d40c400038141c6c125076445040078007012400c0e40400040c030603982c80b001d83d60f12660800014070010b203101380030704071000d0010030800b01c2c0305101d51104092640174000c014508031001601440c2d144c4250044801014902010004950094450b03030191500301c1e20941b003a0000076401c00f0541c01402600d00b170301c1c0090000d100b429038401e050084110f4101c0480c40404060b1000a03050781d840d4000d00d84144100000b09200032130b524040c013150300b84583c441c060b0314061849842a200c9024007000100000d0001c6403241480c2001c0c0c0701c85900740031885541d42c2c28a0b0000502000003510782e400c58040e10f007081070703030b541c0c000303410300d00c03484000003030004070204042920125000d000e0441808010203803842d00d007201c443c4c03620302e5000c07401410070b05030328030241d400b1843c040c00e001d4010003150020300007807100020700a40320401e40304107100b44800441d941e50040035090160300d800300b0150521180703545aa2460240d80c400000c101c401d41d81e80b150359003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 122721870 1250 122720620 122720629
    0x14041b0602030a02150a0905010204030320011a04051f1707080316030f051c0b090711030307030c0207261c020307031b02040908030105041404330504060b040506 71
    0x1440f094496001d40039200c00c042e960040c0010103003090a485469450030310104800f0300c0144015403180d00d40700300582040c1c480700381e61400b810001381c459142c2400b8800004040c0e00d0318035001d200319000503155480d2090305c41d028040605100422020920102d0386040a03403c1c1818031407500304840c85140c0c0c2d5800541c0d00d103d010414060304000c1302c03041000900860182540c0800390400b1030901d0808010f00c02040060781c4600c00c82611079040c4252410032540e00c1e600b03c3e034075181008550440c02c018940d04c0c0300150078a0101650388808440142c824040280030784200c00400e4075241c20207030702010021200c81c0c0c548003400348108003244024203c041487c0c9100a4003c3d60800d04181c6094900e000d40124413260300000101800040c1d855100b0071005030310070780310075072694105001c1c04200c80324030038084440c8001d40309000104007460b03804221540300d10030305c82e003042d0705454800149a0401c48011081d09103000e1004103c01c64115418810003036804000913580c5d00d0400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 122723120 1250 122721870 122721877
    0x30c02011103160509011707050304030e030c010c031206030b150916170a060801020d0c080703110412060e10050402030c060a050a0e0307150203030f070c0209071214041b060203 78
    0xa05000c10b0303444180f52200c3c020400340030300c8181418900050039000d0400c40360700c141100d124000580010400042641120480d503400c1e005500408074418802c001a0040c2d02c61840501804901d580e508110b0016801c0380024590191030242d46040901c0603091100c2c514134014403c82c003c40001e4626412090040051505a61295444c82c1c9804c0550003910016041c01407513078441d1000b0039113a009000031b08400381e034060b00089100444d140240000b0f4041c1051040509040b85951900a20f0094609503141c0c003840c4403580c800c61400c2c0001b802d050329081004e01495080c001032000d2980b081e44103a000b50240d8001e4002d0004001c2c0520410400e480802c82c01e02452140754843e18000014507000313405c60300704c142c8444141d001094840c0d4070317000581c40042004000160f5401c80e5401140f181414038121100d60f0001c1c80b0500300603c68010081000b1800c581810030360080681025102219052030410f403c1c21001940013201d0904044240c17800001c0c0107100100f00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 122724370 1250 122723120 122723131
    0x5030a0b010303030f090b010311030d140406052808091009030c03030b0a030b0c0a030e0106060207030f1b0308040e2401030c0203070501141816151e030c02011103 72
    0x3010681c1c01c42d60280c000b0010361504085159036142020006005000918082c501402020003034010890805151950f0380c0c07100d004001803070700c1c07150b0f88c1c842090030390301680c0c814103200b03842e598901c990a07000d95840359004c600640441101000030340040c00d4500403140b0303100352520407191152034004d5a51400000b8001096803807040b0110b4400d5010080c001c2b4010310314903066642e610380202440060300c400c401d080b80010400707080c1e0f8161180c076401c2c4011400a2194a1410304007940b00c6407184006070030768540490b00c07004c200c1c0d008944044030404481ca4851141c40742840482600300740034041150b4070140200340c0300484102d02e107a0801403030481c0355544408100440c0034000c074010803c1944404d0110400148082c0144548482c20083c030400c103180c240e1681002e440b10602a41c1103400c40d0b08041e1507030380850610016038071811841d0400f10401e600440718500c181020a05800c00701040e428090343c1a0030641c881c2d40640c2c02031002ca112200000520b01c0103684 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 122725620 1250 122724370 122724383
    0x1b0804060806121b0d050a020a0602011a0a050a0b030717130201030c02060415110d050c0a090b0301150807090302031f0b04020f0702041d192102150426120105030a 72
    0x280c03002d00d0907901d8418444e102d0002c3d2500f585003940030270300710071254001c0000350b511400802816000260985006201140c0c01e506052030280801c1c0e91580a014401d0301d403a000000071a0980194020b103c1d00c0000e040d400300380d140240828a40001001080340001d090241c00150719100040301400390b5009000c04461085164054004045004000c803d0000038080b1308440b6408d44101480b9124041c2400d80c0c0e0400b0344001020f43d44150800c4503910780034001480b800485418002482020742000c45180d01e4031070041c2c424491b241d1000354544107007045041034508106c0c1c076503e010054070007803001d40d40c2c0e00d0400091b030040c42070320f201080341030011402600e003940202442d4008000702041c04500081c14500380054040c142a0030112494000b04000e000601805180200135400b0440c41140100030f490303684c0e85a8042c0e2401201d0045814005100030f046c1c580c0701084510f40302c480c5115141217080c3c00901550090b02a0b5400003d15400c0210759070070305590090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 122726870 1250 122725620 122725663
    0x801060914131103010908030105040507020312180a14030703020111250c0302090103230129031f0b03100e030702090a0b091e06010309030806011b080406080612 71
    0x4032810001c2d0822109035103105041c5039149103503c00384110501c09002e2071303242c0d41e00e60510007400250360001c0d211004642c0b00300102c40e413140c5603900e1250019000c0610521408418400a1410440000240161008182013500018004020680382d44079400a115281d20b01b5a61030460140e01d00d001200b56a68940300c0d9850001c00c44003e0207031081d40c0c0d0780c1d0295100e030045032030f083c4240c200b242d800d641070000d60500c00750004030514000c820710090018601c0e1100c100d20300ca03100600504c9000c042515629259000d12983e8003244c5809003884004200c0c039140d81c00741c42c0300042e40d4004e000303811018994003414020704140310b070041c0c02145008403a60074080614802045880300640c1c41c00d03a1105540e55480d03284c01a83c10440c640c1c13540866241800b64248080c21980c14181f4084510001a40207428558072207400d09181f0102d005c0d8451814000b907420390001d000220004002c180c44d50171042640c0142c805543c07a405c2001d41064556444148054140c0c4042000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 122728120 1250 122726870 122726881
    0x6050a0e01092412050c0a080c03010b07060b0112052401090806040b060d0c060905040f090b070e0607020301050412080705130e0c04080d02070501080c0406080c1b0f070801060914 79
    0x1501020f00345445407804500c800b10007102c030b0301121015a07404944110008040000d960b0090300306400004100c03c0d076285501d0918802400e02c2010801401251140c40283e020380c0a55490089a10180030902c06480e2950038120900e45910b004202c0310f280b851091003951044103c101900c05002c0100071684032904c2c1e101021100502096200e4440e0044c0380005000000c0180182176a4540c668560705090800003030f00ca00500a503042450681c440300032400001c04181c1094440c2004801ca40b0f04401140e03241c4540e0304040d40542c2480c0620003003243c0c40c1d83c0c651150b50b09a44508203030700c031040219080c4c4603480203400707030f068030b404148170810740d0002c0c2c42c1d040541c48807243c0c50709030307034210079030030505001030030741c00368000210070012960031080b41a4421601c8108c185441c1c100b91014054000241c542c92200d4400304904000340711110322010b400a4160468a0f202c000080310f941c0c030b40103805521940c0d402c1000001d482c80a60088024130b03100320002c045255510b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 122729370 1250 122728120 122728169
    0x504052805030d0203190305070c0201080601020c3129060403140c030f01020f0a0518030105161101060608071110050903210103020102031c060f06050a0e0109 70
    0x2601801100200d8208006800d960401642d45802c0c6242c01a6071141500c0d83e10012907031041c0203420515040400b000500d0781d0009920b10000e1342400c0441e8961a0180100d103050240b42125420040440545803140c4030654554001208030780f04c40b4002a82c1c2c2c0980c800d50f40303061400c0f08034540d00b100c0491340800381c600b0b11041e540090046d030300709940ca4440c45c448088044c41c0c1022500b014040c00c0301802c0a20140300c8041c0001c0007580390016590b5401c0e00344c4501040013003004000701d442c110f1440661410301e040f0000400a112504180d205803400d612140b0131320300820054110a145408180921000c44000d9121121191340e400307801c0c4c3d00104441c050007000d001d0014030b176021207800c0c0314440c06110004002c54030740d149082d13003044000c43d5268000f1101c01c1c040c01000180e07400230888003541011640c0c0c140da00076122250014140940200302c0340c1a1420002c0380d09580000a403003403d036550781e80e0840d811a08015140c100031401801515080321845000d040709 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 122730620 1250 122729370 122729419
    0x304030201140f01061b0b19020705120c0d0306030812090f0601030b01060e040509070b0702060d0608010906050a1803030e03160c1508090d030f09020904060608010c050405 76
    0x34000410301d19040d000614840108460b02d248000d1008010301c512540303c800e001c4030301c0d01c2c0b81c5441c883c0051030f00c5860f01c00d03400800b0001c2541c03502c0c0c0c03a01c00c24586034050399603441d48042201d2220303d00c07000321002d94100703545e4407007240324003604407440501c00d000e8401101e8108030b8052404034802064500140000c0140c0c2681c820000c5150b00380ca0200a460700075070041601e42400d50503c0c500410307000749402d0152040b130400060100c140d101242c800129400f10100799555044d500c042081070150041c000002454070f400010048d40c103401c01a845842984100415900d03912194100ea40280d1111410b420b20501d20700000d00070b5211500700301e003190131a030030309502462460764900c075407000b1649541135110030400d8a48510801a442c00c1b00e090010151030050086655441c1800584003091307120b401103d00c006465001000c4d107031700a0b1110680b80351500303041010307180320301c22400e69629001e40c8202c2c90f8440c0c1e00303440582c2c030001c003800c000c4c41282d050340c1007849 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 122731870 1250 122730620 122730623
    0x129041404090b1609151205090c03100f0b040e0c19091508061608040f02220e0f0303060604060c0809040504031205090c060906070c0803030108010204090e15010b0304 74
    0xb0303500c1d044403000c80d40481d0303140d21550f8803c40010440084080c02001c42e40c0e281e00a00200e4500640003480320f800034891a075951810f500010240e4a5520141c0361a061030307641d5406000b06810030b200040190001d1100309d914480a0103105001800d20040702c11000c1c4022441c4c000d080c1882451030855040d107810944000d440c01c0984c1c8405820301225030b1010601024500c064080003015006c1c0400780c0d0190405494850a0720440d602800c0580010030007400ca60004000c003086546003858581c00241d8070741000030400508400c030000b0510742c4140c4403030380300300905c0907543c48000045903c5040003801160405252010607501102c500004480e40403090144802a032a20301c6042c1c803d6000b5a99021034503e0944840103d48000e040b000d031640200c89081819251074080311072030f0340d042d18141c0d41c643c00d41c00d14150700b9030342c1e0300a03103882c3c080003000244031101500600b083d54100c0a00f007080d46002c60700c840c1d9a000c954109604407d04400402c020301f02d40c2c02941d4400e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 122733120 1250 122731870 122731879
    0x201050d0510050402040602010603051002162301050a050906161e0309120c02120102040503120306041b0f0f08060a12030c0c03030503100501020303090a020922050601290414 77
    0x215250f10006081c0c1e0400d0f00001c005030341d251001c2007408000c0101a03544c032143d400440c50503d800e141d840c1080b0b600310000d4040c151900c080e50362021038035002c500c5184560002c000c54141151101c001e440103460b805294800d03500490f0b040740300200f02030036a000760b8032401076412040312800d8844a83e01c0701002070dd80d44800714004100d507011100390440300b5940c0c54026104900c104000c00e904d02a00681c142e105120610441d100001c08103042c1091008036a100d03030301c10000401405e6090014404855051944900c0941201050120381d001d0748071070404810a00046034002c0f411564036174848500340081240c0c090760802850303014081d05d0688074000b032a848950007107800c0d07802200021000020044401c6030f0700b03902009040244003440c0341d403c044d450301c3c0e40c1e180c3c0c80c071003e0305c03c04090020408002503811f0300b0304407130b000300c5411108558a06105444090034461000210200840303448a40f80c4100741a0802c104580c491307050500740150000c49607109003045821 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 122734370 1250 122733120 122733151
    0x60b030f100b0f1e0a0605040f09051b0a02010504170a0819200d0f06080c040518010e03070b06040507090605070809060706020702010e06041211030a060e0304030309050901030201050d05 82
    0x19134944901180d0003119000501107010950801d103c070405c599407000c02040b0003840f05020007070081c0007040c01c81c2c05000d004100b03500e80c00000c41c1041203442c9480d030109000640300c10250f40640106100c0c42c051059000400e0000c0652034480c0310b0307405842e00040b01040042c4d40c0c420382204100c1c0444131080c0015502d96903c0e1801044113028012114000f00420010211720060141d5001140101024440701e882e01d00921f54070190302041c20300c01e80c0c4900c009030000400c55400c001000c0030000034031400d500d8020b150389079404400141c900451000003e10360381080d00529004681c0c0781c0c0c9000603140b40c550211031580040004907804003080105142c02d036140405002502d01a40c40169a5612440094400404d4030161070103141e0501041141c9060b4480c51100c907030f00f1843d00c0124003680c0c2c00107400c0110340d00004041e140b40c10810740704000008080c0045d01e10984850320070f00d890300c00f0406040000d10000b80052300070018495114500e8118a030450035013141a040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 122735620 1250 122734370 122734399
    0x605040f14060f0907030c1401030e03160606090501062705030d0926190303060801020a09050310050f2e0e2a09060f040902040f03060b030f100b 64
    0x3540d85016103079507a501c0300c0284031008a0420080340c11000850003405400d1440d038a1610142e45840f400d401016060601e035040d900940101c000c101d1703148183c170f6031800080041490f0030500702056496510b0a0300116100715a8440c550584105842d0b03803080481c044428850050075045101210141c03250006040c0c03000c1001075002c0b100768030790170f03022803e1041a28015003500d503c01c402005840700c1c070340380342d20104041c1c6402103203180314403081d2400d0030142c1c081d02480e07001c0841980700280c9e03013120b280d0040540341036640850584600c00b414109000c203a8100366885244205c201000c18a11130b4a84280d0b02c0f004050305002031001c0b108041a40c03c0a0075510541540b908401003225041c0c00314245051001066011109940f0b8444c180700507000c4c441c60a401241c000840e101040708102c15100101040c0350199561034840503500c062070594402140c40c0c03800d02a0350052850089a50640c0b0344048004003803070010212041c01800e0750708541070304800c003400002d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 122736870 1250 122735620 122735633
    0x91305070305033c09010309080d050103021008100506070c0b2109070317070507081009030311030f15010e03010c02210a0206010e07030f0c081e0903070605040f 71
    0x40110300442c050343d00c81000e190f84020300d440740140d409260148003480301c08820b10341d909034100c2c2d22180802d0340b03e800e10310050f401480c40318005407220201250807a0020629080941682e200380c4a060100c8400c0740709a50301c0302c05540e8000300070480c0700e041c01141001e40c040d180190041c00601c04090740c0c2c01a04950350300142c501940c294190064400781c0350100301054101601100501107145143c2314842854070600100c1407000f0300080e030b8018050b0410603a400381c0802c3c1c00380c1d01d40512050410000f4545800c045000c2400c0105080014012005491280400a010150540e5800041440ca030230101c501d42c14068800c80524403600c1c24030901403080c440d50002e2a000802d6406898a186441003084c034070300081003c090126800305046045503080d44183d8055206d420080d0050548490b10800346442c0401d90000c16034401406030042200340c0c4038220304460b882080c0800d00c8111441c80702d0381d0081041c480004e00c1644102d034024050304c01a403a803040d035541e49 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 122738120 1250 122736870 122736883
    0x70b1815070302070b090d0e01050c030903060711010c1b020d03030f0f140a020412030503090f0312010905070c08090d051e01020403030f020607021b03150408041404060305070302091305 82
    0x41d0000b983c04248041040300800e003030758000c0344640060a0307001d12000001d021a400c1d01b079060402c1400b2490b104100001c003303460203298000c00b40d0740e05241100e001895403840c154490301c0c0d58200500d8000301030090b030000750f4980c60411803218a441d00c0d000d20400910f40542182050740d1650850385213000ca101c0c0386411101d842000c0340a0b080440010710092000c1c01410503544104820001c4080d50001030464030750500349240c03030381e541c1c1c140c0c9424584103403030f920454000000c0d40b0401e0109541482c1c141c4545400409c440e03140c0741000c85014a01d030a0007051a13004000b00f581a00d0006401da034800c8c450070840d02da6421007060101c2c800a550043c014aa401240a004140e000080d25242107890b100619140c80c14410003555801283d01c10143c2c410745107500ca03a81d840c01d0009100400d02d2461400d4141410700d40100a070303001e4070690030803000a0314000070524103402020200c0760000003c0a016046400708941004060400e240041007030303810000180c41170180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 122739370 1250 122738120 122738131
    0x30c0105010b0405030c0306060d03141201120b010e100b13080106170d0c03050702130902030a0c03020102070f08030d020c0c0a0f0602010f0608210913050615070b1815 74
    0x4083c2c680c0d161105040c80c088240710b506210f03401010810032980c2b01c0403804440281c151920407035210021903443d82c180300d03441009060261402c004070b1584481c0c046580c0140c42f4190241c0b03940c1c2d9400314241008001e0300d505c0042c000618040021524050181c001e480611000c032a4403641c601256013140c1144c0d004084824505c440e10305080c405211090b40c0d0102810711001c0080d06070f8004240d0f201e1000300910272850300381d10261103061684200688ca40c083e0460b00c800c011420450640c2c0400d20080380144a4000081800030a01c0f0b00071080b83c4055008504020301240c580c400380d0406940d82d0024402c4404219861350f8422849006140c6811a55005410000001e00b503510000040c081d103402e107102000360500c0010703540b03010a0800c0d0341c3e24003589105140c0449102d14842d25900030b503014a5030030b43d24a640d020381c1c0100720440b218884500072140fa43d1080c022540050180020300000800981450040005020b80b21041d0f07000d402c1038110b220a40c490a440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 122740620 1250 122739370 122739389
    0x6030106090903200f03040612020d11070c050307050d030305040203010b09070503100b04144005011208040303080403020a060c05090f0103060305030d11070c17120a02060606030405030c010501 85
    0x10801d0040d00900c4c1d0700103d80580805000c2103510a4035160352032103284034460400900c0744a060700c2c05d50310b505a0b0360758020810706100e080150350b208811500104002c2d00e60405a404c0041c07a440c0001d00741c0101d56020382000440011900c0c190000c20004100303070b03095500c0f41c4000c4425074440740703201e00c40c01080d1500d94490800d5043e10080c1c8480390041380207075408000510102281c42600c61844c60219030110203a01a400f10340700401211002031080c220b44442c03450403544211000a04406414080055a0b41d400849035950f000102c00b804280c1c0400090010a02c50600158064020300466a80c0341151f0740b181c2c11500c9071068200010700100c2c1d440f00e149006910409600c1d000d203000c0c0706950030740d1503003610781c4508155900b07995550b5024a070b10404903001c1d142c0040c0c0040c10b0440440c0c2d20391002c0040803030010064510300518510002200ca40e0303040c0c600d010f01c1a4020100c0380c0d1110706002132507001500542d0b846c8801e00c40c00d182400e09000341070181885c40d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 122741870 1250 122740620 122740637
    0xd03020a0c09090206031314160612060f03060509120304060203070e120d0806210307020102012304060504030c150603030909061a07020105070b0406050402180408070b06030106090903 81
    0x3000501c0c035070365420194900c1e00f00300070300b40940d94440a480d00f20980d078024a0030503000e0302c5c2c54021014418031032503440c01150314003160002400c0b0303103104456154442c082c18002e1a1102c60841d0410b0185000302110501c5c00d0010881950040781c0c4884001c1c00c807880b9000c0c0401c031700002c1e001150116040c2c0d13000010805810307400803039403a03a00400c1d250424044049180e0a0b2590f000880b403004011a200004140c0da95017014950b640114081c10403541046d1503019442e40d0009405901560030b1070030b0010011030006c0540c14100360b10b5040c04003502c541e031762840a840301510503400c002e50400e8600114070460489107642d4074a10000449a00c0c40c50080c100340090744c0007144452408004004124000303240110110300e0401043e82d403149480162464081c9210203000742001c40200002c0280e10340c0300d103020b02e000b01e4159418140d1034041a40e1034804413030040c40c3d40001e2090100040883c100075402c0300e80100045540f82d203c911117030480390700070740a80000b41d004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 122743120 1250 122741870 122741873
    0x110915030405100501060f030903090506040f0e010e0c0a080604020421030311090a0512030d110406020c030106060f08070903020301050705070605061804020114120106031b02010e06150d020d03020a 87
    0x40143c1108a0a0b0318001e0085601d01207000d480044000d5211090584501d546000c0503c0350250754050400101007546482e2100340c5032140c00c50500070064040100c0e130010a4204004848510032000d22506515286e8070ba40c0460b8074100203400c05811036000c1c4070120740101450000c055000f07030b0a02030300550300c1a007401819925040282c0200020411040300640c07640e421a80c02d880c0107036900b001c07040c1059030440c514841c860010a0702445e100745040c5a00b03009000b8402c540840d821240b0440340d900400d4200c94252180c40003161550850310941802065015841403c40c2400c0e0003081d981d130007007429a1012241d01c40011000600c283c00c01c015071082980000b000d440c4228680c002d604a448101c0f400b07040a4184034000601c054454807550496561202d402c1d807040782540d4528000e0043c04554901440200e0702c03125141e0007a105114590000c0b21010061100ba120240050814000380c0d26854001c01414000c0015803580315281000b14825401408101c105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 122744370 1250 122743120 122743123
    0x9090f060b09011a0f09120c28030605071209030201052413050919051b040c0206010b09030703052d0703030e060901030f1d01050c04050108010306110915030405 71
    0x1501d010901c18074216006100d480052610700180604508089503258131680b009400b0707001c1c103005507031b03c00c24042c1ca0308080394000c40d480d1a0a4019600040c108442d0b0b500c2c4100182ca42101d0300d01100c4080c2d040002c02d150390040343c3c20014030306150100c01c80500e891010303140a140706602503912041800f21301c510b42482e01d100c02155540303101e610244c03240051404901300084003165030b02c0d0008181000c070140005c1880c994241190100b000880c40c28948403101001d2016120b9001503802c034160600e03000302e200c5904a41e0150203541e0a0554040c200d07007082105070f40521442c0d034040005030301000701402515112900410841032819414040d16102c0c85040058001c65030800c00660400070794100c25034100c540907142c1d1a980c004a0040003024055950f05040031003440000074521040400700851030001d10143d40c4164011055200700c1c0301e15800112840010808914542c2c09481005040c035013662510312110700094032100081604c00d00100004140010000e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 122745620 1250 122744370 122744381
    0xb060d052b0f0903060c0e18070912020603130c05060a0314010f080a0b060103020f0706020901030e06090a03050306030102120711010f0501030f08031302060408011a030a05030304020d0c09090f06 86
    0x50350b240c0311484401624006090902c0e83c4002442d55480700c8505161701d01070030090280c800013504d00c03c051000003e401506030016640180410703c244c034007207800c0a14403000c6810b20b80282c03202c0c1c515100c80f024803040464006090b11000b40d52680403034550340b0a0b000700300c0610585c2e00410309005003800d4100340385040e0312100485d2180a0100000c40000c02c000780b507640c01c603c0300110b990f0343c5801038019204500410300c24520024100c01004080ea0262810510a80c0d0400c030001a1344a056074a09041d00d22103001c0d8001885180064404c600859000c080a8000b50070309000110500740c1240944c3c0b16800b254500011601b09002441103420340500d80c035041c005540365032200b0020341c80c14003020f089220008001240c403075020101441540c2c0c080d140f2075549644a10240c02004907114400000807080d60b949018680000c0f40c040740b54001c00034610b140c8403a03003006680c410a001c2112885550440001ca4550758401e00201d1400358211141880e56860f011080b5407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 122746870 1250 122745620 122745703
    0xc0c010e030a08010e0c040513060602010c1107090e030919030b0c280c0c0801020a1103030f011202030a0605070c140f0714040608160801060b0c06040b060d05 70
    0x50052195298541e4800c81c1d40781141c1c1070052241194481b40c0c0c0720001403040e500015000590a0040e042c580d8065008000f100c00550003046a59241c03503040301c681613400624090703a4040724060110080c10390160355103c00c0039044038a880007580206415122408182c0c0c10441d000c5030800510a00a44141d0712840c07020f842460a03028841e103803100039000d0440c040c20240740e20900c143c58064051701700502d8000202030b21003076640080da03001c0c0d03200c1000440010103040c0d00c050841800410b1740c0c020401076600b158030303030300300002210f484a00c600e080c2c2e403620810420102094881c030855004606030341c0c5d2040046001c3c2400c1010070000d035290300c80c0b5403080c0030a4501c44404954441911105030082c0c01203801c01c2e000402610f92500310f0025801002c41059200040d20f420b072044070141002031003160b5960006442500451200c833220b034000000042c00295208299548043d0007003c031104140e5a0710761510707200200003260036000746c038106182c0c50040b0713100411261 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 122748120 1250 122746870 122746873
    0x90c0216090b030f0d0206011e05030f0706030c0c0206070602031321020111090d12050409020f0903070504060303080a02030604110304030c0203160b04091d12120c071e030905090c0c010e 82
    0x107000205e0020f42d1003005104103070103440c03080c5900c00c0701c0c091030681100409004048800d80706102507007681700e4803284500301c0402c0c40d206000010a00458500700c8a6800a1045007004015240c50011394001405c0d00c006007280f608403000034801c20203011800407014400d01d4800b0703d0742006401c603444140c000300c00500c00c0c4494501303a0b561490002c07606601c211942c110001d9070740e05a0301400f5542044d0b03d45800401d0b003500981790300300901302d0b05204404998010b80d4130014030045800900000d0b0029035450000344413000e01c0c0e0015504290068400110440301608095040d002503504400140c0c400c0d0f04582549010407243c2c101081c80317511560784500d0700d01545860710451103009103947c1c03102d401c402051082d032100038150300c0100c242d40355642d03c00200e500952010702624642c20305440807075031080114003a181901c0d40441c4041901c0c101c9c40c45d078500c902490900300d0401501c0314020900f07440d500382581c05084040030302e64a1303030701048520f82500c41c0d00030720609a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 122749370 1250 122748120 122748133
    0x3020709060509010f060509010c02040507031a0a06020316030903020a0e040b09120306010c060b0312030402090106020c01090501030b030309031005160e13020901020f030a0206010617040c090c0216090b030f 91
    0x4030200c1d5417070508442c0c0a0606642d079a601000613600c520003c00040d5200d813610f0100861319405400001e801401400e290704001110400c010200d03c4500801c40164014409140401400203d20000300d00909261000695a500003080b07000160800141c5074113450070300c070420a00030a2280c0000000e000340c903100c3d10311140d04980340802481941004428458402071241c0c56115400b40b000141c10f0301c03103079400e500310798605034010b0718124011402600005015440465001c2d00f80d0300581d200742e00e1500c0c0500440241c00d400010300d60500040000b052030b43c4e4104540303203844020300c401184503d000002014800501c804000500c07440c0b224400c0156601040d445440e040f400c00180c8407005100100d142c40d41003914005284800504900c00c07075000901641212415500d0f54849030144109000700001524024030001c20204184520102c94010044e880e92910403240050158940f251051f500e40d8819031019964201400f05402d060182c04079004000004020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 122750620 1250 122749370 122749379
    0x30b150c0c06030a0b0d060b030610080c06130e0a050a0e030703090504090809030601080303060a0504090f0323040b18030304050901030f02150a0f0306080601260a0f0302070906050901 81
    0x8807420844595846004004009840401c05900c841c507034910140410614038150b2400f03400030b04601207482d00c203210300350018003117500d640c10300d000365400d010240441030310f8403050001c0c03030300510b00c42290708200320400300c0c0680e0322450040c07180351110008103c0303080ca01a26402c03140300745121490354200304902e00110350819148021160143d0b000249209642400c08031030040010300b5030316010314030001a1151000024500800c412142c03482e4840d56031003003008461a1110043c020081000d016001c64007071009640300d60f82c0380f80c8010b44031801c1940c103845540140c1005c0c13600ba07800301e68407003c2c04440d14842003520081d40294a082c0c1040b00040c1c0201c0d051100400190040b40040119101c04540c000c0380c0060111803511154161030180c03550080c44003c0002074544000002d1082000500702c6c101c8400010140c0c0b41440c2c44030070401001c3d50115840315215884904000508602400034214026030161040b242000c011005441c007540c0154070132034100d0011301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 122751870 1250 122750620 122750623
    0x10b03010617040501091e1109070903060e2104080105090304060903080f0904020304060b3309030a0b0403082203050d0915090c14090c07030807091203030b150c 71
    0x102e401190303680108140d5442c42c1003800742c1590200200803103d082c400e00d83c49030100b1280d000f042d124002c0b0000b03010110091080a01e0112241c000150840500300081840d6a210340b401411200030780780d044000c52040140004041005076001000080410a000d802e204007600240d012001d545082e10b4070b14010f0507100e441c0406440310a0006110b03a08038105821108a408081c0055440749080c0c202407004140510025018400e0844200188114441058000070280c0044030552201c1282c049117900b0010401b43c0620422f960000400d40702000710744079a21a98541941d407608084e00e4202c4050030011100d004d072100c0c00540066080ba0540b400c80c7c20742e0300300003110011401c1139040002d07200720441c0750515100841080c000c2c0300c942403040c1c400d0050354030821221503003030007541642202c4180703842d2030600954000920906449800c40c0d9580b034042e440f00d072140c20300380c2c0c0c200341d0f48422030201e5600e01c030301000c0b820412003200d06141d0110945060845540380c0c2c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 122753120 1250 122751870 122751887
    0x1f0f03060e0708090703060e030a03060b070b0403080a0e010612020406061b030f05160f030e01020307020609040902270106020106060f0c0b07021e060103020a0b031909060b1c0b010b030106 83
    0x3201803042400000341320020412101c2d00844d00b040c401c0c0401030390840016181c1d0b00c20001400040d00b030030008941d1003100000c440f04251b000800072142e5a881e20111090080030344105005c585443d154800141e0901600000c0d00c014200e90032040c10a20402040715099803148081c0b0006000f4a0994201c89540d40300a42d01070600084207007040d901103455100d41a40c124040108144100502c0b04020850807524401d88454083e101c8041c01a6a0713070040003030003980804200800040703030030142c01031a0001d1018000b4084803450201c1c18141030300d11000c50103440504801080410340c240035541c020155410500f00d02259448010000d010300040503002c400c8031404110010f20820003995401c1002c220301021021550f10991508400c0c442688601e142c5500421141a41003c90317000310f0149003018490304910703409001400c1c4000d02540e1155840c60340e02d04a8a6144043c0d4905a106014200000d800e1808109401040c2c01160341103500b4001400020b8000c040c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 122754370 1250 122753120 122753131
    0xa05180105310c020102120903090901060305011401122012010f030f06090f080409020a2015130f0b0103031b03020303070c0f1b06080c1602010e0402091f0f03060e 72
    0x101c1d00003103803c81a03002e4401d0225440051240600300b007108840800a00f10080301114240e1644e40c1c3e8004c11000d5450a01521030b0000c2413404011256001d254460f824160511000c50b904201c10104e0b030b041048002a16241e0100080d02040070b081c04400f140906500c0c02d5540c82241107448440711500702c4400181019590404042170145201c42100703807d5000d41225965521290118040d400c80780500000c00c0040117400200b680300390ba41084920510000d040c00c440703c2165034403050b000f030300d05440b2041400a11000c102100c0301294121700070009902c45525601d80286001e2206030348403032200109241c02d0010f5030200403280c100b441490504101c14083c01c103040d0600070940010404548982c0210380c0b800064101d204860707698503071841c96500e44209019920410140c20803d80041c8041d500541c0201a43e0412131009000142080000404100c41e425040c003c42212a0420610821940d00050340400140c407441c0520100e854549801c01800b800f400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 122755620 1250 122754370 122754469
    0x20d0c031704021309230114072102040b0702100f142a0a0b06090c0a14041206050402040b06160b0606120403170112030512060a05180105 61
    0x49001d540d074a6112640c566000d0a0810031802549840b004480b4881b0045003401459016001e04100c188265032050000641c0b18681e6500d000040300c0c01d04444400e8401201c0c45011000d02a03094405803000d0111600615036a0110340100042030035680b0480c0c0c10800b190080f00b13032060b40b00c503403644a40e058040741030321007801c4603004900c18440900100c10100070101d16840180000c3c80c1c0800701d00412100c2c500362961320038094581c20444021120083c1001071b00c4c000c0788500254000e89103a440b8060030961603490322800c500c01e4032415280242c41e44244070541c606071041100d0003d00b11a09442d00042002c1198143c4010101900e00c40c0b1440018030552035080441d0f550303400200d10010a40741034500901200034501912600329050000445c00d4545c142056540740e03056141e5a0802c01004a1944c1c0540c0c010109508a12008400556505d07202442001c00628121000d0298148824000303031020f994420300340d1000ea509210180c14548600c400110445403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 122756870 1250 122755620 122755667
    0x30a0f0e0d0f09180f1103070507111503040302100b0406050312070c030b010b07060b03030a08010e090705030d031d121903140a050403120b0f06090a090501060f020d0c03 75
    0x1003520f2028465200314a105006090718040103501d0340010044020880108808502d0044024403030104075617520104e82c1c10040700b0040346490440c01389001004140f1111900034101503881500290f5040380075030300c21070349045205428084d031a100402a9001c2140900e0807000940da0f03103406034031021480f0001500010b002c0c03049180b00184d0b40081d03040b031640d60744003c481e01e43c0d4030102c3d068955a1510a0400300c03440d01104071041200c00c0d0342c860406900380494500740245c00b4050780100e11a50200080d01e0302c0c1030204241d81d9041703840000e42002c1039810200c2c0725007510131106036508058004a01d0040c92070a0724080c103010b02049641c402081416002410b5900145142c0d01c3d07240704212000115801c9a84118482da84820204041003998020380c0c05408445078081c5800021800d14240080074040c440300007464a07241594803081c0c0c80c02c68800782c106070001803048880b422490340401043c0c1c0008000d213024503040b0400d1710002e0480324038069000352440e484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 122758120 1250 122756870 122756897
    0x15170d021c0309060b0301050903040302030706180302091816150801030503071226040c05091005060a18032d08120a0e0d020d081501020615061608030a0f0e0d 70
    0x7075229005d80301e80035000300300a0800208850360794001c0c0c8022403081c46003c1010480900c0fa01139203070f00a400f24202c0801c1030555081200d00b00004000103c030b024160858034001c6410441103000610140e043d908842c200041c98040780274425080080c402030310010400114000219005c29030043c520341c0818000304422124840511250702c1b001c3c0042210300f4000c402500f046d40190311901d40e40040c165a1000e101c6285011902119141c101150130001410580c00809010506103441d0f07804420122580c090b0741e840d604141d4120301982414030b0142c9103500104000420784030f5070030300c04045981308035003031090040048002c81c100c00491040c0109400090402d1000401e4404201c0034034402941d805403030641c800060040e4000c243c0494885200d000d403508180d000c3d0485503280000420f0b080c000102e1950003910400c14030b00174054107010008020310890015a41f400c040300418160303540c11040042543c504041009800c80005001003415010709000310780003400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 122759370 1250 122758120 122758133
    0x904050705090a0204060207050a1d071206080102041805040b0a1515020f10020c1011190203030a050a020412020904020a09180203010e0309090f0a15170d021c0309 72
    0x30341c1c80250004880070074004408155000fa10644e01e61340d085854040c0c0e603408000e21403d152250107101041e0201c040b030224002201c05a02494a0504cbe4130410701a101c4642290f5255104480c0ba075401700d42030103c40784092900418042401090000d0300b030585078004103900141010000c10703912240d050f01070003408054402803242580d00c40401c288000c0217500c84003055030450722800744100009880b0b41610984601d02001c800404428403103061301402005015003280e079100f4180054050960740c0c0148c61001401031780950f0300d9062803810641540c2007d004000d21900503c0300744107150350f0b504152076041c0c0454811040e81c079a070000c904a840b01e07070070200c034941c14458440c50150b40e0444030f0324658802d90081155408401d2038980321302a44070781c0d590004107240411000114900401d801103070201e00029222460040100c070144641d101145481218142103105002408203948103582400503042d80c50100c40d0180c412020a948030042c180d40300d0b0380d001445007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 122760620 1250 122759370 122759383
    0x3121210030f0f02180f070509040213080f120403021e0d0b07180603050108070501030c12051906090506100f090e15150c060a09060e010f05060f0604060c02090405 72
    0x2c121040b408011068103020300c1c0d52800c248142d0180f5510000c001c8107120f0008068456110090010320a4a5244080302c0550101c00400c0c0e21580a0080425003590780b81958014806080148541242c03242058104902e82c2600c11943d04240000c01c0942c40302079158100e4028011416442c0c5d801c40006050b05082503000b6018200d500200881d40340c001c0c0b4030044004081c4005014680c0c0c515003201502d209000d6061203030440e8104001a5010b43c00405018403142849400001c00304400c904079074003107072010365600064041c000c80c4069440fa40010b840748000c103100c079181c00f0012030714070324050418004000c8520007481a0307900c108104000f0f070016466222540c00e010032203989006100455030b10844900350615015001e4404564500c151000607150507a961201c6d50001d003000041a25841d17244c81840b450b140d020302c50091240078050001405003000320509c0080817400c0c01d5103005000411052180a0304500402c00b0190b0440c0e50b40140d90303541ca04142001c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 122761870 1250 122760620 122760623
    0x12102030613090f03080105030d05070209090a1b05090c040506160c0f0e09010c0201051b03091204080a0c32040204030b010e0703361407081006050312121003 70
    0x380f5000c0d41d2400c0104061a0181d4030703001c0d80c1c4e0f80203170fa62900c00b055110030a52141d080411010480d00005040501340c0540c00103d4500341c0e920b030405621800f83c0360640104410107026020010321031440c04001050b0040c03000c000641c189414400480c14520070055402646180d51040d1410801d10103405030150003000c200d6200345945541c09594410207451000455082100a0400718414440c0c00d108520b030352504528590120b0700d100c4194000303425401d980c01020342c00700340120301c0c80051008008250080c85298000d0034400e003988001e410030030100110345507107401d01c032000788481d111000c10302c0b010b103c0390418000500240b0450f03100420325203e900000800345000244544940b150741c0f4103100c64484d00e41d01900403200b40304200071b15060162481144608118503c0000d07100c0c0212070103c03254840d0452800005502c00304041d4401402506110311900030301008000c160010010a1f59141011219000b100b6016480d03080d03200000e180340a0a800100066 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 122763120 1250 122761870 122761909
    0x60e0f190305100b15070302030d051303020d020a0521210618010509010e070201020904060b0307020f03180d1b0e150f0d02040e070e010915050121020306 68
    0x10391440030300c0000c03584070312040e2928010102001d1095070300c2d0054120b1108010170b00c0101010503020001c10b034200303003402c1e0210300c014030918030502190701c1418095204c1d20102000c0302807915000f481e1401d10f9115000315001303803800a00140001658489440c0d08484400b1850a10020380c015405041a1000701031050642c025100d900031280902580c02944e004800c0520a00c55080d0b0090071301c0b405810000c0300d40104607582a40040c560044882d200140c502084000000c0a50752145c00022842c07400000384032400d90100000d181052104002d90f04056103017404951000007598814040c00846404008004800d540025181064540d1407402515038480400501d01201c0500041980101800061a00d0b1050a02d0040b0003401420201e03141e41c20700000d07000b503070040101403103414408160921212070150207410740742c40c009002211b6160b0741d40c0da181558805418400a1284034030056501500b0080059a14502599a865020100f10061880c2d250a46c03507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 122764370 1250 122763120 122763139
    0x109291c0c0b0d0c02030a0c0602090402040504020c010b0f0a0e040f020102010905030a02010c030c050c0a0609080408010c020f010522060207170a020f070503060129040518101509060e0f 82
    0xd50050020b048100403c2c0020031400c10004000c0c0c1c2c0c1ca100320340310381000c21025400580002c40701d0b0010401c070603020b000503003000e0342d43c40401c060340c200c00d0060b910340c2d44401010080b4148980700700c86210b000c03640c0e01d40e51032401a01c04401b03040030f84040c001d400312a01c4001564000d400a0507907603404011a5510003121030005d00038404600b8100c001382c2040c2e858a4886d2141e01511016200c0038050b10054010b5a60792000381401c0c8000c550440d4184000201a0720a11685100d0701094026141001d2102c01c2282198401031000962445501000150708007001c924100c455100c08016500d41c0380e8113121096924120404031a281e001a8a44000e540403a4500c1e880c0e0b5030004030b800703403500c800070151104400d0042d4a5103035800301100d20b8552050404441140b40380b01944e25181c1c4410108412545200810140c41d43c240b041c881c0c860a00602c80b4014100001e5413204280800002410b100301803040c40c04009810f04040b141d60b982e02c0441c0340511004056142 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 122765620 1250 122764370 122764379
    0xc091203030b040b060408160b18091312030b0a080106030807021002070915030b0a1406060a050d06241b0311010e1510050102010612240905060109291c0c 68
    0x10303240014060801c2341605900700040f045c5155055a401c0c107190702480c1c0715400482c2c02d00c00c1413500104803150707505d00f00380714001048044048104580865070007145070a860320611041c0380c41948400220380c034200c070400206594000b0341e41c1c9158122510310000b465008200c2c80c141103034001c02c0001e0710300368000000040c41c6c9034031000c81e84262090007980c2c0d45c400510b0100c030a1180d4090031004036000050a03460004020b0100600600304103041c06900300c0000e0444403550084d2407004a807100c802245440c0704058142c10f00c41d440c10300c11116050803004004840000000e061040034451210310f22420b4104004031f60041c41102e083d8080a64003071421441520940e25110302c84c180410741d0752041c0920002d840a0100004a01d001a0340c0d4004540e070004400b080105220450541d089581c042c03200014003540042c074565040c640040100d03a42c403c4180300345e0921503520103194250000c1003040740402c4034604240b0543c489400e5010242c07100040c0a503c20410205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 122766870 1250 122765620 122765623
    0x20a0201080601020c010905010f0311030f040320030414040b03030c010506040e07030314071b080a0201020c04020a1b02030304120f0b010e010806010b09031f0903030c091203030b040b060408 84
    0x10160003680d5414a684070b010043e0f8132548030000e91400034405e01f509000c10f50040310180340341885480c001030101203031040d40070a600262001219408540140028103070720440b65152441c089181910301303403c5440c115643d2040d03216409000c89200b40c022a6940d440d844829540c03005010f80c3d6079030000509490007458225091882507190041c042e09216002400f0f400741e80d80741d110115124804581d85569409c1954120741e90440340d14400044c45500b19040010202580140102d4880d44006420039020048041c05507206011151903103a1081506010030b80c0d03080d2000389074070680040703402e611640c2c220350710026200000b0000c105c0885207135800140204112100341c3d0302c2d0340401007015001c0c8240790f84c56024000522500400310002c0c03035003d40080444e652035620f07414070152034000c1800c558009a80d0020303c014550107000f60100e0410350f103080103255040882d2100c29020b409005002c041c2d49000c064410b44540c0d2001200d01e600800c400e0303c03250355110f5213 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 122768120 1250 122766870 122766883
    0x6040f0f05100801050c0a03090f050a0305070302060109021206040914010216020f040b030c060a020a020a0906150c02010f031a0402030a0504150b03100b03150403030b040e070e01060521010602 85
    0x2c0420700c0d40214005a1070314103100300c900444900300c100740b400c0c002100480260507000b01c207540210b51a90810006203003040000a160f10030b4442c10344410060034040d050040580c0207680660040000c03803070146e00300c400380790b11080413100003800d00a5420505074442028000c2c8040307603c00160000e0200000c2a44000180b00b181e80a052484040621082e2140044020b0f015800014900100c0c40c2a074050032408401d84112480e19010f45c000891510142e0f0000c0d4119586030014056040b0071014206c5500031410010324210040c1d000a1207424280200340030580d07104000c24045064687c00914444e00510942d10383c10800480001800305079070849207180140b01800d2000800d010b0300e00049070040140005100b548403510203014503002480c0c1c0f600407030400c5901c180f6030000560003507003c0d6400150f001910018002220105040c40c134450b0704c103c070204180d07114486501e05482162074035684514800303031404043c1511486070305201002c4000428000d900040c175 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 122769370 1250 122768120 122768131
    0x21e07030c0b0906011503020705061b0d11070201030f0c02120c120309070806100b18010c0b100305120705071806030507031a070305010b03040b04020f0301020703110d02030c06010e06040f0f05 85
    0x40613104111b8006404070301c2101c0f00200117401002c0020241200781e5008a44003403e8510a850050048220400c4803640405a0102d880105581003556410311071004600e07014201000000300341130303000e076032001c54019141403510001000c4440e100144543c8030349103c4030031407603100e0810a0905803030301402c0c003c2c0c9070540704003400100e01e5560280d13840b0850720940481ea24225440e5031003c6000c000f0303061706040c801c04130001000600003480003403040d028441b4036481c003415440c016080165180582c1c54005060000710082103001c1421001c40b041c0545880144012a40003005460720780d00c00b51240c0141000001030086200c5a80b0240300c400440710340d940d84811041e000c80714213000b00c07100e91605000080014602800d40c03a007240c002071848108440541c00a82641e000303000840014000d005242c0440350100070704003080036140091070030003608640290365030105200d222075007c01d50020440e0f80d1966403110f91811514078080c0700350b4155946c4400506000d548 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 122770620 1250 122769370 122769389
    0x507110a050705091506040b0a030b09130204050901020f1b0a0203070e090f030301031509020f0402031501090b0712081f090209030f0c0604060309020f0a06031e021e07030c0b090601 80
    0x5175583c103100e055070f403c05000410090070541081d0707400103150070421a6005050b82d543e690aa103035510004cca00c076002030440184408804c0c4103000580c0c0001d825001180c0c014889010400c2e03001003075a52034014410040907040009491b1854060703440c174042d4043c05107203008154050f0703080200d0700ca6400030048584411803910850b90341e1000340b10240100d8088014800050f00c540c00440943e8002040844075940f0b00300090203da2090798011021805000320840e035580010b80040103140d00c490f276908101458a4141c6e401c5c801d220800c1c10400071600240034820050072403044c406000d441800115180e40101d4000d500200041e8800c0c41881e270000d2103010002420b014040c00130700b0075130411f07203440d400b54003500c80080120791004500107c88541d4844a41020080c00e40fa500030544550031035004024040041c003c540084c01001342051541820184014030405003250680c0c4600600f4120396512a81100401c81e040348800c2c00340002c0c0000360305068868120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 122771870 1250 122770620 122770639
    0x130905070e030706170a091505010b09040605030102030402061204290106080f131704120c0312080903040b0a2105100801060e060f0103111c0501091802040507110a050705 75
    0x81c0b003900d0b07010040f121520800c0da040c00094403840c0740c2c1c0150107802d00c00d5440236102c21091140e08107986090700001204d2401180300c030900d14190240800400c0181c000314598203043e0046a40d88c8101002e04042d80106130110f0200100700e4218200c010404898841030020130800c6040507100b8424900019180740c00302d96401544c611050050710795001d4020030616a80c1e403c10807441d0a0f0400316214000d000c00216a010308510050345031045158140b40703421341c50866101a2801c103410100030454080005607100041140e080e030310070002160b201c1c0520301c003c032a100c443c2c80400c0f590201b102c0440d142c559098001501944100340805102521440028200d13003c0d07114600c02c1c0315411f80441c0d0300c1c0c02d1085200c054000b0624010a4511030707031106032010340c0402c40803c88006001d0702079149080520440380901005101441074801c0c411540c881c00c10a028060701c51a620408208211301a940c3ca40d80302031a238042d01c0314058103061268413440c10380305090141c40d000c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 122773120 1250 122771870 122771879
    0x905040c0f260c12010e10020a1704020f041a03060106030e0705150409050f07020c01090f061d0405070203070506130f030f17181506010e06130905070e0307 69
    0x9104103040d00c400c454941d484201c4280500705802e0a00c0c0781200a010720194929142c1303c04090030f030082d03500c400100b8080407030b900d101d00c0d040d013000c50000203d01c18810f03c5000c40e4440c29500003468240141801c0303803180e000043c400044100480d90103440d0542082420307000781d41c00c406001c0101c0594926a99441d000d9042d01d03c0c843c07200e41d040d00240b009120618022b07201840582c80c40701803505181d2159a2902103810075030304070320700031003481c100300506a042025410b81300702071a01030660341c0384c41000e11006000d400341900b40070740440d61903941c4403045090801c3c80d600030020301aa0410110294136517000303801c00d0301d460098900154400c015041407851095101c070b00032800342419201100c1a1030f1142d0543c0811031340c141103002c55404503800314014890501d44202e40c912418445261a1030150740c401542d80f400c040002d0760b030704444a843c0d0b90005545042d42d600806c0502c1d9061841908034000c0545800305002d0400e40c48000d40035110010350407282e405c4e0b01c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 122774370 1250 122773120 122773139
    0x141306050604061815080d021515011409011b03090602100203040b0402060c160609050108181c11060c03070e0603040c05060d090f0b0402330c12040905040c 69
    0x2a030092610051400342c1400c0c10313140c10390001c042d912a5819208010f515034070084d04000700c0ba070706400141d103c013038183c9a40319581d80040c3c001101501d610031480c0302c0d2002903d0700020f400203580542001c50380f0300b01039000b42880940d400c90030015060b000018035002d0440407140c014180148543c0a207007000000303510850303020715040b440200e02aa21039003000401e6024402c81c5009006402100d4810760545160101808923521624082400c0c05e0004106038001491410000d5440403150aa4480401d01060301542d0309149a03104c0e00594099580141c41d59641000e0700c500c00030040e64032a810b015600950710341c5d03218040309070312a08014090200b910090700d02c00b1a400c00700b0003482c10400a10094464a4012032034070200d0b222008079110320b0b28282e940c2c16903002004110f00e02a0070041c046140d501e00308060610001480b100641804003c9a0031000055086440300d41000368054443c0002000c0d40c0c1d8548450007600a841c3c1078500f00c40c030b04030090010030004003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 122775620 1250 122774370 122774381
    0x3050a090215031018050702010b041a15040b070b090c030c0a060f0903021e090c04080a02130f240e04110103020715050a021b0105012403141306050604 67
    0x4008100b0800c1c0d600400944065500c00b40c00e2030f01241c40030400180e881800d5108101c032000d8500c0008443c6011f800203829200c680c9210b074401c0f85891015503035115040007450080700c0540300350040c0c0c038400b004030109120329008074288400120b03818003041403940321345200d8070001c0b040e40c0d0300328000c10a140d61842c0c0698901d500c4460340700180003152003540e030b01c0e403549094a0228021580c035004a00661100075010080f104604007140c10b074104440d0068010903001c0d50301d407600e0315160f0a80d0315071140040092044990b0b0301159800d00b010380110321808010181007011a0f1007604000308041c40041440c2c0c0c607e20050005030402541d054507100c0c64200001c103500d02d0b130040c0114001d44c007154007203d6285007104000a0001c40c0d00c10b803403103804000401a5511000640710911840a450203a01c82c0e041c0001030000c0702590080e003000b409200c082a01e16010b6890982c00780107070810008004801c20100075249103e02c3d0b251980034050a0100841d890b01c07001e002c296031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 122776870 1250 122775620 122775623
    0x3020c030a0b010303110c040216050d08090c040b0102030c01050109050906180c060c03120a2408030904051e07050a0f0e090c0a0e0d0606030204060605160f020a2403050a09 76
    0x502c040042010034000e01c07502c858600d42c002515060404000004d0803604224030002c122a140c1201c0001c0101c204040300901805007000c28003494400c2a8654400b61032000502594480341c10b4045030b4000c100756406840d81000a02c415a15a04500c004003001c4900b0304a500c5030401149100110410a20320443c0c07440c00780440708071440500c002c0d40d0200f101c8010504c0200701d51084400b00b1041d05000b0030100d01d0200301d00c21028800304074408403519501141d104804108050300d40081181d60079041910082410369030b10469415250410006040314240d48081040c140ea200005084210b40e54641c598012801002200d031040d004007029040b60380e5101103105441e451016001d003005078502a00e00c0007022000c241c01c48000402218030940741c0e00184118a818051080035064626105040c110003400e1a080800f03a004050601c929601c40c0303400795255003089001505094249005840101401e1500481680c038440b000a01d8078000c1071030b40d051030040c2c12425 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 122778120 1250 122776870 122776883
    0x90403050909060f10020f0609070b250c03030302190305160806120f07031103030f070305030916150f080c0909090715020d030507082203140d060303020c030a 70
    0x190881090201400b4040d010135448003807084804000d90b152092100c1c000c41c60b0b4003402e4201e1001441d14a031040141a00b656600001828001e1940c0d000c251a1091880c00d00116440c240c1d4450700c462010880d0043c01d40503032254040309140d050b800034140b00324001d06080081640080c11412108183e808182c44062000c6280481d0710845c10940c005600401c9150940d440100031490f000302513a2064443c1c001100400a208030342c50503161800b8254080c628102c1d0740c100004040c4100345000781440700200200d00e12441c200079115001e0000d00d60402c001d80c448144114500c00d002c0b40d01c0012312000c1000c410b691294400a002e85040c3d200c1038140302e40b4504010300541c0080c40310300300b032042150000340391080050f942c0c0400000d40203001c481c0d0b64004010103441c030041c0584244078928060007500d025408401042c01000b01d000315040003d0710b4100d031044235045143e244c01c8004038002d440c58103594409002c4030320035022a1800500e40050584075125400d015100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 122779370 1250 122778120 122778127
    0x50310091803030b040e0709060e01080303010608010e100302040c05090f0d0302061623190e090606180d1b121703090f0a05070306050105010c051209041d03030a0b09040305 76
    0xb038000e802c07900c12200001e001040984050301c1452030015a98003401000b5154a020000c540001c5c1c503207805094480702552940d0306002003c5d220840600c10401081c008200050104240320352007000765900a009118100700550010001d41162170103521aa1460700d00c1b07400c602d80400d4032190303141e040c1c016090a680e41b86401c03600030031181340c4805016000c8806201580d49941800ba04a0745044494030345158203070400c20074065900240c2805400320914403141d44500190354031803000c680b4241e80e81c03120300c041941c0a940c2100507812018160b50b013010041b0070991028440141620088415034618108000760701c0003901608a40c500303c079880d00b1a070341100540e8080c40d040c0c01c540d900c02075500124548422004280d80c0b580200409004000d005c0c001d0ba07004003000d117004e5801450300c1c0c50f2a91583d070880c50444a10000084544c6070b510350f41c105e29200b0f9503008080c80640d40d44020305440b0350084072079001c080e150207141e0341246002211a4003d40d0159112800e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 122780620 1250 122779370 122779373
    0xc1101030c0e040e0f0c0d0b060906060c150912040b04030b04050703020924090f06130f0c03020717040b0d0209010201060312021b01020d140d060b0a0503100918 71
    0x2071107101d9000d401c004510422020303644643c00f038031641d842043d00411300c1c906401c400d5400d01c0c3c0c9040201e441000d4541d0400c020502031a01146c00c0b100849041d00c0c0e603143e210020380343d031140c2001d0814030b0294000030101004075050f440c0c4601c0b10380040c1d034900c140c0003452100500c10303805180c0c1d281005200c00d1001c40d03441c110346913002d4852012610819200e40000301c4140302110341d030034614555034258500300180960340b44403440a0700c001003241405580140a800001c3c2802c2c00341c56080e0f8031404c1490507400500401d610a242041203004080340200a90701244066841e10b81c42d00c1c2480840c1e202008031411105002602c42c2403040701100f5001039404101c10074115905c0702404800f01d58070071460600c00c030f49900100100e03280c8020102c89100c0d15401241550040c40c1c8100030a9008a05100440c8180c0f59081d0344a4641b82c0c81d40050240d070700640401c004c046030010031706401000560044882e00d60b00002c16654030030f8081545d05408201ea11103260b01034080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 122781870 1250 122780620 122780627
    0x211b041a07020f0301060b04060e0d030804030309050a0605090d0908030405090106120207050d0c14010b100309022106071704020d08030403020102090916030b0114070212120c01020306100c1101 85
    0x500794402403902a40264150000b4299500364101900020b00000c00f0440603821030b07043c8070500e005640c070721103401c11520003900a040040c0007600745910740000d4010090203020455a0300d0703100e94108001d041ca81c40d070981d20303041515180c0100303012100c00701c2c00c924004203640440d81e00400321482a0f00300038084a00001180c0c41c4d200051b004e2000400141c024000200041281c0d5a420305414041c10301a07040440461044003136490300c50140000d8545220207441c0324200d040c0403869482c18404140c041c45600514266000c2c0c42421034060786010130740500a101c666270303101003c200d603140300c0308100e0306581c025801010070072041c0c00a102c10000d15801402400014140301902c0041100181e040314010400e25201043c5185035405100d40084c842080c644603841440c801d41130503440c420441c001c6d00c038880b400d00550212008105c041c0b1803d103001059601c2d03920542065020b50000c0d18000d118500c0c60f90440103003845143d010401c5500001c480c01d40882240056 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 122783120 1250 122781870 122781877
    0x503160816111f021c0e0606190504020705030306011e050a230a1206090204031119051801050f060703020d1202161a0606030c030c0a0203211b041a 65
    0x25100d014903e00d001850110444603010140e002d440942d44000c4590700c0303200c09107016240c4649504d011041840b0f09800a010383d4040b0086e10385c0e01c180304105801541c0315269520840d4441e00010720b00b020884c012001d98007808080c2c0310424990100310000040d08020b03100040002c506100a60450780304d00682401d1592074609101e4030380425400c0d44140d40110800004074004606d05190320340c084c41201c00600540c0d030114146400c51b0f850038104181c80b5561445010408a40c41c04a500100450020709005104980c1885403d1954907924000d215491154440c40402e0146040c280101e800c0c155241d4040d00840c0c07025802504d681c43c0300e00b001503d480e828800c40103000b100c0c125000300f45000d8010303000b82050305600140d0700e290090101d07000b00d906009110035211000150fa8120240c4070180b9110310b403000080b4030b0350250341c3d070040120300742e00580580468404080e9008a105242d83c0064a5200d00d00c41c0e9140705038418041007c140c480c0741d82c40151101c016 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122784370 1250 122783120 122783147
    0x230103021303050604050708030406020a030e040f020715060801020f030c13210c0b04080a0b0702240402010e01020a08090f0d0206070b09060709050a030201050d18030503160816 78
    0x40c280702010003a41405040c0750000c4401d90f1200b400e000038814108050b500808100c4020340c903050404038000d4807401d180e5401401e0006041c001d41c0e10b69116040380c690710f078098000315110a5a414090040b1701601c110742081813808402181104040c02140c000c620603007141c5155440385074110900c2d0384460400c80000d14113038004101c181d0085103401c80c03082800ca4400380c0d4070003820500c950283d254000c2c290302c50b08010801103051702081c0740e02c1c025000861981c00e580c03020010780c10721b03101c140001c412284106510074025180b8030390501440c001c1c0d0310303000281c03520001643c1d11140080080c106000030720043c8a41d24040c1ca407001040805441c054410f50300b9400304041f5000071004403030b90585a030030004407a1040002e564040c0061402c61780d464600310200310a80490b0001030304100c03000404c24251503154025010b00d41c40c041c81143c0f80c1d609400c0041198200f980d100c60b403500c503102100d54141c851400140204105516500381c0d400c070000c01d41d18000705044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 122785620 1250 122784370 122784377
    0x110303070e130f0504080d0b0913030c031709151e0a0509030c011508060601020a210903020607030207090b060c1b01020f0303090105040506060d24060503031305040f02042301 77
    0xd140c03c200f032240c000c040c040d9101d800c9294640c0f0782d4042e00d00c00c2d81c1800401d1230080d6415400c00c40750050130040801c1300ca80504100d0384018060070304480301c9e203140300402c40758442c410900590705000540ba11201d4480316040c0b619441c0c81249003001c01362551080b5640c500c4038007040001250758009034000d00c41c001100d02e015012c00c0e0003405d58042003100442501c2e01d500420a0351024040158400400d1020b0a4140141d03611020b0201034400bc0c480c080c00308000c0c9104090042d4200c8002c1c0d078004002035103901540ca0025074070140703805a4240c06040a0700794140742420403c0c2e8158610703503006080c9000c200c0c00580008401280b403541140700720b441540041d54140015400b840c5000f0010a41d440e140c20442d2501e4005415580170319804071443c3c001c42c8200414008140c46c5c40e100b605460514100e1038040d0400e900525070502000460003407271400c0415450442d201034505100c29a020f010550403070045201d007101001d4200da103d880440001c076003080c400c60504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 122786870 1250 122785620 122785631
    0x2010608010c0801050a05030c0d060c0903020a171b010207050108040807020402071b12080301171c030b0306010906030b0112030504080d0e1914010c15110703110303070e13 76
    0x40d15007501d401401d03060108840b0001032169007080703038020300680002d40091421400100103d007882d000400d01078403003580c0d003134940c2c00075101c4d201000041d6001031082a040f03032500101a00c0c081902c2c030444061007843e000c0701050004071011408420140c028040182c50400103561503140284115551030040000000582e1b451003c0c080365401151030040d0300051480044003c3c000d03401002e4418140d005890006403d00c0469040d501d0001000c4007141885040d54900100307080b030920744010070b211880e25960300d9804049200720480480e07106e66038652441c0125103407400003a2079230450400501010100e4107803d8906807081c5020752505944608103030601040080b8000003d110340244500d503d40000d1700006800440358150307d85241c5031800741d249e2405007003141070100c00045031003481000c850135a04051800018000501c00c02c03080b0f220341e0320045048002c0381c0d5900300901c0d0b18030000245c0e8410403e50300d0340c030b004941440c10003d80c940c00440880d082034a50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 122788120 1250 122786870 122786879
    0x6100302040f03030f11120708070212010507030b03120405090103030318050106060e09010b090a0905070203070203030c06100e0f0a15051903020405090f0303010e0405071a0a031514010f020106 85
    0x80100300118000e9036905105d0f2a030010080040844007005c94a0b544196150640b40300d51001f181d01c030030f902c0400b0a80d02c1785a0710100c0c96044403090b520255501c0c0030100b1403240c1c0c241d00400554071044095450101e4051a031781141c0c02503000309034114225000500009000b540110461041000c2c110030110082c0c0c1c40c80d09403440780e042580012000010310f9803d0414804590140031072044280c2401103440202c3d00c000e0051041c1c00d115921800810107a9000748129080d240c1c0140590382c3d00d60540b12043d0740c0380c4042d00c00f0303e070406a000380096070250004c4418014801002e160f40285c8a131003d0001618043d4235010741000c1e100c9000034036554040c607a99030301c5a014034204039246140108022208000d02c50800b68220540b0b110f00705130040100c90640d0002010700d00c064849040c0545080c03420b030480385807100c4002081030f5484210000c1c210141090381e007441900c0360000c0a1031250020b2041c90070407607403c00802010360041d00700c1040e45c05c1c00c0c40005600b40d41c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 122789370 1250 122788120 122788139
    0x308061e0d05070e01050103110d05040606050a08010b0909060919032d030c020304080c090a0f020313120302070c1701152c090a0305180a0312020d080c030610030204 73
    0x601d0350458856115000070000014840070341c074018042402c003003010a100c91500039040c890041885c0c00183e540c0000750402c151a801072011b480d0182c46202c401d40c444015600030203a685e90355225500c41c40008070b0b04d038800580c2a100d0701c88000034113819458841c0001076102d14400407000d000540c0c21280d615a10f070342d50052001002c4e0081c960141c00c520b40607044a02d205424000c54008000a02512000249400c4c600700191184502c0303580319800240245450280e260710303540000b0074030807206541010011485d001d040c10017810095404250f08174480d140000700b00c40c10010040001c41c8828038200800d81c100000800c40640345a054900003d89030844030032000b01d250400032a0a20301c0207076045440941e01249182004c1c0d24107603480c160520020100240003900814500300c98041c0100c1c40b01c081d1180d650b0307a03106c2c5800e280c1e4020b1550100c00500c95014011051072050701e0950107a003030840702516546800080c030601c62410103c0c4400d164081000007081c181 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 122790620 1250 122789370 122789389
    0x10060303111b0d2d02100c02010503011419080105091006030c05040b0d06050106021b0604030b06060304020117040c1805060a060806030a0c03050a0218072a02030115091104030308061e 81
    0xc1d01079002254082500c10403414245061b071580820150080e1000147d07000000c8906454080d006041e1408201000407200400c405803c0080d40d118040007440c1c050541100b40221608019920840801e00c00e2070125980f602c00a8028a0610400c02c058101903104800520b80507000c0c20807048552034003c190790003a807058005070b1000300041d5101c0b5030221200158482198900d10b810714548403030b141d100e005401d0520030917001001c00e0840e801416551724440e0700a403d54610300e09401d0503503152280344503041c41445e8140e21070104004e58812140308920007001c0c6190103090071030480310004020b000c16014801c070391481001c0b4040c0341046004603c610000c000340704551040c82400e9405013048101420340000b802130880d04a2001c24003440c00c0c00784c1002801080d140004407010655002c1d40651030443c0d030441c100c85c1164600e0540d204003100703000300410f0170048000c40c895440b020b000610000007080d021701d00020341c5800b015500f26aaa504403544d4009848000f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 122791870 1250 122790620 122790683
    0x120d060e13031b050703110303040e0c09030118051009060209060d1d03040602150c0f0307030b040605061306030207080c01020c1b040513020d1410060303111b0d 71
    0x2140310070100c10036a002640040190341184850881d81507a40d400c0e40d500420f00005003c45640740da28501500c007001690002c01c90001941d560b8100050b40b5101a0b0100078070500a5003030000300540700c070390b401c280003000758000014080f1402c0307035285a00034090340c803044404030707002c01841c2c0f00e95407400094080b480c0624400180c2d809007541880310503030f00c0c13009003095400510082000507000314200304080a400d1a03070803156500000100944600d18020803074a60200c00e00c041c1075491b500408003154103175820003015440304100486400f4001c0302a1214030f60340e001303201c80c80c426006031403040d110341f010f6400c2010082d003507400c1e80c101800d90111a4400c0c00c000c0080442c14140d001d400c182a68100003038109502070503000303042440d0183c0038180650b018410442d4120010300141480800d50788900c0c0b20400020280c42184400c0e40024242e8901e0401c80c500860308405400d4200441800b051400c000e00000b94114a4180c801000c801c0502c003080d0042081c0c0f000d00c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 122793120 1250 122791870 122791891
    0x14010909020a020c01090906030b0609070e0402070b040b180c06071103010204030602120a060f0501050901170910110f0301060e0105040806040308011d0f060616080f0a020d050c120d060e 82
    0x71300008001444514958401507071035041c10790030400b15072a02c01050300030809032545220756a031a01c05594010301c111046802c184001295400d001240424038003d42c410703a500401600c6010801017140186081d40c0e600d81c00c000c03610301481c6010001404000e2280c90380214042200c40041d089801c554000e613132140e000103c0c101d402c0c030384004140d13011142d8181080301c50309041d003000150306c072400b07510306000c1d00080d030b541684e01410005880300c007000100e400d5441c0c01103000384c607001d02c110480c2c1c0303035401c0c01441e11030b015245040d0703003070140c00501c681d055070b1909000322040034100c0180c038103100c0200004104846c0a01c8a01e1203503020741c4608496514110200c0c203200a625201482c07824072000b4040c03925a2204102e400060446117203131128a00c000842a009020000404103c40028444085542c44029161900c8181c003515840303554a801a40d507840707034482c4601c3d9a004403403c2c0c01001d906402400080400c1c281c001203194603440c00c2e0006200503680072031030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 122794370 1250 122793120 122793133
    0x12060901020a08131505100302131d03040501080f100e07020105070e0906101d04060305010e0d090303021c030b040f0b12030f09120a0b040f030206010501020c090114010909020a02 79
    0x81c5400000703013504601c1d8000f1010540000d41c40344081c070440b88070000708140e1603030302107010001d000c5940d0014540050000b4020948994036000400c0c8054100540031a0400c1c0100518008415581203680603101e01c00590380b060080303100311000500e00310072201c1c69400400c41c0d00c101c48402c3d104135440e400008d100c0c108148040c2880d04400e8060303101e01001070401001c0d07201d01100050302c2106052404010f002c0011075807400e0f00e0012066001031500d40e000041c404150480243c0402c001c0c00d0714500d0350400c0c0212800d031303294000a00035901403000503803e41009601130006920300d1400080ca0003801000800350b07250800072300c40c080d03103500d484480c920b0801e01194041000300029072030944005410012070007030081047c46400c0340e8034100c4541e6001c1c0181041580c1c0310b044825039103414076203c000d41404010940040c81504000f28441d400002c1100c41a50b00500358201d50386030441540d016840303c11014104104450000351040d01800904001e08654028101e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 122795620 1250 122794370 122794387
    0x80912041214030a120207142d010b01020a03050705010b0d0c030201081006120c09080102040605040e0f0112230601060809190807020f06130f060f020a0c050f1206090102 75
    0x41c40000750000000b54104100032505181c00c28000110000c0d06a00542c49180c2410000050b14071400c6080c1c0134021985010516001107400c006c44180b960080d00b5035001c2d8400e00c0742201c040054260141e840540444080390090f0080c102c1d15110340008a40e42c281c00d804038043c81e034040000c444020f512078003031086603004098103034404510606403807186d140080080c1010702401c0100001c640e10000c01040d45c0c441c59455000d01400d0300203651300c90741c883c030040043c1d21a1040c0d030351512034280492a0071001042e0b01d812110000300b45280035420380c8590521012010380c2c403a060088503d200c0c1c60391800d1060318005c241e2501e4040c0c0900e0110302e030300c0c10240810a111000a4004031403400a2035007015203038000c0d01a40c0b0200681100b2002c20018400d5070b1104119002d045000500c83d00900d6111050b40c0880da2845848440700e0000d0342c0d5810f0030036000307040003203101d002e000c141841008020349400003070680d4084001040c50b9030522000307030707804c2c0c0b62650001032541 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 122796870 1250 122795620 122795633
    0xe0d06060b12070302030403080103080306010c05031309060b04080d1407020d21090501080c0309070f12170304081e1b03030a06150c060e01060302180603060709150809120412 77
    0x10f40c440300b541415441c601d05076800400da0501400000c01a69001c004a05143d11494081d00c001d540241140d540d07048155a0301804900c911130120030034140803010840340c507000300303840c121403a81005204c40351420b03000340d5600002c81c074404440401030003441c000d0390740c410102c1244d030302408030301018045410b2000d090307000400400045c070032112400c0103640d0744074080c9030f8070403d861240c075103075100c941105041c0303c1280c2c0800a8404040404601c6019880a40340585c5c8294084a82da103820f1000d1020390008a8020341101d809100800c980079940250104079140c4009103441d11050004040d060003034072980700d810b070344003208201c0c803070070f40707200700805003090500001616140d13150003000e20309019001080c00c0c1c0c40305040300300c82c0d0003500140c01940e80141450348003c0aa15a128803501c00c548640c0b00e485030101040d1030394007501709107094843e5090b508892620084040d0360b040005490b05005101d154882c5a040c0c160704007401c0a88401405440c60142a08048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 122798120 1250 122796870 122796907
    0x21609020d050108010507050d020304020a031704060f0905060403060e010f05010f090515030303040224040e0415050103080927090a020a0b190804080705010e0f0f0c0306070e0d06060b 81
    0x604c0341c2c542000c0c805406d80006c16600c03030407184240980c0d81e41e85c920104070300203a1540003c01040d44400c0c4000f940b14850090070544120741d40b0b445440149603000c8070080800c2c404c80340c01040070402172002c240c05400010004881c078001040c0e0080300545001150000d90003900102c0c0144404d0264003c00e0003401c0d0001020044081501300d40e1001949920000d08001d10404007480c011840d21214141d038240f22030440f040e2600c550f9541ca40384551038003220200e5142c0f106011220007010548100f038140ca8021484909140d40142805020588206060360180302c407590850341710f1a04582a2042400d20f01408400403a8070500c9030300110b9030020400b400050060f1014150040c0c8406501d61580c9419002c984079414001454410079101801035420f01d406584103450004084a003c5c0110044409a03100701c800640c039441104809640750b004100810030240c032900e80d45003084d0b0003d025000c5002030f40e036104111807099000034810407004c00d8407100c0500c4007114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 122799370 1250 122798120 122798129
    0x106090602010203040209011202180115170f042006030a0c0e0315041101031b03090506070507080403151805060103060606080906060d03140403061a0604030b0a0903021609020d0501 80
    0xf9411401c007607002403202201405040c079003c030071110302001d42d564002c01c040c0e45001c00f1107220203541c640310f903541e81d142a000d41001045a912000e210b046400c0315092046c1a501615001910349030345601d0010340200c083c14204008030107448940da510801980208401503002440ba0290003000c3c1051081d004824469005007004001c02c2c6410f51400c1d601540c8800040351900100d00103800030800d15404480b4840c1c68040c84280f16050352203010000e014100310744143e075585100f02d030688220140200940701c00e00c810030010300003078400f006808041c040441e42008200c541c001034400e100741a1500c1d80900010414400c8610a03000600180c0c581042641b80244016944840c0034250714062901d0750307211000d042c466000300c403829500058031680d499403424448080c040e1340408072802c80356005e0940c1d003031404030f0459040300d0348180c040c0c00654694100b00010440c00c42d0035001d50140344120700d4203d400f22061000b403e085140103031207500000c42c4030100c5905802 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 122800620 1250 122799370 122799373
    0x2010e01020c030f0f07060e010f0522030f11030c011d0a050d05030304030315031e06290a172a040f0203190e0712150219140304030c0b040819080106090602 69
    0x240c811040c2d074004038081d4ae2061500780980ea41e25614418600940c0c000c80080d03a984a040300070080200d0f100c1d982101e00e0250180200c0040350408045d00d44240103101404035465810400342c2060400030981c8076134005254540381f070782e610081018003803001d01c02c81e81c5400c004100001c254242c481e1810304105032490045642c00c6a4400015010005048c01c0c1080810808010045181c1045c00e80c03550100c80a07046280138002448040c4030721401d680301c0c460702000450040283c2028003080b0f0300301c80040181b80e24085140004030b001240e481c036030300404440340300c1c143c94034059a5409600d40c400160f882c50190784040d51075860b40e024505590400184d5801a1030001c0c1610a07101400c40311401d10780e8526104001c41c82c0540c0e108407203400400c00c5003611500f0034181460b041385803107103180b101c151600c1c1615031104940003004139500f00c00001c003207269181840e5015105904003843d09004101c4440e101610b0301c0c0803400107444000500c0196403041c1c201c40108150700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 122801870 1250 122800620 122800637
    0x2030403110f0a081e0c0f0c1c0c09091a040302030d050903090904060203090102070215070203010b150406050d0f0513030f0c2006070f050309090105060c030702010e01020c030f0f0706 81
    0x40c4e4056843c810095611442202c2185480056008600f1282014466401c80b164410650440b0ba2140c070000c45840c0301c0c800b01320500910104c0060785000c036540c80008500c109040c8a180001800c2c84002502c1c86000c0e510310301e0a0b0b01010001c1d60203a4002e80055440303e000d00a000240c8400030152202034009208111b150b44a00c0013441c1c10590283d0301503140d5948405050090064ac400a50f004174419580d282c02160400180703481c900075002800f89440d02028017081e030100c0310803590010010001000000c3c4948042c05040030311090100d00e800415012405459042d1280300c20801420f004204141c0c001682c580c6040c2d07181401c40902d90580c81384948580c0350030088100e1440001042416a540400ca44050742d004044a1101c00e50b0308049980390440515140559070b0310b00040b6545c0307080c000760751300d441604004515016507580119000c038170000d101415441581c4200c449503509000800160b0030b840300416440c141c0704070140c075182c801e601c500b003840b1241 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 122803120 1250 122801870 122801873
    0x60c0302030711030f0d0908070929041515030b0108060d0b060d08030108100f020906030a020a14041404180314030c04080706050a17070e041a0402030403110f0a 71
    0x201c00d032011035420110750290000440086420700c0180113014000f406440182e02d950780c1c001d200e84041d103107401c01b03d0700703c0c54540307000c0340455903510000c442d00400e03803034070003103001c00b400e08524184c0e00504085401c50314980c044c0d151000d1030b0000c800010f20243c4204545515101e6200600001d1070103100a0502d80041411800c50390400781044940c0000107045881d100400e0502ca9804503400e40d0fa0f60707640c985d044c0c0740c018824001d80400c0c1044080344c5642c0da24002d55001c5c034002042c0b6442d6072115900e66000798803113012102400404800100c40a0945000d070005051b04d120f10303680810f0100404c07044a40c10b070808058003003120404004680e0210311044000310300781381c6a5a81e11a00032030003d034062540300110500c2600c40204d141e40d40b21001d401c2c00d69550320f510343c02140385030501891440844460000440ea44c2d006009440c0c19000a0b02075003800d00300400141440c404035090b6401128160040781d10210a440c0c180010009202c8400386180505580c0c0002d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 122804370 1250 122803120 122803123
    0x40b0114030a180f060203011e0506040e07121b2705040c1101020304030c030e01030507020d050d020c12090109080601080a06151d01170d08010b0a020109120302070606060c0302 78
    0xb401501c001960381122102c3c0c80b410303044428a00d034112007a076006152030300c0c2c1580690301c24010323041c0014400012400040302001482c056a02c010302140c245800c100043c2a41c0100070f11b00d0302040700000c080d54404100c2e20600243c0030303212498010040700c4d010090140c80d02807402900010659141c0850b50b07621561110030b6070011100400c1200404400300e44100200002404551001050104040d0003114242e03234a84680c644444040843e00194100c42c0c04031802c10141c0c02c4008400c0d2040d04c218000d140e40c0c031500704014209514201d48601e420b26907441891a46c04c001070071603176581c000703848600601c1c41300f0051409606040a1a89689800d4402406140c84816801d1300c09802040d0300c0241040e0312015500002c0b10041c0b8681810a2241c04062203444c4510b00100e50046a015401d021039126441e090346480f40303103850350344600140011550790b000020001101e500b011b1040c60415500961160001c3c10080300700c9800754071004c1071000901044000980 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 122805620 1250 122804370 122804377
    0x1b16050d02161205030913050105090a05070c022b0602030105040509010216030311120901020304060b04061401120603060e0a030e0301060e0c130b0d02070c0512070b0a090b0301060c02040b0114 85
    0x2c500d28501070f000d03075500d842c924500551042c554440601ca4810030b120040c1e41c455412a00c01b00e80300182d9898046199045030303001c0c0c1d40840060030050000001d801d10160381c140d11a625802010068001c0010501243c080b202c211040c940010041000d85000d01403a030b0481c01c02c0d4000c41c500b001d0908c80000742c04c2c40081c02410b1546480c0804000c0e0301751006d40700b900203406090a03882c9425803c40d8000c0d44102c4003100d070a0300d04480c1c4003240c10103116030407d550700c4070220700d59514072100540e1407203000300050b5906a15090040b000030801c3c02540101340c8048000c081c9006245005099401aa62981c0c080d80c9010000c004441000030829004110344514590b10500081401503145054111580c1c0c11800034444003d4041a4020000c090180304078541321a141e00407c42c0d0f0201d0408440d0701030b800303248103004010f0300390000d102003001070800c550100e654400120b65500242d00c030a011030145007410056081a00404115860900e03002607030300b081040c032011902 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 122806870 1250 122805620 122805629
    0x601020708120d11040e1b0405060d090b0a0506060d091104020a020c01022103070c020402070507030507050f06090a090507050c0706210c200703170c0705030d050d02031b16050d0216 80
    0xf00306c00b9406103071f1240008540140c14050810b56a03141030414044c0a05002801160602400f8002605a19041c0318160142000030091854500c90040c51006045036900a81e03610380c18207018070030756403103200810b2060140d8000c1d00c00106035000290a01000b0880c4044031841403500303252100c45076003100e92011a07402d10150141d95400403c009000f2604001c0c580c0c4980c1c0c03400f1060000000d05d50084038406c4034121115042c0c2d90903c0594020300c0710460300214035031002e1240340c010b07030009640000b5514203181486605203100d4509669a486100454810345d4101d80c160103074176900c002d405034604144000850010000d1691a1150500408400d02c648645400100b844040025504494150b003140090307944002c030359004100d1074170144600c2c540081c0d1410041444136801031291602801c064001101348003941c001842940d01244d498812904420382c040540700908415160190035201e5243c014a0054030440980542d030118440301440c1d504c5401c0041a103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 122808120 1250 122806870 122806891
    0xd05030703050c0403060c110c0103110301050f0f0310050603120a0e220c080603010e0705030a0605040602040b040603020a0e120c270106050d05060105120a050601020708120d11040e 80
    0x10f95506407264810300498100600702814061141c4400b580040114552031304081566942210800150304035808030000c842800d405100402c0a4030f00404a142242c0b806410b00e0384a62480001900303288040f081c1800c103540d51010321100b41801c01501031090959030000c0d182000902c4003501c000322002d5814410790b0881c0e804080c801424840058802c0f1410050041c24202c0e40c0290408404580c030390b0003507103001c80c1484004000a04c1c08120f40703001d00680024061521500080d081c000d105549041e000c002c0051000c02d04001000140403654005803612002070005207010000354a2510504402c030030107030302880c041390107540b00d241190000ca408100e10030100d81001d00942e04041903c428000082d8260050000d0840071138010307081095986031001500e403030007045620500c01c0e402400082c0c0ba004907910103500000305004071207145588100c014030300300400c4e64050387c02d400400c1c00c0e0004600c41c0540794004002e501e10509080c00c040320f06070791000082840161 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 122809370 1250 122808120 122808131
    0x305060f060c1c02010b01110a111014030703020d051501120903121401080607030e030405010c03021501030804081915180c0801060611010209030a0b071202070f0c0501020d05030703 80
    0x1522003c002c006107030030002c4803291907042c81d0a00030b0700030300303200002c640400c0028041d4003c504003c58010704066214450f4420105028240000c04800ea803040e8280482d108080500c40d1885d800340d882342d009a0b4015946088111117881621030240910200d8410300c00c145840d40e0b0085000a032440782c2180002e0813a126007801c13100b90392442420f103101032416803091141c1c60180001c0b81a980304508441d05521400700c01c0b42160b03446c203601c401d02d8100740010301c4107610510690040c01d000380f0458041e00e00c0340480c240644403ea200321a00c0304001401c000d0480148030703c1e14960019482c240d0f8442c0c5075100c1c0a21a110b49003056074040c2e584207142240003410303201d048919088801640016114000c55008200c24081c01020a0609142080c2c40a05008458203840098054885014a56108a10920094081b100380030601702070350301406051001c0d02032240540b18045001072942406400c0b02c01c00c0c2c000328115008000c41c100d540d83c02c42c044903001a0701d407400140c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 122810620 1250 122809370 122809387
    0xf140a050303072a092c0f060103170408030c010509100b0604050f0607050d05090102010b040b0f1509122b09120602040e04060b0a060816031806090b040b070305060f06 74
    0x10007400a80240065620303008243c81c030b040ca6013402862902c29a5100c841446d494180ca41d6070f0300680540070712903405080140005017415114840740c0a040c0301c007c0c14144c40b208080d0540d0064000d5406d181c1d510303401c200c07080700204408800101c640703004020804498022942520481c0a590b0080c00101042d81c03440d01c803602180d8141d0f80000940e003603241e031040d005015038805070401380190f0a00b0f6403031075140341900c5514141000184240c032200d020f03030148100b03c4061400d001f041d15052100148079181c5459082c5859030401c05800a06000c010030300507054042c031010411502013aa51101d25040a103a0041c0d03555408071502041c60361801c3c40207481690001c84000040400b44130400c02c064001044800c0111020410703543c50300422140104211081d003140c241c4501302240c007a001c3ea2084179800069280b80c03041450303d4403000d06541d501c0c84125002120b40c8100400d100c414505642c0051882c502803100e41400d82c0080c0f442c2c4440b280991040900140340c0c0c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 122811870 1250 122810620 122810693
    0x307051909021b06101d010f0501031e0c020c041b0804080d0b060a11010c020c09070c1403031806010602030a09030b060d0b0405030a0908012703090f140a05030307 72
    0x5031001c0004880720351801c3c40c01a8000030303d52007400600008642040d1b9030420b4200341d00d05030b4001c64602e500c45442c24004601621602c0c00010100d01d00240c443c604190354010700040b07640a400920700d840401e0244411109044d505614074120300d02203100715903002080360741160b00030250985074806400c0800040400503411584204001184030807503130401003a0f2508104031000300701c04107100d60182d032502600c0701640d90002002000401184c02900f41b58009401303101c208000400055006146510071340f10006026042d1100030588201048514090180303071020b142880016140036161040700e01004018200c5e020005505448a10510203080d80145031400c15040c14140b07aa1a5030044d00c50b240000d01c5480c1c0032031540b0381401020342000c50b0601e1161f004d081c0b00c00031020940c442e04210b04001c1180700006040140c41810b0b400b801e0f500741c54480c0149148100200da508603444103009070014010a00480c0004841c91a0411040021080d5440300094070307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 122813120 1250 122811870 122811907
    0x60102151005060c10020a1805030a03021e01060504020f070203010501080f070315141005120c010903020f0d15060e16081623030a0b0f090408070602090d05010506030705190902 78
    0x928595102040d00843c05512062900b40908d11840c2c0e95070003601d41c0141500d581c095400540513900c00c9040c404004126810401c076805001c000091243d11480010140d0303011106107120101d010401c1410b40c50280b01d600d0040290740c0007405400001d0407244e48590140c4800380c082d00c03200c820042c080107950413900301c85958030202c1055240556400e0f201070054080c25000314680c5078036040481000940d1084200140c4944c040305145900b0003402c40100e002c1c09401c55140d06001340016440c42001102c1d800200c008182d2604013003101c00e8206004280d2440c42041c540040300703c3da08000b4454100c50a2001c01038a100007644c01d4504842441c110043d8407410b54012200c0d407681ca02071402815080e82c1400014071540803c0110000e5680d00c2c0d90120b0803801042c0055011001894481e11807040942824100000102c0801004030107a85d142d445070304100f45032905202000c013421b0708a404481e85000c1c940b0143c03241e84280116901113030700142100d440c070100d02c5034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 122814370 1250 122813120 122813143
    0xd0804060921020706050c030d0e070504050c071101020106030b0402044b0204030201050909040c0e180f01050c030106030c0e030d0302041a04120818100305060102151005060c 77
    0x4009025800d9528400c070040c600405005020702e01c400705d80244154120340000c4a40c5000350b0401c406082d5a40042440042e954a94441c0301c10004280e11035005e144e1081d030031240c1807a104ca58505200395107120103007489045914020b82840010002034003160081e030192030000300d00065010940750100c40c605520f00300d040001440130b0300503c0c1400700a0340d030026455490455a011000d600303074012804001c3c081030341408044554180702c1c0f107140d4494016070058041e15518003c1c105484000d440801d1032168a034a1040014010000110a070501000810051800041d0103407540810301a1104040d1100c070440121441802480c070708490060550341354200900d0050002c3d80306109044040914039002c40e000d8007030030203070f404a5000d900c684942c001c003903542028a920860700c040f082244001001682e48850001d2861481641c40c001083d0801c2000a49080a43d41c13820318200c44103030802c03132030201c0710036854101d8405851158590b901c0e6000b807030070050f02d0450b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 122815620 1250 122814370 122814383
    0x311030115080309030c0a0f1725050f032a04020f031509060901030506040602031801020712030f091106090f060304050d201c051605071d01080d08040609 68
    0x1004030740c555010004004084c42181140d400300412410300c00d1a168a102c1e031032410440b0700e02040b01800c4004030404a00421040c3c6005000c1d8281d41c61054a2410112202d0b01003c070b0103000909016504000b102c40481c02840f408036035504402c0030000341c4e050b60020360740312040d08005490b42d170140d075081c5040c2411543c482c5042c1b101590803c045c4031005100e440f021020814a04101d211141a6500100074014554513a1140c0303010703520203002c0000740c040c80c42034030342c86100a10180006501c101e404003100c10031000020f05440303c0f002c0e440b00b003038030706081040003841c81214208815815119036864003040f40c0010348100c80c42c103406401003000800c00c01000b0021505090008030303901d60290f850b80c40d101e5100441c40d29007034104c0550002c07499020181c594000322043c207440c0c0c508549880c3c00d05c01d981c15548011502180c140d401400c003884660300310b41030028041e0740b41c070380b8100962400e0850b81c3d0f208006900742050005c1c050104003030140c01d403c10241d150700300c0c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 122816870 1250 122815620 122815661
    0x30d0f02010b06072001080903070809030a0f0303150611070302040b0424090509061005041d030d060603050c0a14070c0302030106060816030606020c060a021f0605240403110301 78
    0x2003540040c40785d1110039103200c0c020f090480540d8007030745020f80141c0d02c0000a5050491075a290040c0e42d2011080d0f980c18406c41c5103110000320010b9001c6000b81c0303c0d03034002c01c0c401d98242c004070b039110943d04020148202d07400c5008141c0070000d915030840b90100c4001c1200c0040e20003081c000c041000c0300c50301803688402000184001d000960049419484042299540d0076030b1090303c940d001d40d1783d0303e00301c0f140420801552829410041003545100d4000e00c0400f11001e0342da24651081d444046a00e0301c1e820100101070300761240035030007a145110a85410328200000307010b6001d0070303995880d00c080442c4407030501100048402c055a07000d0020032102c2d48415001d444904c0c1103e058002a0b014001c0d1500e061082c000d020445400c1d800502514216500b044030340d402013021241103100d003203846030380244020254500c40780da080b00003410600381001d001d06d55003410002e000c0100c180d80c002c00b20703120080403201281e13007006180118125000002c1e02410894407003110b049080d6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 122818120 1250 122816870 122816873
    0x40501140a06080408030c0703030f0504050705030d08040203030a03020318030d0906050a0b03060415020d150e0f040b22080705010b0a081b090705091c020102011a030d0f02010b0607 80
    0x11a2031592640c222852000c055598200302c41ca03031821076006201c91070500c00f0640180360900640704241c0f10b4100410310445c0000b1300011900304660654040e4051402080340b030409000d1522000c09918001201c0e1601da00071075940d201d05588442015800800102c914921040560848420310142c070f070b0b185011603080010b040340d40c0c0140c0c0c15601d00000305500380b101d841a14241e01024019144503600c9454030440c0700380352084060110380801c400a010f4a452242200f803400a121088138281043d02e4503100d180010144407202001c00140004603081040080c0d201504c2c283e02502c102e91607105908c0c000400710300810341d130800304a440400c41d044d0804410307440292441c0c20115500c1c00d1690762484c003060600f01c1c0c050f5030040c090050500058059003d42c03541002460080a940803500855003104801c007040703201c0c44070710700310340e4280160124600c0622580294020b8200000c0d01e40d0310081441d000e016050141807082d50003904040d419000080840303032074040d075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 122819370 1250 122818120 122818139
    0xa030302010509010c0806030a0209091204030605180109030203070b06011206080c0310060b04061d0306010b0715020a1409010309050d030b010306080106030804180b0627030703151a040501 83
    0x1c3c0d544a000c1d5081090f0020780c1841198801d104101c028002c20000c80b00340c080c0041181c004c0c110076014020b01c0319000400041000400045100720000101458018846241c00c0c210f88103003201c40e4100310602000c02c0c1d001040c0c030481500255804090b031684401031703032400e08590000c2d0900341000400190f191010441c3d01c2078610a07003c1c1c4006103014040c40f012a50742d40915000d80500340700600c041ca1040c100d00b41b8a05501e11500010b6603850300007490281d00740c1c40b0501c120800690641003002607000500803140314081542024201000070703000d50310900d4000003074140803e81d0042c583c441d40141d1940e0750840103a802940c806d210003809001c0590041e80401d080c00000030b00d0035014441c0c401103e810800d8581400e041c10600d04070301c06254041c85646403102c00604440e695100142101c504805000032800c40d601400b0314064840d44805100380c112500c1000800d000c1045804803000c80d803000a09524400c1c240e001d04800c0710401c941152800c000441c01800c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 122820620 1250 122819370 122819381
    0xf02150403050a14150c0d0209010e1e010f1d040509011b0f02120708040923010821031501030e0f0f3405040207140102120a0606030212060603060d020a03030201 71
    0x1541964015410404040800381081e51125920f00041000500e601f10903400f51680990516202c40500c80f00e2000601c600b8141804c50300e000401a10381c01d6960b08032400700c40080b442e0400c80c105c0b8800294840001c40ca02521900031621040064000783c420750059028105841c0d00c4494940a074400428000b103405030600544181c0741c4808580b0308507170546500c80d5002c0c503c646070600303004014000d880340181048098250301003800741c00c0500e09403039018042034402003100484050400c94401c19084803101542c00030030600c2860716807090b03500c20414081c200030079004031080b00c8038a13152815885400e180200c0560250340780c400304441d135144402545141c1b1862070000d820204000d0380c10280b40340a01c0c07200800c510b04068002d1b19903103010f40d00c1031070109260516142668010200f0344055445039041040102c1c4511841c4082c210b1071808605000061008480c01c0b880901118415800400040d615980d003062980000e54003400203043e5541c0d0b031a001c3e020f4030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 122821870 1250 122820620 122820653
    0xa0906020a1e110d0b040201091e03062712030c090321180803030a0506060a08070c03030212010801050402011202091e030a020a1203080703051608040c09150f0509040f02150403050a 80
    0xe01c002e800003449182c0c0000c035004407520750509114ac134038664901004050780c000f94100004e83d0040402048224407060708954055501c52845401c03200c1c0040480d107a45501c181032242c9020700b4400b1030800e0900007040c2181c0002b6080d4030301e001e80b00340c0d4054101c4010b6140c5440400010402d181c000c4080d5008145800c0207010f03d07114041040500e00bc0d2086240004004400150007540309080d03840c4040d01a0074010703d03001d00580a6a00c03040260004070f6075a4494046c80110759001060b420070142a12086090100120006603540806c01d5255188070007082200313610359003171100c507401c0b580c001c20014065980705260700c1d0461030050190f0201c1c1890300007941d4640640501845481d1202281c40302c02c01c03074201680c810001a00c240d074071425515010503076104034429100d020105501d5044290f107000e40303034660313503007550012802010f2010510002408098000b00b00c1d40d411680346c560103020f0100c5058501590b0300c094000e1082201076800d000c181c040020021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 122823120 1250 122821870 122821877
    0x3030503090c03031c1503080307200d0801030302150c0315031015030c1d01151106070206060a0609050d02010e030f120301031e022107050d05030a0906020a1e110d0b040201 76
    0x10360208075903074011a51b0740b00c0075002240400000e4041c0d4402c000340e102a004006410076140904580380b450034440030368032008149108014804d03d46c04020108074101c1c101c3c2c06500e145007400383c0440500016050448131050050150b00d0f075034060040740740c0c01c07104030010049070044c030001c4950110070788810b031008001114041032071503274403403011400d040100491417141d00c0c0803441c0f540c10b22804903540812800d41001203a00c80240300321406a400c50b401409907003801c004028091802d1341c080f0741401050402000070f500c03004103844442c1c0e024240a880c840ca00408030b401d00030345000900060107100b00440c0c0c02c80b07118010310b061701e0140d820a40c4001c0c810300136400440304014007030351101030204a01078003041c842101912080d11411340d40381a68a01c04500e91850540044500e80c00c0494141d8486610198a42c01030455100900700ac803c0d50b06c5146100f0b80b20480701c40e103200d01c01c08103400d02040301002e00e507552000d4003000001d019414426004103041e60200d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 122824370 1250 122823120 122823131
    0x512040b01141503130201030e010203071e260705120a0c0201060603020c0606090a0f020d0e060a060510180b19020d09050a05090411030a0c08070e01060903030503090c03031c 77
    0x114104a024251403100c000343c3c1d00d1a41d1910b1a0f4030f840c180386088228105603c610513007152034030a0014502404450311502d115004201c44506134110306107404080000090a0413607940034454607080000307003000310300c100e51034000048400340704039841c1c110f009036143d080c002c3d0040c00e588100035814480e4002c1001036200c0c10b081301030f44640b000d510045d601c000049500d03407030900960740d00501480303400110b0404450302002030307030080e070720615038155608001081c15600f440b1007517005440b8141040348034140000140c1085c500b0000b40104508841580d03008400c0c409440090700300340694a0b2980c4962041c07440241c01144400014002c0300301c60000280205070000981d08000c20150b0341c107003400140725500c1e20007031081d1140c03004401d400c90745803828012308000a019000300c0308440d082c0050340d860b10145a006210003052100100901c9600c441050262603041c9030903036981c1c480384442c5282c44810103103540d042c00006040145004641d03030100340101c1c880020b014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 122825620 1250 122824370 122824409
    0xa0203032a0601060906270b0a1805180a09050604080d150807051504091103160c08030601030507170a060f0803040f170307140730120512040b01 64
    0x2101d103401c4c4680f030017144444609100c840e000b58149446d04041042840650b0b21080b8808104149580402c1c0c0c11200091800c442d02d074081c116031000020815204450340c680808103414800c1060b80c940c1d04101200850210303009904903c1c1d03000d401070110f07403d9003414207000000ba072040ea0110b100903c2c0845444582e0069920b5004607098503014251a0f480c080c02d0040c428030101c0c900300042003c01010501140b54403030000807002d2000c5143c0c9a26005a05070703541002c2c10340340001d008030b21401000041c071100071a07902242c00c0c60003164540720500148e03500644a00c416190721540800c201010390590f000104a42003105802480ca82c0c4141c2183c032489140650110141518030a024843e080c420188125415000302c9181c140c80391185080da00c1440089551500107050800030548124030070b10b007034401e030380b401a01803100003400c001a15035900010072080068010107980c0e80103806842071341141c203d40300841d142c50700d88180400d01c02d01900b24034100c00e54805d0b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 122826870 1250 122825620 122825623
    0x506040b09070f0203220f06170c090d02100e1c020607021e06030c04031506050618060c01090b1014060a03050a0b04020a08060306010504021306050c0a0203032a 71
    0x40503840058102403075921034a000703c070304103040d6040c80c055201c00c0011000b04048411080303070300da00c1c5d800030358206070801c0c01c1c03000740c1d01956009008121000603e00781d00d03c0781140580d0007903047d0140c6030340c40708008042495060709420180d88040303240c0d010300005800008100b020071040302c22030703203588010050080241c840f1402a400c074009010500c01410041202128000d008403100c01c02000d4400180281c2e1007125502c26199021a040040012004030381c6840f00001c0d00034000c0a042c038010400f81d0080401c440c3c0d40308000028001c41d615504210707014111410003c0c0072480f000e003080c5405903404d8903003e04102950b200000c00c1c2000e4002002403200c010700040c548210790b10100c014001c094035081d4090782e525807244040d62107100420b025a040d4459908529003401018140b0724160f10290040d4010042000000102150201640c10f2030900d40e858090060102c1d20780040d549000b03426100c001752904141e900d10349a5107000f04000201e0007110015008103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 122828120 1250 122826870 122826881
    0x50a0210020a110307060215060a080607020304030623060d14030a170f07020d0c03090f030308150d050c100302090a0b13140a030201031a0a06081f050904030f0c0b0a050a050604 78
    0x40006230024141108040e641080c8103401c060300a000e59182c54079081c21604100043d10400f0142e40000340800400016018503101400c84000104070507421960aa00c40c2c84028403440c400c40b10144c518040212407c16164416a114100ca817104038212002d48845000d840102151803610000340c03220002c001085e104040c01d9010381545010383c24162408102404210140103d0b802d020400d91140302c01040250f00950350f10005050450350610b84445680301c050062910000742004203a000601c4130f0044d1007682c60a02401010a0440082c041c030020701d0380c4100121000102090040080c0000001030b84060100741d40d01d070103100d1221840c03c401034210754001010005980254088030300c9240680703484520101034000140d007910650003c0d400b20f1855824000140a000040744203007100090f00c01816040000044494100400050407c500d02084a8199108040c2c4c609450f501071603c0369581802e410100140000b203610a11451515000418514160140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 122829370 1250 122828120 122828129
    0x5010302030a06051b0f0901030c03140117010608030408010c02072903040807061d010c05040e010b0a03060f0e01050906040b18070509130b10081909050a0210020a110307 75
    0x500e40d02d4500c2d650480a0400184600c0e481009038000f6021850714400400d01155600412543d51128000241c110350196007424201860b204000c04107900189907281556500354070720700c040141064843c0503121607081004103000c0440c0000e80808150040c00c00307001150203075400aa1103804c7d01d1500a070241b2500240c3c9a0460400490513090740155040345c02101c40342e00c3c01c0300c41d45800080d0fa070118038188455044244440385ca18080c4100b020f56442454254901442d0a1060720700f0901030180c5080d5410002d041d01c81d19009920480043c4130140340044025a1f41c101d0030b054002c24440c803030003200c0070f00002d29586030503c00c0708106480100120740c054946110070740c1440c8020042e00501c5020440c0c000155980d130320345e04c58140f10940204130300c00c4403006d101002c0d201d51040c1c002d000384041400bc000c1c0301d00301084811540b01c032000401850a040040c078040c1c260368041e4020084811002e0940e0303020840202e098000c6981c1390222015409042d9200160f116 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 122830620 1250 122829370 122829373
    0x803030907030809060d0207030c050106090c0f030b190305060f061009060305060109030b090a031205040201050a110c13050601021e0d0e180c0a02060f06030607120222050a090501030203 82
    0x10144001000c081c050400b10134050141d6040203042e01049080340d20100c3d060300450f00500c140d00800009001d18009882e0000c8144494891000050320304500410f8402c14117489241126450b290804a80408000910b91500141e42c0b814119102d0101303650803c5103141442c00124507040000c02c40380301c1c9109560f1401c22500e848421402072102401580c1041042c0d50004080f8007007010081c01803c04a014003190503240c42c01805052000381d940140301d0a140070400035170b0b04a4161004040c00d801c180307000188600ca814101042070610641c0039010300703032018a4040c030380e000b90310581c000e8080346c2c00c1e201e01d08640c00c40d05900c40710031406503010b030680b16081c600ca0f80e111100000060020011800c000440ea00660030803158501201030121300c011126a040010300c0c0c02ca40300d03041d058120301300080469101ca800501c01000e00588001c8200001c80e40d904450b035080e80d0200032000c3c02d000c04000d0302c2440751031140c94400c1c0b0707070b5071008a850040391064904032a4000c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 122831870 1250 122830620 122830633
    0x2130e030901030905010b04150f05010305010506030a0b030a060903080103110105070b01090b01020f030705030d0c050313030503060f03100501030c0603020a051206010c02030d0c0b0a021903110c010e0a06050108030309 96
    0x400443c082d000079202180c0f42d548070301f10103100b070f2510b0040c2c00008050340e136145602030800c04800340c168070603030109040608000c0100704130745411045030b0700510041d00c04104c0c200818007007442c0584510f0700411403032400694409050b0b012400c40c4c10707030307104250320400c046690707004407218000d4200c0509001303504001000050a039901614a0441c1030055035031300d0104244a5045401044040e03441e40c00c00594070161007a680b00b0040c040741c0d41e042c87c9080d0f0802c9002c1410351850303100020103106c000000319003030f9580c008881203020002030443d11203d41030b030f6110014082c00e01c4220f0b04000722280100303542c1e02900076504800c2c480eaa40b1810590804000d60a01c0c00c05003003603052040340d01c60f290140e2410301880c00703862403a4035004020071071481c191001e004010009003501340f0600525000040503078520302040428500841d0201980808034441e10801180f81040d43ca80a20781c20541c002055200c556800b90100b000541c0c0d0b608030868a0788801c5611881c02d0f08074070b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 122833120 1250 122831870 122831887
    0x30603020306180f0f101b0c120203041701020901030c110a020918070b0c0c0a0605090415090c020a1b0f0e040609061e180b0604090515010306020702130e03 69
    0x7440b51041d241c240c20115400c188203a101305061140e24888200660440b15001d010800340d80121201410700501c5070070b4850700c0d10401000d806014030010301c120b001c0850040600e108200780e4018210f90030f030608100403040f007068000d600800700c01d804641440e508010040c0528030180101c071440024240c1603502c1e5003003110078034000300010b017141c80012200000c9481044010007903e200d0030000e1b601c02d1005c0c840b900d401e04036400284260f100c42018401594824155651a01c09440220760458042c480100c56419600701443c0349240c07101001000d64000f07000d01c46a4040c54486003501e45255194100e003c55001d08503109942d1641004858a0f05500c20f40c09401214001060806665054256909040c0070410030403a00146010f010f10b910800d2000400010140507903482c070358800744001c1c0c004280234481c5a96503c000306004c0c0610a580b4225950800c000440da100c1c54860000d400040c41a8000c45029214150f800381c00d00c94001e100c0714400085040c10090b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 122834370 1250 122833120 122833141
    0x30c030606051e0c030705030901020613031409010c02030a0302010c090b040302060f070203030d02180a080604150b0a0509010b04031e110f0612090604060515010819060803040b0910030603020306 86
    0x10640f041c1e590030400128440910603c007a01440d0f103e013000d1039440103400002490404068a034414200400207001d00003500031003454585c881207591147c0321000c017401a034080541500203074141c00341c8099441003580c194032050b480200d170345484448945400000e40e80f800796010094009004100d2101d020909401919810b071000b81181c0c9402204100171050360410594a05110400d80003040289049403c40c0058902d02d0018241c03072034992039400c11011011907034840c503075585240040c940c0395820b890016000c040d2080a0a595500c100d2070254024402500c0700c140c04400340240f500b034003c41d610903c0e00100040c140348414401c0142c00d0f088a036095500c041c080080c81410b002c0c040180c1d1113509640301078887c9207441e042803801e550b0002e1201c4042002500d1000d0280e0304031030440d801c510810b003180400c82e0b00c840010002e120710342003442d41e8800442c000801d0380d12f071801030083c00016103920350802d0900070141c00341c6001d400003d5058000c8400112480d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 122835620 1250 122834370 122834407
    0x3060f030807060f1d060406050604050c090d020a171011070201021b010903060906050a0f05011d0408070501050c04030c1a030a0e15090a031e020a0b15090a020406030c03060605 78
    0x180400d002640071280071701c086502d14030b0003200703101e50001400c01050005500c00c0f980c0c0010142e40600071841e100c1c800010034801c805c51188501c440e82540000e544aa444080c00f8142d90300200c1030401c141098503646d810551480900c96052640c41400c520341700c800d036084554180c00610502c0c480c4030b84503c020f4113140c0d4050401500707034000004a4080d000e0031841502078880000d250401211401c00e907111440b414484504142c010442000481404281554454031800c225201c0e45400c000520a01ca0b01825641c01d00c0140004810340324000d00803244504100c80c801982c450100015902a1110b600c81d40320074400200a40c500c0d403c0908084241010b9542045030740e19501035000c41034610081c40d0748564215020140c20094a0f4480210000354244007075018800941c2c03a0b064400041c550b00106002c2000207007002420403020400070300011492909135040341c020b400c40d2240c04002400d00c0c40c180b0245000744070f00000e07220180d07145498001c203502218081c51 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 122836870 1250 122835620 122835641
    0x1412031207180e04050c0405010b03060d1707030806091305071403190c06140702030d050c0a050d022b020c0609010504050d0f05070806220f0f050a0303060f03080706 73
    0x1050882d0300a41d10540d140c214050080101541054105820214641205038000500861800d401800352000c018290bd91000c422990500e94001901c1d15408000421928000d295002700700441010341081e9124464201541c0144880e581d03000c1300355400e00001000342c03046e0440300090181368500422090b00580107821152100065103170420002605182618400c0501c00140f1015034480c4c40c00c540d000242d003605040c500541c002a80350318880b0b0b510400d010b00040d00c42a030403c1888410410b40d000800e0300d2031440752050180d12900c43c5036242d400c4644091401c2c640580b14100540080b015500611041810070180159a84021900c506110003030000155682e1090101006203101d00200c1c00b070140d07146000d40c5040d1480d00b1296040c0c0103081005600c4100030a00080c8652815039004100214206a01c2251004001900300240222514140540000c2140b0303d0380c8240c0d0100541d03580c411103c2030300400380c0001001a40100003101c045001500302c8a44031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 122838120 1250 122836870 122836877
    0x90501030b01210f0f091104020d060b07050601030b06010807020c01230d020d06150503150d0f08030610020610050d111c06110f0304020909010b06131412031207 71
    0x810303000118007440e186a510075105143c40c1c40c00030f607030350702240503042d84000c1d035550512440c4c440c6e56416074000e01c2c40007e00e006c0c940c00714043e03480040e140c10080040c031041d034100d80d50b2440c03400d0403521a90240416500c507401030f40411901d511500c0b460384255413950103410748150080c0115600d52190241c0c981c01c0f10352107903c6150103840c5004181083d074503400140d4489086280f441520915442561507825680981403540d400c0021241e1149044d44050304040b07a101c005002030100708805008418016100000c0299490095018003000c8502e900c016031411400c980e94001101e180a40c1c12602d0000c11950400080b2200f9041c81040d00300883d10100c400314140d40054103100000c040c00e41c0200090006520404900d010640034251621144861041031488083c00003401407044200040700300a00394810190740740004c0c1b915594240e000b8000180f20b1440c000c042094121140351141c500d090b03250b84a070031007900055402c1c03050785281072080400090401c0b051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 122839370 1250 122838120 122838137
    0x4020906220c020c01020c04061d040501090b04080307180501021b030f0105090303011a0412021302090d030305090f0102090319020d1506060f0203031003082109010504060509030a090501030b01 85
    0x1a441c01d4015200d080390158002c1c100121600e00091500345861651400ba40c5400001d10072442044144000e61040600090f6161654500b450040099071000b4010401c84010301c0304010881004500880c41aa00c03806801c010380d10500412038640b00c1e00d030260f8050a04644e0f8000075221b400c2040d9801810307a0040c01900a11600b5101c00701c0c0e404400b5007001006005000500030600901c2001c24803d9003420700b000c00c405541088004082c0c8242c030158005c182030107068045552800024255014500080c64040e0151400303544202260141a6000001c2e100510a0300c28044009008110301405502c04403898031900b00d0503038200180307911602c00300303d507001c103003861408120000031418648003000304500d02040490007150410024403002c260b54100c054241c940080c40a6643c81050300b0001c0000803c400600541121400b01701e48403d043d803025110764041c00d400e001a60358a909152a442150800c002041982006000a510070b9000e01c00221040c140b0040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 122840620 1250 122839370 122839429
    0xc0f04020d020c03070624050603060d320c010e060304050102070c1d0105090705030406050a0219030b1003110f03040f0b09030c070b031b0d02160f0302010b060304020906 75
    0x30b0b41c0c04402c0700000f5a00010b244010400d5038491100d0f0000004007800101c1c0801003060002c030341903c50503200b00c0d0048003252845d0317503441352140040d40c083c003074004104e02d12030060404c0007030040c58080040c85001003021484041248211071605945503840d02034040200001e503040035205541940d4240308680009550106910141180810b1003846101000c0f440c1c3e0280c10580203d8040c40440c414441840d4101040e079804c40d512040204140c0d458000c0c400080c000c102d01c4402903090b51030845d4065805034440c483e03020301501c102141190500c015820707032b209400c0e4240e001c50204800030016109001454105101c2c0d21040d004d0003084d04c40c940307000030688a64416401c00075400c80b1070501000114000c00c00d40d5003050071450060010301c1c450036208078410064a002820309a079100f03d60480b0314141203c80c402c280680d0504043c05203125080c412005907107004c180c036590b450310405803480750354020320314405036030746000380449020550b000c08003850501c0300c10315 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 122841726 1106 122840620 122840647
    0x11040209090705160b07210b06041721030a0b010e010f030911030307050d0825051602041a0f040e0316020604030c14040506030d020c0f0402 62
    0x1501e400d0710700d13003220002e01c20560040450b981c12080010b4150010140c09682d00043d00e50b800000c58417a529041700e0941d00180c0c1d2060042c0310802101c0d003080450106103840800351401c1a450201c07140e9144401004c040040780003104000c1e1410721441644074422092806c2d441081c0d0b58000600905400b04000040607103030440102441b210030303041d000201c00581100c1c3c2d1003005040182d2100c605052100001d015400898910b0f0f840c2a100d007592030912000840109581e0340a6800d6800300b0004420795160280c1000543d56503c601d0b001000701c80043c0848410641c00c102c01c1e440c0b04401c40307201d9441c16a02d507101c06000002e441041744450080020700c496400020a40d024a0384001e014a80c181c402156032100120034103581d000c01c0c0c4003840a51145010191039801408d907880069220603410151442c101c00100307481c01001c1c1c0b00615009140c006d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 122661870 122841726 := by
  have h0 := BRFrame.cov_init 122661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 122661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 122661870 ≤ n) (h2 : n < 122841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
