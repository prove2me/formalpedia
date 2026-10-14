-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0419
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:42:58.044294+00:00
-- url     : https://prove2.me/submissions/341fc0ee-586e-462f-8baa-5001f50de0f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 75179858 ≤ n < 75359714 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 75181108 1250 75179858 75179873
    0x1404030e130603140706020a150506031213061b051c020703020a0b09030d08100e0c07050f060105030106080c01020c0910050604080102030603010c050a020c1012060f1508161803 78
    0x40d403042d406000c0d01301c00140110304004c82d45c0c114004545c004003503d4042024043e16071001012030000043c1e540b22000420b080800088254140c0040000d10003840480c80c0b40000480e20580d4070887c0c184512154454044503942e4041e0886d0b101d00c4042c0c6100700c1d41c4080b04d02c032040b1401294003956503030f80481e80b801c0c00c640c0000440f00e80820080c6446c1010b1010b501c1025091501c1c00082c85c080071901d01c24405400380da00207250180000b206109654100e690a41d00881100c00528111620503901d0109008a174025400d08800240b10b403400a152640454140c0142440344940c0e0300340503200000420003031002d28030380000500c40e00e91500510203072a4503000503907039150540a00d0b0a441025980800b00b200030050300144c0d640c0030443d26041d5108859642c0040840d4900300d038030130310402c4c1006146160400000300b51400798502004c07159000e001d011803180c0414161102d80080b034070001003140002075a003007144140034004240703034840740c805403144e101c2c0c884d0123 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 75182358 1250 75181108 75181121
    0x3030207030501050105040903080c0a020102090409060507030c020c01020a03081909030203130b180d03020a08040f030309080a0c050105030903070f0f031106010f06030e0a17030103151404030e13 86
    0x5015800502050060010a004281c0940819282801247c02507540240101c0c03004001c130400e0000400d04800c900e10030b4040722428100240144000c2d00c482c1007600080c681a960070700468680114034100e240045400015072105030080c0c031009045132020784100da0002c2c01c0450007441c81c00c0c440710441c6207206035415980607500070354985640c10765a807814103140d0440340f0035502c244078400c55168100301211040d84c0c217a03801020380009180592800e1501d82008111030b002040100d002200388183d4070880f4041d079207102d0100d81c0c51036166182c0c5110407018008100034801409194042c80045401401c480d0441c0c0c0b030410581c4605500c0c00d020202250284500b510107014140e00090000000d088040988000d5140849614030114503104030340038107496540d00e0010240074410800900d4124440c22200110401c003d0110b0713000b40001c17035000b243c00d000c0e018840c8181c403a64940005000c110b0500740c0320b6850603a10101103004007079004141c456050554510303400313a42e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 75183608 1250 75182358 75182363
    0x8011809020d15150e0615070303151e0e06130903091701020316030e28060e15090a1a181006080708010902090604020706020903061603050703050903070b070e030703 73
    0x24151406807214100040c0c81c0c0c0c08a0011160036046c8040b554840390b03286d0a200e044268580e4486051900340c002c1d140200c09254603168041c80000c181e80700030b009842c028105008440d00e25210500014400000d40344c1070b070412888501d6060241c400d1b03010b40c0589000e410701c205c007544c2d80c40e0f00b0862a45840760000e80c03a5008000d00c110465080c00040007080319023018003d000348850410b80e500c00d810f03d20588584190f000c00e0300d0802c3c0c44560072107503070041006e00c0b950200f80344541d95010084a07500c0c1103541800021219800030030095040d0341c0c404142e0100300c42c0082d010141090240c07504480348900f00d00020340c92410041415000421880490703c64231b440c280c9070401d0b1140d13000d800aa410b142041006a591000e41640704104540050729600b0300c2c00d1000090044600c2c03182c0511551050015918100b201c040d01c80d810f540e000d001d25611102e044003510303030580309601d160b44244000700000e412403060980c00486482c041d9600c440500000b494080c1030f6009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 75184858 1250 75183608 75183611
    0xf111201020a1404050d330204030203061305030a081f1202030c1f080a0209090705040f090612150b15091315061107050409060b0f0108011809020d15 66
    0xb4000040d0841005001c1040302401a8282850f00f800302d25030141036075000309165010540300119044c401505a0f40b1030b417803881c01100361540340e0740c20300952203030200f03912a20a00380010902c0071404618210303154030002841c10b0041c8482d05a510640143c0300c41c11000070106100400714001400b80020868031034070b440307601c5907401494140140c200950b4000d030300b03201c03105611366400100074001000c1c0d0300c1c0520840e0360b41c03030100b4024000d60102981c0309519009103c07000d0b41c080c1c00740c41510016009054030a42c0c9005401c2110190712944010902901d5040040707056102040b4100030f5100b00410500c05041c00102009086102032034000707400b03c0c0003d242e061001200069070203003102002030408081040b80c0842e96407140000700861514000e8920f081441407900500000c4c00600c4601d02c2e0b0f141180180c0780b031917507480c02452000204009581300b000c0f020304880034000c1d0207985c9200b001e00003010b803064031000c0c9e800840390a4800009401c40304001030500c6900c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 75186108 1250 75184858 75184867
    0xf0a0210090f120e0109061b15061701020703080601081302090c0408010e1617030c07060804060b19031e020603040809030f0703030e06030a240e10030b01030f11120102 74
    0x410706520f1088030b01001c108840c41070402c072166040320185d0180c030903070b0400150321884480e00130240c00600c0750007010404084040c466103849608141c042e1210010400c03c071170100c2094a080703009515010340000ca0808c007080595000e010b01c1a08642c0d81e989481a40a8940104070841016100000b1000300040e040040f4007081c41560920300700c0e0b60142c06a944401c0342c0489806140c043ea18000454211409160f501003085030300003010442911000c5561f070344081c1440008039030070b0340ca2034100003a00f0090700c1c0c0b4003503490501d00709081c171450080c21070300e07441909078502400c0c201c0c00c0b85c0005c40c0405691980040c5100314444d0391515510750121050504044000340200b00980c000d03d010300010390440001804080700743da0581d142d81ea02c101200103070141d0704034603a4041c1c10102e02ca5031081d002c00305609440d40000743e40702d1911501c400b24661545848060403158504005000003012114200f0340c031030054000d034620740c11100002e00b80710b41c4d46149001e56940001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 75187358 1250 75186108 75186113
    0x101203020a05011a0303030a0203071115040219031509030302160503090a0f030b041b030c0e060a060809070504020f07050114010807050402031e0601090e0a020408060901060b0f0a0210090f 83
    0x103052000d013041003403d01d41c201c2020200340c0e64000940050040798000c00002e403868030540865021070142011144840f5014144928666050301c0990065202032844440556a44080001c0303991150402c2c0d580d503c00c580440c003d000d500da08408054080104900d15605c0c40e40214500b40036070040c0d40d940400c0f40421190296a41c001140711500c003034100085070040900f603610580043d01c5c000c81c4203080d052580307100456040100795038a944404624002d10110075485880281d0381d00e100313540c80d1001625800d034116108491640010030a11103410709402606805000ca446d640c02d1141a594181c00d5440403582a040040310100411a4007820040407000b050142d0b811032460904400c001d0724038103158400341d00d200701903000c11a141d1107000241c0003000010341403009824a0a01100039601521801815214002c042041d0755410301c036546c00c442c44104020714041c0f407003404690681107000e04000794019154000c0d80d038031090251114480c810b208030b5004842d1032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 75188608 1250 75187358 75187361
    0xc121806110c03011104060c080c010f05060418050d140d051f0b04030506010e090a1202010209030f0106050d032601061e0e0906060d110f0a030606050708030f101203020a0501 77
    0x310410300c0f90703040000300d8807850050f10483d0103950142c5408900010315040402e40c0f0b12804030440050741c6010340d9180381c00c519502c0b660085008031014030504010103e0814800a0040d000d003498000d451160109401041000741d032800842056050600303045e145d80481c0e0003260b20030441240002081821400071342501c01809850000700c4c00d090950302c1380d5a66034814015801d2a007030401c04208410000c21454004030340c00016400302c000e026500a000c2d4001e0300e0464020703c117038400c55020440600600041d40e00151808040c07110940b1b048400c401c0a00d031000c179080074100d440071101090002980030388010307219034241410311508410329a070000c00700c0c410000a60300c0702400341d42c4c03002c08603000134046815a803210129400b8000824000540c124810310004081c0081152580a13189210842d1020407080390b541c602590320303100d90000205204010000200da40101020090700032411440301e8600744d8681482510101080400368050ba011080000400409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 75189858 1250 75188608 75188623
    0x30f0105090108070b0a030902010306030204020c010902132003060117010806060102120a050702101b060905070602063d060c06050601020c1c080708040f06030605040b010c12180611 80
    0x1080100541440e1003181780b0103004004c500020143c44101d4801568402e4101c1c0001c1d6400a1007103564421403d115802022074180490140c03d44425440500015100c0c4101c2407020300010340c40300c1d055425101440d88002c0c10181071081107803980c1d40c000000f603c41400307800800000e10080c20b120700068604a43c2c0594150f07090000c02c080c1c12003503404400d5802c22a410340306461003a032890402d80f18014010800420b0b408001c0500c0b060029680000390024012005c0e280e00781e071691012a01e0f044115030702010219130880244581054402c0c0301c0e4810f0b841045020341c2440c02c0d001c1150741c1107550100c80064034001401c1c0901c4440c0c4200e540010003400180081c845400100c0c4105800092600c00c005208a40100303004010041b141501da01100182e65940c036201c06c00aa00e805000381070020307141070800b00300d5051510819042181c1616080c1080340e1035981c4c0300b80400e9203520001007240c01513040000c007510418100107041035071500c40300a1015444185003c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 75191108 1250 75189858 75189869
    0x91a0406090608060a170d030f06050105040e18031b0f01050f07051e040b04030b07030c0815030307050a050106290a030e070f0e01090513020907030506010311030f01050901 76
    0x50420040001981100801085031150700b440c000c5552100c0000d2544222680940400c201c0d50300403040030f01021a5020903024991010031403440080f03400401c840d049d0245501041c4100302c240b1501500e000319944c40700d140b83c0d81600d04162640f15508580011025042c50420034180500f0325209001070f00783e402040000300420728002d0810419400041c0600062140c0001d200010400e4007003403440d62050423042c265101e41d2084050a698442e20040c0c0c1c044280704082440703503100e4010202da4040d6236a45450329103c1d202040036511400503510f034548020481500084d606004014001d4002c0c070000172194901114400c5042040405012144135100140140e0b035130101528220503c5140c0040c2d11340300003143c1464440d031604245007501d110080041c602c4115400f0728140c52080d0030034003545d11520034002044140140080d4407202040008d05c2c0c1a1090388002e074055414540410750001c050100d06d015401a19035118080e07011f4014845030500c1c06041d0f00504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 75192358 1250 75191108 75191159
    0x7120504151517070806010f080c0613080607030623030a06021303020d0b190627060b070501090c06080903070f030e06030a0b040b0f03070302010c0614040309 70
    0x25299450241c14000d000030002842e64908004403480c0700101d061018203403030900810400d51004a85680b400c041c03107110294480d6400114400030b6007007644046805034070080c8860044101000400d4000b0820f982e490406a040052842030400c0b955000d8440f90710009449130074003a041d0580340280404e504002c0030210461502c0d2000200900c800350820740c0140c41d083d03104600c0c0002c208179030010f980200286019418031100038052401044c090128010204441d82d100d002d45025100c1c0003d11000000380706018854401e0005950818030382c0050b003280c41d03e43c0c880454001c90403e5070300d030f07640760743e0302082044e90307094000a800a0705080c0c66510b04060416640c1c82913101c000d02c290340e50f1101d4010140100d0b2181c50700500244010b48a18118400130b00500182c0c00c064400c0f820201c12003424104000441c2a400c000780c0640486821030b00103452100900008403492642d07400015035109040c1941c40c0610703c681e03943c90402d0b181144101e15040515100b94086 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 75193608 1250 75192358 75192361
    0x50a0c0e13110c010905060a0501060309080f07030e09010b0a080a111b01022802010b0d02030d210204030308041203060b0405040507020f06011509080601080601090209031002040b03071205 83
    0x39078807040c60aa00d59920704011070125a10341611910f80282400700c0d04a60804a400040100108500b0320441c0380e881c041050b070381d039840e0807000d5070101070020705150407c22085078400a10b000506400f4082d04000d0318600646001c41c5003000c00b41c1c081010703074001050344040341c1c1d44021082c1d0001e11005043c004036041d4070441703040b485000800309554412220303103040c440080d0141d43c082c2046030140300c0741d80010312000b41c036204c095582c60010b51904c48000858980008640c036000c0d000b400410b004210340328103645040210280c03c500a0701c2e101c2e4070074000160700040010714403a66520440c0e090600e406807040b040b0b075a019040c103040120034805a20107109503422a00d045502151b283c80e1080240e0418000f502d0078146402400008500e15040d85010168450b0559820541e203a459040a8807854203008035404c0d80c0001d40104031740511138018040c00c910013419108a210002401e00c1207034000d502c2048900004400c00c040150004090501c0a60710035050169 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 75194858 1250 75193608 75193637
    0x7020f120d1401050f190906030b010504050702010207050a0201050d0e03030103141c0c060c0c06050a05060307050607020906040c020c060a0f0e12060f0a0b0d050a060c05070b0c070602120a050a0c 86
    0x1004030991076800fa003802c004085055003240c1a4030010b040587d400c01c0302949904080701102c0d000d0091134000d03403c06000c0b403107c900c148200e5084540260107000e602c0b03215801198141d100940c403403842a10b0b803c000380968014070055000703502c20300580e000c02441c4003400d401d0a001580605400082c0c00b0064501c68221380d00640c4264021000240903070010002e95000000f490040d158515007801c0140002050740142d02884048084440c081d50710f40c1001110300c120070780290000039100205e246820030740c0141d0f950b40321030b0040d11040304072040070032401e4101101040000311103010801c0b0720758111412010010303007500c2006406545145441e91000041c1c01d031807050302c00000203000c0f10001c9d8403180741c4020040204002070b06030b08102d81e07151030258042d6080da1520604810880c00b804c2101c070701641c4404a01141d558040b418500d0fa00f12200a640b103079002c04c16010500310050046100e01c5141d0f600243d541060b13510360080f100c1d0741003e4010300103020782c0f5110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 75196108 1250 75194858 75194869
    0x81b1209011409120a0311040b12010807050109031506150c060e0703080403080c0a050f03070605060a0e0105060706150e1816050f03010603050d050304150c080f07020f120d140105 79
    0x32091110304c040c96a03044042011001004020501103504c900801c011401c401c105009000c10f01c14249401d8050341c171001c0c1d560f04c4845500c1031034003044241c6010000a101000d07500344e0703524500790015201d0b9031247d5481d882030294600c1000261041c45100801189104907105244040000d095603815903958511500c00c42c04041c1c140400451461641c0104000c80c8003041d9000c02551003840b6450040c0e0f940c0d802020044600c1410200041c44038109a08203900702e405910401079680d18000501401d680000c2094810300c0c0c40d5240c2000c04a04440400020460100f41c940d41f441c0400b00c44500407031202081c6d10365040010f0005901580e100f03810b05454045510350110110040040d004100c164030040c114028038030b204000c82c1c3c02102070340c4a2805800000101d00010b4030711300c00c40d400002c50502145960000c01c03240303c01c5c18100b9a01001500440b64072600d0703030840d1440e01c00c032071209840394400094082d813070712154011103a4002c10002402c0003541800005203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 75197358 1250 75196108 75196123
    0x501080c181002060702120906090d05070b0f07060b0d02030606040b030a06060803090109060203122a03090703021302070209040f030302130e04110d080a081b1209011409 75
    0xe0140001154007072a24414021031480c00200034414450009004000ba4075010102d5820015000780c00381c104010903c20110791f90110014105403800b584030040110a404840c030644262050340d2001c283d00382004000e0044504500e00a03880d0303403117807070030409594400040500800340303141c0f000010380b07001500580102044401180c072000400100e440c3c0b105694003d002c41e0700305000005c51007001700041011040a0fa03550003541c0d1560300a1740c1e60f02c02c000f0303600310481303034100081c0111104100b90a050814600c1c0707041540c0b071b030b1620f20722141c0054984800f1900007400400440c604290f650300008203812040d41000c90680000c1d00d010b4000307201501e0558045550010540300b503040f100d2800001c0b525680d4652228040a50307500c0032141142c0d04c40c500202d044103072038200c1c4860006ca074410001850030000d04400c9aa03041e0103401d030720740c10005c0b0810950b500c00075005421015078104c001d15083c54044003040c25221032060301d88030b4140e004148504500b0118602e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 75198608 1250 75197358 75197371
    0x10060501080a0c05160b09011409030a030b06040f0902130e010b09010c02040b09040b0712050c03190e1209011403070e012105010b070b0a0c020309040b04020c0601032901050108 78
    0x240710910b48015152403166171000c003090940d01103040100030004c20054060300361800200b10b01c104120381c40741808029507543d5903a80c4203201080e00d0131300ca90448044a48040c024a0130580d55400c40d2103402c080d5005040b800342c0109946a280142e00d09140003864000901552035140000d03e01c014403401d0600c3d410012920810025511745800c050340540000e03084924914240c1020600d80324241e034030f40c00050340b07441011681c400b18002d4078020500c0302c0c0f20030710b5a101c0d14518510340d1000740e140025103480b07115020415005001c00c04943c000c0004e01c3e541c420b101c40004082c03100000082c0c10040b42030050000c415880209200442002e007000802e0081c049804150007a100c2c000703040d4a1f040400201e0600321900280102601c102242800790300c4a10513181601d0700d03d10b031400140e00070702c040c01c1549020b811940101202903c01880c1030f4070906482e040c201c00340c20030342e01ba800da03801020344c08110003101c0764007a415a449072a29410000000c04100024016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 75199858 1250 75198608 75198611
    0x3050a0e0102070e040506090d0215060d0311060c130b1c090f080c010b040b060a082206050f1e0702060105060322030f0f020f060604020c070f060207050310060501080a 74
    0x40642d008002c0c0780040e09a440880d4403a1034075241141e600c401c100c40d0200039010700713070034415910700000e114401c030305004117035410654600d0180420340912540c141c04102021354103441a101c144102ca0044040c800c0c803a50300c84403400401c0000d600303680442203d0a0412103c0582e0390a03130003a404d03030000c1100118420301d041c1882e010f03000d0550f2016001d4440020011030080055000c10364001e01600d052003400c00c210b00300606802088682400301d0020400562000c0811042c4104411b0307a583d414000d107a241c135898100c40c01141c2008450402c2014082c44160000700000500e2125040c5001451b1510300203484240c18444c250290303101002140343e0b8080d40907000d001207800c019a00c818616410018100c004174070454010903c80301c080c0c03e00b20310100d4a4400312452800406c45604c483c804e010023980000c0b0000c040c0e008880f80810b1201010389d420b001841c01b68001c1ca0701d141024201418428000c00e000001c42c81c0250811940e40c0100e00306500401e000c07030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 75201108 1250 75199858 75199877
    0x30d08041e0507080c010e041803030c0519030501030c0801020403121b020603070f030506040203011d0a0e0d020d0801060305010e040303020c0c100c050f060903121302030a0b0a0b0d03050a 83
    0x280c02200303030744071400070070600528101080440c80000c07503080010382640c2c0c0800030a185c0b0103110459403454541c0120183c0091143c010074029002020040c105150681ca024009644010401c825180240000b03480d400100148007e00d03c0c03900107099404000c52404d0700d141e4882d1018044014101c2c02e0001e200b400c0c00d030240007440010380854000c0e00c0c0c5075503850088001019400b00b6804d5070003291504d808110941018820390b07060f90b0f03054042245602240c4034200d12004020100000b0f02d40b10801d0300d50720601405040300c42002a00204000155210040e0040300160041810103103031400420070b5100d0f1074141070304036400d0708005a4940320b00c0034882c2042c1d94a8001600038500c600c00a141a41c085181d2548500030030540d000c00d05918906610b51006441c4080154022701040e2022101c0c103616640041001858001c1c0d191240d01090401480c0c2006640d0705000504200e900f03017403401040c5c1010000c8441d842048001e40e005481402142c0491003080020344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 75202358 1250 75201108 75201143
    0xb060f01091a0423031902090a090602090301020703090515070201020a02090406093002030403050a02010503090a0f1a06012d031d1b0105030403080f040309050613030b0105030d0804 80
    0xc1c220382c0a00001035050136070640e40912032000341d00405005000384104c005a00c4941e80300341000e4902e42d40182000402e445203000440500808070f07084d5447d070707400c10485400f0b903070034402404e056129403941c001143c1381c10700b00506010020301456003400100b240c40d0041c1c1e03000c03d0030a180e0f0381c121440c0c0d04540f285d0400000078044000c00810480000c40302074141c0d036840c0c10070300e9908611898016140807502d0100d031030340100d100061040d4054004840150300900281d0b81c040298400c6841e801141e13111481c9c415004002964140c460b99110400401844034096002500b03092000414002c42203d50390140540b0385d642404800b03a8450030514070079081403605801903140035001030380c0b6050aa0302c81c03958694001d110101342400901d44c2d402501500e1113583c140d11014a10340c0c0e04c1c1c118001030080240b084007040036504020034a0740d80c00d00038010310241f022160660604526001c2e060080c11b81025100741d101d0001010800e40c0015596409644807420f00c0b045030018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 75203608 1250 75202358 75202409
    0xc080903011503120c150209010516030804060b090601080a0c1b08120114061903110406120605040614040b0307030c06021f180b090a0b0a090b060f0109 67
    0x2101a4036509121180c80150402d200340b0040d01e002d800503281025280000f41c60712014110002e18a481d00c6101040e1010954090500c0c043c040c1043d034503002080b560401124900c20045000c540d600d41400148101c034414502d0154050752080b03a203003805000a4501500185203013802a22141c8082889200d034a031a641e62030143e00c0850070004925001c46950440714000728406441000010265060708034060001c00150901d031410b4601800c1c400c3c0a140701d54000203054403007c009548403c8000100010a6980e680d5480c034817603070071407000791001944064401c0c0d04001e0148050041c0003480341114000302c03400104401ca00000ca4203002c3d0580c005004102d620100003003403a00820ba180048004180c501c00c880c41c1041032a0494400903140e550711410060b0080010720100074840d0001c0043c421290700361015600c0401040b0100c2d44003130740e20748410303980003001042603442e6008802160b08420205100300000d00304804d5219802d03500c00300c0e98000ea1040b240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 75204858 1250 75203608 75203617
    0x206042106021306080f01120210170c07021c0206250203010f090c060201140a05040302030930010504080906070f050a0804050f0f150a1110060303030b06070503030103030c08 77
    0x41041991a401920305840b00f00500f481203401080800c000940b030403070041c4400e8141c2d10006c0000310404150f07000e11000e281100d41c41428804c824000401581a0003402441104480704403991f800841c03042c40859001410050900c03845491312800503a52a030030798084200d141e5601301d00d008689500e0b2000c2401c203201075015482c4c80306507003c1141c15084840d00c580680c84004500382d442504900f01c40040103903008071602c00c401b207030907060a80c010a0b0458000d1044034204851400001c000007621415807010002d6004894034446480184a03081901c00008000c2440c207902d5290582c4500d03a0003900c03e0304001211001c005c0140040c2c040d8980180486180180c2403501b0080b5034405d00490384074403041650303014240b03840030341c5c0e070031a001c003031714200500c00000d2400341c503600106070041c14040c1c070003411035110340f04000482c0c40030144100410308510b10f0a010301103e045001160083c0020003080011510000840c2c2c1142da240c617018100710301a00b083c2805004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 75206108 1250 75204858 75204863
    0x714030114090d0e0612040b0c04090c020601060f0e0d0609030225080c0f03100902041b0302030a0f0b0d11040902090a150602010b031b0a030203010504030504090f020702060421 78
    0x80c10030070b004018000140c0c1224204141d190a00320043c198200440c9000c3c10903200000340e80040010005030000040a80040c4500781e00c6e810552144050300a8078030300502c060050b03001000402c00d01d940711010f8641080107090400643d501c81c808610a0071501d0710150545031509025810140300304502401c20640058036965140081c04a41d03450f000c2d885100800d02c01c01d40386003503038540b02c0b1030003805610080050101030a410300b040040d280550082c0c1e840750b81d98444590507100320b071040d60320b04581da0f0016600d18001e5031181c00c841d401d8a611070800d141090751080f0b0349501101400f034982040c404980c0a5290b40020058501294029000030444040c410103155075000040703581034012096040c01e0b120701d0200d00721607404c1540e80d40740d4402c01c0b003400041102c05058814440250400401c6522500420300b5100705903070440010b100000c3c1003205c0300c203520030349000079680d070001c0d49440100ccd00010701600581c017170a01e40c0b500500d82584881c04a441c541a41075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 75207358 1250 75206108 75206141
    0x60c03030f04030f05090d061a03030307050705010f05160507150603140d0c0c0909020103090f1211160e070507060f02190908070e041e050105040311010c0207140301 73
    0x30700654001c54200042d1800c90100c0e00e0382d284548024020400d8030f0404501070421103c16071b031a15030001074100f8a26090000f00201e002003095142480190712a0f0b119403038443c0c0e203400e44d01e02503003113541030000000308034504820701400008450410001c0c0005180442d15640709040018101c04440079009580d403421a001040080c0440225140d03d002c0342a500e00700a444070564514904990061005080d5041844050819842215006d00614000520740129500d813454692144001c0c0c1c0e251602080c1c030054290710484032001c096019000d030014030300d02141d1400039440345c001e941c8641d0108000400d5035101e4030603510503603007041051000384146501e840c000d41c02070a4511580078400007002c0d0107401940e91800701c904a03402006800d1409c0402502042c02a00c115840c50555102c0c1a0010282034041c04003401080005030904040c50050b20000b10317400004c0040c6d060125008400340c01250075400c645007111819105840440041d00402c2c04010214800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 75208608 1250 75207358 75207361
    0xd1a0405070f080c09010501050d0b1903020a1505030f04290109050601030c0c02190b0f033102040509070503030d05090d05090a060509040204050d031106160c030509060c0303 77
    0x84000510401202d80c84611110420340382c41c1d415480304684008560013040c06001044079520800007403c4503110b100000540c4100080007544c2e01440703031046405900c0e00c190900a6150046482d8000c2065640700740c2010340d0b1580242990100620300e000c1e80c080ca500007030520070030794940e42c1d219039626049154029030040909440001380942c0d10380c0d600e0000002d44550103845601c00700d00c015120f2002c840450b03800c000c00e40c11072009000c0320741e00d21003001a860340c000e03000e0301650003621015501d17440d00901e1421a0301000180080000a9842d50b20768044114290b0b2000f0341c0654004c156556640039191800c6a160300481d0580310004901c0c600c0ba165034459802000c07030406482000c200c8000846a901404600c0b99001860580c00c00109004400a2030400405440541001e60341c800185c07212608401c00d5000c560b140381852107401d018003206030f0080002c0900e110140e0304650042001c14500002000d00000103125110303a030703410065940d4002c40c5421607642c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 75209858 1250 75208608 75208613
    0x3040c1214100507020703141501080312060a0513231609120201090e1f120b06090405030a11010b0d1208090d02031206120a030201240f050d1a04 64
    0x240403290750301107481c040d0010100804225000c2c4500810040e8000c002d80350964803080c0303040002e036405181d203108100c60a01c0010105007458000c0c40094041c43c2ca80810400c1c880390303044000c00c45441a20b00364018400c59613040824070070030000c00400507480c00d580901c4500c1008450181c1041d030500d204001344180d0220b0307103141c002c2650781d6400940342d03100f010f11215502c05070020b0124030a400d080c05102c4403c100710750b010400505480c00d5008403070540020a83c10341191840c4c800103c901c806000800c0c40c002c0e0410020350342c00c800e9260a480b0a52079015100c0c0c000100500c8045143c4409000d4200350641c01d0014190040d01415140809054400300d00c02c1021400080c0000c039103d602103140ca060959a402640c9042ca58052a09805030700900071903106200f080515520101040840c1c044ea00c00e800002d44020700c00401301d00000307208032882c60b0b082c10341001d020544401d607030b44040351401e4810a4150b440d501d0144002026003100000810140040105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 75211108 1250 75209858 75209873
    0x70f0611090406051503040602070201090308160308090309030c060f0d020d02030f180c010819051009051305070312051c050103031407030806010c060f0c030204050307050603070206010b03040c12 86
    0x440c4a02100c080080990304c0080c482840781e00840042041801d20024020460319001000020310503d800942c150320b039a903440036500b2913907500003c80c0704071030a641010740000c0169041070100c001181041c130000b000a0b954011004032502508020032003a402c00100300c2a08c11100d810207055460b00000300d030550094104440100040032070340c0109180b90600c0814120b08079201000d421082c0000c0700554580c1001b4119103c115850880c0c42040002403144902803401441300b014018070304107605051f6880078104111680b000b8010400042e000250f0740100d0398490041c7c3d0008140c440d0688490060440c0c0c2e0b5418094080490013000c41944480c0c10f89100f44c40300045000c030364004c00c2c0b590103543c1340180402d00c0000031840d00d6000d0750400c14072031b21401c2c01140028205070780c0c9041d188112003035004240c02003000d1025203018818040a0b09040d81d0701c9080d89480e1743c2c02582c030481072141e1750000100202150a101c140708a6602401c503c100005900410b85888503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 75212358 1250 75211108 75211117
    0x19020705060c01090c0e010302010507060902060d05040308060102070f060f11030d061e09020403080901050d0f0213050108090f030307110c03010c0507140c01050307110304090507020c15040b0f070f0611 89
    0x17100d0003118040410800c94501205060300e4042e5203003400e00d41180d507100c009094601c0280e900040c140101a828006401400e12840c4290350b028041d003440c600280c60800309402c07041e58191070340028420b03254442600c1016850034034201060503169036415080d80f01d02c1040c11140380c04c00394080798614658012821001c90500060f050ba41d6a910440c101e00490100505801c400c0050340741945c81034000c0e00c0c010203403110001d004032141080908980c0540390114415081403400c02180d81c01c50071640c0d10003414005410080c8003001d01d5a141e02c0010311501c140001010140c071912801c000b42d010f0b049010b4000c000d0020b55840140190b08a0001124000b0041031051701c0180e0103d1001900d84040e10380314159100c8200c2503a00c4803104402800c1880309210006000ea0103002d21030180d0180c4c0c02403c0f212500c0c90a0041112140c0701c1110312400400042044540035000c4601500c8141d00740c944400252a00d06c943d6902694050700311400c20040c80c815400100080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 75213608 1250 75212358 75212363
    0x501030b010f0b0a080403053c03060904022403040309050a080a050c0103050c0d060b0403030f020a05060f04030c0b0a150f060503010b0c07051503090d0804020619020705060c0109 79
    0x6031030380c0d8444068036450900c0c01103e8504109001c401101405801c0c4990840c2c840c0c1440c50420b045a503806440c6605501e1074183d408002007a10608410b200c25003e000c00c40810003407031840e01c2c40104a68640150000f4011001030000c1d4120ba20002d0b64104042c4040d41e500b03503281000e0400906082190080611905010400080c1001d000810f40c40d85540030010305994030904e030040d0001d00000b40701000304041081002c41c001000c2c81080007a1071500350943c1c44504504005241a900b04c20341000d44d80044d1014000c180c002400b01d9200018103441403e965031494210f07a1410340c1480201014060814041101ca59802a082100f00d003500c17125032541c1c610051b09500010f01c82c500c08a6020401440b40d450084010401c0300c4c02841242c500780c0d91a00840d0040c0305039a0640c141d10004001d2000346901440b141c2c07040780c9a031402c0e503d10304003070f00020128802d1440907080010000ea0421541e802440b81000404000348100e84a901c02d0551038060101c40104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 75214858 1250 75213608 75213623
    0x100306030506040c06030606080618060103060503030403140c09010e01090522060c020f1204090e070e01150e0402030403050414041b05090909030309120a0e13020c0118120c020a03020a0801050103 86
    0x202d00c5ea44909c51041c801d05c4024042801d1703000030311001d0301107003003d0031041c1016103500740800c543c3c030100000d10045125030441c0d00081c1c0a00105400c061251130100e1064904400401420644807101070540f802604c00003560748500d50381c40a120208002101c0389645e4510440c02d001d91a840001407240507000e42e005120720340b11140c0c0300c0154200680d9811401d001c140702a004c0b680c81180041d102c001140c040b580c80300d0410010350f6003640320034243c400c4c100c2c078090440c1c0c0c01101c12800e680151019800d5041a680c041c18a004c5c6000d0741b40100e0744c41e402100307559110342111341000c103000341c11410300202035001801903008004450080d00c041000c0740085900004403031080e403140d00075280d01c00307036001074480aa114400300346c00c100100800450030740c1d480710207030306409860f84010fa403800700f4003059007503d81000115001c024510845004610f0610005114111a1410100070303180d80c80020b01242140c0c002a42000701c141d4007094005056100c141030b20f00032040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 75216108 1250 75214858 75214871
    0x90804080d020109121b0501020705061902091e0118060806041103090c01050307020307050d0801060905090f0708130f080304061401180c090503010e16051509100306030506040c0603 80
    0xa90a8032000403008000700c80d501d200c00e905a10904500d0000c0e1b190360081031241ca0180c40d03103070984e00070034401c1d00d042d0440c0060208171030468036400f8003038030070400a60904d441c0d0300c009100303240306c12030b1662108552100e00c3c5132680b26440181c9090b441c241d449841c00c0e1110802002c3c2c20003110400e024070b16020452581c0d130228030941c1c0c41142200c3c0244250100301c5c00440346a00702801a0781540302c1030141900160090281070305030007056941520f5507141000081a408503a0300c050701585590003030106080d4605074113680100181020105e07600ca000201c016007041c3e0030003501001c0e5a001c2c502c200003200c0300440c000c034000e44040c448a41241d4403051120000e02c01c0065110070f1840d003c0b0100c4d019000000403001c07500700ba07201d16580c0c40c0804c2c01d40340210010041c60b0030102c01007036115900400c40d0050036082d82c60111055004422550b28401d4441080c403400450724000940341c0b19030040c0001c4c540c0082034a003141410314103c441d89001d030061002180c100300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 75217358 1250 75216108 75216133
    0x3030f020f0405060c1914060105040504030509040e030408010e03040302040b040e03040e060418081209030c030403150207080a111005150904050a0206030106051c0902010f05160609080408 83
    0x3a126401048890305240c03d15100c00c02c1000e80c031000c1c0350042801084030740e80700348007524000406140148040034542004c1d082860405805070400c500c2185410305000102e0f60010070740703800d00c40580e00080c0b0b14a03080c0c80d452460003658882d40306582407e8a040e01c440300440070300220b9100b5141408402170007000c0005403203526914214507070080c40108030400c10740f6400b80d00140c0140000901c128140b201d000090407a94041d604004c00140c031500c0e00e40844040c0380e001d903c02c0055802c1411420030b003900d80c4550700c00504051441d05541412600a504403843c43d64040c40443d502c6104ca031001d041c03400c2030013005200380186440c0d8482c085090081d548644208411920303103402c04070412a03001d00141c0256020f108500c0000c0040c0c48002c001c0d03010784065151103850307920a101180c40d14020f45014040541006201070060f6040000c030351428204d0700703240781c48440405a410100ca61045c0c054082410100030909001c8408014002c1c3d0784400186c91421201e031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 75218608 1250 75217358 75217361
    0xc030a031503050604290c040302030f01140c0f0c010c0e030f010b0303030106111c02060603010609140402010305190204060903140624030106050904110102070501020a0507060e042703030f 83
    0x340b00240c400e81002c00014006001c03040560b451030854644c03200b03a503182c0000e031200308070110b0f0b00004400700000c060081d072404000103048100010000c0c0070701c14650016003004280508131001d0040301140b404003410141c01650641c64946000300b000c100c50b030070300400480440e90f0303a500900030b9140d00007039030f40706000d03045000c0c1f0007500070751842e441c1c600101e8900700e80b4618101c0030f01603881c0b940e0503a000f03040f080b42c01d182c45030b0080181381050750405007158040e52002400b40c0c074111580b8042c03800c010903a548180c090a00058039540c03400c480d06123204c00d0a2038450ac0b07100103001b213049a000f0b04100b007564006c659001c015455a581181d90f48010780b00304000b041c4941c0074240003586040c002200c0d00c4e002e4004281d803913a4030040b40707000c81c0a88040b900c0c81d00c4800b0820365542d04101603001044244020107156080c2c0e200d07151201154040d000400c43c80d207203040d00903115508140c000c5e201c002001a00d402c1c01078040d0026201202c0200c0000381819096200f42506 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 75219858 1250 75218608 75218651
    0x602160c050604270b060a090509090703030212090102070e010b070615210618080702040b01030204060503070c050a140318120d0507020a030c03050601030605060402030f1f05060c030a03 82
    0x545203c6102d03800d5072116104119114031410030713090388070b1240d40030a888420180c04c00d00544e0310751074801400c15080100402e030007030401010741e0010b10b0400200344c0c00a41c0250501c222851680c1e03c20312131004034100280d035009000601d5000000190200b40d1400408055000340d10030001e820113111000c0724a03019200703041c0d0420040c3c610304400e02043c02c2c150070041c0f080c80005081c40c4459601102900180c4050300c108801181d2130741941080e0203403240e19503003403a0461600d414141c003d44240806030001c01000102102d4900f003080401c0305486140d000101440c4040010764515901d611845800c80c900a5150404446047c43c0e100d0280840340d01010340081e10700001c1c110703820b0304100b03016a849044010000042040b18221001540c001c0c40500115030560503ca02a0760024025501a5104104011042051641c0150440380c40418074440341c0030390312520b10068007034008540c401d10010341454200000401440401d0b11910180300000b0b914108003003e815 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 75221108 1250 75219858 75219869
    0x309080f0c0f010806030a1202030d0e0303070503040f261c0c081b040f030609020108070206060a0b0903011e061e0302030d0f02120d0203010e01120c050906010c0602160c050604 78
    0x3410031030b075000d9070150185581c0410003504654995003c1c3c0c0340c000141540d03500100140c1c000082c1403200c0030385801113841000885c1e0042d803035800c10700b000900c1803000410207480c40c80c101d00c862041200c8030705d0019200c0c18400010003084008a480046075002c281c0749122192442c00d00b01503152140074410055005454032055a0356584407013043c80c1c01040c2504692004010204580588a0440000d140902d50002d0343e460f00c0e100141119002400802c2551701c000c003005890b943d1070613240161880207040c039456102c2c500200e409018038070708514902c003040f86007802c11501e99004800700e540700300001003010b8844a84440c015140d02002e50541c000c0c2e100c051f0b1244c041c40f007000e4441040e20486000b00420609600150015281c00c2c14840c4c000004104202014190a0150802540c041404c80302a6121510a81c0620a4038022041400021250f83c064060240e40c2e5030400f405547d00c0c821481180700304031280c042141c1c80142d0308400700c0c0c1030420390241d6041d1003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 75222358 1250 75221108 75221119
    0x50603010902032e06082d0c1e180402040b150304080901140406020d02070b0a17070e0604080a020405011202010f0c0f02040c030e0105060f0f190f030309080f0c 71
    0x600e9a1050004544da024412545807038100d5008441100351141c031005117454000b4110900c03072802034000740040321440c0b0b031140e50101d1511210f040003090442d00400e0481c0d0072224004038600c21408080303420762a0760320605900d0819081c6417038940d9940315030b10880e0104411004c041c10405035041c011182d801412080c030005001840e200010140d04405041824072941a85444500e5500c00d402000040c0c102500c0030340c1060b01000140068601148050f003010141c2d48014440101d214080403030202130404900f21030700403055a049901d0281c007256507540c4501c0030f0350769407000c25400c901a62509000040c4500c103064164100e0394141e507946110841c0440803106039a602906941600305d41d4180d42c0165250320030000d0174a030503240403c4110714414800e08503203004000c1030003003954034080c000644e00c0c1d412403140b8050032034440c1203202e072200c01d4003415101d58001402d55081000301105240c0c00540350000c55030000f0488005030744410500d43c031840b515994030b4018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 75223608 1250 75222358 75222373
    0x2070608060a0b0301061706010801032a050303030106030b01090b0306090103080a12020706231b0a0306090608030712090308040b07060905250905040b0601180b070b060405060301090203 82
    0x29031240400341e40014004002441c4aa00d406007500b0a6100703038407203808580f9071100348189440c21100d55902500c2424850510340c5035072940f11068414040100701c45048202500c5d00d180c202440d20007418000c2c04980c0c4942e1665005001415033030361040c04110113078000580885171170101d078415031000d0018420750b4a15a5010342d50340000c10301c030080c803805011402c1d0f00310152001d04007081c0a1340e00030611050100203c0d031681300da0060030481c26000010444a50800d0800d10703d04100203e000ea82d03240003030011401041c003a00011680c508249000a0003100003000d0040c103400380d120700d000580030f0038007600c01d404d80d44801018030038140720801032920804042e02c4858040e100200700740100341d4a103401c040d025010a0b01c40d001e407051801c104800401071502070f0044000800440c205900d51031920000101180c0c10000203400000120070110000c0d40148140501107844032602d02d401c0c55100c80454603d4040d620309800103680740740500400022035000360151828 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 75224858 1250 75223608 75223619
    0x90d051204080708070b16030210021c1a01021509010902030f010203010f0f0f140a1e2603030f06012607080a02040308270d050109120507200117010e04020f030d0207 73
    0x45521460702364154016800030045503502400244006903984150b80390700c0610101102c200c0700100c0070804002038404400e400c40c3d030001740c001410440d000b1a0380090340c8454005001d00701c070b900000e40501610344403308003507054001d14180c0f02e403000d01904040c3c0740c60550744100514824000f20b41400e6108010003900841e00c04000340c009048002c903503460b42c1c8511a611600f120086444044100410502d0b0300d11101280244181030910314032620220810b5903800040d02c09010680c110303000c10200c0c4c0c050807084000800d01e07a0b09660118040a410a8400c1c04a44400c0130038525400100c9030b500c0d61084605880e407204107903081492128203607104440c51012883e2042d20755416100175a0b50407500041030f4803800000ca1903c0b150301e413929050559600d0324040c843c041c001e4400181712400d082181112640c080781d650b035020030040302c1c00d4000300301020302d116160f8004128141e010341d03064480c900071b440302c3c0c0d080d620001c28036946403c01c4941400603001610300380003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 75226108 1250 75224858 75224887
    0x806040b073b01030b01020c0a050f040603020301112d0403060b010903051204030224030c0d0219030b030d2a0f050607030b24070305090d051204080708070b 69
    0xc092000c842401164988120101d5100c440030106460304000340b41d00d06440d684c1170065024211081c4003034030041c211403010800c11401406400e120380d05021041000d910b44be44601d0045400400a10441e41074881603612036202d031a11411001d8201c01c900089030303895081a00c4840c02d1405c0510301071a544400c13005141400c585410050100070020200d0010001a001c00002d19801a56207203144100f00e55031404850280e951720601c045000c00d45965400d40c0c0d880600f6400a590f681c249c80d42d000000d12440074560610818072049900c40717585640f14624005007501290310040307030840162100003088031106071018044907000022080d0b201011140c5100700503c0d03104440c07523515103003803d80840b40500020358070070310305076545040d8040800702c58045110b02075540d41f5098032210740c818500f001e8148100040c456505031150b0940c0e1020380d803c00150740c4444d44060b48006a60302910504045100c0e049010030134a20200320713801290b201440481c901401c5054681 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 75227358 1250 75226108 75226127
    0x70302030706050a0e060109050108070501020705100e150304050606040506060723030c0102040803030609070f0c0b1305011a030d09050f090402042007050709020301030213050c091e0a0806040b07 86
    0x82d000c0e03031034075505c900c40030781006101e0185c040c0d944049880c2d8148000140b0741281d4ac5d00581c11075005e50000c00168450f6441070540300220b240020200c9600c8005c81c514510560048101520000c01c1105004012400c14081c40049030140300c03580315402040071740c0c003407484003408101400d1044807028403e83c1e8144040ea000006407400c00000142240c01c9030080d0b800f18405800001c108111380c545600703429404512400c02403907068856000420404282c9002042c003036603200802c50035a13100c00d25240302c642c0b0000a10a9043c450200d000120980c035609000e0b210b0307101d1114030640150024010b0310806070289414010700010401c82503005001a40c105e9540e4941c0204001e503407041840001c009070f489030342c0341c20038502203103003000c8c0354030107240d4038414401440140e440308159402154510070110319502d41c540540168410300c040d09038082c0f062841505080b0222114401700d480480b1807070b04550380c84a0302900c03804100c1e07004002c1012200012072460050311340e903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 75228608 1250 75227358 75227371
    0x903060b0411091e030d08011719060b031c020f07060e15031f03030f1b03051c060504020d0b0906060301030c03032d09090c030c080127050106030e070b07030203070605 74
    0x4204c00c0e82d00d0f10200e4140383caaa0342260001c1e0003000180221428410b450b04026a40d034005c0000034500d400c812000e00e806100140410b8403411184d105a80400121200900c158414a4001204140695108890362a0042a0040160004091b805403040900010000e094042c184450f01c03003038425680028582c029000d82443c4850b0303013808002e60003001e9442900c035032a4454039020f014141c421407080005030300514960410009520a0998a111086c1030080c050560441000b10241100c1d0308195006480843c14050040d0070713810402000e10143c51101881c4c40320b601b40050352009010151825030f01c8441040000d100f2504c203040390300001340300c04509240040000d46501d26002c8100000c181c89002d02803240b080c0700d080d45600e058101007002c5403441ca4084c203205030520884920845d221000c001c00c80080521030400c010a080402c05907840e0300c400340042041e10060121445928004103804031450301311542e66426400450030100b581d6251405028001c000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 75229858 1250 75228608 75228649
    0x25050c15040909121b03020d0e120f0304050f060903030a140705010f0903080a02031003020906040e10061401020303010b03010302130905010911280306050901140103030903060b041109 81
    0x2d0000c02a01c10351010910402e5039210000030010024207100009100301e11240341d00c60300e00000b907000180310581060b40e040210102081c43c00003469003040c003200d110307203015403900c845620b04048001c01c280c40e0100c403190003940080c1d050201500034804a560194010003c1c040c101d406805e548200d1088401d24902d0810b107a5a56820342e0305403222030401949a4902408041e0030038005035100c040d40d2800c50840ca4031103008a0f611b5264400a4000e10014000c1060b41e161070f00948140910070040300d41800c841d4400d00f0043c4424401c60b40f0f443d121000441c05984007000b103d0480f0741600d081803c0d0b07400d580801011502400302c4a403410b54810007840041d400780500301140d400369450f03450384070040c418041c41c2c0700c80340c40900c040b062841c04031200004c0d1030b0414040d6500040001916036580b22814010084100c080c05505014400082010b9001e40311078142d034402c08040c0400c014000900066440f0400c2d0708607229400e03c0f12441c107040220341e0030326007010f4581 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 75231108 1250 75229858 75229867
    0x6041104060315090203010b040e06070e0102031909080c09040b0a0e0106090f020d0b040209010f050708070615090f02090a03080c072304050615030c0706060503030a0525050c15 78
    0x10340b02c0400782040000c00f103d035140d604400540ca02846680f00c48101680c091100d00c02d00f170f45880e01c401c401401c03401404808030607050903900c00c10550380c0360003081e4440340d14070180b030304090000780340c92161003903070700c60000040c2403414101e2055010b690b2104003a02107446100400b005480006144040b540d41e9000014201364580030305861079021160059887e01300da6643c1d41a10380c0310342c0c55030040f80100800c0150780d9015001c0c56920440341350240e21080b491421160754840c0385400781c1828100001d51450709001d1001c00b085920003102000410080002c01083c0d01800c0c0c842c0fa48403404803c2000032411aa00501d16403203207000b920740560321019272080c516081160302038202c0c030380c030070b1448241880c0c490076030804411105005018890000440280b00041c0403181c640d5001c654001040429085074000c1c0070700406480e02c8900f00c24000344160840d405400c0e1103240b00a042d0512011450300c0b0001c1500000600340b100d0b454001d02100e032803111054042d80b0320400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 75232358 1250 75231108 75231113
    0x120601060c050a2003010e0c15090a030215030f07182706090204090e031806160507090c0e040903080109050712020c07090b101e0e0d1101030c020d02060411040603 72
    0xc200b00030102c40f00d82004d0428460402d050031a0300001010015601010021400d0b50b07807060340d00050300b007400d401a9038004010125030303030b40c250380e100a4102198052809881312400b025511070440d1891a00316543c40150071101e0091881454500d15800304040c450488200c450200c4081c410560f03280300102c0f2915001210710540c410880701c2d070f0124041c84065070030301404d03200d0300390325000f113050401d8081d810071302c01e080d803010505c100000100041e1701c0c90003000c040045a00207040c1e82442d80c5d145142c10281a603c2d05600c00a840c07a101ca1000b0b142c10303c50a00c03d19096519104180e0801d0320801c01450050162800e100d643d0f1488149004580010080f035448807001c1c10440d4a40712800069600790004140304201c801000d070500382e44559030010070b00640e14009031003000441d02b61507811015400d02d4001c2c0350300b000b090600400d00c6403094005401c0e038040001034000e540c200e86070070b9070b000340030016080300300490046441008002000c46008100048a540e80d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 75233608 1250 75232358 75232373
    0x40f02030f01060311010f0207090203220506100f0311010305060a050a0b04030b0a020901080a2a050c07080106230f0d0b0a0c021204120303060e090304050f120601060c050a 76
    0x101c1e100380c0d181c0d0720600800a602610007a4880b080c2010150094010000b0f512a1007a0051124180c0e0110000d880349580074400c8811074000034075688210000e090103034482004031070031502009142400038155421180900c1280c0d000b0286c14588800f00b401180a40130180206d54401d0038030b8004035003503851801d40742c0140b6006c0c08007503890b855460036404001c0b0080069220034414002d81751a40d810910b140c0e80440800304c0021580405090351404440c800640400c0c550500054610740d030700100100309801e035500032612216621418079081e51014065030012140846100c1107200440d40d1102110302d00074a444540c000c003a02180b41da203c1000143c07616141c0c0f0303041c0480d40085228072000c950f00da01c050101d50450000162081c45503100d004c1c4054200d401d0801030511130b83c8403001a20741e208d05c3c0021410010381c0203a90703820030b0096510400c0506086001480d101d40c030202d0741c440550203842c2c10303031900ca01960301030b1042c42c0c00d480c0782c0100b520340c40015a02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 75234858 1250 75233608 75233623
    0xa031806060b0702130905150c041e0512010b0f04020c010e1c17040201050301060f050d1a0414040b010302040b01120e01060e0702061e070912050a0201080c0f09040203040f0203 78
    0x4030803020f40342c980342e00400c540c0c60035900c0811340b603034582121080452808101c10503d05284044c01d10140c4a64900c180389229541c489505a032814618081c1c1d0000512400211441203500c0e526140100c07090600b2030f1898540c070b070741c031007c40d280300d00c11400c0c60f8001d05849045040002444104020301d1030400328003c010010510600190341041600240c210041c00300e0010310140504d001da0018001d4070040c0605001c0c44032084002e11550701c100200c07800074026003403c0c040b0290aa041501030b401200580d0300c180c3c20b1200004101802c400030318414be422001c018a103920b141c00380002819085840b6040042051004019110701e00440d12551080000010303910310b0f0042d031452440003e4103081c00c542004042c0030b02e1620410390000300c0b0310801c0d80466a03445821040c1d83e1b180b1282e200c1c9009000080209003400008181050114002e8a805d130165852403c6a201072040782e0281661480c18041034006052650141d54411701c5130444254240d80b44d0002440e1108 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 75236108 1250 75234858 75234869
    0xc03020904051905011a040b0706021b1606020d051801030e0604140c0f030307110f10090311010c021e0607060603050618010b0625020612090c0105040b0a03180606 72
    0x1180e40403030312078411481303054010000402010003001c4150450910b9104074400c010541c4d001141d03035010302c4150b03811960b94180080400d0141c078184084561125207840e040d0642d0380c1499400141d69002081d0760308108a240c0d40c240c80d100703800c3d8441c21420301d840c41e01410950344000b17a042a520800450307009900034408050300006043e403141c0b90100c161505800381c07140019880d102e403400420748258583c04010060640c04010105d51038407200020554004e9503174401c040c00c2c40d002540c4000340e900401060106913001001504c0d10044034070000e41144040c0c0d0500304880c02ca403a5030b001d840d801040320303241c5611500c1d1030058480d070750400c3d0350740c4d0031080601450247c1d0390010941004504024041c4140241c001119030055690b241e8280080a170340241c035030000da034030010b070a60080038262200d000000030400c0e5003086407550701c00e2046441412a541c010b00603507040b00c0400c540c85c2d02c1c3c011000b00c214090010303100c0d910b015480c140d64a00c0058500d00030b0742c01910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 75237358 1250 75236108 75236131
    0xf0c080a050708010606090e180106090b030715020712050118110405060301111b12071101090806040c090e010209030f0123010503030304020d02130c0201050402010917060a0c0302090405 82
    0x44641c01d040342850040d80c4420f0705a8500441005115008680700d01160500030b245a4181d030340a00005a86022107100c5019520300300c400b0403884901d50091400c40000c4c0c08990b4082c2d00c60344054441c00f070601c1d2150242e44010010000b2085954076811164482c1d000807070300461000b11350762802d07c540070403610300c03c052903500359906080c071030f040c1c2c0800100c009000984501d10140c000d481070134140b844151660342c0d8030645c040c081084003140c1d043c004411307546401c40d0511606040c1801d503014006200d28000150a14000070321501841d00110010201868030302d40314002d0031060070403070186d5020300c840c55213075400340700400052409200101d186030b1012014804051054803114012450708014411174500106403544940d050b01c05c04e0314002140002012406040f8003800001d082510b41d0005680c10740140c3e0003a4070030b0300c485e03003415190010a201c0940e80c8030070041c1640f04c03800260300020260000d551102d41818018507110119001c80c00340d42c41150382e0811803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 75238608 1250 75237358 75237373
    0x8030601121a0112140c09060c070b0d0507020303010b0f131707080616021b0312031008150903030a05040201050408011d06010b040e0406021806030114090c040518040f0c08 76
    0x95811003013150790901e5111082044802d060b42c4220f0545000d020740f110000041134030320840d2151003c07103030140070b40d01c22542d645a40b03044c1c1e0b91065000c0b0000d4400e0900308404504000e0000007900c1c10390300c240036000c0c10b100c0b00c40a091040d411414408240c04143c40c00042d01c84c003c1000716201c0070121b030140c4000c1d814640e00926145000d01442040701c8450503541e8071550101d480784080584181c100314101c0313841d000a1900e00407001340d0080c5d02c5e0000500001d1404076807208103c1c0e0a80058980603080c4503c850f0782d00b00c041300c45d04020340003080010808841170703201035400362050404134203080d1103582e0103003100c095842c0040c10140d81241e021840e60200803090051801040d11482c09017028502d040800c2c01030402045240c010582c09260482d401c1885e02518024140581341e40c0e445101c00c0c1501d07112403602d400344459802186500101008070b0f82684c2c00900b00c0030349844100356075a44504020320545074543d442d05854006158072a220004000300380051848 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 75239858 1250 75238608 75238661
    0x30c030f060a1a0309120c150c040501050f0c07080303090a0b01050603041208070203090d060c2705010c020310051003020a0e0103030f0f0302070c080d0306080703020a030803060112 80
    0xe03120203009a4424054020100001400d040540b008000704030001502c0e0703140c24403298a040c1c021944284100c0b00411000c00f0300030002141c4103202074681c8458210380741c952803218030384120b01032180000c104000300c07e800039254004144840c0c2b00400c90b41500d41d900c020a0440e00152880201d80e00608019414801001c6500307000d002c08640310b5186040681e03840b0760100152000100b40031200c030000d4600e900a0041c4c54180c18060901c820640d1a460710074014030300503903902c01149141c000130913401c01c044800021904a901072007181c500b818010b5450710413034102280d041c860400034001010b2507029040c021869803450f01c0c803607821403040014848094004699401e43e4000400119038450000308000600b03082820740e07100c2801c0124003900c1814409405540744400014001c0c600140c0c81102e1146d0b99000c00c030460701c58050a0301c42040388406548900c0307204c0d040c00800c24040c000c5420100505201040c2d201001e44101038820f4020181ca0751918000c00303000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 75241108 1250 75239858 75239881
    0x405010b0316020c030d08090a080301031b06110c1302070807060605010f050304051015031b0801060b0f03061903050610060f0f081605040f080708070605040e01030308090a020402030c03 82
    0x15078140058075040c4110f0700030940d2040741d46c00d400308201e00c3d0f078089002c0c64030920800300200e4008400d41e54070360b1a814a10005201641d000101049103100040c00d64440c0e06010f900c03a4003d405042400c0040040000541c0c501da40f03100e0a030390030000c0800184d01c1000400e030781031043c04041a0b1514000c0050075815031801c0c4141806000c0082000258001c9080c43c440102c461000810080c9220380f00601411b503000104026422580710300d004144d4100032086600c0140203200300b580f01c9000070024001e20300c101c61041410700c0440c0003403411400701000c00d9540d408444270356649072501da240c12415100800e01200c080801d2040941c05404401010101e0070301013052400e60030006d025480052822008289600c01104040d102c1e0040b076004001c9034022006c040d4440c2c0303086403034000c20300c41c070b0419210b100c1002510701d00035400c0d45c04a42c1003040c1d03035250340c1c61610f081c0c0e001440105411441e000c1c9400d81c20069543c1d01c081c5009940c803140558491900c0c1140c0702 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 75242358 1250 75241108 75241141
    0x20d110a090926030f090709090f050105060619140c0a03110118020604140d060203151c050c060a05070b0f01170c0303030a020a030f060e190b0906060a020c0405010b03 74
    0x122004144803111544904482c01c49421014003502e100a603900c031b02080e824000d2540004c85031606194002040c4a4644001041c40c1e000b00000c00940e150441000850300c00c021044600c140915002824540920603a45506c600f005445141ca00180881e0342812601c1c1012400320b0b45d1100320f011522024466030f0f00807000c0c1e4400030403006d1035800056003405248540090340c4590903802c001030301c43c0394401d00195407042c02951281040c101555582c0f01401200303000b0f5911001178103403020004c02204480750040d018004030182141070081e0380e40034803035203420300900704201800140c40144142c86025040341d56500f17541002c41c0e90821850845038000e20364080030b03840c503c0e994044116078220030400c10060340c4100c040d0090780500800741703034014068540600010741c0c902100115100c0d031450801d03860307605901e0b41c1d82030854042030440d41c1c1261003034000400b1424101d00174100149035004440d80800040d0008041d01e809800000c20440c0120030b000c00f01c04c8100816 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 75243608 1250 75242358 75242393
    0x20607030c200a02040f0e010c02061e0606130b091f080703020904090b0405010c030b06070507030201050a031b0f0906020a1a2502010c08010e04020d020d110a0909 72
    0x180080d0111100042060b804482c00244220080c91806400c00080296200072540074200b07100101000304044014410302c400442154208018894000d02c0815068881d81d000782c01c505407911010309281120400420301d42d08581c08110381c601065400580100030514140107603600c043d00703400c0c0041c5a2690a038501703003901030842172000e103401840c180c1d40651580740050702d480c0b412000502402e2040c0700a0f240c41d0b8a43c00b07003c1400742c19008504580c0084d281803203e05a5903040c040305210b20364000d802908013440500c015889400180748840882c03a001c00c3c02e0395402c1100107801b00e00c0702c850020540e070340c4074070b0b044680104284004203d14000303800c07581c042d42c40383d400e11a43c0d0f10580e00d9000c03280002552138450701000946c20341d030541300800800b2612070080d00800c03450981801003a815800042c0c1d504400d0007480c49554044c100340c81c1c0e182d080e42170041c2e8170000081111507a0b44403031661041d4440b50030840c001d140e200d5000c2044540380c100b00c0c0c12000900d660 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 75244858 1250 75243608 75243611
    0x20d110703080a051504090302010b0405010e090604080d1b02010504020a05120c130e0708071e0b0a0c060b040c09170133030209270703051b010309080a030c02060703 73
    0x300c01080d041942654030140b001d00c0494503503901e80c0d03020700c8100d80e1070901e988540b03420394800c03c2c141d0552014001c09410b440c20020f90f42c031a81c50340d800100854000c0040d5110000080010395001d001e418404c5c040000440c40b0084180d8a440002880d494800142c0d580e004100561a101ca40d1400500302520310303140d00503444008940b550280300f2401e002d20101140d500c40b190b940d03405402d5404008046c2e030036260f11260065207658142c802d194440c6071220100720003c1054000030100d641d2100039900d05125604240d4160020950985199966160a48080d169400b90323490390405552030060f081d04000508621100310502d81c603d42c0c0c9001000b450340b07160f201c813560807007030104a600040940312180d14400345842c1c000070742080307080c000c0c0800203011904958400052540301e070302941281d4042c6654513170a10003d8203c0c1c0c08240c141c100c540c1810300401e245d0700c06142c046a40c9000c1d8480d55040e40c4000701c240000b80d40c81d480303240115810302c13009802201b603150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 75246108 1250 75244858 75244867
    0xf0412060e01051e070311091002030a0206011a0712210204092301050603060607050f0601050f0609011709010b04060305030703110d05030423190c0906060c08030406021c020d11 78
    0x1c4618100014040d4051595960f51f540d402c450010030340e004480010854240e00560b40d1000b9100c0c3c2004a124025128400020400000d080d5241046400700c0040c1400c0091a03100c2c10800701c000d140820901c60aa240625042d0890611b0b80d14842c01040140c1c1c2d80d480c00c402d0400301e400c09201c242c0c2c0d4000c01c13440281d1558411030703491b04558045800ca51a522942c0c0042d501d403241d110001d01c50711600c000112107542c00324600b41203071400c840840340701c00e408052244512a0b05082400503500c41700d2400d00c089085100c03a0040b100b08000502101010003080071100744e1307082a00c455002040783d00401d58001c1044842c49035074005494280d0750071001410038080680005d00d480208201103940500300c1059518030203940d812a0105d40b005040b0310302c1002c6200d000e0b2258032040f00082018070581c0038000071914656500e134034075031503030301c07804402d0300301a0044851580800054100110182c02000141d4a8803c01a524030224038200102c1d8001100d07503c40000901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 75247358 1250 75246108 75246151
    0xe010905060301090b03010b060a09083c070504020703090e011e0303030203041a15010311030705041e050303040303170105030604020f010302030612100207050f030702150f0412060e0105 82
    0x1054904403035504d10040307100045480003901402103c00004e80084002c01e6440d90b80d944070640d0f00484070500b05540500b1100c450360a1290340b55a002c800000911740ca41040c4408039041103c008421000c8c0c0703502e41e403540009016130340a620264009071107550700b805004c646201150041030b03126030aa00751034900c2680310880c800e0781b0010f4107140e804030010f81442440c8401e03445010380c44181c0740b070528040c0100e60910a603410404e0000e032421459003440300d81941124000c21898944a09241c1703410000d81c0825920003001c11076403800000015030791010000381001d5440303a01c45155100d004000c404071204140e1119100340c0c8288244005a01c40002e0400f020038207190160b0381e41d45280c00b1507078840f4620151400c44c49503440401c8240d22a60141c00194401c04c182c41d10b113000c0701402556801042000795008941030780c1700c424464190010700301e124503200418241503403403580c01c441c036007424401c0d61380c40d45a8003d110781c80710a109895201500c4503000b20301c2d26011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 75248608 1250 75247358 75247369
    0x1d0109090b070c0618081809060307170102040b0301090501061106040f080d1407050a11070812130b030705070c0602010c0905061b1c0e121b0607210e010905 69
    0xc1d0a10b000e00003a0410720f0140300701a00103c000c00c003030302e407a08041403075482c02034902d510660303c1c06804a81c00d0f4100005181400c5018000c803801001011140d003000620f151141c0070b420082c0c841d660030000019419084c80245008000c40300000a03103600d17248000d08a075640d140344042e6904040100400101ca052a6048194000f079a0648601e0002410b400420580700d0011005602c0020484010390200040203c6170f61303035560039010b041480006984011600a5181036081405100c090060f4440500103c0c54507540320800e55958001c1000326500c00e40310240050703000580fa0003030110459696008000b00d2008005040038a5002001a0014082d5511600001410514000c0e40c0310400385543c00032016101e00329904035403e001e20040c003034000d000ca5000d240a0b4118507103030804410039891840540065400210504000d49101c81711030782c49071f01440b803040802c81040d40e81801c08030010305c40800c00445c440140c00345816400745410010301042c28001511030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 75249858 1250 75248608 75248611
    0x9040309090b010512130201030e0307050a020d06140c0d150e15040e011103040b060301020f0d020901021e0312060906060a0507050c0d08041403030a050301050f030f0105011d0109090b 81
    0x14110002102c08000d00126107500c84c0c484080100004602802480902c5414040401c2d100b40ca08102850358250f1464407030240e0784000c0d2441d013200ca03e550140c14000030700204144039041c0041d1440b109003440189000541da1000b0140e0041035180c100f094520820f0000f00c0b90340c44038074a061810001c81600c1000604950a10918900000350740d103da400001003552040002c0c480701e0800a048651078100700c0d81074030508004000304415007810b03c21115030303603e000280c901d40038a00c022140650300c1640c3c01811031007114080200b8120b940b04410514014101440e644d1011054400c0b203440c028210034411514541481401c1d95220101d034114816401c000d40c50319132504203907040c0076541152507000000c000440781040130200040c801da42440b00803503940d91404081c0b41d507a0140c59030700300100b1401c200500c15841c0220110b07045000050407180407202c01c3c14030b1403e4403001c0c1d0207010075480100f021400c802400a0450140240c80010440300580380c442c541010700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 75251108 1250 75249858 75249869
    0xe0117040212120c03090112090b040323120403080a05060a12060608010207080406080a0209090f0a09150e0c06030907030318080f150f041205090103240e0609040309 73
    0x2020101e0302d910031030070b10620503200703c903092541c1c540c00000780003600c07a885207001c24001605450402902c0105200b0000c0854110383e44a18541d2180c0d01680c1480d00050000040d51a844403606911200381c010302802140c2c0302c00e0150381c1844d01c0c014086031070140c900e80b41a82040b00300000c640f50b001068046601700034400e4142c8159080c007000a01164008001550001a00c40d00380b10322203000f88226002c5a8900c1c5040d6070b2030703180354102e0280c004501d0b448080c0c0c1d404118001d07000310185400100005000a40c00c0e000d039610020b0302008044803070780316180e118603083c010080c004681254400e8440c6850743c85c2c0380610030f0315820785020040520075941402c0304e0180700c00980c2e001030600f0314105c603040e001c070300300a941d90031940140c03003000700449001071401c4040e800b86600590340100040c2982d0154101510281c010100c1a4101a510107030540b0300e03200040300800c403c1c0c004180c2e8030315a060030b000c1d00c085c800c0240031174000c12214051000091340403949904541 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 75252358 1250 75251108 75251119
    0x61a0d0809010315120b1608040326070c0b0c040303082a030916060302160209060103150e040203010c020606010c1209050a06020607020c030d0509011b060e0601060e01170402 77
    0x81c0c1100058005040c0c40b8a06101c05081080100317040c900d0488215601c0d0040c6403020b0240d5488404144802080001d407001a41c40004038000074040c07509212501c80200210f907181040c101d41c0031007194200c81601c00500040120010b000008040780c0d00325440600d003600c2d190031900c010f42941000741c11310b88042c094180ba4400c50b410030b401116000e06441c00b644d503d00f4034000344c0d565424100f140105c401010640014007038080c1c400c40c0e2080245100d89200500241c08102d92120f00420003418951290342c61218030013500c1c2207901401d4200e0300021076007810300525003140e01141181040d54042814008646c0c1c00041c441040da5000184060300c4810032412584445564000c0340c215030003080106a00c4c0e00402c0b554450007403503003150100b01140d02050395407903040c4942d1020600130003850070759500c10200e4842541c41c0c03918085040c50156204011580b1800c201c0d0101d401c03010040c0704440c7d0020680c2e1045500340b8252400705004140c00f07401c00c00240c8004e114a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 75253608 1250 75252358 75252367
    0x280e0a030b0406150314010c0f0e090405010b13090516120209041e06020919030308240604031101091a030105010309050f06040b06010e0603010b03071404031b03061a0d08 75
    0x4510390f08a403071a84001c1181c4c2003c9566442c18110700c02c40c00401007155400d01c4580c014840c801c0f200c02c0100c2d4581d035a900400704004051061082e40a03100703484554a4602c180d01c1a1508007140203400c503d2140015245d4890609608000703101c80100b2882100b81c8007004030ba11f44051100c401501100c0b00450341d190b900d002d0807001c0e031240c07a040140c0341d42c041d0340b403d1010329030113040000e80c20b603245102516406c9050042e50110300004012a80c40750100d1049110301c20010101c1d962000840d03641c0d186040056400c0c0c0107035108540c0701c200c0001c90503555030300a540c28020030741c1c0c09810f10340342a14805c4036214001405410f0406036504450f00501ca030070040540300c032907001c1c2a154141402d08000c100350390704031780480c0803881650b00e0b20705a04040003282d0403507080c80002c1d402c41d11000700850341403043c800381e5240c50405000100105001840e421503142c065000045100d1441c80d001381900c020f01c40e00880080c100803a40d4854856604001d2911341c41050300ea43d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75254858 1250 75253608 75253613
    0x902030114100203070b010609030204050105010206060d0b06040b06040f0f12050d2303100801050705090306010e0606071208060405060409050309040902060d06030f05060906130803070c08280e0a030b04 89
    0x1354001c1c00300c058142c203215000040c049810140c6034080d00c0c001da4040c48560380716001660348080c1500c0c1550403c1c1600c1008002c154000002504404028000320ba08100200010749640003900009120384107403804002400e84076403405c000f0060003003200d0003129180c8a00f52140c2c40503000e0710905c200e106561032201c0b0342142d02810005000407135612030802d495404074500c60b0f8007445000350320306804603140c01c7c0500b06407020010010700900c3e00703a080040c0150740c00c2c00a0040f0340c002000780a600001954056003810504d5190b0714000316260290400c0180e81020340000d002d90700d803c0441e00864008011500112010384003c030361403107984049081c51195031502601c0b00e1a0100101c2003094440000300858012000c8030b10310788079040110f445074000e40d000d0f040c00d40ca808004d400188980c0180d94010301a0802c0c4c000003000d511000019805a510b620807255141340710309000c1c07400118410031000c0e6241802040c0303460710125401c0c00980c0000b504104040c0001801c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 75256108 1250 75254858 75254863
    0x601031e0c1a0703080106031109060c2119090506040b0c07050a14150306031f090b040b010608180601060c150c0201151a0304080319110a0909020301141002 69
    0x41001c0000e5a40c0d00c954228107402c1600010343c1100020801c400019043c2e101e409402400041885a6850070b80c0c54010002698041088d1340c049002da00451801d944802c04444d441900a010f1a03946d105210b001030100510a80c160007800307040c07101404191039807010741d0191243c0710340195440b5207220100d46031440c2603101c0c0341e2004402030003155912401c0505c00306a1000d68100780e000341441558031081c00115880b9402d0343c0320840e40c12070300e910070311955100c4c150000c0004500c04941c50f1030305203c90466042e200010b0000040103029400318182d0748c4001401d180c002c032100812145d0b40c5615040c8226000c10420349040c000b4401031600b20802031950340f004000003030054034003a010b4a100c0b01c03612110107090000080802e142c1440c180840500c001c1c1074950f5466036202844c0c0d07000644101c541d0000301d00100f820559903c40d1000c1075144052143c1c403140ea02a0003040401c65400255100d80144010404241d130002040c80255084071010110440800300300c2c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 75257358 1250 75256108 75256133
    0x30a09050c101d040b0d0609080f03040605040b160c020f1816110f0a02010c0f06020c0c0909030702090112030c0813050103060e0408030601080603030c010606020f0606030601031e 79
    0x660241c00d200644600315006600d03054041d50089212650003d80e000f000125006850010341220482c404080092910f0f070010071030074800c1e01c0340c5050845040d4102c8980c2c00445017140c01c0b40d034800900c418850800312440d404118204030748404001e81c280181112101240240035410260881c0210b5440c030007510740f08602c2d00d50507080e918001809100070088000400c0c042000042110140100404c103900c15102960080180d246c556004483d050307030408054856400080140c00003e00500084c02542c8140300100794150522003040085a0701520f03c200c554410003024005894402003241110321014408501c10582d00b01500d2440580100404000c00002d44488240310810524242c1e18285d904104d402e880700f5807000206420760700644211014000100a984178410f01c503804ad9025003907905200003c400035003540c03580c2d0000300240e0003558031194045820003e0703d61044044000b001176515548072030460180303403420580c52040342451841030013202c0da07559 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 75258608 1250 75257358 75257383
    0x50a0b04090305130503160b0a0504031a061005190e0f030105010807030c0902040605031303020705030303090d1205070e100e030a0b010303030c0e090c070c0902030c0c0f0102040b030a0905 83
    0x140151403142c03030003c2142c1e0281400160059041c84041081e00780042c03c07858806294200c0d9074942d0401d84220b02e50b4001b034100004200c0100f00100c00640045058019032107080240203480c1880d00c10003144003090803904003001018407528400c2d40c1203070140382c000219030174002501e060380400b149814401c010714541641c00c0600008c0c074800009005422203000c0c581001c001a11010044264401d034400d4200141c41030002c65110192889507500302d0b03120f401214511583d54000ca0305642044941d54041d81000c65407040b0303076070059500c40e203812001600308601c4c80e000e00041d0000c420700206034042d002c50f03c0e090000e81d00980325041c0102e4001c040b0351178014145030072038281d502400202c001900705628100c00502034503a1250410004014204603175410320844100e030031440307050392100d800c0d80c00007404080e0b07440218024510780390f950f641c83c1c0c1001001c914081e11031644998a0307204000030051115603106503900024400300c04102c00c6030078105a1702e81640c072990f8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 75259858 1250 75258608 75258611
    0x305220f032d030203070209130b0f07020c0102160e1902040e041e022107030804090207020315070206070806040e0f0d20121b12070b010b0703050904050a0b04 70
    0x12050140c000391100070082005480301e0306a104640021100e40c2e403040040141e03000340620401442c2c4050120760084000f440610070070340503254903403030b108240e40c80c2c41c0703150352242448407490303040c45650002402030000700804a26004e8a041c0c04440c0c0c4541508040c0007c003107071803031921824000191100d4502035440c0c0303440d60068401c3e10f400352002c8610f4005100c840c0c1040f03041884920085400608a0780d03503a1000221444268032800e6044003802030341004000600c0b501e001c0c0c00541580c40300183c5800f003030b2051520b0700110030301c44c048003c0c440d000c020074260b000408643c001181e00c1c010801c0d4444401140c0a01003d203a04201400381c80040c1006020010b0040745010340d590303030084088604c0450040810342020404402c4d0001c0854401c0d218810300100950450141440c41d602c05000714641030124106040c3c0341c4110004e0a58140010950038901601031400154a0401c00e96400380562040c1c0540c80d029a0306c950000f009403000e64490440200090710 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 75261108 1250 75259858 75259889
    0x18020f0a02330712021306110d1403130201030902040c03050403180b0a03021803060915010807051e130204060c05060a060509060d06061509060806030a030522 70
    0x4060b40310000204000044200028890300a115924403551481c01052003248035848481088035568800010342c880e6580800504161000d00c440440c020a0990340d071039100300141e92400c4c01e00e95680010750802c402c0a0018407a02c0300d8200b200d4001d18450402d29000071544016001340c60700f81d0340030303500030b10700313081c1c14000d03a00340e08003503c01c5100781c1d80c0c20f040c0b50300e500d0400004c00560240750600301d001d01c440c85c200790095005011f00810001c001c1c003049621000a4500442110f00300f90704d40002020291021090044c030740034100140c050102c0604000c0405c5002c40c3c0a141815440651038075107005441303210700004e00480200d020740da51030300c4800141a22004030003c48240c49224009020140c5034418801a5036005143d050542c0f581410001146001c0310306543c0c0c941d85060000c2c007192010080702c8102c13003d0302da00c101d0070f1605101918682000301841d00075040005840000f940c402c0403115450108044503011501103002d003801105d080d0031403000c65006e00c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 75262358 1250 75261108 75261127
    0x70e04050c240d0203060f010c0b011401050f03070509031504170a030e0d0207080c010201090803041b08060423011406060d020904020318070b0a090e070c0b0a0c0e010e060418020f 79
    0x400546c8034181c2034441c1100031503400c00440d5106c03e2110041c1540e4802030040c482d01062008410701040b0515000e400e10041c45088412548103540d2240410000640c0b0f011504050020703441054100580c1c000c0340c40e154032108a007070074440360801da0300320020358800300030300039803004a4610604044400340d402d1100c000c0c2d5644a903000e00c040e24804d07100030030300961050080c5400d01d58041c59040c05d5440f02e03562002d04001020400484111076003000c203090f1010001d4030f100d14080e801158410120203240e24031400c91034149003990341444541e0601884071200c0a810036021340311a5502c032000c1407040020300650b03165642c02400082441500c000c0f1a0300083d0380003002090711110b95540c001d070300042c46122104004150012000c2104c040c1145030f555201200d070410701b124000310340d02c44003c0e000840350284500d075a10120344086a2182007510140c4081c200031401002d0000010305c14007491003610b481d160102d86494445500e9010744d501c103001112840e442c5c0d002e25 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 75263608 1250 75262358 75262361
    0x6010302071a040201080903071115070b0408041d0402060a0e040f090803010302130204080706050a140a03020325020c04090203010e030a020f010b0901060504120606051908070e04050c240d 83
    0x143e4061780040d1244000c00c40114011040b183c102d54488041da07040a003810a21032487d00d001c0d1503100300303502402440c011904001c1a184154404d00420b5504c034103040c0c3c00d4541205501c5440c0224a810081000680342c50f8111030100c002401d109900036078250014026216000d416001181040507000802480c040614140c0788202c82c0342c40c00582c251a08000ca0040d840382840341c4d8050f00c800c000307050103140245540741039842c0001440484055401055200c004001d000950004c2000b4034089040c114003a401001c4c9001d50528414540007903a078060454558070807991480390404541c1c0940c450700d0300c44240c0003602d07100c00c01c0300c4002c0c0d2660a02d0206115550901d9450443c0e032a004d14114103803942c50301c40a0516040c401000b032001e005040071246142d803980045291f0341d030611001703000c64101c104010124100400d0f2824a085a402070640540d51310074440051004210010b0503241500d02c12440c081c00515513554520964424114480c0081c811a84c0c01c1c06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 75264858 1250 75263608 75263611
    0x131d03090117040b01050909010905070609090c02062e15020f0714131d01060b040501020705011d040905030d0207050106031403030f04030e01110102040e0a050f1302040506010302071a 81
    0x262a411424002d0001102c01d1540c1214000c0407415100010301003841c00c000d00d00e810969000001801c4401030303441620300700841c0c200744045030710000c0800c4044404e001301a1008424409017145c0d0900000c094480c1d080801200c0200712100341000090184100307403001000c0918222400f0300325890301941700c09485000f1801d81c020b050011901e10b0b20700301001144507000e8421080030307841074003800080c44008522059030950303c082c041c40050901440028000a0f803c0c10b81c1c8629060003e0728000c2e040e031100e0706200080e03860000c0340c0c682142e1408640d0040d980817810414a180103030440c403803402c0c440e164038030101c0d2003420b200056021001ba40d110f0016082d0701e03644819280d59070b000c22200c000950706a80300040000384180051101e080060400809102800c601c0909a03005908407002ea06140c804210381040703240252174002d8400c2c0701d40d65481c10310074100d1004441100010b03001c0c60b2590301080341030344281e04071500b064110f850704040d0020486900300a080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 75266108 1250 75264858 75264877
    0x90a05030409200307020d0c110306070816110304140d080d151706160e060408031903020405060d02070201050409061805060f0d1b050a1d070e060702131d03 69
    0xc5042c80422621000d045a00171061a0000d20400e01001c108031180d895100c411a44070721032034100c41950720104605801262640c481e0b200918100081e10403038220800081d00700700b403081540c898001d000c0200d43c00d4a40c2c20300e016149030030010200d05440120342000b401c40d07000196000c10300c2140e5000b5160070524511000071160348013494000c54695401d0f0740d015801c03007004104000c005800c80c41ca0780140c0e003812140c0210240c00103400360001d40c4000400d810020324642e1104102c001121213034402c0c1421401c090526000c150240541e804425226500061074400e580c054001c4d10003c020204060180b5030b107450078070240c0c5000300c108541d500d0801c00401d44030302e007070080703100c40d0600541f082807441401d40f101c060030082d075400494840c20b852404501038039400166806440013004c41c0c5000110340030f20440010005041004000315403102c012190344103421511020b030112820350124510185080082c0071070600c800100e8a0311045d8122a0310200141041c80c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 75267358 1250 75266108 75266141
    0x1b0a020609120702090604090501060314010209010909051527040606081005012306160503030621060412020f0703050106080c010306050a030204020a170103060b0f06070515090a05030409 82
    0x4200341c5202d501401046002540010080000b40302d0703003060303030086507a0b41c00342c4000f0074030700c2d40c0b0b1302ca000e400e203460881280c4613500020600c0e00303940c22004a500920300907034100481e2800c0c041c5002c0802d0b01000c80c91003444480034403c481c480004444120000403800e6520303d09191030b208004003802d10440040b4054a80c1103641005180b0039581203c2c58a502c80e41c60704030f0384283c0018012840710180e4001000e0191511400e0300c1c104191405200b440210b54905201d020420b040365a1000e035480080b40c211109107612001c40d0039504190311070364500c04001ca980e0b040e41000400b00c5208a02e02c41d1a03000810f10505411840c02c80c1d9000b0240c50031420508011416203202e40151500030400510070401030a1070303030090149000c5480c018505075541c8601d814415801c1c1d0045c3d03a070a803a20030203220340c41c11030002c0071340b80e004680181c98040c240da00c0c1515002c2282d03012031040c08160004501c0c0300240084201250b009041c0d1307a07166100d0b02d03800c00802d444e03000300d01e155 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 75268608 1250 75267358 75267373
    0x30a0b090d030e1617010603150605030c120a03180b030901090c17031c090b10030308012408070905040c090e01050301020406140306040b040509060615160b1b0a020609 74
    0x3c0401041c46110210241c1e144502e46042c424503000a030800c012000340b9640c2e952001001c1145020f1681d0012416100891041d10300810586800b0002c2e0f0380034842c83c01e45160200385c0f440040d1144489915042000003075011401c0701c50051038a034040000000300008118903183c040d8000c00f50345110303808400c4220b8851400082500b1031407003081180c2d1041255040301802611000c401c0c0211b2200400c010803030f81e40b1038016107001e6500c0c004400d211a000d10030150440b0400e03014003440700d6600c00301e4007414000d000c445c02c0c1009582c24060040046000648030b01404005060041c00502c0302402e24000103000082a12884599005c070000108031850180229421604203540d100c172110380f80d0344000456030001d07010642c4a6559200e01007151200c0c001d0354822410740300a0301c00c03480c00d04103201884c0705006840e4850340b070800840020264002140c44019000f2150f4905540c0700310315000030204030300c4110160b440125a481d401540068018131484554050b00d614 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 75269858 1250 75268608 75268631
    0x901021903050603030d02070618140609030304030503041b05030102160b01050a06080c03072606030d0c0c0603020c0c030303041415071b060f06080102090114070b04030e030a0b090d03 81
    0x11a00b00303880459040c0c05c1000520841c42c0e0b035401a0042602078840054100181800041e4203500c0140490740302c20a0284100f1a400074003075194003020034000f039480c0d444c2070350340100603110041000700002c4680e40512079540c2c1005500c03010340400380086651f05440000440e40318180d07001103440312000000802c441c10100c0c64002154010384030b525041d152043c2e0144140c1000300300304100b020a202207100080020003031480c0c4582010320350400d007018424581442d420700404c1043c09003484c0d617140040c410307049070811104185001030300d6481045005042410f521091581444003109101c203008039040f4844e92540c55008903020780030107040301ca040041c111505004203e81c2d0540c2c100c401403191107651a20f2141c040020070703504c1d4070030302e07000c4800982003034075940c1d80800c0307060040d40c20060b07055641c9a441055400c01140d076a802c0c90100c1c000b00000e0070000800e42400741900d0801c040d00080d41d004810b02c00500d840003080c0d83e50220b440603c0d000a007060186801d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 75271108 1250 75269858 75269861
    0x90b060c060705031305030a0513090203100611030f04080708011d060112020f03010f0c0e01020f1002130509070c020415051f050c01141e07020a1104140901021903 72
    0x4104480d100680200c0d5240201610a5040200b0503440c04001072030001c005103062004041000b91600c4860b10390b10300701400140b040c0c40350448001140f040050000c1030140c100048100c55035031400300c0442e03409120f036038150300421a584401c00d0740803d02098a0708046540300030349030000020000c61090080c480e4000c42074055000c8180c001d0360040c41900380c125031440d0020f0018000c100000303100310200703007105c00ba81d00e00e25289030780d02500382d0220360040c8080140802440104040c0c006080f500381c483c250815082c1d0030781ea00045200840fa4042d402c0401024020702030205480c0152000e004d1010320700d4100c1c415071504440c00c0d201b00090750202e05855000e80a0a040b001c4504c00280c4661080c0030041400403e1010304d0b803141c000d000c1d540d1484904201d443e12418490005803034800701503060038119000108200f0005c0d40083c035250181c0d0802c0b1180c000041c07290100d001480745210450707070313006030a040151351401500142904940d204c00c020140c0e120280450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 75272358 1250 75271108 75271117
    0x906030a020915030a0b0f09060105010206010815090a1b06030f140103020603060102010e03130302031203011d07091d010303081501021002070507080a2a061b0501020c0d0504090b06 80
    0xa5000c56020b02091000700c3c801440f1140c201c0103022145800003540b2501245030007150070305c05080146081041c8071030b041c03140c213004080038001060a9410015516128200302c038003041821b44580c0000c0780c0328400c0041e01011500328079666501000c0285c4001c51407618056840440d08110b5071039094842441011580c015002402c1c3c043d909550800c0266800605541c0c115034841071105c80c445010b10042c841c0f010802540c19886156106060034002d0040c0380852122007400100460300102c1c0e0452260f107074180d904c44e401c0d540c1e84019144240c164000a0441d0f010754221084030203002907081c143c90194840744015500c04104c410f0310025080380f6070050b000340c450705120400c01c5c0c001d401c11b40d11030001c1d1000103403281c020919200545006a682c5010000005444a01400320f84d0f000006981030b942e801e424664081c100036010340c5240d00c2d02c00711085800600000b075040c0c4a40c01e1507503060312000450a1001412a0443c2c010480d010389072000810341e515040003141c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 75273608 1250 75272358 75272363
    0x60212130f0b151905130e0601060c03020319120e010b0d020105090103060b07050105060f0a0e010b070807200411040f0504090609050303040f0b0105040b1f05090d08090906030a 78
    0x1160141e501c1d41c40c5210420003500c01c00f00036540070300b80380040d543c842c161241161000c2e200d141140c5048204094000d0240070b102d00603103440000b6202460105020b03055400314200140c1c0100f181c03504a2a42c032540b40710b00d003144014814109619809001103c02100285c400d01800c44002d05180c2285c0d0030400d100d500081c1c3e02804801940900c0252072170070014180000c0c0e070360351041501c003680e100c000100c0b0740e65500c82c00c2020314502002e40da0303542c0301c0640d03060840500303010f920501c009042c054908024400300d940010003480c3c0e4100d4001691045103185818503440c03035010008250008148100d0819403640d10300010741017aa01125040b40702011900d02d410180401484002d9060ba80c10b5182c140e40c0b000700380108001c5004602c2581c2101042005046c49000c1c200180c00c034620079410007190708403e40d00c00c4007851516441640c0000030140c40041591284940164207402c2140e00b4206028084080042d002c080d8043c0c8005006507200000c03d9140c80426100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 75274858 1250 75273608 75273623
    0x5070906020d0305070908011103010e01140d06020315040c081005041a040504020d0c120606120c0902160b010609030302010e0f1e01060504060308040314010e060a0f061206021213 79
    0x2d078400c40f4803a400182c1c119204d420b10400c10341d1a170380000e095820400c2d980703410b924008010020000a000d05d40d0040221020034100c0ca4014800144070a240000140840d81c02101144403400d201c1542012140e0041003042241e1508a0160034804100e8a411201c000da00000415003030901a42000d044001c0a404280c1d03002410800100000340080c3d8104042000650029008c501a00b01410445030b80307405040143c9440f20a1b101c0301c0c5c000001e00a2114095800038480c0740040b03060343d55884000d0b0f1200c0c207614460040c3d109154000e061860581c0001450540000c0040d09a0340690300a000e56070103038001c00d0360b4040181113402d40b0752000d20304c0070021811180003040050207000201e002541c4000141c01d1700c440390000d03684147c00003401c0081000308404003d503082580001d1200d4078801d142d403030312a14010054034190b91116000b406602480e8003d43c042c15600141c00110701c540e007400c1009401955a88c0740114200000c50b007112205020b01002c0c1e60300c54103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 75276108 1250 75274858 75274873
    0x153c230a09051e0a0209040605061003020406020a0201050708090406090501140a0f03110d06050a06050f090f070e040204090e0d20030d020f040b0c010b010207060f12020310080d03020304020102010507090602 91
    0x4100c1d88418202401403942d000c2d5944844c016510030303417001e0049004507000b1030305080c8441001038944400c8112800c2c188104020003a00e90042440d0403200c0e0242001a1616510300b00403040d8498416150752040c03410b4404540407210780d111034103a4101402e20029112400c003401035111482c09000110b82c818801003001800e00d020b024403100002c5c08103d0700c03490542c0d07801c060311000c2d114010031540f1000d061046043c074825008401030101d51480503428024a10a1500b5004e84224100000c03011901400d407169011200203005007041040700001c441f000355241c0070614254000559104183d1400c5e0406e10b01b581c2c03410042d100075514005500483d0002503201c0300c82d601031900305200c0055041d2855014041c0c00a5080010801144601c0024201074040d0045028451041e1080408503070095100030000d03102007005990f0740700d40c202c0c2d1203101820ba000c141144206181c1e040e525501d60050340c0520b200f03800034001c64071804815601c050032070266400580c440007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 75277358 1250 75276108 75276133
    0xf0c02060405040b06070b090c090703090b27070602031806030403140c07030f05030d050c030907050d021203040b1c060e0609040c030c12153c230a0905 67
    0x20701844d0350b4400204020b14142ca04d075a903110703140c0708854065254010f10000801401c040f0700d4264409010710b001c01c804031943d51030389a40c40b0003819806050580c08120f5070620b00d0391454504099404049a6a003550b80740004e6480e405400245000051a80415050b00380304080d07d0059038180c40e1041c100d11510160b0845800c1040c0c000d51502c14031030004040350444880000003401040690754901a10450000346c1e40c015007600d81c40002042000103040e008602002075403411103016468060300e000040301082c414010990600001400140c409000001400748500c1030303003038500d103200564290048450922810228040c0140091103c0c45d00301d50faa540540b061408540c04c0b40c5a80b20f090026900d034204074260810f084400043c007410031194108000d85031400e010080310882d18104401e010201012002080701010f11100c8201d00b0300c0301c0c1c60700b042e42708000030b040594040c0380403030100380b143d03901c5868807010995484c8075006840001c0d4000008206955110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 75278608 1250 75277358 75277361
    0xf011403070c08070b090f0c0a060c0501110a030903020f07030f030302070f0501060e090f0712170d0f020703030b011b0803060d022e0513030605130204020d0603030f0c0206040504 79
    0x411075001c018024607070a001826102c05402e41501601c00307554145003080c9498078280300c034082c0006030751008021240c0c5644c0e2101ea507090340c0e078600c0c082d800000c59140090240403504041088110041200004241e25900008640340030390f08030b96960030392104460b01d6011500010b01000801012500801e0007600240f809604c6040c0f2060401c1d10383d00e070b0718219a10f41c0c00500e0008000d03c01d0100c400802c000704a415051000901540740c03030114141c0c610316448000030140c04143c0c0041051601607000ea901c02485103005210691084010303400a60182c1011070100b403802c0c81e07403030385944100c12440000c010343c003038400104195200d950150f00000e0549030300c102e101c001c800050301d402880d810360b0000042c408a251501c411581c1c8078044440300c41e401c110003407120f0380c000710794580e9a4040725004a000203042c1c80d402c080c0300651408a001941041c00061103a071684066484107040b64080d50f0340e403051940c4140211202c04591202039800b105c107110900203854507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 75279858 1250 75278608 75278611
    0x51203030106140408010221160c120c0b010f0510030b0d030c080904140103062007060b010207050612150a081519110705070515030708040c0305061005040b0f011403 73
    0x20f8407420b500303083d0b030f4060311426a0b000010044007005014103841800c14a059801e4015080104201c02101040070080501e041000080c101480b07800340d2188460042a007030400542114400d4803640e150490801981c2c0300b8818107000310320441c130a0002d03501c6441900c1c100c0354000c3c1498403080468504076400f0340d881c1c805450303070481000240010354445c400c015000c0d80954856265605d141405021100c00c003d440c4a03001180c07406507041e600010448440c1d641c0920000740d42d419400c0102c2c0f52007810b400080e0050300c0010b02c1e4480c17281d1014180e11880d0000c04041e80e120000b01404152403c1e417040c50750070380c41111820801c28800c2e1142da40440360361500e10508030b02c01208429034813500514601d03004000790031018480180141406001f00f0340e600c4442e007006a05441c641c3c0f10003029003080011040214080107100c203405001507400100722102824880c800c1c81101206107e0f075407240c3d241000b03408441c00c0c480b070542c4140c90161698080e03a0a02103a05202d50700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 75281108 1250 75279858 75279887
    0xb060307030c140406090608070305120403030522030c060302180d1509051203040602040f09090b010b030c0c0f060709080604020312030612010e03090a1409280e010510051203030106 80
    0x32290000301b00102548500320051007018020041c0b54030f0360400c141010380b06046200018010802400881d400904640d40c1e0b60018801c81e08100040c004604440d400c6d1304018070b0141c2030440022051b034181c0180c6614422202030001c000d801000300141507100d29002402c5844580c0016104100c9a00c0942014002c0c42a40c0541010700c071408074540c4110b4040396016130109090000b540c01e01c410001419070b07041e0811881c0c1064a401c103401074144102d0f0103c0d00c001001528912040d03003607408030401001100d8540c032480d4100d03912144211080c000013004840c0c0020f002130f000607080d0040e900600581903503003103503d18807155031005002d29001105426845c0e2194001d00c0f0b0715030080c103200301641c0c46502000c200940c03810a584000c1c50740d001034801ca12240e807000002d0b504801c4010b424546000e807840100020803545601481d92450954460010131064000f588501d480711001e41c0c54549580400180308882031b03804200f94018001448028042c4106514010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 75282358 1250 75281108 75281111
    0x603060a020c03160b0a0e060f220204021b0610060507020607050c03100213230f040b040e010b120607090905040305090618030d020304180504080d050f040b060307030c1404 76
    0x7402c039007000b00192030454003103a0a00d00c0908114401d2024443c03c0351f0782c20048094140c80c140001c1d2441381a070007030440d0200803181110301030108030902c421144a0b81c090300540d2200300c10259601c0018020343c024005020710000070346c100d00309840e2001a01d4003911030740d0804255800340100d50b0042c0c80115568400c05424010359a4200030080881300c60001c0540d440c49424001a030600c003c2d071080010140020384021000ea0079166048102e00035500d00b1881c51148000402400d640326949400c5840d01c4001d041c40041034111468040e001d9411400071001c89042c0d960b60401140d00b200012108034003401149030b20342002c1d07003081c0285012414018140b0000c0e10340d9008141c5214042e02d000c3d070403561410140089410940140051810989480441880880b6440b400d010381ca5440c40024100322a0400b07a039400b02071101c0411445ca85036080509000007540e0503180180da4100052541c600044c00c007060342c0d8050800c0d25220329001109131070201d40404a40d01c103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 75283608 1250 75282358 75282367
    0xb01080910020915190f0e13410609010e06121002030f041a010e0c0d1b020a0c0b0313060c0c05060f0601090605070c05101e0203041d0603060a020c03 66
    0x1e88400d0007070802c114040c0251710300e8102c81c100150401140c1d1000c142030008019600c84940d0300c05900300808801584040341400c48000a0841580b034844800307622805008804001c841001000d441c40920400c4044540c8603a4200040c81e482481100c812041c0800003800e03a0910340d141d24800e607442c2d0304986d442e94191b035a031410398100f1504c0400c41100541000288403950385d55813070b204851a5207442950504a0020107940c004209104141d07000407440540c04050b4000a140460005a2480b03c040c28100a407a07040152051754003d1900f034010404c81031007000c59000e049546e15401038206143d030342c0070140100821032414403419001480201c2c034280300681c460001005c840c240743c81c040001504245980c0c01034000c0220911100002504440f07a20066030411160142c4400c080e680440c0c04012258158500c5543c0021000300c284d0000054010758000b6103400c80d0031070030000c8080b4180012610301303034181c1c000c2000c94240c43c500d0b0700902c5401240320586e07107071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 75284858 1250 75283608 75283639
    0x309031e120a0f180f031d090406050a0501060f09090f091a092118060f0f0301090b0f03031c11070b060301140714030601021c02060405010b010809100209 68
    0x61020803158110302540300c8080b0000043c403440341800303d4140e0039041c004040541c48070300540d0640700e002030a001112621541020b44c00005c000060802000e00c900f03842c003450600042d05040c0c0e22003503036505000000c07485a019030000110b4100c03030359400b2012490840c60308080e005800c090710400c2d69402a0201040802403444a0b0604003405000c50341020400c9515000c1d0001d4a90050881d8840f5980c4060ba41030480c1c0c00310b0300301d540f10780c03401108400050540c41400d10324500034100207151452114440003850480b62402400c105035034818080c4a5401c0d9490f4840f41d01d038008015440140134a45420407180c10402400181c46006120005503603002200607a07800140c00c0420031079140034020400502441e4092071280c0c1021000036001203112411260f0f615004400104140d101700960218108250402c11804203500310294507580c0584e0309a409500700354a15007103501a10480d0302a40304e00009141740e00e01e42034458025041880303403070350050568080442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 75286108 1250 75284858 75284887
    0xd0e0a020306040303241d0604021c09080405120a050105011203080703021318020c0709020c0c090405030f0d05150d0506010510020109050d021e0601030308070c020f04090503030106020f01020309031e 88
    0x640316041f5071040c044812011404807001c010035803485640104045a114604641c02c0781d009205d5460104900341b03103140852050050303400a42d008180440000411440082c00c00d800900402c02000070340d032a074004411520f003031132000c1d020485040102d9a503920aa0040c000713030384151130b2007071816180d1003008074003100c0740300e88a4030940104400d5015001400101c0c000d18200400310b140c800c418820030745070140e000495209203d41000a014024140200c80c0003100c1444115554503181210200408059610501040a581c52090a81020320080480a07040002064143e01e410200202101c074001198110b540300c1641000040b07040000ca80310700101d070050b2442c88107540c20a500f16200e69151111588460010804250001406604503260745403002e422a418000700380313044600f8520035005460718030900180031001c0007542c180d59680d826950180c2040ca051030130707800306588820302d940040100c08400d007110030030f0b10000782c8a12800e50078052030b00094007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 75287358 1250 75286108 75286181
    0x31f0b03070b0d0b06070203070306020a0513030503130902030709091d01110a030c0c0305030f040201110604051c021b06130f0609090606030509060402010806150a050d0e0a020306040303 82
    0x8109401040c40c81c1400d503c1d014060413a01d09482c02d506020b0a6000695907944512018040942c0040d10701c0100c0d10400446d00d41401400040c6240c40e5640307030556aa9111005030711000c85465404100d10340940200c1740200c1203692010455030400104600a000c40301c0310641c01400d408500c2c03410700e42130003088648420050f0042e140c0e40070513805004c0ea812403040030304100c200c03100d10340025001800ea07a007004100c100f20f21240d5803840140c5040000354580407c0b4400c03281000100003000407420307414129002400711210142c8000e0b81c2d19000103840c400400000c0480305c8890428002402d8004e450a203e9800b02d5541c04842154902941080340019030b9104113002800c25030090314001c290524041000b45040701d82d445d19600003400090400c044d80303000c034a03a6920210107000e0f82d072440d4400341d9240703441c0c040038010b0303801004121121803c08a40d135540040101d0200300c01d0740c0203000307815165101d0350100d00402d00010380701101081e141e0ba0010704150b03e41180c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 75288608 1250 75287358 75287369
    0x40209100c0c0605030906010608150d0b04200f0103020c0312010f06090602210d0603060606030902010806030d09062105010611061f06030c030e0307290402031f0b0307 74
    0x440c01075216003403012610100d5001441448020010300c1120200001d4181c115070452915081c81c1d200c3d84088080350040c10180342d0f2245d081d0328900144118050054040c61103940910300310521031400e4075011000600b110341c048800d001070a0203500076001400340800d00c1c0c090301d14110613211551502a4280c03c605080c0000300420320402ea00601401b018010700d000600c100c0310401c0043c0c82d868030b8078004014115000c26003103220425a046000a1a4014814044141c82e0030300203001b02100802a80001c400c0c0022441d1428003050500d441c1495a54010030b42c0c0c01d255050310040d5004a41c0180d10b00c400c0329110200c1040c0c8944c90280c101036565100107c25180d000740781020140445440c200e4180d03407004117a010745503075000c03100b803810040760281c41105d003a4010b1030074403012100c60000103038900401010041640d200104a580984808944600c40180e0310742260000c0d01030b480325242d001c01d400490a41c07102c6c12823106001c43c9414110011905007030459216 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 75289858 1250 75288608 75288617
    0xd0f02071518110d0b0405010e2104060806150301030501060e06010201020a080f190f0902030d05030705180f18060102070501020f0a02060c0c0a060c020102120a0e0f04020910 77
    0x900c820420400c9410508400d4814240305144801d1101c00030391025910003441941940100f042c603031a0500b031000010780150418a19140c81e00b4164060b105843d10205540906a00c0400c0f90748450010941d8100c0c00c03c4c203500705414500c0c141d07810342c2d0151a42da4030000d4000c040c417280081c403004501a620841c004691140b610800200c0d03040b000c0c00740c0e419640184036400c0416440042180d103c3d40c040d813042c0c100c0d21491041c00707140100744400420182001c0d080010f120b001d801464526200394111108504111070032545400b01b651050009142041418443e007030410020340404401001040c620b425a0006000d0454001500d40c4501c0c4220402c4405d68060140e003000301028005040680e541c50161a10341c1000c4000911a040105d20018000c1081102503148040a440281840d48510f40540103921400c1d040b80141320304a030b180c00c0a031402d0f080d64101c20381034032400000c4568004100089010100641d0000d40c20300c030b160f4940d43d800100c820502a43c0c0c54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 75291108 1250 75289858 75289867
    0x90c09020c0111120426070317070c051203040201090b0301060804021905010210090f0c06020709050a0216030e01121a090108060603030304080c070321020c0907020c04110d0f02 78
    0x180c2d094401158880c51081000d03c04030000402070b9515660107030b8010881010114082d0f80c48521030703c1c0328502c00c404040810040308141c0c002c0c02044804071081c034902c00a0303480c0c620441e20064070345c40051142d0054040022074001c0070703001e95042441410300110306611b030b1107240a039030003d0f40090006070019083c0402c0d810300c0301001c21441d520303180c40414142004e001075034170865400b01c601c4481c4e841540f00c00b406488003124000d254048041403802ea51070034006c0d41d501d454000c44504034588008140000304620031511000300382c00e80042c209009441c107540c0307540441c0c0700358140309600e003161000390703103500c40c0e0b441c0d4500c002404100705500406012803014144c0221940e0750000050102036a80003090b01c1d489a13200d1b4803103a413070f0200350741079040c00c1c0c003680000c001c0071850302d0721405041180440780419039103500b2034446101010401055a2003a5409809600501c102c01ca103820107400009440c548400080d01e17080d0240c2e4040d08a0b5200c0d090000794980c08079 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 75292358 1250 75291108 75291127
    0x9150212070812060d08041202061c02120f01080d0c0813080105090f0102040b070b040f0f0305090405060409030e090702070e042009012409050301090309080d05040b041404090c0902 80
    0x10b03180c10407002e1752119080c14156030384014130302c03960003001c252408003c17060086594040803940078000a01c80f0020903070300540d040c00179411810490101170003040024044601e07840728141290040d600a0a905135400800d4546851244082e620602c0400c8036840040032031241703000400306c0720000203503490900350043c18802e81020411240c0d0041004220100703e80381500c02e030035000b81c01d258050b101c901d08400c4012400c0750040c00c0d48482d02020f014113410601401c0b4600054a09010726034448042204440800c40028040b4900c0466803800341031400045500240c42e004460029440e102c1c110f45102e4100c8045401140019100c1110400d04a10040042c810703a180c10240d41010310182002280d85000344271540620f00d514003080c03090451100618010303000b000800d841f410001c3c0b1200c9207000c0c0381e20034440c00680e20030952080040720100d52005020a00307082c10207000341c034005060301c2003540c81600e4407680c401240c24480084001c29140b04e0060f41e600012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 75293608 1250 75292358 75292387
    0x312010303020f0109110f0a051804031d090a0c02010204050a1e08010501060f030c090308031e060f06160f1b1401020303010b0a0f14030a0c1e091502120708 69
    0x1d001c2c3c9401641007200c8800050448900c0c1c00744072004441c0044012208804901562015808554081001103c4420031003070f0400c0c20f40039900a9544c4a503040707a01c181c0026111007003c0640d007003540030340010b0f140c0c4400d9210070880d55152001601d8103030b5a00004252034010342080408510b0642482c82c00051030303030120000c1180d00d00a00440d0301d4644058001c03108811100c040c152112600300300716120f43c0c082d10141d84d002d0181c5889090500140c0300d00d100c070b22241000d80c4480000700d0b01503c0c0c4030b0340e6136208580080407180303480c41112000460075801c0400312440c10f0b0300100300c0006140400100300c044c2e20401d242070900d2501602d4410060826465415508200018801141c0074801c6840c000c405081008d01b43c1c042d01400c403040103020084c880300140200512408400350340103100411580e0f5a03a03e02422450b48141c101e0302100d4411003c0b50340c0303c40400100c0d011030180c00a00403c1d00544080e15040c88018529501801d401c4560010000d40441c1d0001c68 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 75294858 1250 75293608 75293623
    0xf010b0a0501021203070309080318010c08060a12020307150807120e0a02062206030204090605040501210311030a09050406080a03020a03030e0f0102190906050315040209040b03031201030302 84
    0x11688416114a4040044c2d2141107441076403820400000001e2120360081e044000740c0390b400fa800c00e58a02c3c141200c89a00009468020319039401d1010b148421071140e038865005081c000e00c000440e9140003049a1703401c02100049805010f1400002085c0040541e8041d5200840e200c0c1140c0c0d00c1c22010040541c1c50a090240c8903d28001c0c0b880b140c0080050200c000c15410354009035181401246a4410001d140340844000815072000c85c1d029070640283c0212906000305222850f2600104400d60f002401380e01c1012501580d80c0e261141169002c0303482c14000d080800b030200503182200d0441d032103851400081021b41300d080140d0708003449044000c0601c20050500c8116036035009441300300e800b501504064540b8100081d040b804d10041000c40840c80085503200b10281404584030031000e034500c04a03094200000d0441e008904807881441c00c00f07801031070b81200300c1c1004029084040a0740d00a507232a04203507601d441c02c00c018006818894075035003141d0b1462070001e151403071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 75296108 1250 75294858 75294881
    0xe0111180a0602060406050402060d05040c050909070b090d0c12030e0906090702030703181203020106030b07090510120f0204030b0405011b02101d060c0415180501050a0905040c020f01 81
    0x1400d0340c10402e640c1e0105400e0b0b0003617407015010440703407214000503003180141905500c3c8a80b60001388420800760403010b80c12910240e403c0c241c1070365048049030312016103100d030b000110ba08100c800d605e840d2841c43e2940152044498801d0141c491a21081811007410100c0118040032a010b040c0c0c03402e030b0404c6d03510200440305401c0c50310300964029124059070744000c0c107128561120440000c14803480d01c000e0102074002c102d0540041c20000d01030001c500c816174050a0000105907002e100384c1e0240140c1e980582101f0944254202c11540030000f03400500f401540c0f03c0400c04c40caa254002070000b140509981002d5041ca801c00b0f03400c50f03444140d801501f0a06003181704403990040b54200c035020f10040002504c81134140007a0308040c0800d13120380140100300c1000483c41e1050701500941350201a070040341e0180c0307a42651f0017000c415011414800c20b6000300081e6208100130320602c507a524140b0891541c03030f008101502d2103285801c0c096004600d805548650900c5080b20414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 75297358 1250 75296108 75296119
    0x905030c0d14070c05060903010906180b01050405060907110705060d1407090e01051e1005070b07180e070522090b060f0a050a14070605070e01030213090b01030e011118 74
    0x61055442c030840c0c000d03a05c135080c00b405d400b02c4d03290041c2d41c1c290310181c82c068001c0001e00c150450200002179030104810100c072080a03510021400c0e080c540b00d59031184c1009001d000701c0d516007020907286598413030180c4240784107114000c0740d26100d08001d0003807a400b031380010880c0300710000d01400d0442c0003007241040090103c41040680b82d0001c042e81100e00a440c20480710801211006040f984045007540040094520030308145d8010010030407203000e082c203890542c8410400300c0e030307a11400740d03621080002404103200c018000d0348119017180b007506007946071843c51880300d040d95109401110b28104c0b072440170070070f82a5501908911a0b011141c9a2410121910720b42d0640075202e0701d4010018049101c2200d40c1c00348040500b01c0c0820301000c1e886a66510786140508411604000001c01d4410a0340b5254085d0081d2404203c0840e9103c52003401d081c1c0c4174004082c0c0325052410103440c0d40004004107001e218610205028075412a510b0480281141408444440050181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 75298608 1250 75297358 75297367
    0xa14160e15040b0301020706110c011104080604150905060406050703060b340b01090510140d170f040605040f08030901080c030c1207020607030f06061b0203010905030c0d14 76
    0x405208800d60307200d00c0885000415201d100c0201c0e00a0042c1000107203a54500a60005000c9a12015001c400003480084c080055038240f42000c502940c071400f24258450800f0a0006000003030241c0c031840131040000e906401c54903403906c4d0034019501a5207507940c034414011a08d80c0b500035a000b40080910b0355242a1a07008080765458400503c41504503008020840b4100c43c03226003040e807a0040b00e5400b240d47c580c81500002c007800d5525140c02c0d91700010005401019900b9a44c50725030040c585415a0700e96100c03a4401078113100da56122400401860900e0040007000d40050540395aa203034407181400858041044142c0000a0a90043c4180f15407607900015003a48110910030040d207a440b80d0040051600841050303010640e441400c00041c6030b80015134521a00305590b00f8007692041c05c0007841129032038080c030760001e0031440500d0540d40c1c0c032401c1112ba4601c007800000300301c02c10f40c980c1d60440d004520b0031005074112102005515501038201e246171a114420207140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 75299858 1250 75298608 75298621
    0x7080f010b041211060c03120f0103020d02041d030a0207080c060415110102070501360503030705071506061e05030702030901110c130204051c080a030209030a14160e 73
    0x8034042c1e4810f02c02c02c2d0090b020b00c0c074108505800c07091502880a8002a101e8090000254030703500116540c07103003000303032038001800b95105c150294104c940141442c8000d150f9134090001500800e8468030131199000b000e141e0340c1c03004000406403103c19a01614010741042005405c04091501d00e5120301030506c03040c0002c403031081251600400394117144100301c5c0d42d24082d901a00032058064020351078001803030410603544600441944605810f88a00c4804650640d40758903408400b402950062000404640c020300c010900140243c06600c02e110711680000700359006600f0410000d03001030201002d40c0c03901004128142c006081c01802e43c500414025940d014100303000d41003000d80680f0400407201848035064425010f003095051998078001d95000e584544103090080c2e102e004050851607000100000581e40001c21034508550840202c5c00394006100711035150080e6a40310000030141c01000d450410024007070b2400104203441c04441c00400e41c0104200081e89041198 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 75301108 1250 75299858 75299879
    0x1d040b06180102070e0a05010f0503031303061104031403120601050c0d0e010507050a0b01260307020907030e030403060605040c0905030a0f052a130920030a080f0307080f01 76
    0x3401100c0d04014610101e9500040f49002c50343d501020302c51502c0b5051115418154004905840d038480882114590364414103940307101d45000b0a0030030f41c10032000e000240968000c1c0010140d03114401c0d09080e2a9240d80c1c004c4980c038400000a9400010014180c5154480d101d03408002400c24a0604001014003521407007040c0110040142c410085c80040c2c3c05801500d5003035820100300c0e0940240c601c0d00d5012413038280620b480c1d64102007950448d80c40b010843c81780500c00c610182d0305180160b42409100c4001030000000c0c5034450090b06042c0a0030409400214054240880d00c60b24000c02d01040b00c01a601000c20000602c4c0305028540300001c1604401c0d41c0318603400080361a07400e140d070600030b113204425034450341000d00c000040840f20390700c4910300d02207030b108000400d030114a004885100c0030043c4100003814102014603140790042c0c86d10b000140913181040300c280c0d122940751744600a1500d0b00c6c400131042c0000241e00070b0002e98803074204c94500c80c665040408162 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 75302358 1250 75301108 75301117
    0x3060a1401090b0114071a0108060105010f140c01020a05030f0a0515060a14040602071716120c080706050d050f040c120f0b0c030403120606080106120e0703031d040b06 74
    0x51a03450301d0f0358091907482881415a010700d0060030607110403042c68203004881b041c0e0030050206503a98004104000d000c10064120b540c140c4a00e403107144c0840081e0740300404c00c080c20208003014031900781003140070f0008144110060b038a02e9a24540106000c0c10040c000d0007060301180ba080c1080001041c1844154003408101c0340c03d9141c00c808502110342e41216102c02007244c0001c01c0000300d05030002903103016031740e0409a00c9064442c04410664504240090288039040900d040001501a02d25108924004e41518200384d03114425946820001d51100300003c10008040403010000c0c49403a4000134860503000c82c1d802c060f00e035403104141500441d40a402d1000d001070030880c541d000c86060a44c040ca000000340341085120b001a0001c413819000f250000d022201130840701d124607400e84905484d0089140d080ca00d003240c440c2c4070320009148240c0e0320b03000c0722018101080403000451080e83d81107201c1042140c1c5040d65001d600f50103005a082025019141d0740e59070640c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 75303608 1250 75302358 75302369
    0x30a030503060409020d1110030504020a0512070b040609060f17061c0506040b04050c090708130201210b0a0501050408031608070b010303050a030b09041104090c150e03060a1401 78
    0xa031640c80b40320000d0000e100c0b6000c000d41c42640b000e003001c100281e120941d15043e01c1100d0f201c81c034906209040c5c003595800c940082d40801601420b00840c6410796072880701207034000403a8101904c6200c0000c659005401c040c010480101742040300c558442c1d010015440140343c030010b14160355403c1541e038080940514880c60204407404500d8180709d040d0b041c1c0030b4112040b5226410107007440004941f0a0728191b0300c0b03000d101c5605a03d03003011446540142e01c90b03130340d07030405035140303507100c0f1180c450000101d0410080c900450903103c0c0710144620145007903170340014294100300401ca2000240c0c0d2100d414054240010446060b010003034519850307175400c0e07885500c0d42d6854560b03031030b1240327240c000e001610f00780010081c03640c400040c0c03a040390f180d01e040196103401c004201425104640041c004003d82c0d455050074103098201c600d90a02c18100b802c960358407001c1101c41804400030020004103500940b039a80d00e0100710326900b051700e0720400c00618440c8038000075140c01c140605e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 75304858 1250 75303608 75303617
    0x90303050d051b0a0e10080405100c0e0423010503010615051602031501030b0906010e0114040b031c0201060e09120a050906030a23010605160201030905060f09100902030a03 76
    0xb0207800d032001c02c0e4514a2483d0074a56518005007a01408030004000d110b40110a1b0811590030f103401000e10034080c54000c00281031101c1c0c0700040324003515070a10304404200c02c49012007440d8a5500800c00135041c00f11078068040c2d03d005a130210008160302c050320070380c18030404202c40e48002c113610005d00010320f4030139510401c04600060b00100d40300b00940611520000c0c407001c101e0700c03400505892050980da21a9100d50030666602c0e80f080c05041c2c549084180104a025407500a80305600000741020500e44400c030006414940c1c0005110b4401c9880700707960a045e80d080c0710313070005842000711850007802c01d00d0000c0e41d070b4103c4c4d08000014240002e060b01c01e99014809640c0c00c82001402c4554914181007014041d021170f071005980115065401041842c0400c0414140c5020355245410400036224000d0100340e0310500740d062650b1002400c0c082041404a0340c403c0078841c40d08004c070b04240340b4117440d101c80c016a0643d460b15040c15040181e5020031020100c130b426141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 75306108 1250 75304858 75304861
    0x2010e090c16050a0804080c0a0b040506040501030b190b03011517010501050f12190c05030411011803080d050906070207030b0c030a0b21160311040510030f06050105030706090303050d05 82
    0x403c1ca103840050301c000b40c059800414001460940052581c00000007a00c03440c2400c0e0b40c903510b1200c14020341c0207a80d40814240401c1c015540320b81c0c420544d2800c01403801611102d850f00103028071000b500040e0501c02c00100620441ca900781f4004002d1405141c440b045201d24841103034500410b004260412070002052513000c1d0040c1d0569800b8500495400d2035814164803c0140b010b4659071000000d0070f182c1c40c0d40106008000341c030301c10344e00071001480300114000116038140344224000c8003400005408800f1543d030102800c80507105480006890034135201491402c4401000c01d03007194044542400018411b0311405d4101e2030b004400c41d203070388034052200003406505850381d8100d684042c0f050082401004044802c2c003040c003e40710540003031150810050024080606a483c0c1030901c1041428107074001640f01c800240308101043d240d6907804070880e00748005407041c54850b001400141350900c5071900900302400c116980c41d1860740c02030024000c0741e010034007080d030b00c2c030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 75307358 1250 75306108 75306113
    0x920060d090501091211070b0c2509060605040f05030d090306050403030b0d050c010f081005010e0d080301060507060b030105060d02040203071e0302040f08070614071e0f02010e090c16 81
    0x4212001c81580300400c0c0e170a0402c43d0304002c5c00c00d0200c040b00b0300680700b89080011040390000c11941546102d07006844c448188552508140038038500c0c1c03808140c541400010582e41c0c901c0b46802414041e940c1c107a50354600114120746074120b4100c2480303600940f0700c094155800840c203a0450b41e1000000c03031a0703a56400c0543c010441b44440c203801c540320880b0441040b1002c900040c0b0800c09894841038508001740444a02c04100c0301a0410300d0f50719400c1c400b80d0301070b803854451018010401c032168003a40d500d84425030000e0b03003c2c40200e0004502c2c80100a1540280346160740c003a8001c00082c0f8114001542117122020040d003d0766000000c00c0b2070f28440c0d490904805501c0d00781505d01140c0c0e0303100800030360042c8507105591054140114003910046619030803a030f0250740c0d5041150000440914541c0201c034110341e800440c20701d4100184c8540d00c0000041d000d0200580091500d00000d0b001079140c0b42c0145c800c400720000c0000b00f41c009020f5a0780b0300c008802c109008030b4640b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 75308608 1250 75307358 75307361
    0xc0102010e07122003010f050601110105070912060608030c06090d0201020f0a11030c0105160f0306030809060a02150705120702060f0103120c14070311060c0a0602030606070212010920060d090501 86
    0xa03c0045d0503500300382800d0341040482c0c20090040000382e83d50030300300e880c484409003251030a55200001540d0940c042041581d448030f0a1034050182200080702542c0741040f51a550010805003030b56002a000c103c00880c0c10b03c03481c0030451690000b980350198011030050b4501c030350701c03c680074041c0c1d0620b1032405000400584140294132030080109081030842510845021208030303001482d0000d2500c2c041e03100c0d0144c0d00459034031005c0c9a04000c101d01c10061190003164150003180308030540c0a944441d041c114500038152501c0320b0360754846800c0b000c841140024150300541d44110103100d6a0b0090142e03050440e5040710800082c00310b00b00044a16820f8038402a0640904880c285c046043c04a20b81c81100d11640b44003501c00203100c140a0380b4080d08540300150b4200b5070414000c034200e40c0045034081d60061205107810f10a900240b0410516408091169950780c3c90100304028617a030b100240f23341c03003c02c60344c1c00c141d600015054450404219100e070744400781441000400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 75309858 1250 75308608 75308663
    0x50408010c020606040b0f1302030606070209040b04150c020606150d020d051006030608060a0e0c1302070614060d02010509030705121513030903140c0603090c0102010e0712 76
    0x150003807203041a0460000d680c3e1406a4446100d42c1c60070141e84014070701030360100304490010305440c0d2400000c2c0e8040d0001e4100a24180d00080c0400c10354005036640e00d810ba00c0740e88034821f1510b580c24142408034201841542c81112589425941d22183d1380019499602680440f01c16003440c0854001903940d0045411041d0014000701e400c843c00b0100d40c1203144541c0c4c0701c0b4402c00c010340d5205000c030203680340c40c418074445800c1600441c0b0201c456800544205002c60b0444e04051582c2e070104d040c81d15100309081003941c5c041400400c101d214044c0b40c1c115140ca02107880c00741001d10005002040c04100241401800980c40000741ca0a004000040c10000c2180c42d0a0f05a114056115902001401e5002c010310f000a140306929102c082652905540c03182c14031821070fa40c0c1803c40c1c4940b0340e0406c4900c10740702c50b038a583d43e90b080110b105000c00c501038007601104030006425952005112a15500294802e102e6000d189010849858011285404032a0101e1446e00080c0381c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 75311108 1250 75309858 75309869
    0x30403110d020a1a1e1003021c1a0c04060c140106060906120207080d0209030309100203130b030603060c0a0c0503040603020403020f0402070c060509010e03030408010b030f06070e0d030504 83
    0x5614100314070329004030b007075001d4134000c16900c21504081044040700c1c2c00200c0714569058171001e80b445440020581c3c0325409801031070021001a120380009066a0544100e060314200c40801881040b500c182c10643c0400740743c050008504020011402c980101d005807070030007001c6c0201809100d01c0e810030703451270b001d050000c100d829250f1100518a00090143c43c0204001a074413600400c0070340300326001c09811000250030b089c52180031101130350003c0342043e8184018030104c1400d503203100341c001c0f1540c042d8008550302d28905c0b440481c915003551008440802c2801000080c0e100824210740c807000d40d01032256210a0704009a80710000404090503501c004a000309506400d07900410a590080300c0141e20390703801800700004e03489440c0b4001c040c1c001000d420401c5500a4003d4071525105042c480c0d0075280307490201b89075800c41d6018400300d80d140c1400d4015400c0a01814108112241c003929661400c007001030a100240d420950144084220f200245031160054801410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 75312358 1250 75311108 75311113
    0xe060f04151d060405060c0c06010315060905180c0102070303051903060f030f1502030c090f03190f06060611071a04030804090f0e010b0f010810080f03030106020c010804021503040311 81
    0x1400d402c540e00c1c102110100ea00344541e102185000c3c1200c0103855401d80000d00038103c9a003507903100302540081d203404840c4103440d1040880c403003141d8066207209850100850b203201d45c06d80070461602081d4030141d41950000001803021030392140840fa02c0850b0a07448038001c400c260b004074003e15065000051b848041c1101104102c2d03801500042e04c0d0180022007905403a02800380c08030311060700c1c50410707500100000760b03050414500004512200800340c0b14400110007a44c010364144440445924044120520802c403080c868a00980b45038a0542102098a1180c0795140800d0241c112150b01043e10700c4015040301c011903001e540d01003a80c6031203a54558042c4040d14a041d401a41340381004400380960304140304980c1c882000512125042c0c0042e00190707003210340609612600e6035444004111841e04000b550ba0034806400195682d614040c0000c2c00c0201a8001c2c504118094041c000540e43d40001c0c800882c44d403691082c0d881c0c64518003a0360089101d0075140050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 75313608 1250 75312358 75312401
    0x81503030a0807020f01050705030105010f0905150703030f0218060f09130903081302130e0f01090305040302100c0206180f041518060b0a0e0d080309100e060f0415 72
    0x7241c0c8900b0060080e540b9070212840c6554617140750b03083c2c1d0003c43c2e6000010301d040c00100103a41c420907002100441c4c078100700070b9080c1c42c0e2011031000c2e024031441d420001000681303441010340c5441500bc1031a82c18408606104403e402d442c00a43e103419100e108050200d14030312038400103812106400b00080004000c8000e61110308003800f4985815400304144000244214070365000d070301c200580c01005903c14001c003401c0c08000701410781c10f1002600c690300b11031f20345100c00d11583c504180651030300e9488514500c100803401d10740310048410096003805442c01038503000305036070b01c94071144071841405041c8408079401c0d1000c5500e80d940700d824101e00c1c00714120b16505480c1590010889800d43c910b503841a03c0684025101c0c000c0600300030481810110f115440e2100d00c428003c20b880346001840d15162590307002560101c3c1e0310782005210941c8400c1601c50300f030500700e158000d406149803074144503440000060006c0c002c0760181c070104d852941e041c5d00c05681a800c03a204100d41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 75314858 1250 75313608 75313627
    0xf010f05010317070506040b09072d06050406230f0d0b0a1409040b0402010207030507060e040b010c1505070e04090b011e08120702060f030f0613050c090108150303 72
    0x1400c401e1009070ba503403002001100001c10300d803049601c01d0340c100d00200b803640c80760368540300a880c0003007500070140141d40010a980d109900003d000404280f90031501c0191030300304804541159200310144102040304002003500320716043e055011200c10702c441c0e0084d0b0840403c0d2441071000201011800068030680404968024980c03e181035448405091312040c4840309401c154001a9004032002c0001e00011a01d01d5410360081c81032050300c50301030307682d9240b606d030400c190881d10118550302d001039081c1c18603110788801d481003464940007102072600d800700c20324034000802136001e85510014007824001e003d1010007642c080d0041142c141d150602031480c1a0a0050300034039a00900d5410a01d800101c03108159464030340a0050303030134100c0e5058103551001c00201d0f0401c03020b0100300c6124200802440c842d8620406204141c0ba08804101b00443e00e90402c2207906d1500d81813024107a01d000640b512010b00303003040c170501d490703410384404e9000503e8402e5a0505c00002d40808 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 75316108 1250 75314858 75314861
    0x3060b0d0e070602120f0d11070b0a0b2706010905030d090503010f09111309061b020c030105040b06100c080301090903080c0408030d020702130c20010209060703030c020f010f 77
    0x1e20096040d1101d0945440c4100e03110750000044005401061009600c40d8142500401c0303c80400e100009030143c08170301c5070905404c020340990710045403a003080b003030925034094524002d408461989618072031b44001030f81c108100840142d0306d0003c41c006030160b4055001071003d400c00808540028281100080c580042d50040718081c0d424000035201500ca103000d0580e0341c44c1d03c6074010040321071000c01d20500d01d50042e0304158860326485810041107443c405d009802000f0f805103284214050070180c6014000c1a000303000341e14060030000424400490705412001c00c45d0308030302c00d45030074030200c0392032180440c0900390342c4c8000000140c0700c24076840103a806100e40c8030740040c0e0341c40c843c0d101c606004a1180c000d1540003004441070340f0f1071590060600601c003d01d050300892a88004004495035000601c01041050416002480301c1c502c3d07034040819000c00035442c10900fa00800c4c40780c086e1904c01030078540c0701d50380c08650078000c0c81350340c644072040c400801407080050204030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 75317358 1250 75316108 75316121
    0x90a0f080a02120711011103070606030b04020a060206070801050f0d15020a020c030321190c02011e0c170a090b071d010305011508041106070803040606050406030213090303060b0d 79
    0x10161190010101d9900b142d074099a0341a90085c4c030000d0381c03480210040d1040b442e100000c40b1035010070001000010314034401d58010b0760080c00d181e080c91500744184684400030741c100c40c0666102d43d003007121242c0c3c00345003903064400540e079503002081c8202c041003801b0088400280350500b0144502c000d002107a02520340c80690350b080f02c2c4c2e945040b106040d124410710340b07200c440d0118600f92441000c4221161904926034801d50034000441d45900422644105190310040c4d4445001d0070003c2100714035100703e01080c05080101809142001c0c01c1072a0302d0008450754400040080c15444c01903020b02410b03600020084c0651516240c014507180000c1070551043c811112088031039480fa12505069403180391003030103d00e031402c0c0c098401c000b00500803540400b0704401e0580030b894140290450504c545107058407410180340c00710569403545c200c503000301e181803000c00160756004100341560303120450001314007001d401c00320042c1080b604012140c0a0000300c104120b1415030018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 75318608 1250 75317358 75317377
    0x40c0311120a050708041a07120f0b090106081905040503090d0c0e010b0a080f04050718060509090312010b07030e0a0f030b0a15151e051e030402090f090a0f08 70
    0x8100c144d450a80640c2c041c401585c019000359040d1200017402028600103d4220100d4103011400c02003810782c50003521198011031848944907580321405091142c115400f5040506040310782c2d00d01401c1e03105207403c0300007590115640f141d0100c4d00340801030080310782e2400c0260044104130203504085880241c0c0c0e104d1840c04844c0c4100000e5142001004c1e1840241c0c190ba400c8699100d105810706c030003d0142c010303562070003110f400060304c424416002100741c90742c80c030206400d8600f60400140480040c400a01500100302c40c0c4540201c880304541511414142152580c5041c10f04450345940e0340003442c4c0103a41c044004c00e003c402c0102c80001c682c400c403c990015581d08100e074090b5000296507021040500d8024410b0070740320207200c040000285003003070020080c1d803099280c1720004030318000843c4001504009491400d0320b0b4607002000c101a00d40303941001d901040c810700300105002c00d035101d050003185841d0001d07c07107011000d8200046240903441401d1880a41d4442040d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 75319858 1250 75318608 75318611
    0x60106090e0906040519021908071d070c0308062709010c020c062506020703020a1502070203070b0904090b010906090b0a0f0603050a1407020c01260406020d200706050708040f02040c0311120a 84
    0x22050080318142034602c40c0c102d80d40c0754033700f2101656094030030240103445103a003c1d803201e4035010351082240301d44c44242e01035807034a42c050605080d080e0848080503043c0086410400c0284220349890301142c2180e03507005040046081c020001e0710381454840340060101c0d0001520310281640000c900c075660b03024a404c440000c128110550484c450318100039016002090304110707444086024002602000e03002044030300590b500d00d07041c0a426003040b240c1e107503505030a100c00712849c414444020f20075102248001d0418442d0004294584503850806171544005250306c10550025080c0041c3c0c0703900c01c0f101e401e00c00c01c040c0d200d460581000d8001a00e036910a160840ca40c03070b044503a10100d00b800d0300740340c40c0c1d61203180280d0320510304180200d0b180c160705170b10078204982c50351400200301d09840d2075800c030b440d01c175050b202d018108104104150302800040340450010748007256044800007910507151106038050800507000f4040c8803400701c0e1820444101c8070000c2d11822070040c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 75321108 1250 75319858 75319889
    0x180a0807031b0b070c0302030c0703030201090b0603030406050f0c10020a0e1f05090409020d0b0c0715020f03010b070507030c0b04030605101520060106090e090604051902190807 78
    0x7a19411100075000350201c3c00d49070200c1c5120340541d4000d4030550103441541d242c070100c203400502d400c1540d4401c40040c1e6482c81d00744103001ca0041c41c2c43c0c110b00c0403406103140c50328004e0000c1480c0600c036900c0c860818001035140128908101100799070800d00010b5496480c039510181c1901c400c103074028055814900a680920400b8400310715040c2191215801e209606090000910450340100e030403116500202d03002c100318242c03003403240302d0341c480300e995038285480d10104404104040051050050202030503081519041e641520842a08240c40d0841810f00c0d0f80f82c5801d81d400607110001c2e0107804108003d01900900942c0e024071400d00164031442455604041e5600c502d100040202480c102c1d0244500d01200b10401c1040c105a000d451210103e81081802e920110100e010041c040081440702400706038002c3c01c0e00e01400b101d1070141c0742d0540300d43c050300303000300c4600100c1606001c41d070360070000c8000020f804a070548026107a020316aa0385c003072400ba03080210325030395 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 75322358 1250 75321108 75321137
    0xd270f031112011506030b010c0501141905070207030f02180a150e09030a0c150608011a03010c02070b0a050f07060605031203040c09091a040605060901051203040b03180a080703 78
    0x242040c003480721307200803011a290000c11801451020b22681c10803c1c040701c030030042380090103240600160120540780304d05002d88500240d407900b45c520b00c0b042d8180003c01c158681c0204001c000c49410140b01d40c1007101c07e200203010810140564500c008288040c80394054150307100c43c0180d200d00c03a480140b00d0326000052480441210300220340e84c01041300d2606548500110f1401c1c0f4802c00300796065000035103c140540d00d03d5006800240e5440300c0342d2042d0510790f0030104004900703030000c0010050f208002508c400c9030740200200801d00044070118284100101d0b02d84603000c40e178042e1a901d032f0340f41c0140500703203c5c4a018031900c40c0080311164000090101c901403684141c0307801405c2e00d81500c03040038121144099605513802c80f51b103207a005801280c1c0d80301307610030705c0300281c50328025080100565040e006180101080c0918070b103010400412507003a180889151a140c0c0c6e104c07510f40015810101c0000d1a031b0003400d03100000c100440303000d015024801c0d100c620310360703c031078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 75323608 1250 75322358 75322361
    0x1a160306030809060c0c09010311090c07120305060105090a0b040807080d020303180705060301090e0f0303070e041a030f0a05150610030c090e090a05010605030d270f03111201 77
    0x240406442c42104118100007403405800030710310804000f081e100e0400b43c00002502c2c00b00c003640140e5000d1280d00c08c0d070405103444045964801107c48089050035440d44801610500c4a100c1030145503890011807003681c00344090b6410344400404407080313240c0b00e0031001003503002445100c42070f00c1002c0c1c010a840e400420030024800c0a64011415980d51483e5144444c0c11103010f24660b0003010000f16460300c0300b100442c06018055008075896082c041c142d0729003c8072510310f0809070814400c6c4034000f91302aa1402d4244822240810310004030051180341d603059940ca1945032045190410540101181050b43c6a00417800e4590450a0003011010414111101503104500303468814a07507000394407500504e040e84c034050b400942ca4004640b4a105c09882e40d40c072980c8130a035010108a4240207041c043d25069000d891446072002001d40b00b0014082040040800c03082d408980014040031540184140400007400300d50703a09150b508064106003440c01016a242100c0d04210305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 75324858 1250 75323608 75323621
    0x60d0902040203282f0c030d020901020f06010503100e1e010b0108090703030c030f030e0a03020115050411030a0b030307060531150e01020d060902090102010501051906080a091a1603 80
    0x20841d5a5a00c5c4c00850342100000d0750340054600460800d02101d10140001c101800a402003200c0040e9605031440000e440c000761142441c0541d031094006004546010660310b80f00d1000810104015200a0155041442c00d42252f07116000c0d4403031903c1c1d031300310541040000c00c03020b0702e400e0f4650311021103080d2502030030f00001d80840d060a40c56400284600d401c10100c1c1043d10f00098110341c4642a28280b800b009019001070791200000b17404003054500ca0402494100d50400021313a103241201e6282c00010400d402080d03681103400744c40e44041c000c0f141101e900078410001460303c0480a15003505100e03190640a04440481d01c0d1411440155041c0e55084001580110304452449000c3e00d524082a00195005c0c010796078203a195004070700103490441d50250b03d0380ba40d40002030850303005a01291168a0301640c2d05040c05900301c403801680c189180042e503554483d010308000d0015100000c2450020ba03141080a0030300c0c40780140184803a400303128501235072001c200e00340c428 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 75326108 1250 75324858 75324881
    0x180225030305131a060a0e04050a0615051e030304080304060305160305090c0d02120307050703140303060a060c020d0807080703030506060a0906081509091605061305060d090204020328 81
    0x1040c1c642d00b0715244504028550029001b060101003640703c1e0f400c4080c1d41c409550845080d8031414000082110900803070640e880110903030043d00b86420001881541ba507590402807062060343c03070840307840600803100a02002c4080340d81c6e9642d9140c0040041c40112600350f840c1d0411444010407622901400307020f041d0b13403030082207880407d2040000c03055441c507040345d000c1b12012010312690410b002401c1500d0048000c0c00c03400c0c0c03450914580d02944144040c01303e810403c208441c07680c0700c01c2c6d102c080c1c544c1440e1500c040c1f4102d20105e0710702415440c2c00f80c142e00010600c4010030800d44010300724948a640c00b4040c40e10780006015490040c54520b20100d1003041050003901e100e52502039000720100341100031600c400d800301e014008142d40000c195003083d104d1039a0b024594581c5801031600b554031500c3e10705154030700c1e0303d60001c1d400f130300b4031841c40000e201c20319001e20b0f0007211007250010000c550741d041c401d03490004103040100b0505040360025011601d500c0324800e80c0c900c0c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 75327358 1250 75326108 75326123
    0x615030d050a03020306040e0118050c0d0206040303120204080102040f140103050f060d03170403030b090c03040201021c110d050a021203090a022803120e03010903020718022503030513 81
    0x90020300c1a000780d0001040c5a40041d88d5024003c1544400d00500070010b02502c1c20301e00313074081424224104900346c4071316400740743e00246280040c0c5500d011201200e41510b0f100b841000341c13100b1407000c0d1049501034036080d0f0003c01c0200300e0180e8031040c2c80444900240c0d09108000b030710015010740d4000c40b41e601c46540300740c0010398181851402c20f10380921a00e40b9054840900f4031071010404195001d4000940e42c090701003c0307040031100b10390017118010f059030640c0b9181c1e000035540e4030720f00024081c18907801d80250155020301d41d01902030103100203869401e007882100900c03681000905400502c1400e10403014003c0c1e40003101d01500d0480050010340f40c0e076800707000b01e4001740c061424841c22942034507400b00501307000c590040c43c4105141141c0e4801c4600080441c010849864805d034989404400000d0b00064013070205d5000c0314688005111581410700280100200f0203941d101c4480c40c614080c1e122007401c0c4626121b40c90800c0b02e0703142c400403115003800d821030040030f01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 75328608 1250 75327358 75327367
    0x91802040b04020915070209060303070f083708070507020a09020a02032101080c0405070522090f060e0901060303090311060720030d050910050313060e0615030d05 72
    0x1810181c00601150300e0103030000d4980f0498401041c501084814555021030012500600310724211003030325009107007240114200001a110400130100304c0400a000d00c1002449119104024486000a48050251646000d51000c150f4449130455400b5000030341080001085180241c0c00c0e21007540c2c014044401c41130800c00000300079480b20100e401580720a000c28491000e64842d00030301148241006070b619450f100e222072614425070450f40c829800c02c020844080da0102c15075982d1102a00c00750400300b0f0422200008040070b40201c048142030080d5031030844040e8002404860201207150b42541e103041c150744c22591079020080000390b07100800c20104445201003042e4100c002d04651819600c0d40d10400c50b52081c1c00340c1e041150310040744151501e000e000c0b100d44581d450401914090064001130b00710081e228298040c003402101045180243c2083c440c8a40d42c0b151080052900240300d8903a2540101c4402c1154909400a4691803c0100380b296a0501503180c06050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 75329858 1250 75328608 75328613
    0xe0405100b0d0e030a02071703030708041203091b23010507080a02071e18110d1107140610270b0303070209040305090a0503030301080706030504020a0312090603060918 74
    0x295020182e42c1105545540481d07400c01c10034002010a0580380d0003d01005180c0700740e41c2e0001e1184810300800750001e00130040c0490700114501d41c8281c0c00b80000c1442803610300250002c00340a84050038903464a1403840d507074003903640c03010305451002030280041c8015401e40050038040040d100d00040e400e000500020303041c50003415200d652401584c0d881600c40701707000140540e940d00c6684c003030300e600c4e4200445c001009610264600381c0c402840410084894120a44510302c0b82204c520340d101803d0b011f448003c416a465180e003c202c106102c000e00a005550740c20640e0035200c08101030754005681c04006a25444000c10060000e1100c103100320504000c18148010356054003080014000503680e241c0401e02c268840c3e03c4560710b0340020030500004040541003240a98001c200500c140c103400605002240c40c0c500e00803030300e607650744003044074a65603500c01044001c504001c8000b260300714000c44107a820344e590801005541e2a801c0050b10800e6000d03509484034864030002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 75331108 1250 75329858 75329879
    0x1404020d02060c070e070207141c020603130605040506010e070804030806040b01110313080c0d08030f0606090d080c0d05160209040201031e0902030f03030c0d1a0d03020c010e040510 80
    0x206240f10240c6510650b5038441c040c1e140740403141c5030b0060b00325540500c4101800000003507481010780301c0060131001ca080700766403c06c035090064450342011000803001c0c44c95805126100780c3c03014091103541000d1411a503118030038000e4120350300350400003510480c407648020f03214507010b40d5a01000c0e10b070f0700705110080106040c0c1504210050040900c0a4010401010030344c02e11514071452510306961340341481e80d1000f01a108580c080e4010b004501d42600340ca400407015807a048030313501c4640c000b80051003515101500491080308400c02c0c0040d280c050103041204000b03890458510039011100c9100c0c1400041c000700041c040c0b42c0c00342c20900c81d000d510501c181000511140454441c01c14400010702c480701c115201c25180c130450405004a03007000e01c12000943c11410b002c10305000c4e60240c02c0c000c0e18210b503144120851051200c0b02c64410280281143c620000d040c1002500c400014035080d02144485801040078201407041c0e80c42841c0c02d09040038070703d080411200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 75332358 1250 75331108 75331117
    0x50108033103030e0915010c0b09030f03070804020901081f050a0905070e07030b150f0c0124060e03030c07060507060207020402070629130e0106091401060807020d02120a110604030504091404020d0206 88
    0xf040340b0041c8103041d6610cd1300c0740158051b0381c06d61074441103031405104212007460160041d81c2c0a411195046400ca1040c4504004074404a0004105070742e0303a07607420005114510001d44140708001000480e41211b442d0f00c1d02807a00c07035406101a000b1441440b0140c082e0300d001d100d01420030070104a241c0d66040150100c102801e0003c103c020601c100c1240e02040c440c0c100084501602d000c009960b0070412241c0c4040064000d141480c01300b614158807400b480c0f0850062100004400c1e041011580c11030b200d45a00400c11900ca200d103040003c01000c0b14450000e160071041f01041c02034100e1384455203140401031084200c0d001c400c5004c1301610554609031003941d203d180c04a010f00e00f60252206244103a680315005600d4040e00810354100600640159000102c0703a00b040769000c90412610780181c403846076903c41c00101114400441403400764103000c0c9205000406500078002c00c11106242010702c03129018181580420303506880007540000740d103865000505007c4043c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 75333608 1250 75332358 75332371
    0x3110405040504060914010f0f090c05010320030c030a0b040911010513050301090503030a0506010c120c0c090c0f11070605070f0206070803091609050108033103030e0915010c0b 78
    0x4034060019607030f040800000850920f0032030351240401a600046072184030250000c40c9c9091113003083d15120303104031a0315405494100360b110200650303481c80107045564090700c412441d0f5520b207000ea03400c2c0c1568005903040d40c081400e0600518091510380644049903401001046100060303a00640d52035202c2c00ca80c551344416828001055a020710070003900602601c05140e8900d0180ea0120885134000c00c0c04c1d05201d08001c000c03020460140484c01d8000c0d50b070a151101c1052401e10800781485903000400c610300b402c0c40d10b54140e40c00b850f0242d180300c058846021581043c0307000b5486500c180990341c00260240b1212021600c20610201e6541c00504000c0c85d200040c0c035201c100d50300c11102c940c0554070a40f00401c010140060800041c494944100429410728040c04d460380300301d4103103500386e902030704132b540d00c2e90106507400000980d442c00e1095000e40d01e280151160010281491140c21100001140103400790924040c1c00310580d02c0200c000c11300d40c0d83c50069000079021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 75334858 1250 75333608 75333611
    0xa180506010210090b0a0c170406020d0207060e0a02011101230c0f070302060f01050a0e0103030e0a080d09180203100605070c050a060909050907150c030320190311040504050406 78
    0x4940f5200024410f102004d40a1160521180f40481120040da0b00c038104d810100302600c21600070041e803100240e40c000b60302c51005681c0d0091881c851019000d041000381025280c055040100040021401c4140f8801e80314078a4800201e1051400c0300e161003414603422107922150600110128030440d40311401c040e156080440864104000340c00600b13040700540c1c841c0c800c0c407006412903507000d8010b00003196107403600b5042020340700c84104103200040c240110a24044c00550380e1407054005000518226004050f2403000280400e0b014071405420003411042c80840c000f45000300c0c0d2083c02d4501c07601c0303450341c0313000e508413201c1d8000e50b02910001040c03036003c00d4540d42e4104a20003841c040c0d07912800a42003a000c0c004862010340178111551020108212220105060800300002414610462100d905083e00580444003a1101c4c1031040003640080f900480046c2c0000c0d003205102a081c0031610700b0543c1200c145001940b5a04000c1c00100182d141a410036039016204a40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 75336108 1250 75334858 75334873
    0x120203031207030c080a06120803131a0106030e0f06070e030a061e06050906010c170d0203040b0a050f01060210050403030e0118060e03120103080702061c15050a1805060102 76
    0x401c011070308016960b490000c0e40b07900e10000b50070ba000b90700c40c1d003000071018100b217201c0c50180c40c10304039101c88500500110000c4001491110001c00949800340c02c8840805000000360a9244c000000d0040002080c070340110907440c83c078001003a0074455002d00c000c1403652035089d07007034402d251a40802079161080318115800107000c0d000f00a43c07d41d060004520f0b11100b140244243c90030b070f801c040d00915640080042d50b80e03100181072040c2e80c0020349580400094400014280701c0d000d10140010300000501041120f51a1214411600180b040001d0b4480c0304d00848411028420b000040c2e1180400300c1c0c4002b010381c00b007034005120f0308002401d903240e040d249003914010012031034031905019294051107102d0040141e201181c0b0065442e2441b904031003241f13a5010700001d08542408503d1600310341316034003180c00034881c0310100741c00c181071a0100c101401803280321400280450200140700c1c100703011403105850780c550040c9402030f01040314500400005041c141144100352 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 75337358 1250 75336108 75336127
    0x603041103070e04051002071a06040f0c020a06060803070b010b0c101409060106020706200c030a080403140d082410020102130503030304030e121213050103051f12020303 75
    0x218810041c8990001843e035803510713050060424241c00302d221a4140100304d0840000c0081603601c808582d200d6200c07049840305800b050051030b040300f049050900d0407124918158000508a181a01c41c007801d110458881c110117450f40a0b410f03004200481d104014400c06d003201d0060401c0c180030204a50380708a0f15100305044d03640351602d07414207c034032800b80700409100b4424103001d0b00846c0001d01c081490725000600c40400010b403409028030b0654a4403142000344101c44814200a0803618802c0003828240c132940d026210031141a903030a0307015012002d01003405c0d608819280c51b00301d40d666545160f40c2ca41e8100880110900091042c0d0900d1550f402c40e03080f8280780d4941c001600c90315840784070414070b00180c200c28400c1d4002d1042100099010103034034030210f0140d42110307010490390b01c01440c0c915200c0050700340d10070100d9826500c00c1c0284201c002c41c0c1007680c050203241c603810191290190182281011140342540034040c102c580f9601c42109032026048a1030b000204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 75338608 1250 75337358 75337363
    0x5150406080a020721020c030f071401180b0901111b282d0b07081308010603060b01082a0a090503030c03040306050c1303030e04020405040911040c050c0c0603041103 73
    0x241c1692a4403c00c032400440019810442c00141d941f06400900154189400c600d96a900a01c109084100c1400c1484001c0c3d2140002e102051200d81220f520552505001d5205421090f10396002910a1005580c45000080d52a4003d00b160300e86140390500ca000b801030a42c0407803031040403510a603018100f000e500000c501c2c010f040400e44000010802d44c0c1c4907441c80920301c0503110700b8004910a01018a05204558011b507000050315901c4015030709070380902d001c60b801041d01e946020703000814004280c2200030826400d9943c14610341e40c00c103040c2004000d40f400c43d4030100000c0c16400741c03000c0300c2d00200b6001101d42425061240d4681c00603107543d228280c1724800b40c0000c90100104806405142e8209404003e1a4248884942d000c0c82c1c01c481c5100281c20001d180380564042c1e15580e0449000d803002070404c1c02401014100032000150448800e07000c1c910340880105083c0c416801d50f6170304a500800381002040b10b10403c025608040e205a524001c440045055036908 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 75339858 1250 75338608 75338633
    0xf0302040312020a060501090204030b010510170403020703150516030b03010e0a1406060301090305071515060c05070b0a050a0302090a0f0f08010c020d09090c12050a140105150406080a0207 83
    0xc3d60090000b05081e10304030040c0c1da41a889020001d006200c14000541643c10aa06403031043c0c0d000d2045a81c000300071204e150600e96082c0000018030280030506501144410541e0302540d00e100b041084580c00e20111341c82180c1d1400404880e9801c520028030a80000100c1f14000f000801c01c0251840000e040c8824a030007120310f0004000314418068003805580e620002c111300070442480d41d0b8030301034414409e01e00020400d541c0d00401c0f01c01d14080c1d0b40800c0b0100c45034100d10b000346403596005410000428400e540e03d01c107144001411051020446200c00e8003a0744040c2441000d0302c00380d0185d0005084194803003141300001c900f250104009200034100c05000c03103445d6190039512030840e030300c6410400c119040f42c20b01c0842180c004c960342d421540181d4000440e407040380c40403640c03e0300c0301d5580081d641c00c10050040c140440e42116a181e10605d8003c0c10790391b61002045065030341100700160703148043c002006424012009968026910100503140c81007958824000104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 75341108 1250 75339858 75339893
    0x3050c18181f020a1704020105090d05011b030e101a04020d0209030a05070501090902090105120a14070e040c05040e040308090712060204090b1903110301020f03010f03050609120a0f03020403 84
    0x5010640c0c1c0c503407907032000801c170031031416448165060416400003022413195443c5503019000002145040001c02d40c40a0007112541117207000200c000303c4010083d10345541107908501c581e481d20035060030b691090380c206408541400d485e00300c0b003505200c080c0d0000100c06141e0342c1e0070b00c01e003506610103024195080d4450000703409800d0506001518001e450f420080364607206000c0400c903030741c00c41c0071107a003d011a03c03502000d503200c01d0360002520500008100480c5c159085c04482074111460040d401400c603404c1c00694158002150b840c0124411007409030480c41c003181c00710340261007844c0c2007010710741514811520b41049070800c2d4504202154401e40c0003c00f00300003042c920030200b00f020115070703e020321500b68549005c244086c0c0405050101070384060043c0c1e030390942c11a005144140c2e129601e940c5d64185100e8031941a100640b21400b0b108000340042e507000c101003002400e8002c803d42000408481100c06401c200203000c14036900304800700114070010b648038011078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 75342358 1250 75341108 75341111
    0x50d0908030106090e07080c180d031805010c0503250f030804061406130b041517010605030a0203070614120405010e0f01150504090204091b03050c18181f 68
    0x51403c9402008840a030707001c008000c0f10754091000d03060384125240d03004031800500c2ca0312011a01c007086045100400115848607409044504040c0c008200d01d030310510b80d80c4005405a65480103484891410f0001001c45e04104511010701e11590741c40541160b2503200d4502c04e09483d034500203401c491a00c290003084099080204000c8180100a61000010300c11165410301c2c3c4007141d50400d5486030f05080948030300610425861f5903002c041145810700320b01c0e800b140c0c0c0f41848038001c04180c58814941d420220007081e281400070721111081d41c0900203000452900384221000d00b2448901070741d100c81040120000004010550302981c000c0000081100e590f035441d070720b0802d0304000600164140b4103001080c1e4500500301046030010350b00410400781902c0014010003400c200100789000c07802103502e06040051a1406592181080f5000c84440c2002c100d1105c4008100c2d00342c200c042c00000d0840b22072640c1609242060300101c402e094001c22102c48907003100902c003e500d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 75343608 1250 75342358 75342361
    0x6050c0a0602030705071b050a0303080702011410080114010e010b0a030605030a080a021b010207060f090b0a0f02070b09130f0f0c030b1003020301152f07050a050315010312050d090803 81
    0x201c0c407903050301e0300c0f0100075140481c1f0b60f10f8030007c224810343e07a01c0054207000d920000504802c0c000c1d0012241b91007505407045091a001e003034580c01d2251030181080c13940ca00401c2c050700742c441c080e502d03059a04203000209240c0c80c101c104d100e00d0f401800300008143e207030303140045e25480400400d15001c0c0b15a84003074448105601c0245080001840010100200c12100c05070385d070041071070000d0f2003540c901489554060b40081d124a1a5036002c5010070000240c2814116840b40000c00c0340d110301d41c25200003a035560383d8083d1901035030b100664813002884610300c000b0141d40c41007045820b000c1c00400d84804a11044d01140d20040305030010a4a40c0040101c7e450800c0302c1102482d298241181076504040151034810300700301080302030003c62140446048449462136600c00400159640c00161400c003442d11882d00f4812180030310700101010540d80b0303010a121592484107416460f090f86035803114074541100041c0001403043c1004544113000860150290b00307801002250382e42e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 75344858 1250 75343608 75343613
    0x51908040e071d0105030a09080304080409150b0405090a11070506070f0309030e1c05060103061b03021c05041b060203040806130215070218160e090702030406050c0a060203070507 79
    0x10003800030a4201001042502c0c1c01c00c82e00307a4240f61440c8402860100c0c0c4a65401500c180240349900e405000090701104000402c03482d01c1c01030064400c0c00c40c091100c0200d04400418040b558000c81000000603c814405800c028103034603402002d0703500104040007290215030031944001c03420368890f040030b002c01c01080e800c4907062248001510703040054007007030389000380710324000715806120741110000d102d48941480f50709a14540c121007a03c0072543d50340b030080000c00364504080c071110300d00601d03100458000e1094030344c841c0b1340c0c00c0c10052403d5090b4a0200400c3c000b002103030045001805001041603692242016000303540007951b94a04150180345403460040030704001304084c01901c070041e16103104c0001c0040c410107160791100c0d40b80c40044d0707a440040d41000d0481c5811020002c0d00702d0901801c030501803140c1c4501640031009828840d03100011141800076920400080001d01c1c0b06600074083e504c2843d007650402011980c0345000c0e03030300544034a400944045072103412f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 75346108 1250 75344858 75344879
    0x60c02090606130314030706050f010905060d0f03030e011104090608060c0309070506360108180c1909060b09120304051003111201031b1a0d0905190804 67
    0xc10031001c4070407a0400c4000e2843c601c42c3c400e0ba000080074140c06581c402e0f01094108140c6865aa00c42c00511042c50880c1d000c1503902001d01c5a0f0403d07606210120300d6505103a000012060f4202000c482244510b4600754068408268008015981c40c148035078103030000c0024001401117208003003401458404250300e00100a040c00c074504d1800c006000140c03400140c0c100c201d510507589207444100041c006070310200080c440000f21200a2428001900c00300d00000b403200c402d0300c520540c0e40310060f2504a4030700b0504809440c2d4802004140c00d0310f00503841e0909010f25007000716400c2d40318881c141c1511040da116a81c10342d40480c06105600e400580300351048000030042d4249850710780040c101d60311618800d814142d0791281c2c4682c1781c806004803842400d580d090030219503900d240910700b1614003032119035030481d00400840e207030b1900009980700303a2401150504220420320346100a20001208654600c161032040c01301e02d44103074010303210030702401149849910b0070903c0303070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 75347358 1250 75346108 75346111
    0xe1f1a0102030c0a0314120108010c0801060809070303210e0102040626161106090c03011a090412050c060108240c0304060b06040b0d020306030115030203070b0d0f0204060c0209 78
    0xd056402c00d21a0f0007460b10006884284140c0500c5c18400103600d030003800703c00e44501442c813a4018070a100104951205402c1b5100d9010305507503100d21607980f05411500c10b44191101d909076000018100f0101c4e2080c20101400c000d2668500c0d1411041e00c40442140d00d991815100d903500800c0801410f508202106030720076040c6400c61309541e920410071b405141c01011410b0608d208440421100d100b41c03000703e8458440d00444000f801e100c01916a1a044904928420b40c240324903c1c030840c030f41001a2500d814003600d0302d00c20b0b85030751340c80d1940d888601078050104030042c0600b034110340b810050f0781d0091035040050030180f003884818074180688584460f035882d004000348100803850038100c90388150845400545061403a0005107a84200d40c4441180030010a51100155081e0300075030103000220300030071520000d0707aa81e410034805840701079416040214100300003c6590020403102d102c04400145420324000c440c1b0807a000f40d0171050000e035100c0918411400d00c1c1050a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 75348608 1250 75347358 75347411
    0x20f0108070519030902180a05010b040b07021e0603010312090806010e0c0702010905040608010b010813110d1b0303090914090309100201110f091f0509040e1f 70
    0x21200d070300c0d00800250081c4100206003d0035402d50006048a6220740e00605400303030300810340d018250091040c0301d403c80c1d003036451a0140d0f00e020000600c0310341420480d0115000b10304000e00b0880650200310440c1086040d800d0703161460340003040640c0d1080000c601961003043c10a02c03100c00d048005240400a0f0803000301940141c00600c81c41521144081e4008aa010304035039a8515100484440f00540d1103907800c24145000070803114019000a079100c00c0a80c0c60551036915132000040b00480150003400094000c10740700c1c003d0620f00760440446014102c1c2800d004201c41005284000d01d52080d00020104202800464a00e000d00c1558050346036005905051410781c440c1c880c46003581980c46010700e00c080d010507074001c0d00980081c0700030081d00368a400d40c0d0480d044981d801a10040d101d050440c5e4000c0d85030080704100d4070400155034400e4201136a4400703010041510381000c00c4148203000f002480b1000e01c14440301d003840d1980d00030a0b0b441d00c0503441c4800c2c05500f42c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 75349858 1250 75348608 75348617
    0x20c0414010317090307050409050313030b1503150103020d080705070312080f1501050a1416030e0a03080d11040503010c0c0510060605030a020304110604080a021e090424020703020a020f01 83
    0x752444c90b03600154040a0300c44c1144d000032000404d10f045450741c0b041c05150000782c00d03603940c000148003081c00c105100312020b280d50418504001c0030151075a55000c50203500000c8180103001605011040301c4065125261461404800d0b071034692900b0388680c412912002c1541404440d10b81c4003801c0c6800200110480b019410a00c1e015070070044040350483c1002404119841034030311032401c1080e503203030031400d41d03544400803140007503110110700c03040d4081a003400d000d00f003500340725000e5030403640c1204075141024020307030990000e04144018521800e5062002003000d83c0c013889410803140d42611078280e002c809280107400d0803c02803048a05a261410400c10550094112540304004c0c400040c1d50343d9851928520f4011024506504010040f4000c0381e010b100003011b09100b4002c8070109460842c0c019150a0401b42100c1150400b202030049800903109050106468a506044400200e13140c0c4900c030480c4c000352001e070010303803240d21000e003907040c4142c1c21032841d1400c0c46c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 75351108 1250 75349858 75349867
    0x9050d020603130326180f03030118110f031905010501120b12010509030408010e070f0302040c1413050a0801021908041a100315090c1203020c0414010317 68
    0xa8282c04010a44004440d07100002e20415201d010350820141200d110796a48600380d12040e8400300040314152001c610354030700101c00c0080020381511110300304c402140b960f030030301c140a0700c2400c00e80540345209880b190320450920181002d41600d40c000c0380c2f555228503064421456003c40003c225026600c1d01e0300503c404d9a22481d002003d0360054808660348900c100403039220310064101880c503510f40028452001c1e000300052044074608002400f5101d08441d1442c3c40314140e1280500d441102d4000f0001802c16401a07004e0801ba818401d10402c506008040d86074450000301d0008072100400340034920f03080400b100544042030085080c001140b8103000b22001c2201005d0078803080c00c000030304008040640304580c002036622420607042442c01101030320310a02003183d5078900c182080400400a104a40e8096004000412400c0c60010592000383c060281075046025508811246440714021801c040084848058640d855810800108140f913103402003040c0c0d0421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 75352358 1250 75351108 75351113
    0x60d05070f0311250803010303020d0f0201061d0603150a1506030506090c0705030f040803131509030b10050405041109060102030a120209060d090b06040c050c151008071509050d 78
    0x1091340d1030500c0c10b444581025010846440c080404031303e0051407014000700110406502140c42c2c4000c00e11611803140103040403074164243c0346c0b54050124440c0d20b0348940714400b840000403036000100a000d031031013880703541004440311004541d2510a252140d00c41400c8000c03403000c8400a001a240800441c1170210020780480300c05000f4a0a030b110105105080c400140101d0365903400c0c80c80c10581e00da039512166a01c81d00100820169180301c02800a00403551031000400ca4201d55600c1c10050305603694041900720203003070756694016440d0003184139121440f80c3c5001e82c1c0205602d61101c200c001c104044403a00030701c681c2c1103410a003e21900d5540019074961071000c240303000341c1c40300d5101001c1030190050901d80108903041c08058800c0c84101c446c190b006003401d640c144803450311070106550f1482800381c1074100c3d45c0044117030542c80505084036908004166130340e8040940d1280750300c1c81c00441c0c1e082190240c0090040141080c1c100c0320540081c6001d582901d01034a4070b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 75353608 1250 75352358 75352391
    0x601060507050606091806010f061e0507030809030d060b07020306090c09130201120513020906060307050a08040f080708180a0b04030f020a091a031002070803040f11060d05070f03 79
    0xa404c41c1d0040d003808000c80c5d40341614000f2200415414001c55019694844032545100000e2044a001c21500ca08001d8860701c01c1317600207508030054440926014560b5012551410b0081164516002c14040c401c105011030080100800c4070400c0706484000500401d8240321014110703984c55480044284c0c110303118100380d207030f1180c0c1d500c1c078070342c000181e60005032103244c18810000703c05490441004030540f01c2c1801c090542e4000d0765081c1241c4d503006c0500c10301e0300c016104040491410301003820024400c4491642c0310348502c0202100c482c8035a90b81180d44c010f0141150b0024020462503021515100f000c40c0b20003080b00d482d45168940000c2124600c0740e40009820a030041c1418001c1d92038000c8a1001008050020400401c200071807020603900022010b100340500c0b0200c4521080b42d000351982d441d048005286540c40c1c654454103408240002183c8440f140420300c0315a545032800380075940c0380c110f004130f03e17854109001000c0c0d044100001041c03500e0500740b8069a44007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 75354858 1250 75353608 75353611
    0x1503010b030601060801170f0d05031e04170c0109140c180103080304080703031b110f0105250915080106080705030910021b030d0609051e070e0609030a0308040506010605070506 78
    0x11703071551f130448500b00c2c082941443d00ca90321020355489400b20303e16050798010011031040d40d2100d80240b1510260824400007a400c0d5070140940300715884c04006410050010982d114134030000045a05041d5141c0c10081e140245800030b0341c101084101075400e00d400440002e5003c2010040a581155143e40590101400140c0b01e803c011a84004260107580318403861006007030781c2e50125803c00001025070181001c00101806515400388510b1343c1402068002d040c081b4814a003041d100c8001071400310541040002c0021519000504405000d0b0300c0d105485683c1d00c8454940c18110050700c6800060100000c020040080020105011540035040203418001603079810001401028226a0f42c10320310550000149180082c08954040760445014800905c82a51405d6880d015501a15503101c0107001c00c40000d80564403940d07590310090b400801880c1003000b02c0b404030385003840b2200118042440001400180101048000d006141c585002464181c43da56055110b850 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 75356108 1250 75354858 75354869
    0x8030307050708091206100801200d02070c06030204030c0609080d0804021906020303040501110f0d0b0a0e0a050702010509160302010e0d02061c060b07080f07030c08031503010b030601060801 84
    0x80106500003040f1004049a0400100500101065610000168880c04e090b0b4401161004040d000111107806000d010454242c00440c1e00c114407440303031840030035440343d280c52801c50390801603000000c6c000302e102e0000c0c2c541680e0042c0c540e410340c81c00c0d04d00030481d03030050f10500514107030800880ca0000751704040c0d10321524101c41c03551030354404501e0754104c544010040c00d803280300c04106140d0000146101d2801070780244640c50801c0d204082e00d12482078042c503821020005c15541c3c2c145500b1000c551030010b00341e2081e0703595a862041d01d5140c10340e001c00b4101c0c0c0320b809100d00c2e40d80c24060355810a500070054002150304a4101c40c0200003480000e0501040c0c0e1800c00321a0f0340d801d080058580c0140c000740c3d0303500e00b081e4491103549103048004481e41c40d112000c41c04030800d07410741c3c0990303900841e09481c008004152240c15007101c40c00324100048594020700181c40000554004c05101d070142c1440111942010300703444060030510300a5002c83d004010140c1d02032010f1f4115603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 75357358 1250 75356108 75356117
    0x6020c15070c08030d270506010b0310080703030c15060f0510050d0203040501020307140301180f02090d0c081005040c0302010f11030414011b1214040807150e0a08030307 75
    0x2540c5004100d06056511400c140e00000c100f181c0c0c81700c03043c0c0180104c40c00210b03405600300b207408240c03807880300384410242a41c0c2c00040140001c0c844a401540c2100c40030300d40900e81c50351000d109181c0880c0e9042200001c5008001004100c65103070001401d2003000760600290341408854110380c103c0d44245032042001e0f24080184a008104030382c0c0c10500000190b40e24541420428003075402910310b000020550f80c0310300a43d001d940140d034140c80f001c1e044e110300d4040b070b4169240034083c00510891502d50801040f40d083c1d0302d000500442c0761003000c0d001101c900d0040c02c5400d00401c0000008170a0a01041100140004540d6001d496090a26012101000d241141e11401400d00c800448c4000540420500100a01c50201d514240d903105004003205074014103424043c41e00a12072018040c1d00c1d010a40100d0090100524a920660a043d690705501b894121580d1280201103c981c0588004a500101180a0113420b54a840030301307140c8074449989101c020800020070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 75358608 1250 75357358 75357367
    0x109240e06190609050c090a06080903030c0a031d06010f05040603050a1203020f040f0e0105060c0307030309030e031203011806031e08040504020d020a0206061212030a060308030c0c010606020c15 86
    0xa0801c1e44150003810816401700554900020301810715801a020f1500ca00281c0400141e024404c20080780b04000d00f5000d10f0031600c07009400d00e40764001555440a0584510200603500064800d210088105a004154079407403d60f004440c08071340d4100c54096410041c0600110f000002c00740f01081e800000040b045190403c200c00900401d45c90b65240c0100042c002400207444000c07500b0749202240030340705c60340d0391340130046c07588078916200c501900103001400100e4040e03400480340714080d092049043c006840000c1c00c1045890104501c0c80e800b100500c04451290706c0c92010f01004141002074904580b12801c000d03080c2c06100d6025019404201c04100400b802d40c1c00600001d4070075500e0302d03600e02048000e900000800c0005104070030004940749402900000450910300c05840c0c4141c10b00c00c5540c407580001e1030145d03003949881c000000190a68000c42c8581c0004c2c101d980c031383c80c036860414251201e6034000d104641c050480b206407950f51400c25499040c2943c0100d41d034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 75359714 1106 75358608 75358651
    0xd020102070b060904051513060b03030403030203040b0d0f02070606030b0a0501030b0109181a040c0f0803121509010602010605150301080d0507140109240e06 70
    0x440244045802801d00084c1690040d02440070399004c1003076a045803803003400a0f03400300581d240413907042d818007040c2d00c9a00301d102170440c050340c6800d02e9500e00960b240a6401500c1000200040303103002021503910110800365501002d545900c0341e41400001003420380b1054840c3c80c5224006128100b5510030075044c0e0341d0116820001e642480c040c0402010680c0d100c02e41a9800c00c0910007068885113030383d0390201c15003400891443c5c9480d00c010724640d1503200e041800400305040c805000e003c003e98138a83c503500c00d00e09031039a510240801c4601c000c0c00d51500100e541d40040b90f01603043d0081c201381c072801d0302c0d103100054142d09022000d1009100c1c1c02c5a039084083c04001e020711850040044602801c00182c1403804141481d0071518800030440e0903581200e040750525581c84400e050b4181d0954041141000f59500641c648038010560402114825240d50a = true := by decide +kernel

theorem cover : BRFrame.Cov 75179858 75359714 := by
  have h0 := BRFrame.cov_init 75179858
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75179858 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 75179858 ≤ n) (h2 : n < 75359714) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
