-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4597
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:07:46.969885+00:00
-- url     : https://prove2.me/submissions/f8552a72-e227-473f-afcc-a35bb31f6011

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 826618705 ≤ n < 826798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 826619955 1250 826618705 826618717
    0x30a051207091206020705011404020a05061c090b040c08030705030909070c0f050303070e120c04020306060c061312050a020a03030c300615140d110d0903030b01020d0e06 75
    0x140000d540000c699540c40103d4443c00302c1c05440c0142c1d0350700c00c601d0110308451340002c00380000d500380c9081c40010707620040780e0f004541003120710b00d85030030072504201003041c00d444120b91014544a0000c3c100701001051611807070081203102d10260786d07540aa0385034400c80b00c000301160020010044c1500e05036401715000207603440c100c01d8800082e89c0301e401c054203c202c207450583c030200401c144941c6c0804406000743c03080d90511690300300c00800641e50403110581c81d00c603d401000144140d16450151000b41d40c0c454220f51913401d01840e10041d00c001503c0076500c400745141c0008045024104070358441c174040c1e009041d841d5040d107084008140c0e001d5043d0800c01d0417480c1003100c1095001031102c50f2003a6210204003105036204504850070382e070000010b030007007100740d4003001c2e00100c035040070080d000d8800303503107420340782c140d40007040301e4445107051000200313150307945003e240c0c04100154030a07141044000e1010300160390312103a28103240700107044040001c6081c00c0950103412 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 826621205 1250 826619955 826619957
    0xb0f0c1c090c05060d1407090e0f220605040201030c08090a03180915051c020d031809060602061608060a171203090d0201050c03040309030f0212010e011a03030a051207 74
    0x40c2c0151100b000a000d9445021144c2c1400c1c0c0300c00042c005807902009017070b00050103003451040c6501d480c8020100c0000100611401d00941e000960b188003403161507521141c1d00a03502c142e4040504d869401400140d5050b40003a103031400c0505001c0c040d207450b50084010400820f075149060703a044a08201a0038600603882185a00040c45c90160150200e00c0c8840c000b1800036504010621904101801d42c000c00d030507005080c180540c0b64446603400298040c6021103800d0014803209484904540c040b400e400c3c9000d20000c0c84030f0740030420501501a9404207586e1038070f100b5040740c0c4140161811944500f400c1c0040091852480440c00002101015100203201c8a20a010144c108072a011196042001c00841e0254288590355002030301410316411414580c0303000f01a40124080146244601d4500702e05542d90001c1e40101800403070002e000c04601807400764007030300782040300c0741d40707484a214211001d21700030003030320300d0200740d0342e9007606181c4440040a40c0500142c0020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 826622455 1250 826621205 826621223
    0x10609060509220804150810030b01181506080a1407050a1107050a080d0915020d0e030109021914090103080928320307060f0e09040b0f0c1c09 63
    0x80001380106010b000108008411041a1107a0130409841c44200400d1585148c0441006100041b000c4980b1130554004000c1142c070116440043d4000700582440b11790b01e94041000061079551103500c3c0303807281070046014800400003a03560f03d1100da003500d02c000802e5041c8850880140315041c0c2401e10002e14041340c02e5269110b02045021101d40c01c0b800317950b00b150080c14811500700c0403180c0100914520409a000e04040080d200d89801c0e400404100c0d07503040e01002035509400122f4110b030000c04041c0c1d26594621200681039081c0314010001c01e803640d41c856546000c01c0b5190481e0b4001c5501403814403c202040401c81030014800411001e031070083d4030340820140750a001d004d0010001250344c8080b400c00304004902a801d42d24001140d401c200c0d00d40700860808101d1303009042c010200c2085400603148030320007241103604000c807001000103002c40180024003800c1d918003031000c070b511030110020f02489629413205018460a00e190300d496a25400680664011f01e160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 826623705 1250 826622455 826622521
    0x1b09090b010c29060a1a0a2d020d0203040f030605060d170a081303170c0c0111070b090a02150a091a13061803170c07080609010609060509 61
    0x1c101d0300403038200c120100803034840581c0b0034924040c480c1900030104481c800341841c074210f46034903406d03200c028000c5030715404640c0c54803d03806562407504000d41c22101d2010b80c5500d001c010320302840d0035021001071085d40c5010b5402c0d4000300840d41620b86c00c010b40f00b00b003400d5454550142501409064110303144005031000b10b0b036500700f128116138200c40c02507907544540500400b5171001030240b00321403001c052030f2800250052041c2c50112807845140543ea5504030140000d40a070403032aa1241d402e00c0c01900010f1000700003050040d00c40c00c0703002d0443d02c440104540c2e464800e20000c0d008410112400f88403003a0001406002c500c5240c03250076507485800644056502600c1660061008641402a4041c0c0c14107000038040701c0c904024104030300c005c0c5c1002c507010341c40b016100080801c84840c10402c05d904031031611002c207088541003940c65184a60342c0104a404242d954a0500301145105080c007990781260402410f1104036140c14560110b110b0781200700d0351a1003120b03000e03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 826624955 1250 826623705 826623713
    0x91207050a030305060a0f120f050607020c09010f0f0611070b18120a0305090f010c020a2d050f040b04020d051906240e032b031b09090b010c 62
    0x4011462080020340034050a600d030103030a8900250009114081e086c0082c05001503000c2441c04442e0341078034150040a00b800c2c40b6200f47c0c0d0700c1a025056014070020440300303580014580301c60040907148030215030780e96921240700c80141d01035500e443c00d04480420000e4407a82c00321030500300400903180d44554030205009164408040c4025410244005d80400c0c03800c4803400e071008000d00041e1550000c1564010418401c18030b01c079200e040f1503031890007140d20402c2e02d03508090b800742092800c0c0c1e0300d81401c2e08803104809140d10039007841c040035040401640100c202200d0000d401c030f03000030703220104000181c4208101c40b90403903820f024900e0b4488650056034000e00c0d036046807226101e0601e04200c103940c40c0340c02041c6c010030724030440500e850100a18094054a61074094411809040080e041c01070100c603242d07542080818003940b141c0740190040d09408151410001001141030011044081d0701d00c1c00e01107040350741c041011103030b02d0b008030381c4a07007051400303091001c40307995 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 826626205 1250 826624955 826624957
    0x182702060d1a0a0603022118030409020c0c010216230d03030b0406060c02010504210b0f061905090a0c0311070609060b0409210203090a09090b0708090d03050912 71
    0x59120b11840072030b540422400c2001000d40a082c0c0307031405601d0708100381400d40e59600079038001c019030481c80c40003031188401c6160311883c0d0141c6a05130b983e02d686c4d942000f4043c0d00243d50787e45450084c0c1590042940c000200001c070341a00740c0b10300300202d1a204080744205146001130038810034620702103d41d590360f454415078080c8a03840020310320756003070140001c407041c0d07800903000c1c00903403450440540c0e08102504e08845c016003108044d00c600c41a8400603071403403c0010710014104090121141800080c00e2140c0d0041c0c440c1c005106c4180c8202103155818420f0580011b2108007058070080c05420000000e03181e41004610034a400b103c2c1e51b9160b102c00819142d080d940c19109041011900958255100481e4103000121007a00c898030308141c20901d80103204c1c102d0501d031400e540284141c0b582c0b501d00404081480e035803001e10354050840c6200444011511000160b540d500403d80e050041900c0e80003020320340c0030000107500030000a00300100310703c1812070080c0802c0ca910 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 826627455 1250 826626205 826626221
    0x12020105090d2418061e29010503071b03090e09010603051b15180901180c142b09060204151e08130b040606182702060d 53
    0x20f4403039043e2036110b01c104103182a450140e20485040070300b07560503840d03000f0010424503009000081d514240f0074030084507900ca15140c00d1150305140c141c189030040e294500032403404000e55284c0115008004407450311044885002240d442c00794040f88400c0d1852608e170f024801e007070600740d054548280345604032040741c0c0380c400d0303a440781401e104000042c003880c0044010031200e10007881480001500451008550051038200400c090142c0c2890076143e1400c5640038000c668156124018080d6800c080c03041001e2080c1007420f000c00c4d0034800c02c01ca141c50201c1501070f07401c0c2038000301717003285c10000e00103200f0b01c03162811402d000881d1144694055140721b100300690396860208450006c01400c1907400c02d0001c01c08141030120750001c0100d86542d01440d246080344c0d0380b072300e245004011459001d444440f103001044100f1481c0e6108100b52601048030f0f40b042082400300c08103880c4241103100c981b6400c100304500043d9101284100c103440102541d0400070002c900702d0440c0d22072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 826628705 1250 826627455 826627463
    0xf080108030f0d0b130f060602070b1b1005130b070e0906090712020f1b0d08010e0714130515090307030b060d120e150325031b0c0b0c0a02060112020105090d 69
    0x920b2001d40c60346c4103105034001450280060031130589006019195030280c19050310078a400070a030564482401e100805801c00d072101c0800241c1050b0040d01c03074442c2c844008031140310781840402c001c90b000d040d90b58000c00e00101203103010f5841200348140c00c00d000e4142814889000003114181446001070902800310b1400700b078848000d4540d401d10ba110110032400d40741c11282c00020116032041c0c91905541c004075294090391540441116029840b40a00c05603907004201c840c3c00a01010180f0115201264880031200d17040702504400d101d034900d5140d2583c44100c040000547d50807682c0e900800052401011074620b40300c8145221105051000043d01c7c805a000700d07207440342c40f03885151600c444150951402500c2c801c007901c1d0b20340301107501c14450f4140d500312611030313004408512460010310031409080c0f03c0c09000c008030150201c441d4440240010740c00c2d1a41030660741000e40f164020300d9580d29210b451000c1200c20001681046010031101c0110345038031362001465481 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 826629955 1250 826628705 826628711
    0x12090b0703080f0f0c030f100f0b1c06050d141501080d0801060212121003020a0f051c12120204050301061502011506080c0a0521070f080108030f0d0b13 67
    0x10565070b000f0f0010010802c1c2c400d28014405035034440819282d006c0301415602e041030700c460700d20200303810322540080311142001c40c01041c00300400c0050603800351824119000c0000845500d42542c1c0345014694022881041030800300d031400e00151140305040081d0742400f034900580325000c1400742c12032170752030340b14400c00c03158503902c03000e628010309551001c0c007070b0004c6031402d8048511500c0040310404100c0303004107802642c06403054006540c0205000503042d558641180d82c00981c2c4a20351080c50540141104081d118802922031030b40420b418000944000317045d14054210400d11000590a010200b2651000d11a40b000b41000d071030322041d69000c4110003400c2d1202901d000606403440d41c002c20005801c6034a064100080c0c0f03c000d5201c002400040714a07020b48035503100c4c2030000a1044a40000c0680114000d02c4a640c0d0100c19800042d000d40b4a90710070300c1000c0c9640d00c1003003460103a0000d9070140001a520a40116600c1403040000f4150030680003011b030443e60f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 826631205 1250 826629955 826629961
    0x20a03020c010603210804150903271409060904060e07151d1e013c020d023009120601061e090902160b01061107140d12090b070308 58
    0x40b003207801c0c41703140d0311850200003902d05580c178a4110f090740c03a90444d002d6100d0520380c08140c040c1100303558a114025000c10000c1c1801c03848190040503209400071138402c16150031103410008005c911805014008a40940340d51762107800502c40800412280d000300440450000c102010b40112000680d480481c115840009400e0028040e80803a01c108854064081592a140c9018804550034241404170030020785007188140d9070b00e6540b22070b078904c3c07488001b0194022901c2c070101c00c455600301c44820001c0002aa80c41c12160303040d814074031700b0707011000003a440089a00c001c1042054640e0601f10a100407802405501e807401241790400b400520403164000c00e02c00152500c0404040c408410f404094420030090045400240e0005003001403d10444813101286601a801046c40e60b503a8000800c0c803030325000082d4460044807400924000420706000d08100e004040e101c842801d603840111000101d11444288106081e00160104008020740b240d18020303255102985 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 826632455 1250 826631205 826631243
    0x10030e03030901242603090a0b0304050106080c060301030b07050d022803060f0b03100812121e0f0a0e06010602070f051c02090a150303050c0d0f0e04020a03020c010603 74
    0x1441e100304441040854580405c2510002c1100501000f010524071000c001c140d8142401e500c0340c81c05440e080358032140d000a9804112000b584103034085c100070000d464460b202c2580f604c1c03000c035100e0f6010100f030005001050000d030b5032a4000d503040c1070072860a00300c580b080086e600209075486040c00c805044180003108040309094090703007460b04000ea141415420142010240203c1607802c4010001603001803c1d403c80501030004881141d080034240c0e0000e000a030301451071209443c01c40d6012608070079191609800600300031031014150b54904014000c7d22400a1030f44c48c8c4036850f8a02e002013075005101d014003a102c0c590140c55024140b81d14095110a280c2c4414020005c44900002e0b802d80030046111196045401c2c114070303220349074102c0180490000c042c1c02100028400000c0540182c020440d4000e80002d4585480480701d064030100511180c03200426042c0c0a9909289456030061004d4005402c005040a500d48552030840b00c454004480100c000c3c84101524 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 826633705 1250 826632455 826632491
    0xe0d050c0c0901050102031e07020604030503090a0f080d08072708070e040c1202030a06050a0c110109030e09130b0f0916061413030b1e01060203090f10030e03030901 73
    0x1800d40b04024107500d0003000075500d00c07442c1482c050065422142000c81804a000c44901a070002c0c2201d845503200c3c10700c0d82c0c41c0d0703004800716403180402d00c2000528142d4407031280121094040540000411f980c8242c0c0c046000418603401c002c1000404100115050b0a0402000d145040341c81d05504002d4911700c0d10700e50360071002280c0149401c010000784201c00032010355000441d03001a210191002c00e103400402c3e64002c0115080400f041380a00700c1c1da10454081c1400d40e0760384082c0c1146200d00b0300322004004040d0004482d449a0f11450600e07141d1181c1240d0041140c1400b100a9201e001c1c000710f0175a0100e52400a000610980e82401c2241031528410306140e00a080d28054000d0003450248030180c0110502054288404120000e510005c40c4c01c00502642351a10580c003002d107250300c25a00d034200300e450002141071407002055a2003600054403501030350302c5041c00c0009010840700c0300400c2607203882c0740c084072031018005140990784401c00401e0031517100341d64902d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 826634955 1250 826633705 826633723
    0x1a1906090e0a060b01050405060414031b010f1d04090320060106170a092a080d021b030a023a02060d0e0c0405100303021204270e0d050c 60
    0x42400c00500395071001d40401c2c02107207140e0181d800500064080d00503511406240d1000b580300301c0104001407030580420001c001d0007011801c4c0c440350b0655000012207804008a8240069400e400c052078085c01901400c614070312005524040341c4010f00020103548419900720000340b02160041d190040044110074803070b450300094501c40d030502500401c001800c1a04052aa058501040d09101241d0002d10083e8000e02c0b0001c0c20001c0360040c1c2c008604180800c2d08414030742d8800141c00b900820002030b01c0c0b00550251118041d4607081d10049074040c0f03006030b0300d4010880090010b0703071078051300c58102c0010070081e1400c1d40310300e14840303184142200c1d954800d145500500016601c3d8400c0b248030b1000d5900001e43c8040e45000c0c10b00e000700700c1447e142c000c0e00e40000d200d9241801481707070044030f103c5c2d82142d000b845090181c14042c003540c42142e280c4848280104a0005150500410f5000a200010b42c10032822000303072400188071404c10201d40009101c0320241e50a01003010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 826636205 1250 826634955 826634969
    0x2150d110306150f070204141501020105010f06030c030609020a02070e0c040b07060c0215041407091109040c021c030204140306061509010e0a0e091504050a0f1a1906 73
    0x204520b0844045403805503051441d002c05500010300002d28814a41a190314640203002045200810305096a801005039018440c0c1550030403410030540c41409014142c031710000c20f100b0600e15080741a4064042c0340ba1150616440e0000880d003d00684040e08083c80300c3e40c0107000b40e5141c24804824500080d05080b4130707103401c20051006400303480840d4201c03a0300c40340c00940e02c1c0c403105049003014101660290803044150034031040c01248070000120020040942d003010b56115601c1d41141c010401ca0072207004103004100551806130700181c00108640165990031000d9280c03411131001c4900c500780425800308050200d68a0141d000b030240b001034008010a0821000082c155089112010040c81c000903030085903034811402014800344c0a0a02104540ca802c80c01d004207400b03c0360384002e84241500e021a1009041c041400340c0d8118025181f032504546035400c040c00c44000c143d40850b0380103c12904140081c03501c0c0e20039040515101100309800382c4090654000b580198 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 826637455 1250 826636205 826636207
    0x1030b0d080a18080a0605040302100e0601030b0402010201090c0f1809020f0f1f050c06070207061b060b0d0f06051f1e050301090f120503010608010b0c070302150d11 73
    0x2074a80040320b0103040c0904100c0c0946000f540724903038010054000f80241d0003110480d10805c103250304942e00451007502510280c00f2000184011100b219a25403043d0f88030100420100f40441040b940042c018400031030410020703110089441c0407584490440312400100300001b850102900c1034000c030030241032000581d1038000442c41910008441e22545a0549003c156542c0003044042d05400785009544031681c0100540b03d9084450466624024280001d41c854030100306101551250344901021741c030249074543c4641d640c0c25048400b15a18880510a5900c523442082424421400a5405900780c500031041e100b020703085030652085029004400b81d1a031503a1019182d8903104090080503244003d415030b003290344200d03019440c0440720b50a01205245010f16980501c5040701090700302c0c003040b00c103132109100f5500090012001031001048000050843c40c03889802c039040e036074417500010369001501d400a203c1d0500041c2d89400c01c0300d00c1c000c814004416180c0d403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 826638705 1250 826637455 826637479
    0x4020f2805121f0801060915080a170d140c0703110f0d05090102340b0403030806120f0706030e150c0714150a0204180b030705092e0501030b 62
    0x2420401c0c0001c0e000f01140b40c412060b20845407102c078524001030403014000c0c4492a555954200280070804a04c81e90450b0309a011940150000715002e0996000040c4021100d84d03c0c00e034130241d0024009244015181c1c0107203100c041d80d00c09400d0082900803a500c0d1769040f41e01d8058003080041c0a50030140c1c0203c0c001c0351003120701050716603da00c0d0034104a6601c034070600040b8100941c1140a09805440c103008200c00c40810b624001c44803095014803002e25110000ea000c10301541c0300040004000e0000a030007410004003140b45111001d007200c01103007070380030710508051003038105000003907481f403452102c10410440350b0480000e5004404081c01c1a91001c10144100b500c00703003070f8500000d1100a4810204a00c07200780c0c3c1b82075030920f06030034003008007000ba601600c10038048083d20716010080880c81d10901c5d0316502d009009082e46c83ca0701782441307000b0303a00400100b144041c642d0081d43c3c40300410701c050420185443c0d00c11402d82040000740c01c070780040c45001d02400c644824 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 826639955 1250 826638705 826638727
    0x1030305190f0e061c1a010905120d05090402070f0b0406050114010210110408030a180905060d0605040201030612082205060301030303110423040605060309190204020f2805 76
    0xc00140a0004c0e07030602d40d203401503160002d40340315403400102e01070f2900030341e05200b9801e009240e1803000e09907210003440c3d954008000540b6102d1091050395000f014035100581e008070700070001c4120103000581031840503292001d6485c84400255021b09400f800c201c1000814402c1c103002d41819006603480b4100c2c140000c0d40c2e21243c141c86a000b55946804003403120180d010b440080092100b00c9903203081210008200088190307403003240b00c54620002c03840307004c54042c075441290060468800301c2c000351a4000a000054030603418590f0341d0748089617030741d211005034000901401c80599120300c1000c58442140740c0c4c00c0380c00320b000a040c03410b0081c2d5950340c0c120b0341102d82616000c5109503140d0007452940c070560388000000580d416043c0d0b04002d56802c40c0208803c00c80d02007201aa45c5c100f0301030700707100440300780f03180c0d0700709008032a01c0c0121503441c441802d002400041c00c101104409492913404400d83e003809a20016145041c1e040d007040c802211121840d1103418a1140d0030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 826641205 1250 826639955 826639967
    0x30201050309100501080a0b0a11071218091d06040305091e18010e130c06120605041a13020a0207054c090b03040f0201050c010501030305190f 63
    0xa0411600101040368204104101d611052031001c00300110750391043c0640e540c4100c034000310303122251031002a07048100352281d040c20741c2a408109103070000c2c5545043c00000100c00e0f50044c0451000400d03960700c2c0c0316442001408400d14001400a070300f80c1d092015802d100401881ca1f4046820800020344c0310054440383d100a4800d40380c5d240060b486581e547c940081c1c140d0f003100c0408100c5007001c101680d03290403a00a02e0b6207042c1521950184916000da403034000d04503a5400d402048024880c0c50034202074240200c0001e081a00c2c5c070000b0b0141c6040c0700b00c4440b036014001d1901c00c81e1074206950007466414107002c40c50515005800f03502e607685485918850440d1003080d50110400018080c0c20001d41e4040e0900801c43c00860310b405502001f0380f684c503040f520f050080f550301603001c500c25a10700381c600b1411552640d17508540c015401c00100d0400034240241c40582c08240070702c0340038620a486498442480c05018146a082e82c800d0204000010360702114040d0031071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 826642455 1250 826641205 826641209
    0x1701080a030c0203030f031608070309170f090a1e0509070e0402030606040e0709030c06170f09030705100b0312090609100e0d030917012003101703070201031113 71
    0x104100b90034008500009080d80160108a4000d800000802a090310340d440c0d808841e06803511860f2403900e8650013107013110010382009241000c0620a80590404400a00081051850b000345000c81c00c4000c02d00c42d426a80c0040340380b40890103540314655064000c9030140405842c030440d0340c40c080800500d00030110681e00e00450303000000c40c03015102c180c2202c0181c454400c4480040c01c180100031700074040d03440140d40860444001280e80b5116940d205142c0c525410100074645601d00100014180501002924882009040002074040c8050218030105410008014402c2c001341810012107051407054820108100c500070b0f03441c04207898500720300395000441620705035410b8940781000700d1070552140100c0380c2ca004255201c16450280c0700c5e064000c4448408440c0c1807170980b031150b05103000e8100050104800d00b0603a0002d5070740884200b5136a20165a14010b03211040d0b01c02d4006030464100040000a550301402466011480007801c24030300b44101c0c1104186403228 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 826643705 1250 826642455 826642457
    0x20307020a06090201230c21090424230d150c030b06030a020a030f0e061b040b0d0204060e030a03050301090f140702030703020607081005060a2d1701080a03 69
    0x140800800e40e480b4059903180b502c4905400481000c1b011500d00c80c40d04454029803503440f0f03c0c008043c2c1c0f041071036100d503d91945001c210342000444810800a800644001040464050100c0d8103064240b502c00f8014546074180059803c9000ba0b18640c1100350303490b4502580320f4424060000700c141c4005041d0705103418000404d4040901c0490280c18120b80f15a40000040240302181050303600074040c4081c191010013035612019003a0080c0c4104074000816034000000003185c18251400c0500300d40c10300c0240340c1c0740544a47c05c15010703400c181d2281c05801c0e40860b00380310850304000b207150794000403070003003030000380c1540e000b00039120500a91003c0f030384a0140ea40e113910590090b06441502c11278030113040c60b1001000303607260445c18080e4014498903010403422400386080501510003c40078486403810b08050100303590102030204c080100c102c51048460004004c810502007802c00403580d6800305c260002e0448207511605070780504044010090180e0000e080c14000e541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 826644955 1250 826643705 826643711
    0x150c02060703170a0f15030c0509100e0901060302040b03210a180306330608040305090405090106080c060406091a04081501050411090603041520120a020307020a06 72
    0x420710b0110740d44584070590908011982c424403103010b909800ca01c40c60200200304218941d40000030820030521444042e080c05000e0601340282c0c203001c0c011a034171900d45030950005540d0b8040a12609000302c60001803650b45000900443c5468000c81d2020300c1d0480007030004510402c030b52240c0b00015888190340c00340c005154140302d40201e907503001c2000e036124049900b50307032410540003806d505501c5112210284209603555204100d082d07178041c00d2600100b121a083c503405503049440070b4026030a01c40207001c00d1007036075514040c1520600d02d040002c1106482c041516183c84001060389102d020244414460180d100000c0710444200c20746904a520301244504c1c018816500901ea007405004c00911004110b4618603040744d2040c0c40800040001c51090340715400742c8588207900030410070110780071800c4400c4140740e40c00d02c83c90000f0f044805050a0900e89840310790101e602002140f5002d5035216604141c0c0d01200341d200a51661825000c02900d901c40300b00000c00c03040d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 826646205 1250 826644955 826644967
    0x10807020c0d0812010b030c04140102070f03110f0402090f0f0a05040623060f0406080403030b06040f06081f0b0a111209040b0a0f051309050304060c0c150c0206 71
    0x32080040740d11140e0003802054105025090440d010303409080600003034a01070000040d0900c0c1c01d41202e11a400c0c404041d41420305001046c5003101c00113501c1411131040301008100581d001540700700952046400e001070700da040c42446040c500b4100018404c610610007080b0310340b41c041d014401901c04072004100301e02c205000440d03000680d000633406c03a1415801103180c40d010700b21010100c040c400070656107140b40040240f1845150750304807118000740410030006028500194019120707040c082440c0400d4404515983c0059100030b40040500204101c5581c000f03039046d41000032031500740d080103108003a5002041a500c5090700e22100062071600c3d0b00c0c41101040380a194075002d40f40c05190410301d40c07160740c01ca0a44c2500c070314506200395282d0301d05003400c3d100319501071706c045807014981000c02c2482324059410b078848a8550001000003002400200054220713622254004500c0b4203125030f00407071607002094050040c141100001d030300451040785203507040320790a03a146 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 826647455 1250 826646205 826646207
    0x503011403010f1d060f010305120901030e0d081902130b0a05190e0a270f0608010608010609052a0a030e010c11011b08040f0c05090c0706050711030306010807 70
    0x1411203548030060300c4c003da4200d624040c0001552014103da00710385d0385071214100c03602110800c2c80300500c268450760710a10b05000c048040c01f2411014100010341480e800704440c02d00004400303100015080008025510881451130040310078003040840c2480180d200020980304140a0307034200c40030108007001090710407003c89441894001d69a034558200c0741d0040c2c104c92050000ca849a11110000b007203000400c1404001e03501d02c50110255014160001d20060005c01500101c00b5252503010500182c00d004841c000c100c80b2000045581c1742480e0f0340202c420241090000300030b11000b903c5910500890360900c8140b17a0141c66907280c100400b98010b05084a0210b45542030580f090b44403500240c02c2910000da040c000d002004036403488082ca4118003441a020404010100f00840c0d0030712000031036280b044004104003500c0c0c800140b40084101c0b02e40b40c08200000d089000c001440c05001d40004050a08402c581d503070b000c0079503c900000f000c840c100001070000460311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 826648705 1250 826647455 826647461
    0x60207020a0306020306030105010e1314030408150f0601090b040902090d0210050c1c0c0b13061b020c03010c050a0507170a0e180103081c15140111010c050301140301 73
    0x580d0090111001d56503a1a10741c01030740045a0103482946404000980c1c03643c040d0708540b044d01100c0101201d03040c03039600d140c203001842c0d84080e503e11080c4400700d008203041007440c090414082c400c070811b03e842040e180d82860010001307410811881010003074092040305030342c1604c3d0488800750315402c424000c540803d460030400303580b02001c03031895492290080000e00d071000c200c900741c5482c02c0d003810010790701c2482c000000d000140c004600501285884c024241c0040c1c0d40703018000d13a01c00030340701c0314240e55032046180a090003900c0c100082a404100414040e00250000d000600324004041c025003c4c0160260500a0000310507007000707150340d040d41110230750880c20794a400300382000514624403a034040703001d20004805161204904d0118604a0f5841480e961400d20807101840c0c0d118400841071a1345920740c0c03c00d1941c0c041842c01c02001c1c100360300050300c0c0c0b40d4500000420000d8004000d01c11645025400901c4c564080c04584c10740703641c10002c00c2d01c202c03680040381c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 826649955 1250 826648705 826648717
    0x171306140402010e0a05100e130c020f0f0622030c20041a13091a0408030402090a0b0d080c070905271c08060f101112070f0f0602 57
    0x8228603016034800940240954140118001e907190340d0340000c440140240c8a80d580a090f07840b03213501c5005007800e441a000107070540c8026000c5801d03440c0c0300e802e19050704c590303158020160304144510b4202060400181c50f129408000030304403814034009078a684403002512020000700040d8010034180a07004051449510240e8184090501c440c050700030040720306040d100324101071902c0c001e44003c4c0000192402c00400019240d8003030300b281c200070a94040c003200c401c5145100240401401e100e65442540220380980da28600b83c8100609540c00524407003809262039601001e58070369040e0000c0c920f501000c85e581d12500032107003601d090083e50040280601f42820001501c2d0045e0314a00500e0304580da03c0052015074035450745444007030045240c00404c0351844c1014074070034003205400c850081c0030f0740020310a240104004074126554800441d0041d05c100b5101d00e82080000c1100c10000d20389400c1074040c1e43c07007083c07041c0c0b031000107829104520902d00600c1000c3c2c0c11140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 826651205 1250 826649955 826649963
    0x8040206070209040308071d01090b070215040303030902211c031d072103050a1427010801090b0607020402030a020424030609022a0f01050c070b161713 67
    0x40a4a814580107004000403109000000c6204250030304e04081c003c51303010100416110303410072b9401c0440140c5180c12034117041ea4481c0068080d1000006064000c10145009640100e01d01c01540144650030041d541080071300000500f0580c03c0a201040d0020341913203004003a94069003c0c80d08230042c110402080d465017015041c800e140b5600000d485045402e104842c0c14280701c180720014040c10080000f07404070720308104060340c0c00d01c81c0400013000305a076007500313040c5025458102070b09100c1a620800d1902050f010f12119038003c0e007090b00500c0060000d02040d110000407804900401c1002801182c011010490701200c1b40c06031005041c000c80c40c407003062045109000c10360503c0c0818030201c3c2c0307440800b0480030740d9402140c481c03050b0740c410b000c030240c5111710780c4842c001210500303e001d0055030b4600c1c0303a1000070b0046901913000d0900c00f40c1c0350b000d1814044a4098050b16a10042851511701d5418981240555410306540b448043c42c40e80c400380e44809612031190010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 826652455 1250 826651205 826651219
    0x3040f061d0f070326030c03130c03031706090408090f01020a0b0405240105010903080904090213020c070f260a08030709180b0a09020a0201090213061505130501080402060702 77
    0xd0b4441c000600507044902a8003145003210020105015802c2240803c03410321004100054080040b640210b402000640982801280e1a10f030101d040100750001c8000402d400d51708000341c440720800c1c2d6040001203a050b0510309187d561284648203a000742400f801d201012011540e0090010b6400e840c3c2022142d03500f4505032601a4031080505c41c2c180809008419007150740e502020064103880b0180c5401502e0b40c1140c5805d40140c01c0801c01c903901a484520607401a1507045840745001440c06016840354a01007000e400c0c0251900420661501d0100801100c038035404091414080038512100055a590b08142800c84104026001000c00014404d2855003c10100101c59030a88802c1800c84c04c5200303001900c0d1140b46441d8486103880d010b00048049500070840003540c0d000015951b0410703030100d0a040b00117440450300c140d80355020030100300c5011030980a810146001842e05000c5d1400710b20011480c042c1c10b0402c43c0c500d0008045498100403140111303001007140d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 826653705 1250 826652455 826652473
    0x40305010e0d0212131422050403031107050c0607080c0604050d020c010306290c070f0302041b0c0f0507030204020d0f0b010503070906081902120108060c03040f061d 73
    0x42e0385001450041c801132140c50001d9510452090a8034822107003401c0403586140b801c440104910001903055034081c40100c5610000c40c001488502c0350303e000d01d4045001d180900b4042d04455003525030000060041080340300107800800c0c0700d00007460480c0c0c016103851845c14038281c1402210340d40503840c407a00042c0000e00c4000580f0390780d60b00e11a400c0300c04c04000c0700011001d941c4940b0500b5550350740d0443c0120038400040550f110b0210882c80b0710704090310030100514211260b400485140c5682c1d0041c002d5082034000d518240c5411208ac448850f48280d004040429002c00134150002056064081000601c8280010b40d001002591100300c068003030f000a01568040c1c66955151501d0b11010354000c41c1a28880c004070b49403111407914100050790480304c000c0c03041d44000c1c410321142e000c0041600c0641104511140083d9043d0304108a4501c0c1c0749014002c1a14041e0510030080010349598100c1160b07a4001d00c0819090070781020030492801c00c2c03031070701e25070f010320504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 826654955 1250 826653705 826653731
    0x1b21020a120513080304080a0e03061009061508060607060e0102040b0c16140415030807081309090c062106080f0d0c11010807090314011b051602010e0604030501 71
    0x2080d1112041c2a04000945407000000e4071241010740041c920601031000a002c5010500601840e03c00d6003484030009502000003800e01c0e4080310518000721401c00b01740300199192103220044d061169500f07070401044040904540390051000780314400018032882000610717003000c2100b65401c0f0017991aa81c40d05841682074021800043c03c620895400d100366020100f10780c0c0441c0e407408402c0000c01201d0741400041d1000801c04000d80403500000000561f80500a205147c098214551140401d480a4640700020351241c4402401c2400003808202c01c16a044100c81e8a8101003d107008048070300000d50115030000c00d00c152a00c48006078551700801d441e00c00d285104207071b075510340f0400400e50321945403000140180f071340c551043c0c1095003c0d00301c4582008a034188801c5c4180d503a601d008052603440310345141a515407020415960a0460075403801e030142c07c0190814a007100602e44411000340c0180c10001c07401c582d0046034a403c0304540c059030704400240a01d11503a41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 826656205 1250 826654955 826654967
    0x3030a09060b011b0b0a020c060c030612070b04060c240e0d0906050f090616030509031b0102031c060f060206060a05040e070303030509031201091e1b21020a 69
    0x2569007904080104455610030f103800e0001070380802d103496480844c2d40311081600d80060161000581c20040c2c0d001140080160a02c030724103d449c840d90768078082c02030002c1e03140c07411b0000c0c03074941c0005014455180140c1c1a941580d20b0ba117028002002c803800c040d03c52258000034142c8149003100c1c0c0700581c10890b0456010319080100712402100350203400c580701c1000344683e2000a00500442c4e428200410040962801c000e00403400c0c0f0402c030221807a02c006403802140172650004441010742410b1010a80e21b2500c0380e100d5448900480010351244940c1c037005441c880d10b28510705e0380c60f507642d12a5002e000800c0444040a44070380700690303500402d5401038030030011100009000c0c6054001e400f40f07101c0380c0c005481040c3c0703166016400b03000c0182119006000c00e0100e111000300c2078003070900802490f5004154006146265600003058854416405040c40c62048074800080100080400246040c0c045840c2c40c4101404100c40201100b80d4640005a0500d06640c03180c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 826657455 1250 826656205 826656221
    0x1608070204140603030409240e010806130f03080423030d1d0c0909030708030a0605011116060c020607050706021c020109020d03030b060c0105070306080f0105090c0f030f03030a 78
    0x91410404100c000080040040040714081c1c0d055108000034405001c9513004241d120326591300b50040f02540851036074254080b60811840c04140000401c202f01040044640045c84e91041c4001c00c01181c440c101a0464180f002d0284030944004c1001c10840c100903429203850145c0c101801e071500d4199a840750b0080e410903078403909002c90703d400140f941a8800300110200010a0017482031400d101502e000245280020300040c060300740850241c8004500c070380711070480081c40b1030400303002402d05804071110f46007a038881c8102594070b64030040c081095429904000c00c0300d40c040c0c0b0001d001c920070000000c060740103a4400040307840c1c0002c0c03175407002c00420b41d80100003980042e04034200c51031080040d40c07240c0f4a405410129009511030283c00d1400fa0000e868698121115400d45000792038201c0000e6458404000245003404111801c001c228002c2c040c50520449103503640700107074040e5110707161422187c1c04507902003100182010350001a03945a142900d8000010f00c003070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 826658705 1250 826657455 826657459
    0x131103062407121202041d130c030b060d0f1109130b161e0c03021002090a0b090f0306010807061803051005040c080f07050a0906060c03080c16080702 66
    0x9881c681c000c0100a80310040c00041010010309000881d03d03500b0454503403064500030712030103007402c44441c030003400107202500c00104075103980341c25580c81240d424070080400c061032024503c0030001890042807032088a400181d107440300e450320760018054036000d200c000e001d003900c04070100c20403020240250460404503054641a61a003c040c60072080348a40144074640d02d02c00118071010210301050043c03910f2405014075140386400c20b440c5036140c1510004200981c40c4201007660411250346d00100c0742d1001c2d414001c80502194000c6035070700a031030b8400c2c408204040c3d02d80f00d801b08206400001005c844071560340da100c0308e844141c1c0780503900000e0f004030012601009003000020440c0c0d8804000d11710022040035100051002500407a5524094040098141d0041000340706000714440075180c00e034a40401c100c0d10440c1e0340e0042560600f0103008005090700500b805a0240c4c050500c07000300d55031050300762807038460040c8030400ea0b0341d10104901400203401c05042080d1003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 826659955 1250 826658705 826658719
    0x603010b0103450602120c13030305160f080a03050a02071a07020705040c030c0915141c0911010f030b1c0c090e0303101512020913110306 61
    0x341100441c2074a0030321406402e00394032080302c80101d1030704124010351880403004446540c00b50084609005400340300a556081d00802c86010a40c0d48001e46034111040f400510704e0060080407600216101d40320180038480c01040000c0d0041c1c80d0303180c0e000a6680a09000c1c0b0012492800e004241c000500d1800081c0c98503000a14410061003110312075900502c2d5021405030080464000c3d00c0001e0201c02103000c0c01d07500007056100d900074a4400e40c03031074402013020001c011004246c58541d0384404c800c800000c0031041d0341d81d00b02d600c20b00a403424020060ba0b5428059905900d41182c001011342d003454182c00380c080c06070207505401048000da842d10003611404078201c0c1910715519038258000c0307841e00015021604800f4440302184070b411a012041e0340ca807049022190b030301000d004203403c00010401e869a2900f920b1000d406052040701e50460007a100602982409001d80c1443c0c1d030015020140355580da50104002c0560242404140c180300720004480d0030580d111400303108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 826661205 1250 826659955 826659971
    0x3030906081b0306030f06190b0f280b1204030e0d051f0b06070506040c05060309120306120616080a0b03060a1d1e0706081501030902010302041508060301 68
    0x1100714049401086001640c0c000c54800e0265070031a507001605441c0e0510a000c44a998070000703108040c4250021513240500a401c00030f200c040d9040042040e10a5481e03e00815080e80c641e940d104803625404810848504006042d07140004540c001a604001c0400d20710b001d8844004618891071013076032941801c01001040c420700700d0304030600800c00e410200030b5140340460840402480f0040c2580802c40e20081030205403103500001c015102508910300700310a100104032010300a080a03a0101d2851601c40c5955444214145842c11407540010203e5000d03a0f510701215541c04808081e81e009051000244282d00c4c1c1413003401022038020000201c02c0000b40c1314040381c41c40d020300a09034641e83c3d90904001884c031a00b042c00444007070a0300c40200a010030002c00d041340f1003075150b203000e000d10142070314142440c0c0c05141003080040410960611700c1c58140a800c03020301340480e82c44160710040e0007030f008903000150102014181d025459038001d006c9070080400b6002004040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 826662455 1250 826661205 826661207
    0x62e0f090c1d012a081206010c0804120203071d06090c190c1b15080c04210218090127020108040b130c090515030c031f11070c03030906 60
    0x2454000c2c0b5050300300e00701104007030756500940188041003503042d00c108240c00700b44510300030740c982c1c00c0082e21a000045440480b000114482c15040242400c0c03c4c036aa00c0d969507070b200540b203240607004842840300001070449d182040560050031028001d20000030003e8521582507104540440c81881550042403c080d032400c112012003207442203001d1011000801031310107528100c4102c50b04e46180c0c0d401c8039141800362103a40900700c41c1c03407407070380d03800400c00005d00008010b8402c00e1811010003003003040c01d9601c00c0c3d040c030b01603801d645d40c001c50100740001207500e00b00a000740d10222000040010500042d80f10742d015030400c0c1055181488541d1700e20b506002c020708000c0c049504540841c0215000c2801c250340283c22040074240081169200909540c0a034405070721151900c080c407414060108022441007401e80c0185560070300c440000ea540c0380e040c2004541150030898404010500d604001107540a0854243e41c1e8481031400e032100050900c0190002855504046002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 826663705 1250 826662455 826662467
    0x3070e01031a0102030406180915031a151002011506081b03010305070b0304151406010305012103081801090503040f0e0708060118090c080414010e062e0f090c 70
    0x10b01c01a0b00071410f10b07080c8801511104885409407880e0b2181c80d100141c81c8072107000c3c1801181c410070100c00e806145140c0240a03040e40c030818103403034005d0f00420140e41341e404001c04031000c01300d4000e8a1203a0001050f1b0041c88100c500e8600346c49010360119151780c000c040c080c0503540b5404200c1c41c3c4078129101d044140402e000040080d00b110304208440340d4900f000c1c5800c11f02410341140007401c040350483c00c9405462031810400066010481c0c0c81d03806100c1c1d68010b102c03110b003901002c0c4082c03400304030341415441d00505020030140811084d0882e00c0e06001c14070802c400800041b041824400d40d2034010b80710300d2019450b0f4200108046090713020a501a00154503803150a0700e8010065a81c10500f00d030302c010b0440ea14200181d000030764080e4000b10001500e40030210704081c1010380b06140a00c040c0705051b8140700301c0c1000c4140028040e17034021050141c10144440201103c415081340b0b41d03060350300701c030048000724848460321118070455135211400c00110341088401d690b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 826664955 1250 826663705 826663751
    0x9050a0507021c200c0a03050609010615051c0e0102041215020405010c1202100c0f030b0301020901050913020d0e0d020c150a050d0f0f1d0106051516020603070e0103 73
    0x6040500c4400e402c04d02c07038070b40e0040c07440d5010a0307a510a1842000c22248200c991080c4c45961105061104015080c0b0661000e0a19040086403940305604094080d100d01001d80611440b44501d02daa05006035203c07401e00140c4000940d03580703541e50564034030350a082a0035920a007000b16503820742c180d079200312002c441043e120507242104640b01d81c0c0344040c0010b803250079130140e42c0c04220500f0fa14440c601c01658203841d00f0021031304030040201118090b148450080e0720400000080d0781e0031000b80c1d107604e60100c45404074624011001000380c0900110b8070001403c010a07094008008192500380802c5982150020705040081011101c48654030700b20484080000c4448984108000c02c82000c0804002c80d504c0034851299046544e24107907109402e540e15030721255982540403124408944e82e0007071004a00304400a00311448100c982046954001a9840d0300038502588103d00b0b60010103554591400720000360901c065030742200e00080c5804041268070058051070f00c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 826666205 1250 826664955 826664957
    0x7050c061207120212180c0103060608011503110a0903021e0a0902160c0b0910030209060412030210020f0d0e0a0b0610090302060403050a05070509010815040c09050a0507021c 77
    0x103464803160340c03d48a181d2440d81180540e90200b010003c0d03000390070034203401442180b00c1d0500b0340c0c00205403207042000109109041500f0b2040c01c0141e15405107440c0d040d2010744101c1c0507000b200d04030a80041c1800d241e80380c94071030041100c80845801800c40000c50703000351440f10031361404c8010741d04414034480304981d1218541000303001c80d81d03ea5014018069150310f0110054815407188403280c44180d1118500201c0040d41d2505428042c13680f11800c600c908096050400300b0001500600075401032241c50164103017017405140c400c0003e8510b030541c0b1402150360f50100e0303545944681c00400d2240b01c16080607804500782e01d001806000194100104050503160741080003100e00540a22800300506002d000c40587d50b04002080294406c5008111180440c60442e06040d460350140e0321454054004001c404808200c04a05103200300c2c5031212662a854001807903003450300104038071460002000314140150b44594091542c0c3c0d000c45803a52042203410820080461002e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 826667455 1250 826666205 826666237
    0x3030717121807090f1d010c0e0d1a130c30080703230409020c011a2101110304080a09050915360a11040308030403110f070b07050c06 59
    0x200300b07201340c0d00001117840c40440105140d411915031a440a0052980002503592180314a01080c4c101c0f40095900720705603030a000074100340e11400310b01a1030804601a00d0030b460000b40c08100a2804004041e0340030b0a0142e03000d84400585012400e02c1d0062261182140da41030503101035010590035441e03001d00c1003807615005e17580031503840716100703401c0c212400300012005441043c0000b40025101e00400180c03100018810326003910010301c00920580303100c1403081e4140d122186085400506400c13440e104890b0162054014651401094115070f004000c0c001000b101c00c00822841c00c0a84d2002161511001040b48080d81980d400c3e00c41490038100142d1414508080a009054918100d18078240f9900000850031414242014420040204030242c05a0b205000191600c031540500b060300356540c083c0b0714400a8809000d000320f1580344150203100308100d0580e10701c51400d49003110395400c803050807500040d334200ca482c06285424001d5040010903500d150400c10a02c0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 826668705 1250 826667455 826667459
    0x207050a140613030203030d0f060506071101140903011a040c08012702070b010e040b070807080a02070227011508060604030609050a0f050604060c0c0506070e03030717121807 77
    0x20b0507034080c412100610342c04560000250b03070240050305000e24400404201d00320310b0052241290066000a44581c20074407540c004907070002c032a00c40f245420300380220302d240741c0c02c003500082c02841405a459070030892604900194200078188150081d0b9061000c3d40c03040c03509031030b148002d0261501705c20015102d0a01c00400f0001d64584a1161900602d00856621500d40c803501c00d030411600c208e8100140030400100b1015660700541615080e415801d000343c0c0140f404001604001000e030300400c024096680e0481e02060001e1602c0d080c041d42c1e0805c8007404d03560502403090007458003440d070301c000c2c5076402940c100d8845c0c81c00802003490035003940d071220020055070f507094038544580c4481d90000340741002914951402403005241c0d6140602e08402960a40b2080608000d9401d0303d0400140b40058000d41040081c10101201580c03000070034a0f5005030100a003203015284440c0910041c00300c000c24a04032610480095275640a10081032071200c004640c60f550710030401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 826669955 1250 826668705 826668709
    0x30109380108095115030312040b06220b0f01021504140312040c0f050411090d0503211b03040804091107081209060709140d061b0f0207050a14 63
    0x1540d20380700700800b9003000141c01e50803661803080c0355048015841c4c190100380090301c5408540c0120194080300154605080081c9046890a010708010300c070b40362005c08513410741d4030740c0d02202c3c0f4580b04100031080070f100741140d1005407200c0131034a40201a101e4244400b940b003ca0701e82315806260400c5181a00da5036036406200d502d103501e41203140400c1c00620032400d2402c520710701170382c040d02d000085c1908103452010000026030140744203929001c5070105400c8800300307540080da821a01d8031200301407401c08500354484c3c160001240725030400f408140021400309a07000d54001120503040a502803010125848240d80261010300280800c110700c0c0c00941016407038210a401060811080d40c1d210b14207600101f1109180001b58800c10503440410810507510050b05d103810519245041c0340541c14850103042c0303a0003902c04c00520018004240c0240c2524a0100889000124a14070061001400303244103c0103006040000400c0d00e80702c011101501c0c00c1c0134078a0f640c0303215a01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 826671205 1250 826669955 826670023
    0x3050a05011a0d060f030807030f0f080103061a22050604050403140a0e1003050a050f040809040c1404091b020309100c11130203150a0b03010938010809 67
    0x5030209025110500400d80340c00c198040b00081d40311f001c002e80c40351981c1c500030300000707602c0d285001000106454410703001e40c40454941181e0300300c0c0303000030002991004903903030029442610390800c603040c1550010250000c5180f08003214074104106a480e06820041510010769010300012441000c10740412041c0700100002d030342d02d05011020034400804038171f090b6840800c00021a07030301e0b0b08120742d901c03550041e1580b00c0d000181c0104a864956501c0d52207008050b526400359a40d43c00d07502d072060144840c0f40d0900e0075000381c01d4a0715903506485014005451110b027150220f016604802c134000000e4441400000700382400c0031314050401c40c6c031003810356016542a4001540d583c0b10361100c22020a401c3c00d185009aa60301d481c001000031a510b424080c0d000700800c000400c08100000140c07410b440c4505800308000d0a445622070004c10200c200c84507107850500412100e00c84008406070ba20000c5c0c0301c1c6911552a44580c41e11107014010744014040c000000e40c116180c841 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 826672455 1250 826671205 826671217
    0x9150b12090709050106021005090f151e01030602071407030305040e04060f02070302071403190803070306030218010504062403090204150602161a2d0d02090103050a05011a 76
    0x10308a0300c0e250343d01d042c420142c1ea020b91102c40980c1103c43c2840c00c2200c1400b0700c541c030425280c0180300c90001044600e90301c100140c280e1451009202c080f640062034004101b40341c0b04940000051940c503400e01e8002503000403001c072202002d0a201d51441400441e025040700d03059142ea6003068070b0a5800110540e00170403c407804d03591035406003010005440508002c0c4d000ea4003e00c10b06040c4034041c0b40001c04070700c0080c8a03500040d0040c010700009503030b4040d140d9101c0b02c8a80c403912606010b1b0040c16035504000d50110ba41088031500030030944086040303410813a428498590f407100d08002c00036000da004904020441c3d0320010903406038110380c41d290300c080c100040804031003151079101680f40e04040e005812245150100d9400030b080d810290550f50b000c2e0500401000e40089148205110804600050002400c0ca07890704c6a1300800300075180a03190b40c80f40030015440083d44030030f41c4a80402d1502c404a0400318841c4900c505039102d50032101011107640440d295a50041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 826673705 1250 826672455 826672471
    0xb070203030f0406031a010318060905150412030f1e0e12030a02041a0906070326010648110a030309080d0807020c090901140c0409150b12 61
    0x10450b0b00c1e241544640140014442990001408030f02d0101da00007445803010010704140c1068008a11000f4076a4145102c039400180000c02e8641c915101c2d080c8003540c20981078150072402000244030800406210503402c5035410806200c80007441800c49009241c0000c2038048100d12030020410340d0b00c02c56120380720741d084824490008901c01c2c0e503a0320444107041c1c0c040e0041001c0283d07084642006210360340400e0b9980c2000850004100280030340c06000d0204035170003002100a42012600060704d0100f03159000082d84c41e0390f00641919131414003005802070800c0d41c8100420500d401e80c0020780221103445451000c034001841403014110180c901c900500400041c541d10702c51008019440b0351a100701c01881c08a803d0b0400c061405202c06000c1c243c07041000c030550100741078602c0e600840d0b40c101243c54105c095030041025075030200300b040001d400c1c03004140710803003d4800c5032010a010f2105801a03440d10316401202d100d180c04d07008091014081106041034403030303800301c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 826674955 1250 826673705 826673707
    0x41502210a080403120f020a0e0d0209040807031205070512060105090a0306200d0b0108220b1308070b04020316140405060102031903090201031413060f0209030a050601081b0a0b07020303 82
    0x158040c0d0384200d0b803143c0406c54070341790300141c0c02d80f644e900300f15081c070305130012200000501e105402080c0c0b5038500a1000304002c100040e48010140591800ca003c3d50102d42c0400062400d0807014250ba44250070030300954000a00066140d840b07a41154840700c40607010071314040c40c694a02001c0c11100010415080c0341604001b00345003010f01030003003401e2006010450300444000075102c290f001c2d0a83d03940e543c1c04502c07a07001c000c00400c00c11460382d00562100d03440d0b0310844114002c3c440b2070401000c0b40400141c2400740404a102e16003e64021810b581c100e61068074080000d08180c840c0003c00803041d844983c0600d803550099503c00d2060042d28900060340306100101d17444151400042542c40f02090306550b41403240d10900340b0301d184003031070310709010085540011a40c0380051601d40c5511032000f00e0252501619080c4201030101c4881514030300d06039840c3c0d1001d0207140268407a00d007a00d00f051b8042c3c0c24000c40c1c03404c040c040c000c010341080c810039559032103110180d8143c80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 826676205 1250 826674955 826674977
    0x38040f0e0a050102130b070f08030601020a020a0b09040b091e180109030503090d0905060f13031e0b150f131e062d090e0f03041502210a080403 63
    0x5428000075048a1203503000580c2c5100d00c04950500c00da0313980000c80c1c402c806104010005030300b07045103401e050b045a10301d03450384d0313903400103c0c0f5107400c40500070342214094500040c02200000580a01e040451303003400111301b04c1082c041882d02c100d40083c440700f001c00d180d10188a0b85081550002c103035108040540046010380d9083d035001080031800903100204000d14101d05008081e40d0172003500d85000500c0c503000c001161401007610420b0a03510005003036502c800c400b00c1032002158810824400c5031940302e600700d0344002c400d00039904801040c000981d881640b10a0040c2c0000041c840700050441c0030074041741d081003902884800c3c2d61004841540004003200341c64090038908003060300c0d400c000c542d100040f1200201d2542c2c0008050100142401d407041406440700c00c0b1001900c841956001031800b8204070403501d25010024011450385040c3c4aa00303159070164080301c900118800741501c0ea051421201a6a00028044484080e214182081c0c000c0d0083c034091150306 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 826677455 1250 826676205 826676231
    0xe030903010c021501330c021f0f090b030a02030403050d0f0b0f04141b0f030a14010807030b041205071407030c0609050d02040b030102071538040f 65
    0x18402c40780100240c1d1003524400120030b40b1001c140c0c00b61010151844902d01140d1003031b0076000d01030408034950461100b2030214203214201c0440340c0d40e001400c2c41200844c2000700043c03c1180014031002500305a8402102d45c000d14041045400340d40078503180d0b0303a0308046074009410140046082103020002001080402d0213240d1001780016000100d99401c81c040101c0c820b4140c1205000d82d0600d040318850b01c6403440410303440540d020503551040346003405003c1034455540141c0925601000788241c1c4400ba0384021103500d40e818008455980f03500c01c50365244880d21005042ca01035400040020751038143c0382200d03502c00d00303081c5d04003542c0c0d0303895038540c2115041e80100d55200580800901c11310000e9200182504d0800341d43d180d0030040441c0d034810722100041e002c0c0b500d9240801603038500350f04464040303030014150b0036400c0841000d40d02910300030183c0c0403411080606c0c83e0841c112101c5283e000c403c920720072002504403000340001340c403481b0181041c0c1640d43c20340035054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 826678705 1250 826677455 826677461
    0x24120a05070201050f06090f1909030302090a060507021c020105120903090915180603160e0403090501030203070e010e24070515040309030b150a0312030e06040c05040e03090301 78
    0x1852401a000c95645441403000b400c40f080280901038545114090003d192681034070650003600404000440d41d0721050040c1010700c0f903090707034580c0600d4401202d00b8140d043c0e0161821a034111082c6911540c0c071002118903000c3c00401030b43c00b400040801c201072a0b20303440605413a01c1818814284084d188105d400000103d07403001154100150070600303454441c40d55a4089426042c1c40c0e03107800548046031450903419044801801610003003207003035408000b6008161040404844041d4075500e410102c48420b0ba02100450156103022656601130700959120301c49660385e100304e0501c20f000442e508081001001d4204a050400c880c0101c2c5a00701122030703111151201c1d0f520502803034220300d044081c3ca1000810b2034254140000280e003c8001d0085075000f10440f5041d855045540f001c103246910041e0384244000703030001c10403090b040001c19488060300c00300701d800d40d00d0700301c2a01ca203011500105072a41c0d545041c491840c10f61300c00940c0040110451b070418001c080840e0071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 826679955 1250 826678705 826678711
    0x210203150105040b1f0f2c010915140d0e0a0302160803031b03040c080d12061e06110304030c1e05030d0c03050a2a110409022412 57
    0xe105610014401400c3c140508000e422050720648110003814002540501030600e200b410051403060343c2804500c6006501c0c0100c01010b00542061000c640ca03007068010101290b0105103001c00c00900c51a040c2c2d10000702d40349580315503c00b8000c0d00b0501d50740342c0c0080c3d00009600d5503412020f00e1036070100320920a0903c00d4005092030903010010580c0304009a000381469442001003003905403c0248440e10b081a000866440c0d071180d1400350708840c2e00e03400c62320b01c9100c1c0109880c05070b03900884102d0600c20040007000a5900c0301c14880d110041c054001000803000d100800c203040c41109402d030440c00100a49007429220340c0c2d081000c9010b507006060440300180c0e02260303590200e01030401400100c004020b492034811016041c200f522002500f40b04010500d4042c1e10b0040e42d11414010322102074000003c0000308040381111440003d03a1400145081b0140380e08180c4280002540c00500c1880300b40303880046100c445400121000e0410014400451070500f40ca48540c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 826681205 1250 826679955 826679983
    0x3130308040c170c0316050d0204020f0f03070518040603030f0c050709020a0216060809211603050316031a060c070f080a05010b03070605090906042a1d010504210203 73
    0x4e10014500c20103141c4600350700760704c03009004d24004000300d5171602d8022081e141c0c1610301585490a0120040d840c0c00b4001c440540d810000040009281c0d0080040607614510300b006c3d28000c100809200403a1031f00d000c000c022802079903800c61064021403103552650700c030790304130384c0e0740340d1038071040700598020800c0710015134440c2e121391450085e50300e40b480207030000e8a8001c1e254a40124981d0344c07110504181a4060a4000380040030750b1410f00b101c510481002d059807005910307180040040d40129900303010032544d204800419031103801540051031410b030502c580c0601180c01c01403541c0c800300b8034a01510406200048295629542900411240010741411034450810600790f8040400c0240700741c11079a02400200d03001000e0b6400b68105841035590b594408010030000d00b0300304600c400e40b1050200107003544010051100d449136240ea1038170f00e15030b5010098003440566907003a40c0418800d020074400c407884050b4815000f00d0740480650100d00540100e81000c0c0c0c0821541 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 826682455 1250 826681205 826681213
    0x20106270218030106352a041407110f1c121d2116060b03010f060f0801060509130f0c090f050c0306010c0b06060f03130b06010503130308040c17 64
    0x40d07071500006558120300c000c480c418005100400b142c0948501681c410014031141c0c00790551070003011203400001a08008d84104080307110102580c0e02158215244400070300381c40d8107400154000b05020b005691210000d00b1448180000c0500030b02002e22100200402801152421003150040d60040115412000c640e035840404071420810541c1000c5500070210140c16811301001d02121038100c0c2100180c031288003d49807600262034507a03103199040d802c045041860714959803180c0d00f203404104400702610f9843e51500c1c00e940581c899103600000c1c0000041c42d000a1844002e1503d100d07401c0203030b4001241c0d0b50742100d41700c82d80121883c1951003403a1540040c0034842c0302d030800850b0110f1821807500600083c548821014005c2c00501d140c400300b4880d4a4000c265034070070140340107050f16440c0c4111b05616407041c00c9425104a5a103c1c0822169406a802c50340a034084210881400450b920b040d200400b02801c100e4030000188c00006403e0b1320003148000c0705030204058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 826683705 1250 826682455 826682489
    0x10141308060609010608070c02151813060605030a09060b060d020909100e04031805031e070e04030804082109030307020c06090a0603201603020106270218030106 71
    0xc52810300300401842c060030001d00140300854110b091903070b21020030b10740403980a0302803011032410200300e00d030a8008000810020402c80261131115800078041d42d005100807040d20703842040e03c0b072522031380c40800c104001040301010b00350408000c440c0a20030110b01c403004240810752650043d2691916542c0c08100d4883c14505601340a810501c07882003402e00905000b070740e29540001034170007018084940c240c00341034140f4210190091100800b680c17050b801042c80d40e92040c080c42c0705031803c3c1c0103d5030702080c1c4880040001b4000d0f9015983c0c0c0420b55219900d002c410707400741e050b4500e4000c402c0045810b03165146c0f41e40b88904020b902840e202c3c2014107002c1d280c001300d104018030640f000d10003582c2940b0790034080812180c01d4a404103002521000003c1021000c01940b4810800090303580004280b201540296510070740c020844183c0c2c51511081c10001d01c590f80c5400462003050f182c3c0c3c0400b0390090402505260b0003400064402000603003151400d070704c8817254041c05c4140e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 826684955 1250 826683705 826683719
    0x301020f130e010f15050d1b0908011103010f051027050301050f010308180d1a0708100f140310050a05072303042607060213080d020705101413 63
    0x200d50040810360039000b9005d040001c5000104450b0700758400704000401c009134014196013107441d4140798032030507124200350000010a542440c0c0140d408640c20020041d5020703140381c0489048807040540840d21710304010804c082c805042001100f005100100340b000080d92001010398013a4580c00d5a1201b407412050500b5603a0081164045004050040002c03507401000c840500341c496100708e0a803d164030010f0703950307111120050005865803881e20308000400e05140d002d81c11903143c00c8081d548042d012103801070f0728003070444410103001040201e00e4003081c00081c1444000d06440140e422142000219001102c12030021030300c4105001c9511342104481e039a000810320001005d03d1100703c048503074840500010400075214094000e415108840c0c038000c070801d508165559411070400c0c03c00380d002140181c010300184c0000144610000030400c90118083d00540203ca00d84410465815205c80c104030074088102e284209818160380101480480c0c0b084028030340e810302130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 826686205 1250 826684955 826684979
    0x324060d0f0605190c110c062b05061f05040504020f09090a0c090605090f12070302220605010c20030f010603030c0b070525030309020a03030c0b0703021e03060301020f13 75
    0x5c288020b00c07076229081d000d00c140209002064600c20765803503540e100303030b1907054074070b501c0464401d00d800c048012070143d0034030682c026601801c03089408003282c9070201c401c08120014465268040740c6c0402080080d414a500541040684010700c0d90824500c0310100c4c0b404801140c1c24041c1c20317602c03010052070310f0300481114040c18180c0b80440c203011486000c51400040c036800d183c03040d00d908a141c00c18400c00c10525010750b03405000e080c01c02a9200c408503c0d03041d8802c1103103515007000400b00d02944191004d012071a00030003030809030b41e502c08403a14240210070301140c0600542c2c4481c0d0260304240208802540f00c0e5030b0b004081861401e2aa80078900517000c4c40c1000010012030500320301c3c2101d0b021a02412060580954000b8501940180308800d0029008504900c00206040e040107070089141d00a00d41207400741d90f42d40b4200c0c03c9200302c001050a0719007a44c2d000e4107010001e03001d10703400f100c041c0c0018a0800001c6c080d1301c0303c2e0490525428a0b042d940002c1c80b10641d250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 826687455 1250 826686205 826686221
    0xe100510051c1b17061b0d200f180f30120706060b0a021c020a150c0215060a15140304120f020a03050301052e0e0324060d0f060519 58
    0x421030910b81c0d082c00d40200c580c1f040d81003000455031101c182d01054400401c444440390b00e8580b0065950581c5540210607402c01c0c010801050000310700005a41002014101803890080030009942c01c0401c4202e90303403003400f010711403203c4501d68842000e2000c01c070f12140a01d92600d420380760b41061501c041680c110381c000110084083c441d0b100115000600981d2200007181700b16099544040228540b02e60004040c08641480d5044245041240e000102003500b990959a00c8420003880f01007060040d14a0380e0012402e0100f040b131301d03a00380780c582e4850a42d85400c07841140407034060091b40d00b065030291050054003000403030445e00921612503070102030000d0301c1135134466200a003141c0414032415005071f00140050110f00105000c00c59181c3c402d00c088403070480c8441c401010094400c1201e03010744556210150300380740e503910254040340c2c0d84480300f0030381d40e851052000c43c04000504407030020200a80c00f00040d641d0080034400c0008580c800b4640303d4810318001034540314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 826688705 1250 826687455 826687471
    0x5041a0103030201320708091609090c050306071403280e0f070303022a040c030e06060a030b0a020c0f1e120a1715040e100510051c1b1706 61
    0x1840c0a164017224544501d6200c1840d0402a030680e983e206400e04100c0440f40111000f14018004100c0700303d170707520500703c01c2e0040398001092a1140103050fa1000240d0341080400d81061034094180155401998000c1040084242701c580280e04030420013016456554035a84505040620580c104000d104151100005180907440c42d00c000e9100e541810f800039207810001545400c00719002e0341110030301c50103002003041140418000300100110035603c0100c3c003401d40800d10030f01c3e140124006032600020b03111b030140c541045040081d480151249903d000d0212148150503091004000012451800d113480c07a48850110b4280407414141c07004141c0148684007549074060b10307000311a00b0f0740b0200002a10b0318001901e44040ca0b0005170b83c00382c100401003070403650120f621600c800c0b911000b4003843d01e8010b044000b522060080c0380e08800c185400a8800740c02c1c1c2c0d196080c150081010300300b41051000c1d0000c40d00c069800140f107125111901203011042044820b92203040c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 826689955 1250 826688705 826688771
    0x5031917041d04060b0a03031715010e092703070b0108010203150d03140406022104060f080705040806040f050609070e01050d0501060b0d09020112110a0305041a0103030201 76
    0x4140c5200c0c0310600002c1c150489040c1c8100040c10449035500180c0703020001081054000d40e649402091400d11048221202000b00301107402419500c209040440c4140c4420055059480c140103200b00000c100508104010070b0700d000c0c84400001d180050b400200181d40c3e101010b041c29040c3d0030041c1d1082c000d9a104001300a44d11400c00310f140301d4554211244007a41060b400c088444071000d1000801718840028005003464000403080c0c1c00200312682034404000d4a032850016000d0f074400c0801003410b4441040f415440380070740581c421030600b401400c250700c900341c080c40e2002c00c6400701e030303a02c4010241c542440010040301c0e62103007084000700140b508004003100c3e98041845010700400d8104040301c10400c081d000b5030080c0017440111910b4a80d90240366016012442d802d90100751120781d5003000721214050070b4a840c5040c0d03a0030380ba16210101c101c1c010036005009136a0800102c51400090411092040c001c5002e940041114125600d40041900c184082040d81c988 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 826691205 1250 826689955 826689959
    0x504151e0e07060f0203130512010209100806040c320d020a031a0f0a090209040b03011a150a0206061302041e050901080102071a07030617150a14130204060503191704 73
    0x3820300c1f00501511000d4030302c0d2812200c0c441150340a030081c013041d03d500010403a80b00b138031a980032862034854802107400b8494517002010070740b815400c5036540c43e912001420000c1f5089034000711000510481121036180202ca82c3c005000c980104900d40000398072030b803420000e890039100359440c3c0b1604843e061100d0690348001070041e40e1910903000715540105440d0101d9840742d02c0340d982a40b01400034007a4041c54100c4c100341c003210300b00075481503a0904680c2c03049191030040e034610541940042003d500c4060802c203c1c8103400354000388094007040041010b201c04d40310402000e0828801e442014180401c010001e08160481e2410741e2061000314040b8141c69202d403a00840004040b44076202d903070044018041c40e80200e050440710780c0307000000d50780018400c1d6030810141d44034403141e01c0f002c5140e0700b603507000c42d0502c0d0306090365000300311040c40b100c40525850780f0050000038581d989102107424017121150000c081183d068212041c01507203030420050004a4183c06c1ca014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 826692455 1250 826691205 826691227
    0x1050a1706061308060402040c05210402031f020d1b050708031806070c063209010e010c0201090501060b070b0c07050a0807080306030c040504151e0e07060f0203 71
    0x1100d003120204419001000c101240c40301000c8072402c54082c0c11a042458541101640d20801698101d0040740f4054040142500c120180c41500f1007141d003541c00143c5243c0c07808019400a00300740da040c000c40864a40400700200c09100100c0100005621502c84815410890300d109071260030884d50b440d4921503441c1d20404481e100c9610055030b5840c0c0e04d60402c07052421100704407500684c8552030a1054607500308511394542403142c0f00902c91400d070f422458048144012081144003051404e50313101c80402c144042d0f04c189a40c0002a01c0c080200311642035a0320b0303807508805070b50b440c60b0400070b001c07080c0a000083c284a0040610780340301c6035a50034241200030700a0a1240002c178100080010500448243c682c000f86040d840740c54608043c440c0390b2058860b284203100308031348401142401d008a911603a0007560301031a4610b10000b20019148102200707949905800e400301a03504070348100301c5804090401050f83c01d09142016105c61554040700e4250f510074880002e842d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 826693705 1250 826692455 826692467
    0xa030920010206220f050a26090d0f0f03080114030f0c0103180f080901120e07060e03070302091602160b070303181a0a050c0f0f07140a060f060501050a 67
    0x291030300d07411040140d01c41c0c04e0401c0a100c0d40340100320400d5441502e0034810002600c1003882c8c040d011400000110303140e0400344c48540c1c140700025400030300c41950185000c0700c50208560040008101d19022a0f45030444000d8941e0103d0115001c280140203c44000c00c08100701c10040c1c0041560310005002d2590791825040e10b01d04150b11082940c4c024141c0a02401119030f0000c0810003070700d00c6181c0030582d50450045a8001400c403601820f41ca4004e00a601c1424a80c10240480c1410120100c03061030a000b04a0b40501c80c0030000001a1100e00005105a00801c0080d03440300d071107080241007071404d02d8918007241d07100d4400e010013074860b0100c0b038190f94941070000301c404640c0f81840e202154070304050081d1100e00c03501c401c0103c40e060001d218007110030003000195515100000d0902a01502807a0145c0921601c800442e82000801707009005d01403040c1d80e40050501649000d05032002140c0c80c41e21030400b01071202c010300807000a050b007400e04900300303002c80c0c2000f081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 826694955 1250 826693705 826693711
    0xf020601030b1305060702010e01050a1a01030f02190c0203010506010e03070b0a03090602030c070201090f0f1208090604180605010f0e01050711040e0f07150c080309010e030a030920010206 83
    0x150390502c00700d440300701c0054940c60507650200c181c2d180ca01d40564081d008042c000c5045050354200000a03d8045481c4510203040b40c1303040b1042800e501e500b004400920f1000741042c0c2c495401c001e010050000030441d80030024a0741e54248000207a071052600b9240050003540c14040f41d181c415100780e9000c5144000d8880b0141d0040e11113490314411009000c0c13404026052620020038420388824a8005018841c001c1e01d50f0296a039840d014bc0200d580240b19000f8852200c100501500300403d1070011a14060408103080c4891040002d005d640254042d43c0c0c801e02d20f80b980c200c0500503028400040000342000c0415070300c2e623440a05403201c01c05a45c2c1c100400060901c04000e480e0820120001000d0700c2000410b030742c0c032503c81d9201e41d1a2031007a41841050400103c20400c500c1e4030b160b22030070703036611340c0c03030308030980c0d07107109170f4102130002080c9548400070080070301030410150050803440e07503012a00310220304003d0f041300c1e0310000307055030401c4915a44105903000a0b40302d030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 826696205 1250 826694955 826694963
    0x31306021515090a180606030b16210e06010f030201170603060106030c032c0709062129010f0501230a0c0503070c090608160b03070e0619030c0f02060103 68
    0x111399244201d08000300280035103410015040e02d2540d0510080368000f0381628810500e851003510b1f005484001d44012230b20000000785210311481103592509603c40f0308a40c0c42c00045102120140c12070f04080098105880b11218600100150345c1d20207170300f5644c3d2510700c0f030044071810800042512800c0c140140018107481c0c00c020501a80b003540844000d01244003200c0d102500720f055a00074022030012000c0a00c500080410b0010551140c0300c125040c0082c080402490b13042070100908000f00c040d900690720014021b18207048921081080c601000311180d40d40c100700040040344c09640042d4104441c0d2580980d11841003000b80258500a040d4603440345041761003142d40d038401c144e00a00500000c125141086092100c15041c0d03504003c050120701d4840c18915621141c051005103440107044003044000a40402150010414a0010300c16040c1e0303000f01e411030740001011b54020b03614002003540194580309003a03095009103000c14850007010030095440c903041c08050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 826697455 1250 826696205 826696219
    0x110c040504150c0f0f2001090302010504140c0307030b250203130605030603034e06040b1003020d06050406080c0906060307141b1f050907150e0a08031306021515 71
    0x721500954035440581b15400c0c20090010544610b0024043c040a032021180d08054412100c003e880104a0020500d0094003d080c0149951290742c101180903201000700c0310400070462900403d03148600c0c400900d41c0045584425181186001004030360220341082818000d03c14540c1c1d0100407200c500803001116147c0708001d410340c011201044201d505a00300100d000b00140ca003032241c040030480e0180368894075544a03010303c01990141c2140650007150301d40100c0c0e06600035805441c0951503810000380541d15070002c28100c0b100c54004c4c2c4050340c815103003400541f4043c0b10b0540e0100042e10b020342141400c403006041e0180c0c0750691140c400d40821841c0709020200c2a1242846132842160500d12043d07a214081c0e804090141c0519402c00001445030358000681c5000c40300d583c98180060b100a500840e8a03910304000598844407a07070300010000c4040001d40510910702d0400604140740401c0a441d0241c4050341c80000007541040058003401e04150001d03450055030f1403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 826698705 1250 826697455 826697477
    0x5040b0a030f1514060c0606060f12010311121c050c010f020d0b0a0603060302010806060901021c0503100503061b03040f0f111c0c06110c040504150c0f0f 68
    0x641c0504502c5011503107141c540001c403000100546100c008039241c1c600d112061200140038400c0703512450400c403070685e21402c0032400904080d002020003120080105003865469034451101714800e90003074032480c2c074164088030300745403892010411012082c001d006ea644030701545208910801d180c90107004011801d8200041c1c2900030821b8100704200c11980e40c212007591900400843c80303220300071b1070007031004585030340244100c0f01580e8058443e00b038241d0754242000340301ea009682103411070040308000100d90105d461407841000c060740b82e1301d4a074030b061500001100380d030b984240d210b0741c40341040c000741c0c0e18055200081401750159590b41c0e55514144120140c2c0c052400400e4120800c0e800e4090004401c00c000381854129007091204801010700607a54080c4580944a508815401c10043d40183e15114550040070300381c4036221030190000701250411101947c610a51a2080e444544280700d90200d07140c1c00d0070310080d10581001b000b00007980c22039031101400014007030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 826699955 1250 826698705 826698707
    0x420011d03070e0f0a0b1215060a0b030a090516050a03060203090114010303020703030f0503070e0d03020118140d0903050a0305130513150e2a0c0715090e0705040b0a 73
    0x9103014280d42e01d00790115050101600701000c80c00c494000010303140c140d10a40c0c07490f0080b425690100c1d811f00030585000c442489030700c424009040c042e0f0050f8000000201c0a10070ba0140d0700ca80031600000955502c107080c82400d00c0134181c2320084a1000b400140100d9032041040802c3e203800c40401601c0399205e1000d103006020248070004082507800000003050750000c2d0502c00d4031321036600c81801c2031240314191418003050f1075070000700e24110290380030384c100300351030103045806032001040f0f03410b0001480f0000800f191007942e4019994004400c0c68408024080749030406184c0480e9003403854803240c1e202c04c0d1807600201008000901c114002012030101c3c8050080240130860821404174140010007024051111300d07581c0907000105110708121881c41244024540300d84031000b135001a038000094281c0039282c070702c28051502444d408100b414041d00140d1560754280b03c1030316014045014a621080605030080b081124842d130003400c1c0d404490050500c16121514048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 826701205 1250 826699955 826699963
    0x9051609061203051b1c0314010e040f02030a02060a0c050601080c1807031506050a02010c0c080a050a0c0611070507150f0305090c0909100b06120c1317060420011d03 73
    0x1a4905180704200c0242c12048801c01c22486c0c07561952030800c003442404c2603c050b4400244152201d44040d5070001d40810001903d1101c0316100505480058620741d00144441d0005610500040c0390b1900c400204841000001d02600a06c00242034500b41c0b240026004000030781a5601581424003142519000b07400602c51003071508070302e41c105034031007100820b00d40007058650019820964050040703401440810390007074000485901c2c04000102c1030314154001030000040081070303405480030621621440d450340b4611005295101510300b0802e1400c81c3c07603005144549144070707207801203c0d0000450b800320145403c1c041344550750003042c9410440788458080d000308503c400c0001c840c00100f40c0c04030382d0782c03064010064a40c0080030710805000d1940383c5d00341c0320004804140c404c05100301030001540540c0440c11040d440c2c24200c90385043c03440c1d41e100507034090401d2004004c8004030154a404440f0304106508914a00007400704044483c80c03180314009040502c0103403070500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 826702455 1250 826701205 826701247
    0xd0e010e0d0311090d290a090317040309030605150301110d0c09060509040c09051806030d300908120405070911032e030f0b130b0106030c0c060905160906120305 71
    0x83c091106864040c40d480040d104200c1c0450001c1e0701c60b04512b2800e0740c1c94103114000c03609540c07003a42490841c2d8801000707000240903017800305080e6036522400e9500740140e111074890810b5041e01e610410300341030242c0d001c800400d010b00c001410140040340d40b2005540d4000002c960101d500701c1902c1c0e0650304020260881074111180341007000c00c01074054a0780b4000c03001901103d03803000d90100200d6081201c4418618108003604006030140541c014101c1c0e40c1620400000d0304410341d5031210556804038195821001c2101f04010a100702807000301d00404424074184610401e4090040c03403484000c0c0704c9403034000c4808444091460000d4095000200b4403194031150b42c4905104191981e0b2603811208015060005490421910304601c11542e1082e8003503c0c0c0d1342000d0f8180e0190064900e0801001481c1829002103074060185c80582e6000d00b01804500281c05213680c01000c00d0b410142c1011f013020800c100301c10043c41107451594242c80c101d61505690551103a411f0301c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 826703705 1250 826702455 826702523
    0xc051207180b030f04120e01120f0608030a2115050d030c0615080106140a031e080a031413021e0a09062d0305120d0e010e0d0311090d 59
    0x3c010810106185a04140510301510428082c4004041c00700c4a00300e860550f1400210b010105a0700c1888a4001e04141d054000b0046012511a11028a1a0403103c40200080c8203400c40c08004212400b174606c80010f1050140000701642101522410040c8515801040150b5020060504c60030311410129400307002030140b20b0030040f5a00e180310b80d0380110300b123070352910783e002410404c429154081c001c0003900f8280114a1521103440f04400019004c040740c81c45004100002e404330020428911070307840014190700c3c6051110002000105441c1d0011480c80245000d81c0d40c1000349401c041510010401c10f29140740400c00341c41c0140d005405050078a40c2c040340318030a01d480c100406040340418000740c14070000001c503002c181c0c40090620780003150146c965500b40310003042941c0d1a04000b250122456820710b085601c54501043c0d2900100d042d03803000756140c0148021466102c0e8410b050019110000350103c040b00c40c000d01e4001c103041440e030341004a00884070001c841d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 826704955 1250 826703705 826703707
    0x120804050313140f040513020409030c15060603050f0708150102010e0703050a2f060904020903060f0619030305030f040f02090c0a031103090a020f060c010e0703060c051207180b 78
    0x154080000f4481d1414410038481c0d400200c003030481c0e04182c400c09110340360000a2018400c802e4080c0401030580580940030048504156808070321414071800d18030024810000c0c1c05450a4002400c88001408168095040c5824413504992240c0340c1030300803100314007a030030844070180103074010169201a040c541c0030342c01000050060200d46074114a00900320b20f002254400440708070074815000c0070f1a44c41444901c0b0045040c1180502800f06c07020300010300d40119400000e01d40301c1c08440c0c004000340c41d0f00401a55080820303003a100000005500c04890303045030741c00341007400000c040c0440704a414000809001c00c1c12020002c25401404501d13003070616041619890740003c640102183c20400c1030404a2020012684907030054006131160b60119400c00034403804895905901c900240030fa45080348080c4100540185940014085580b0314500202901d4050301450b003845401d000700b5026902078101c40354440d4086c6000d90a0807e000f81c4c030110078169402c0500c0c4404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 826706205 1250 826704955 826704959
    0x120210021e0304030507060c03022e0f0e150c2b0e03040f050105070b01060804110a0b1c1a0108130812150f21120703030903110703120804050313 64
    0x4070120041c03050780e02980642d0040707034840e1029900e249802600500685c48684145040301d4101991440c075940c84001b500b03400c803c0891082603070305002e074407503c090741d41c0941d00200078108100340f80450300e078440c41e0807490001d912507101d0064001d4480060503460b0714140c0403005020b00300d00c5443c2c000e420402101c0c1d040509688e900140a112007010600c407005c13800e9070042d020b441c0016031000640b100d981c241002254110405031046445d8030094906a4032541c0d951210005401c0e2b05000b103480f0050b4036144a00708040c0c100315050244ac10b0104854001c01010001002c402070900241070740700c00c84a09102c08451401800d2440086021003521014100490285c9503074032040807036080141c20442419039444142d40c0c00001210f82a02c62000124110901da05840a89524030303101c14850781c0c0c56021a01c110f00180c1e0311500402055000003204a104007a030000b010040d0840d034856424282c550b10705000c2c80b40680003c0c0804c6002c01c22902c10346415000c400c1e1a42d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 826707455 1250 826706205 826706263
    0x20916090806130c08030f1c200c0c0402042301020a29010e16030507050909040503130f230a0518010501031a060313140a030e0406090612021002 64
    0x50f1840360221110780b0900350000301c0d9900013003a50902100703c44428a80002e504042da40302000700c0c0b0b480121034031048900240c00c40c0c4042c0030080c0c034a40d40219602c26201c1007680c100102101d01c1031007684140801d020103038030001000d502458040005100551280050b440c00481d01d00040496402008844030700600003003031100741c01d0441c20545641d1300ca0010080f51202110800d44c07603601d4000d401c2402e0b01c03913007050381c10080350b0401078070304603050001c200344402c1100e0550380350780005400701120140d02e40310307002061380b00301c0c107864a41400e0081c20f00c008842011350200101880701006a580e604018004000052800c8100c1c80300d103a00390200c01c424401d09000c20300e01b0050f20034041c0c140041d1041810020409031440d41e41c12076034902c044c0410001d5403041c4000e4a0b0712645031042003080401030080d01c03840020020031003040155285900702c151220f040000c104a8002140001d401e150b0b0b04990011500d101d450303081f441d190700d4401317840c00c1c090704400c41200c2c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 826708705 1250 826707455 826707481
    0xc06180a031218080f132112050f0408030c0c061c230103060c0314090a020108100902030708090706020307020a050603040f0203011e06050f03060f071101020a0e010e010804020916090806 82
    0x300c006c405800402d242d41d40100c4401e000402402c1601080303002d800d0f400203050791380002d07400c0300900f4407506014181d82c043c1c04a40041e00070351610350001941c4030700c1c100104181502d6510865200d03290042c0b1541e40310f041c60110b5001241d03d0385511a601e08005c55014201c007442005540034660769490410710081c1103149411000321386002040343c480f920825105200c1c201030001840c8103070b41c03503004560b007001c02842960789146109004c201412940010b500a02103560b03103c0143c14007080d610b0809015a11020966204102880050711588200d10881e20115070842d01ca81e55401c10070034400010700025415407030042c1c8007100b03825010860400483d072a00410015494a0520890503084030b0304680c580d02090001340015403207441d080c3d000250f464690140548907810300e003aa00400fa040e004262101c0302e895555910a03a14010780c002440e1038076035420641c002c2620741202070418003008000e90600710700e0344d004102e15001031003000c00320780140c58038022000074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 826709955 1250 826708705 826708717
    0xc04030611120f1506090414011203140c0706050c0a020d0303061701020319110c01150501141330060603060c0c0510051003080c06180a031218080f 65
    0x16502c140800e508001d1080c0152085804185904c006a0002c0c1040358a800244c6c4907030b440398031806d03c43c45850018050500030074010084506281213440e000e000c45104012507031000605200c4107041d0840000ea41c1c08880c15400c02654420020036051b090046410019400c0804000385030109585940010225544044040c1008940c5084242030748820b4401d0645401044600703140c0070141d501605000c01070b00304803464140150261401d6540340042c403c01100035800c00c021079600032040144410403140c06074a4206180103800c8040e80e58001c2c8082807007c031a035584242500c14a801540c4040d200000024001c0e180c258058038a0380005c0301c03c071303041000c00c2401500a003200005a03a000024002c1c10706980303800001420001d2244840104210000001c50042c800401d043e5002c00040c04061801090590b241401e8080900c41c6621220b00c10780400e0713103c44541e0303640151050108130000804000e84221810602c040d211610002d05100e2220307010700200306d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 826711205 1250 826709955 826709977
    0x61c0204140f0606040608150a12081903020307081308210109060504051006120204050904060203090c1903260f070b090606010c060c0c0b090706140906040e0c04030611 74
    0xc2c107a403004144107580c09036209803000700f100c80740881d00c05031030101a00c817008400703098203012594554544148030042c071400e0350801400110715900d14084403c0030303880012418194658180520000e0403c0e40050461b440c0307045600070f03107040000e00c00c2114022205e181c0413200039030300d03404a81102da001303218030744066180006c006407508080c01014480c2c2c0264003c039040c24035240c400c1e00d411962003041441d07541e080001083d01d40e0740c1c220039130007180100401070b141d192002c2d00900d0110087c0555100744101000142c1e91280d801b001016264814001c003020741e00d46005600c2413002c440c019651240104901e0392000071000581516405801d03a220282c656001c019140d0005a81590004103201d10190104940c0e1f0030411000849203441404209240c541c07003142c82c010f44000326190424142005419485602d10003084561000c2c02c1c540201540002c4562045120314102d51112600086014450500713840065800800901610f03c0780d44080945a0008034074071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 826712455 1250 826711205 826711231
    0x1f060314010504060602120a0c0f110f0f09070507110301050915070906020c0f060d0903030e070609080303061212070302010203070311070203070e2214071d061c020414 74
    0x8851400b80130f6401100d41c1c907009005610210190601c40b5413002004205001c280f040210003c2c40102c5640d100c240a41200e24000b05481d0420148400380c00d200752280b880580340c3c034059039850707401682001c15030815650325095890f2003440c00800c0703c1c5199041d480d2401f040222540404c0c6a12210400c00b0b221a945c4d440c50804d42e1001760f68000d020051344880c80c10306840c20482003906411a000f42050304011800e080c0b075040d6012a142140040e480c0c0008104200042052201030302460614180f524100103001e139483c04014200c0f442000c5050000321558018800848040052200c50340d41e401e0a050280c041e501c2a103424001900e450000c40141c09040d05460483d03500a010744009403400d40582400b0102401448142c05403241103042c00c02e080c1c041814403881960503820340441d00402508162469000e2a244800c0141502c0f1001d05200d601e5030200041341c2004480042189000055048920080d00703c0e261a6a014400d030703200c18038501c560a00c0d0b100e8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 826713705 1250 826712455 826712459
    0x51e0d021902010806130f27241b0c020f010903020346021207051f020a1a090c0307060203070b19060b03011820031f06031401 56
    0x807a922640701c00c14481c80866010700320300540c860745603140c00150040c443d00d0050b849a080c40c049444020f04c20300320381e590f044070b402c629030001d10341f000103583c4a41c15414500c10380c4622451003890011809418500b07039504048250540c00046006503907180340c81c1300060028040e044400d2604103a10070403407901e21070781035032044440b681030b294040c000d414102070300b01e02c4e0071314420f800c04900c0d80749250783d00340640b84141c8881d00141d5100610441c41040303141c0140403d05100e240d070144650406c03c000d208035223420400111600d0350000d05c444003400070038100d0600050750401000000036a070003400c540820800b05000fa0b0000040d00c03008075034802015607a440b075100f0600941c0040c401e49001c544014903580c0e014920034050001c0d0024107031007000300e90a5410030f410403200840180014401101c114480c05190b035010459041110359104c16a04180c01b01d2452007400000103884481c8095a0440940f00040020a06444200c0640980300e07029011500d0303c448400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 826714955 1250 826713705 826713707
    0x1816022a1302121b04060f0f021e0304030c38040f0308270f012f0a150608070e04060f0f0203060f0409021e060403150b04060501181e03051e0d 63
    0x1c43d412586d06856504c00c0309640b0009803540c0806006a00a5000320840002d912606002c00701d544844040030b580d4070b5007503190031100c0d00c0681d00070f0101c0070f1040d13142000c022003503400e1491104410070801002c1c4400c20064a10344115045000c003506011390000c00c00000380d01800d521010008503002d603120302e890856045103031000e815071080004000301000d5010303550003040070300c800350300400544086902c10010740c0c0e81c14110909600c4007100e24144050b020250846502511003800070510701507006a80b401170b40a00341541d01c01e0004141005956409051108103c40081c0b01c41107951550303030300079003044400e00c2c011020941c42d0030302850b080c4500f1110a070300600d100b40c60301c0c40721034604082802404003608070404120220202c2c001c004c103900d1032240440b020814200780010300041c3c8007a90702103414801264502016034518040200540700c0641c00c0e09120551051110680509940090712500072440c006108401f0215162003200382d00c8100c6880c4090160 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 826716205 1250 826714955 826714957
    0x62209021002010e060109020f07080c0f0f0a0308011a04090903110c101b1a040501020403020a05011b0b070201060b04030302071e030b04080304050c1816022a1302121b 74
    0x1800100d580007040180f0400d00c7c543c1c00b4041005407070101a0504049545483d62544106242c04039640400d4240604080411411120f04150000b5112003511036601801c03644045c0550707070740f4150069800304210590810345000303000600052101e01c185040140c036000e05190400c0c0203010342c82c035411281c1019030002402914aa90f407a03840b4151921600c416110140300b11501000901c043d012643d00c001c0460050b03024030b000513503985c80e51040001d08031550f0b1025050210180781c0e41a444080718014040c03507002401051540e4840720100d00616294001c10000318020901009065000500b00107840c0211f1207080d01c81240c000e0240b2303103602844000e241000d9000000c001171206005140c11a106001303c454048040002400030401d10000b4400309102c0e00400003034624004a48041e40f01c2c03400a80005180600c1200358034588040c11028004041d40c0030301c16407501103c2849500c0520000c44d111005000800402c81c801c0c1c0b141c00190300300900842215002070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 826717455 1250 826716205 826716221
    0x3010c090501050406202b0201050402012a08040f0306050901020306030c0d290f060108090606012102040807050111030a09050d020f0a0b0417010912050306220902100201 75
    0x103121a82011314042c030071142c9903500015040d41c10890007403008109010464110311039074207050040c2130101102c4150011181c07e0800c401c40e1306140c140030160f60002100c10103108107503004c1c440b110800159203210103002d080100910b000250015500d20040c40039801c3d070b0b1180e54144803a45420300c0c503500780d000036a02190b060300150003030030740c610707010041a42540c400e41c15061981c20802c1140c00f001c0c0041603102450a00c201008103802c3c0780400568044001d003802007103800c1a01170181d0f1039400a2286060101c4008170b415031500a002c0c544c40492a003d003550b9450301c41407480d45a2104d482000d01003941220507240441011003560600002c9a8800303902c0e6181038100310601480b00f100f6600260902000c1405072501c0040303102501c80e4444065449161141e0b880da42401060000d00344c2c1d15040800000035440c1001d121401d04610f05580c0301d40f04c14002401502c0c071801900055403d01d42d003800f451103079810605596000b02d6a0110001c0100c03016405e8401c18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 826718705 1250 826717455 826717457
    0x207080703080f0703112b030519051b070c05150f0307050f091806011b0503161109011203230d0c11030f03180705030304030b0c071e0203010c090501 66
    0x40c04911a1003d00f403000c2d10742c40340a0b28080e6400f0400d4041c0c5424141d9a81200c0d03081807d0a214107608107900600d10b5408000345070030040d03483e002c0c000c1c0c216441c54054107048a82c403a00400d13207494141c00d00000c0c00102021440c1c1d204403625240140803064400d190150603a020000c1c4141150740c15159683c0445240c02d1541e5958001218158800d950140407420309000a01803a1117200e6440720400010316110b1903804d0000c005400d000d0100c50410540d00d401d921000000c0c4c012040d11170721003100c0c0c1100c0400d4403a1911508ae0070b101c000c070640100348180006040000d0105040045000341c550481c0c482c5100041d03803400311414502c48201c84108044410408558850203183c0705a24041c10040512078442e401c662000f8916040020007000740708902c9500c9040b59001808131004051143c9400302094980c001da1102811540080340018003072040003046400e015408040c1c0a210141050400004d00c10024264080e600e051072500d803481c0200403d805a07541 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 826719955 1250 826718705 826718707
    0xe010f081203070810180c0315050d02010e0f06070b0114011b1b090515090a0902010c080a120f0204141915030608070605030106021603120c021807020c01020708070308 74
    0x2c3e14400f51154400500780c1001d85a503070400252202070814051148611b4940124541c081c8040c004e00307450011222461600001a0401241d952811744100f81d90382030078040c010550b40300020b030b594240b1164242d088940050b040e0100319080310b041d0305840380c0623416145031095500445088400360200b80002c070551071034801064090740201c0008881c107047c0f02540d0346500c058810340301c081d100918485076aa0440c5003e00e041d000da243d0040c4404805c00c107c803001d0300003c0400500c000068648040000e5051106110341038503a110351131104144105544114400700940c080d104644815905a205110b90703d8007410300d802d00d0381c8d008140203030b04c3d04080c42c000441180d00700c0013080c0b43e921100095400303414405c0303100811580d140c054407580f410b04003900b4a629481c40050041a00b282480098081c0310b50400101c09072901030303000d650610100f44042c0c40f21014880806550701001072080e8002000241c1c2d034001e81c00e403513003d0340d20001607940c3e0089000013402050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 826721205 1250 826719955 826719961
    0x50a080a0b0d0605090c190f050906090403033206100c02030d030c0509130c0806030a1a060a05040f050123011d0117040506040302011116020d050c0a0e010f081203 72
    0x36130003290708800110255130a0922000c0014110b18000c02240720040700e4440c20071078100a00b448030f00a1506542c01d40c400c1c13605800084400c10001e1008040c5a91046d46c040940c2c00b820408041c01c5000715012108510407840070030b81882101c00721300c0b5903110503044254031320488500000346e60150050200401c0c2002c03d40103041c0d00e4040c2001c0200074416030740a55903202101c0c0041c000102d00003400080c1070030007840080c0040c5000e00961100c0c03090400644181922801044c80c4c52640c2c0007900d40c000028841d502962010340e2243c1024150b10120a4a51125040b03c42c2a141c49400380c001d141a0003000d00c80b904030740e000c41c41a2081c0003102c2042d45900300c02880502d4101d4040103c1c0502010089040d03409a4041d40040200f00c1010340900c20840703c00f02c5131402a041202c2c01c41c100000f8100e01000030300584110210394104a0100010074240c200189030300101d54942c503046400000900c25130a505403c000000390b91403010541810507020801054a165 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 826722455 1250 826721205 826721213
    0x2060a180201021903140409050604060b0304030203160c052107050102070f0603050a0902120d020f010207110d050a050105010b071b080a080714030307110c0111070510030f0507050a080a0b0d 84
    0x4541340d0a40038441800080308241e03010700d00820142007800c40001d0503082c440181b0089909035040906800710410521001c82d4000045d00e005100c8580d07100750380040b07444e040c01041c88552045402001600241000c42c018140b0a0319200300c4108544510f40c1d40c07001240d45103220b100f000c0c42d1742c8903254248405031207600425409141e4070b1012580008c1540800c043da0a03d195507c941e41103452440c008541c140700b10255100c00400070350a0503d6507c0e419011440710070001c0c81224005244c008000041c80302c00c4489800c034000b000725695070b500399a0f40d584103880c206c9031140e820f19a05a44600311300f0140655030030380010404d1903401d0341c0301c0480c0c0d4824541924004031480c4102c9012070f08000035442081d5641c0d444501c0b446402c6c0642c60600c00240d06814890441ca036840360000026403441242c1017101c0110b0703554180141034004003007400c0c03059082801c00c81081401074200c002010211041ea5600700350340c0d1114021000c640c039680c0e84aa100c8000c0c3c04001c042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 826723705 1250 826722455 826722493
    0x2010e0d0f030e07031a07080109020408030f0a0c0605010303111207080f03090712080909150d080a09030525081f1104051e1306080a020d05120a02060a18020102 71
    0x107074100d011611420f46940314813900300040510a04a103648000300012039238844641c50040000001c01c0d0705090411038025281c0c002d4001514006801040503c2884d1140011440c0e00782c21001c104803e584a040080043c0c0c960603400d00188034003400360500c2d142a4044944040c1c000b0401400c1c601b203010a94410760014100990b14450325002080c0c0c00911420582107502c40d07050181c1e1145450144000c200000f083d295103007480c4a84420741d0f071503c484009556511900c0709030b545019110586486031560070103001841150040d41c400403580c00020300210b04003c0c2d6030702e40d42d030f10b00c00696548014640303076481c03082c0d034005807000b00241c0e042104c0c00302c002c130584d9080030349440104072194404000b4102d08048401c110311541860082e05144596000c0306111043c01c3c542c40d42d598444000c0c0c000d0160814505a9052110612864600d800d003544e0030340c3d8034180500000d580d19003e55001c2c10752458200d4000100f0280c1c825060503d83c103030058542601000c0b50002a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 826724955 1250 826723705 826723721
    0xe1803090f0a0b0318060a06080d0f09090e01021804020c0a0b0403050403240b0f01020c0114070c0e071106061503071e020304080106050d020f0d06090203030a08010602010e0d0f03 79
    0x7000d04902042200d0f0500140d4480e41c120603c0303090f940381d12000070340303003c501070034020216281c142c007441101e6000c00d980d44280014240011a0301c100d040440f43c0e440c60b9841800d01d10f141c20038580540382c0c10b400a0460130008030582c0300242618041004034840c4513041071a81d03000070703002c8002031002220b4503489402800c01504090f56921004025030301c10610900c4103c0720b85401c40c0201080c82020792008050300d44844604600d0f00203540d920300c000501d4180404401c0c82d90581c0320500440d19620351001e81080415510000d40007900810f5902002064440040e00d0310f142c800580984141e0008103004040010744c00c80b51140d03030001e0111401c11001d128106008002200711a081c41070701e50080d036855142141090840d40540c0105104200d91240000940d45044009209820880e80810000340c5031030400001c161074140290036020205e480601103421080f414100e50b01c0360000e105071403802c000c180d22130345506210400701e10340c86a0f03441120700c04c0d402620 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826726205 1250 826724955 826724959
    0x1211180d0311010609050f16080c0c011b0323100302090c070204060b041e08060c16051902090601021504110117090a0606060507050705040207061d0105010e1803090f 73
    0x210180b448400c0782500c419800501d0354603213803c00d0014503120f120300140d0002c2c41410894100d0b20064006015013005400025200000b00b2451811542980080c0030010462a440e0040c500c00c40301601420340d800c80c5016a4030380a083c50351101120800034851240180509050760071682042109a006440840840070038840c6100507241c511401c4c02401c60400c21584131032134248240b80c3c40320318403c000d000307140c003281c100f0066a0001d111900805041d080703944610994101e500c81d0041540b01411a1203094400700400c0110610442601d009480c0d140d0ba035a616001603030b403070700c0c440e555884c02558900001c001ca1303280510441e840005250a01c1c1e401c00e2005900c40c0040d064900742c03100d03042001c6030ba007080200e109450050042c0d003000da0070040d95440b003a403110044c1c880c003402282c001400d142000700d580e004020781300038070001c2018240c0380203640e030080009014100d50b42c0f03007040110780301a00c0d940c1d000a09408040065180c101d500041c04070804541031038903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 826727455 1250 826726205 826726217
    0xa0c0609031b0506150612060f1f08090d090e060409210e090f0108030301062a050f1b060702060c12031305061b040320101211180d03 59
    0x1507650b110042248003580520002c04da5400d0520562543d0a00e01d40060301c80c06003080301038030055107440c40a500981c1203d54103a0300311000d010640308011860000e2008441490600c1ca143e080b103507903401000c9075000c840400b600d09070255035004240c040e1000080e183c00001d075251800380c11004a00f80303c0e181c210b001b042500c01e5220440002c200d03407000301e41259031070f01460a110088035441510403200300155450143d89540303d10060003840c08101c20b55001c610480030302510008600314145404220507a64100710380c81e4105034150b03810b1405040b040c10401c50986408015140000300b40c0751418143e0b5080040702d41c04081c83c00058040c9109243c0070303c3c50840a5071090031182110207005250303192460038010000d100e907440740001c1032075043c81c0c400401524141c0c4d1b8000300500d9250050009254100902c240d0a0344c1300380461025901c2c00e40c82262401111244407041c411008224920000360264107400684242c04540f201060324007000c4940702c55010341081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 826728705 1250 826727455 826727477
    0x1031518140106061b0b04030c03051e03190506030c040e010b0a06031b020f030d0504020102011d011d06061e01050f2a1c11071e06140a0c060903 64
    0x8803050245031110740c506030350b40b4441081440d40051031104400d44194110180d400c03141e8a0f0b0703000c090054000703030401c86087e04000800d0b004100300c41c1c13035044220b15400d04000c0d410141000d5031040710f4002641444d807181100740c0c105400b07441d014140003006812800090300900008000c0d03c0e0151445640f00c202011440d201e129104010b44500d40d40070a01002c0c405000c01e18072095043c6e5400c5501c0034042013407010000c000e544600100d0396002c2000e0300e907400100d0250000b08502c1c403920b5130085251510a5056021008080d0000890709903020b6074807149440356000ca41e107540200741d41007d1440e41c1d00190001c514080d05040c154140551070548403029002800015a075210102000d06900103443c203490355202d0080040625458143c685000000082d07641414040340c45c0d680036040701d003400308002034134001c8050441451001580340e0703c11107034450344010600995101101014003022100425070a132200d000311107880d075560006003200c1c28250f081100520380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 826729955 1250 826728705 826728713
    0x10031505060d2712050a080f060a0b0c0105090d031526030409140c07030c02101b150b10021e120f0306040c03020405030d03020706090b0f0708090601031518 69
    0x1259110b000800b403c01d42080161074403400b46491004000d091020034001c4502d250340c0608441e5110395046240b841e503407188400b1462100d615081407134000c2001c140452a92415070180e4031951034401259500010010241c0858100041290b00c6080496007808001d922450301083c20328120b08088504820104a03821600711707411200d0600c1e15901c103c0c8a12011103101a001404002040e2421202e83d0300a00f00741d5001200030300807040b10300c0d00c90b80c140c0181c40388600b256846c104040414282e103000c1080614948030b4403441407070100c07031781c00d2410920b2800950301c0d03840d0001c0501c010100c0240d804407004503016202c40c030402c8801101420054050310000302d128035829101d042c507404100540341e6076001d50040500c10b000030485580d00240c03882a01116040050f5180d10301c4c200388000e810031300000760008800c403051219040d4a81012482113102d55500e5078541c440380350b03040c1c940e902888040c160180c2c020b540b40311070851740c0c010041650144c190180380070302962 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 826731205 1250 826729955 826729991
    0x7050a0806071707080105131e020903100203161d03070330090b0f040e1005130c0507021516140f0102040509070e0604120503070210031505060d 64
    0x240c0101d030010418460b129412407031012004018444070480751401100050415005214070707842400c8082c040820b292056014110704410781d24072a007501160780303500d00a580114030440c068454104a002c40d400c0a10079640920300b070800241c546c9c511440304490320b5442803980c1284401c616600c6005d603070b0401026008502c6400c030180645d80ca0309440201c07011f040280c5151445410034405c01c594040c0711241510780c2c200226896031044101000a4040d039001080340005210a0020b081319480d004421034078100d0340b15080c110300501501c1610006140c031400721300e051010130300510b80201c400c111325003d00c0d001030a1044110700da6050152440b03041d2a03c0e43c9044404099444c02e0041e41c2d070380c40910009502c0d00b440d0001040303c5c500020548030401425508400c4d041d80c030041118000c288202d0708201152190804a86a9011950032072054202d01100c1c06820f001c0c0c000c000103c580354603085803840c500b0b014010503500004610b20358954071565840c00100c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 826732455 1250 826731205 826731209
    0x71b0f0305062e0317040b0c21040608010302040504020409050607030606080105060f030a110f0c030408071d0412030b0612160c0c140d06020f0702090a020f0f0c07050a 74
    0x5001440141006030000d00c0030250036410308828460070f0425100300203143c2d84401201c0d0b200c183d043c0541782d41041441d2901454004813494940080c400c0d40714080010300c1c82d01c0e0607806480020241c18000700c4044d5105901c00c020114030000c1c01003003d41b51951100360f01a002030004240609680d031001d0130038000f210060b0200780d803540e092281c0c3d64800180f0b40035040c103540c101c0c0381240343c00783e0190341d01000300702d840000c0e120b04503001e054600d40117844600b6000d0004540350324403149995105e030090701404050703105101001403a0701d03c00d01c8000c01818041c2c3c8003a86600ca94841c8003092a9250044c01810340b40c0c600b4003c1c0d82c403500001c0c00520003032061154a4145210210010790b005159102004440e001450104078614160401c81e0004038000c4903600d0f40c40089080c40d480d086029100303601c08910004490a8000100a80343c42100e0086080c2c2c1c40c1c0c10040c04034050380c204400e24600a0044c2c4030b07640c1800000f00582c6842d44200d8800340e40c1e03000082d40070480c0d6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 826733705 1250 826732455 826732463
    0x1e010512010b0c150c160f0206040f030b07030b130b01020c061903050c0f160f05030a080601030c11031c0207020406060c140703110108070c06050c090a0603020f071b0f03 75
    0x2503243e54081090103052422079441800044904013a52414202c4c041d032100c00c16103500b4002800f04200d0f990025074245507001d86401c0d20703140d954401c200288101c3c4801e481d141c0141d000188094803e20807040082c00041c0a03000101d94070400724014511000740740e065228401600c02e240e50f450b00a04202c60440d500e0f09062507403500c002303054072005000114000000e01012220145aa042e9504803900750071039030468240d42010792007071070303003d202911500000034003860841d400401103200d5542a24140a41102c000003141c20399484001d0b68600e4100703001d0340004100743e1601a1204110035005400d015032500000c0403601c083d40a1130200784411590b1040104000d0401036800700c030b101808030b191035510740c95481500c100031213040100c14000200c03040d02569101c0c00707068000c5403c229514141640000780d40c020048030744104801034000440c03034030078001c03039043d8850341000604205840d80e6450f500300c21034078080d10020f42114003040d95501c54002c17600441c05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 826734955 1250 826733705 826733707
    0x9160314010c02060402150705100c0905120a02150c160e01050103060506030408040e3408090a110607050c03190308060609030d0e06160803040203070807051e010512010b 75
    0xc4209550864a5400d0642e080d500240700f000007580e0740c0c041c040c0d640c20954140a03038403803039031404030f00b0040c0b0b101e4500c08561078480c0081c0202c3d0301c08540b0b810f840c42901c80100760455000b040c0e0f911603810030001d40c881100450710b00d11207442c0d00680401501001102c3d000440e10300d458094095a0300041d903484c10100c0100880c0da0306020340380003010255035503881c41c1071603215664140305034051b440d85000b002e40442d207280f076054010100303050051019010201b041d89d82c401c261030501c10703800010b285100898070720000880c03100c400c19808101c0c0d0f80d030400c6807010700485070400c42c010780d2603019050341140c00e900c0070300688141e11001a2288881c00f0b141c54040c2c11201c0152016000d90780901520030946c40010306400c2d40811401e0070317081409690b0004042d48240121041d1880c3c14442c418100103020016500840c421000c1d500e16540362900d0a5132071001d44282680503014000920a14102030b24507a03042c101850325034503041040341c1c1400310481c00e1b4000a84650 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 826736205 1250 826734955 826734983
    0x1e0106120b04170918040c050a09091208150f030a06060806071d01050702011b0204230c190c03020307050105070e0f0f03030d0f09050f0c0a0923091603 67
    0x2055880150f440b803540b01c3d0550a120107080030890b074800c1c0030881201440b1800c00b2405121520007940001d210041c41a501192140010f00181044000442d0710003141a121090380c0e020b8282c0358071820088115920742040c0004010301c6a880c103d43d150180599180100420a5400f0f26409230000710700501560901c0100145010781e03407054a00b218043c5101035090b680c4c0f003000ca90322650246010280d03001d4403d400c2c07001820a9100941c404e1901c0c0302006011a188144104031003004a03114a55450284000180c401d00702c415400c0d0800310444030380c0328010303045900d126009104580c100b100303940e11142182c00503211900410600e415010181ca0200250440d000003605e11284540b44a40030941e44c0c050407102c9545161200b5240380094102c0d44401503042d042070440b15003c003c1517a694443c4846084980610030540d80840e403180140245004000d014039513101050007039660f1450408040c01c0310259024900c03504010740341e241c0c203020255004144640381c8035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 826737455 1250 826736205 826736213
    0xf02120a0b100c020904060b01020f07030606051c0b04030c030507050a0302331911040b09091608070f090e04140f07240e06040f08010c05030105031e0106120b04 71
    0x8000c0c900c41040000f83e40c251001601c41c1c800d0326400550010340443e034010071200603403c2c081c0701e03d4110307494030804000006102480c0c001c141120010388d0b50f489183c0101c00140c4101801c254050190545080440d000903c030303030318408003d8080c1c0f804a0510986aa510741000d40c41c4d4400da006178060151900040e0703840180d03c52400300214181000300c80d00301c030740400310030040017a13003800204007180d074150403650058640500035500301e596681c0c0310b003014891134100c1c10560f40101c0111000401c1c2c120074004075404120140c8800e2403070703a0f80700b4044034010b1401450000704103851000140b02d24203c10480e000340e10a003058287c0d483d03583ca416180c5581040d4481050380007040400050003565103070350b0130002c0484140d02031200408180c84c448071164000c2e800107400240000c2108030003a64006036030402e1f0090110920b055011500760100380101985500310203100820b20307102c800d0703150700c280d0f002c40080380080d6144101c4001c2c14064109071000300d01501008104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 826738705 1250 826737455 826737469
    0x50a020114161b05040603030816050702010507060b06041703120906070f120e030301120309050612010618050a092a09060503280603120c0b0a0f02120a0b 68
    0xd101000c119401c080011100b00309850401c0d2000c3c101a04031004910301c0000f0b0071042024020140040c0041944ca247c010001d040864558013010066017101c01d80034440c5045603440380e01603680608284240d254000180b0440c00c4856202004001c00100f82100c410582000031545001e99164101e079460301c980180010910740d402d4000c0820002803a0700b007446040510841d190120400c030404400e00000c109010a08034284004400042c40810350070340620402e00c20740c0ca035021030f0b684009000c03150160281c0c2c05004114000103005580c411358a02e401140b9130111060020760340d00120724000c40b15080360020b5502c8881c8291410082042c094549940d801c000d1669540c0000080400c141801040c08100d800008603401c000c2540d1641d810040c0240b15441003110324800100030a02c03403000312380320012110010480e50040640e240d0141e04070683d0f0307150f80d50b901c8041e401812410b134101e00080c0d00707000030008580c911800d10712980d43c0307800000300c2c83c05e114200090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 826739955 1250 826738705 826738727
    0x406150201140105030727090b04050d03020a08060904051f060918080703030e0f010c0203070311010b0906120106080a0c050405060a080c09041103030d1d0c150708070f050a0201 78
    0x28103030307442c80104965200000c0a20888a500d04003a92140c0e80c8401000718035030380380241300c0b01e80c24040c1181c184140200741c2402140b003a000c8842c43d00200100b0b5017a4061551020013003441c020000d0054280589902c1d40280b1601c01d44407000b00b070300c4640013802400350401e0000396840d42d050280840d14810140344404001307410141004590740c8030040d02c40c0e094000c0c20103840d50018441000d0810000141e4044000203025540d01c0f032400030750700d40152a040c1c000488044411740c01c00418820f80c1e24403280038049005540e0b0b03020034006442000c0702c11160315940c401c000100080188160005540706584e1860150300d00810041690b0028180314460307401c00c2c00c1040707060800103207580015402d0700d114180b540d0340d0034219408603505000940601001402c14034540640d880507449001007031071005000c1201e41072586e5080703c80400780c0c00800c900d200b440310642240103440e5080c414160103180c001107960300341c007a1504803022900c1d030b4440c00c524403c641c1c000114082c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 826741205 1250 826739955 826739981
    0x2a020706081012062c1507091401080c04092d1b080c07020604030b100f0b22120503040f060305060a0b03060315090a03081305070b0a030207020406150201 68
    0xd049410700448241111243da030041c80305581e10580b1111000c0294842899144101d0301c0b20a182007030009134a030305c203240350003001c0400c91001500d268042c0b840c0d0700a40d00306074803080041d0000c1c40152001e000240c0301284001c0d0911000030009000e0190a43c0c0d00b404004c00d5a042884000720342e207a5030103d9503e139405080c84c02064040d002041000500383c5103103040c001c01e40b07485480c041c00784a40f413000b94000c440001c3c04028030005100325405a1aa00910302d80da80d03603200c4000c40c0c00742c00d018034a0002000c1011486d1130075518070041e10000011000f0102503510000034017400600c400c125440c2e04085410455000755a010070010451420140400e103060340c001140d4400c60b003e28200003001001080031a2800c21803076540c02a07072001c034078a41c2070403c01e450b40c8041030070049002441203000100c0400c00038885010b4030b070380710740104012800c1205c426940c4e004070b0243c404040d403c0c032009003d40c1d901c0c041c810041c42c00000c1455080d8480320007d09485810303490301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 826742455 1250 826741205 826741231
    0x30e03010c1d0301050f0c0a2721080a18050307170f010615050f0d060605180307050d021c0b0c07030e0619051602130f0501081b042a02070608 63
    0x10250310303c1d19041caa401030340100020380e900c1d811741007600c0e607035200b200007448a2080c442d014605a010201d4500342c40725029600101000b81200c034010b00142b04005041c2c07203090001c003a00c0c078018140c0b500803203442c1d82d0000d032407512600030034500800b6a0101111041180c61131505640c18410011b07401180f000034000b15040c20660340c02180010090010010b000804a201c406188203440d2140c101c1070050002e81d646480040076500301d9401110b107031340d01c03940910403071500242d09401c4030405410900781c0000c1d50200160f00c100c4e8103c41c1252013800c90050300040e24100403600c2400960070682d250451410011f023141c4400f04003600030703041044ac0030b000c044410882407800d18a1b02c0c0c011780d280140c0080588503c0032020007500b081400c42d6060058100307420007141d0300c00700a010019680e031040e4a40d40c802c003048408002d0340190740c000780ca07820590003000129446500502c2c035210281d440358014011103180c80016000000b0a00007140e10943c01380d0810001580b50b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 826743705 1250 826742455 826742461
    0x60a091205040f050d0f0b0a1505040608060a1112090d1d031f0f1517010b0d0f030203120a051b04230a0504020705210f0d09030e03010c1d030105 64
    0x3c03940c0383c0c0c0a4010715200f00001c0b260700040111075a21008182d41c440501d480c00e050014201000d0000c07411110b2500082d420046050704040c0302c0e500450b404138004100c692204403c80c07000740704d042c4030034065a20070404c020041200058082c01160030341c00400f005210003400818020905c1c80007002081c001e40d0a02c401c6d40d000411040707020700780f928801016465502c500040611018800c04a82070000c8440640304910355071085a90603907084050711308074081c0c5400c076110314000682c0003001001c0e9001181c0003480f850301181c42401200e14100500e03070400b580050031940c0841c0c02e52501c00f0800803103410300b4010900b002e6007040d035040c41e08000070442107d000000744d4034507441e14410f41001d640c0302c6484c480100700290086540d15154140316440740990b0384460406404148480d4031011502c1c101e841c000e0608a200d400c21419041c0346c1c000d001551015404c0200f045036080d61580c083c0b1914038002007a4907015106052010344844900c41c088200d03210764504010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 826744955 1250 826743705 826743719
    0x4030b0712021606020a0903020306090c04051005060714160e06030c040c021f090c06050301080d08250e1305061e06090103050603030f0409020d050c0a0e130608060a09120504 77
    0x200b884003a41c001e9015881d005542421511042240e00180d4541b02f0b100901c00d0454000c200d441c96180d00351000d000654580c04070a940c6201d5100755600274404004403400300d01d03255101c071900c20307810099030080d590007000141030503016001460399401174030601610f49804c10031480030010640e01480300c080480d03c01380d10b42c15103155803805000d56001e580480d40e4950300c0209401e600c0b665406c5036a46851005150b50800d0040c90560721404031500d0501d03000e80c074680e03c40e41071012260342000c070001e0820722107036400210b8414403030322480843c025a1074240f000200c4c0705002c0006120b280c003504006d03211b62200300010035000b0040a0880c00d856580403201001c03000c0c00c0c003140540311040864038500c903841000c0001c0501007400301d02088d40c2c1d00281950340c65040148003a46070304031400c0d1240329090744400850a080c00c41c0d551410003010b041c10007502010700054181d55115418108030086501c2120290703106040300030003072039458039408c8800c0d51418900b064140303e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 826746205 1250 826744955 826744987
    0xf051c0f18030201031e0e010c02010b030708060106050a051b0a020a060e0d170903100903080f06030a03080c1c020405040510050d060504170703023406032004030b071202 75
    0x800390406072540d90303100e00d02010b000d0402c01b052041c1d10410085412289680c004c152103014034005500300020768000b0f1400240f07000c00d45001a016120303903480e1290541e084d9000c510a030051003030078004048003c00003091320341d0719001c000180102101500c10032100b00309a42101c02485481c902110300c0780c581d0a90004101d034044400b5200d040040d080c02c0e00c81c040c07291480c2d40762180390700001c40740741c1c0c6402030036459100e500ca014181c0c0301c2034105514010200c07001601640418010008244544100d58005224603601803610380796a0030400e01c50b1400150340c0201e90000b800300086d0815104e10382c0d00452044604208508080000d580c420011401420140d101c4c03011034103111305580b04d03410704804412002c1e540d940c2c5290207900c8200c200303d80b000a400030309003040403905010010900c520100b00e04010030342804c4060b40105110780500b82d42e12604800f965840781024000c0c00914050f034041e0715203203803000d0300034440802814074a1000b801070100703200c82c0f10121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 826747455 1250 826746205 826746209
    0x60813171306180512070e180d1b0f0f082a061015050405041e0b0102060402011209050a020904050c09010f03030507080906210a0c080618040f051c0f18 67
    0x42c1d40c1708051022607189482d21815403c40c000ca200740d041801514006220700400c070360540415103c41b4050580d041d035004800326840d0362401c4e600140f03c8001000d542e000e14076140310700816101c00b1021b440762003850300720800c00c1d00c1801ca40015a82d40b03516602c540340c2c060709070070300610403454114066000341410b0b114141c611102e15682080710790244096501600c4090400c001c8955411908551504010742e41c00f1070314502440341e1541d51010862130b101e00e4068503880114a0002001c1c0c004000f141c2d025a01c130301400d035103000140d9400090300e014501510050108192040403c08000d0060344820150030700102c040000030b81010560303e4a03a000810306848220600c04034050b8401c15516180da41c602c40c0c445040701480031001806021184001c028041d41c040055030480c0055a01c6980700007414501d0701881e0740001074507401407092800031003840c504c1c3d64141c6040040120080302810010784d8012495011840d001104003c1c03808806101c521040160a40101c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 826748705 1250 826747455 826747459
    0x1d0f10110a0c170c0a0303051f031407031401020c0606060715110f0c010c140403020a03060203060301090f030305150a0e0f0406061505070204110a0203040608131713061805 76
    0x901d90081402100d40030030012005495155a664a4804c055505d8940ea50400c1300868941800300f01000d5041d81c101c050301d1940c0884240c40c80c110f40781c60700300340d100c2c43c04111548650200440043e14804008030410400f400240c0c403520440090360511100038040340c0100c0c420300070800850b80110740f400a49028040006148043d50810061032150202c0041100e20018800b5500a41540031500c0b400c0a6941c00010451013000882c1501c030300d120203540950840c0d801e03c0420707882d500454005400600005080103555603107a00c43d000d000c400d4000c680e03030760704000300e4410310030050581c0502100c00700c4041e414414001d60301d9202070521841c0c880c00e4400902040f20550043c0080c0c03c048000400c0f04124000042c0039602ca20340c12070050781401520044601c00c00155032402055401640c01e0908207441260301c1c100007028000c8006440843c01e000c83c0c0e0b140004c06a080c40e859010740d07942c10103400d0842c0011940e014500b0000f69180c070044140400650209485007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 826749955 1250 826748705 826748717
    0x703120515150c010605040203061815040905070f0b09060a0c050c091018020a23070f0c2322020c0709020415080402030c0d061d0f10110a 61
    0x11102070040c0011854101c035040744501c440b11540880000c0642102c030781d00340081c0309090701c50041c84143c0c082651407542001d180d140440e6404800c0b40030960110181d10401c900031581000141641c5115900b5601034011000901c070700002c0394881c0020b8240301d140d00d440c00146001280300c0c0e12421100b40c040010840388141041800e01c141400c0c508011302208643c20041c4407a00d40520721300c00c6000300c03000c00101c1c0c1c00310000340c02030365140101c0761140143e4034884151220450010380b00300015940810259000410418032103294501071a08110740c1c40c1020f040341c400400d003400c2001c6e4044c09a9800c2e030b4030b80e620060b40c803181365034500e244070b204841d2400c07a001c1e000d5000e9011090080440c080342401c0e19902400485460031310710741c01481c1a540075502140c00352000b940503005126904e9003400c01d00b4604041a1060700c0c001025030b00050034428140109006000681280408603c1d0b500100b01114a0410703900c010084101d1480c01d00340d1034400e41c0441c20a00003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 826751205 1250 826749955 826749961
    0x1e01090e0f0d0302090a0819081605030f070308010b120c09062106011701030803010b1e070302070603060b090d02090a06080604080405400608100504050d030207031205 74
    0x4003800407034000c040c0c680c100d03864405207040c09000b039003040c601903018110340c00c0001190800051800e080910100520014858907240c1030204da200030640340c56241c81641b0100010402c1000345220400450220f8540b011450004c0400f01c0603481034034008000e0200030044080044900d8103d5808199140e40d1180100402d51b03601132038818070300107907007803601040c904040102c0d588101000d90703501d0000c0c844100e02d081d07207100030701000e004450140018062a040e00c0020700381c0d0407020700c0d0820b40c4926001401c195501c071000c100d0040c0c02041c030402c65150980500001f40400c0b08005040914040110303d50300507240002c3d224500c1140810140100c0390b10a03405802e6007010781301146000e040c070548951161003544c0c09102c128000d04800c080c159070903183d805104000859500480d0a0308410400072032607100074542d91840001d20103000c01c072504640e00c12042c08111440c26040660919416400d02c0007070500402002000a03170004d4011a03112080d040016692 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 826752455 1250 826751205 826751231
    0x801080c09070e210c030109082506020c1b040c0f1d0405040c08060c030105090613150603060602070b0f030c0d230610090e060103020c100203040c0503061e0109 71
    0xc84404040f5070401c43c00001881001c214903c48a4a070320002c0483d904a205001410b00b00c0d0300340c0602a1692070184083c40424000c60031414102c4410050071004208a4a03894201e038003070800d510302540403014005591015501033012140700700c0701005000c58828001d4960321412004000b001100924404a12410070680300400380c00f0300100440c0c035252800070b1540c2060301800182e4445c520010b069580000c0440b4103940c2c010b4011380e01c80e29890184190000a02c1403d18426200c44005090140050b00e07080202595900070482601d4080080c0c1000800d030030000082c00108050034000840408494001040000090741c0c2c1610855000040c026144500a249890340762a81c082803146071440c0100000c8441c0c080d080c0ca1040c0075075046c005403040d03c4205450030002013143d03009130301074000c0b0050381c0d040d907000c240c1e83c0160000300d85c03003160704a6100c084260705000714202000b10070362007620140a0780000001c83c2d01e10f0920f080510816004a44448550f6000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 826753705 1250 826752455 826752467
    0xb09120a0f050f0f0406090b130302040906020c0604030f1101060b03060906120d020a06110c07060305090703140a030215131704081b0f04180b091603120e010801080c0907 75
    0x903c00d4800100e8468030030207099a078560140c401d07000000c034400720100c3c1a00c40c03041100e03401c41041c544040d00c00c0c40c56003400090240c584003640c4007542404409084207041c400d8500c0b880c401d036108000c20110440240036900c0100c0ca0b2589a0303d4010306000c510364440071243c01030411542e01d0925520000003481195036100c0004260003aa6a00088590001400d89001e48900300503c000d007903408100700c50340180360385c00c0c8107944000410828a800b9520064100e02d0000541c3e80c80b0342c4a861700500030716864050300d8242d006d0b0001070181581405445103180c21090141c00c0c42c06d00581c003580104da4200d02404143c1c408501c1490100460708036801807540b00180c942d20303000c02c0046070700070b680b041d60350f8000c501007004001c2d03610301841407510240b4020b0b9180054540750700e40c000d107401d0060a46003648100014020300040c1c3c0c2501c10015807003051682281001134000030404240960b03000e05101104006005409002c01d4000941d40280c07101c503004e035180c803004c8601d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 826754955 1250 826753705 826753717
    0x61507050d05030a0b0d0b0406201209010f0509071401090e09100c112a0a0b0a020d170106081023041b17100503190b09120a0f05 57
    0x9105045080d81d0164210300654031900401030300b0041520b0380000c0c4907400b40c21600c010003150744800050009034143c0d11020145110a40240c2d9a0307800301481101c690001c4044812481c1d810100540c1403024000d0010306c1000d68424032807810031001d8907aa40c42c1c180511500c2c4458102e40a10f00c0e4812082300300100307000c084c14011401d11002c1592030f00d81d03000100010750304246408851501074112000d00000c1680101000d043c44c0b008103500189600d01c2078031040e00e0006000310341d990b00c1c0448018080128401d656070103241006031a01d105104440140420640101300700420240218119803181c00c2c0b0403685d69400000b03c903010040d402907100100c05134450360041d100604d504a003100e068908000807411078003502040703246081e54000050401010f01601a141b0421f02e8202a0034400c031401161910b00081c1801e650011081150070010800400c0c072002e803034000e030000ca082c005414907141c1952070707000501c50f00000ba000d000848846120483c414004c8580c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 826756205 1250 826754955 826754963
    0x2150d02030103140c0a06090603020c03130e010e0f060108040209070302160503091311030a0c0c050624010c110405100e010e0708061c0b0601050721020d020a0b061507 74
    0x50340350703168505071803480c0c0003e84c54212880303542030b00c03951810050380c1b190a560290700d4004190b840e1840890180d480000f0840031800288100580700e01c40203901030140102c001e07481459810696103200300c5000815142200d01b4860511510f030b60080c020b0750700160151001c00d4980e5a1507000d5000c0c1c4112054049100e010840c80c8050100200281c000d0600441e8030000201c21150380d141a60b69075010070751800b10400104000701c540f5440381c030880305c880c102402010066120181401c500f15052941c074007186070a02d000120302500c900721540c0900304146101c0c0c158513141c64041009810901460761200411070322031072041480300401c141e6000e148150385509164407590400c0ea14100411084c1c0080751aa24151085072030910740484030f156140c00e079469554144001904441c1400802c005410104104281e1400c801200c012102c071460b00600d4020b2400e43d140710007000b19000446c03104009500180c4980d08000d040714407694016104c803082c0810b10684100034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 826757455 1250 826756205 826756207
    0x6070f050a11040b010507021c05251409010b0318010209031b040507080405151015050c0706021f0e12070b04050d080705040323010c0509041d070302150d02 69
    0x4070800c82c540c03415000c2450155404d0000d106900b006403014001e000f0000d40c0b1032500030300c080400d41c80d94900309a4501030402c47e90503004014070170800e2084405c1142001c1e01881d030601c071450f0341004c0c0303030301404095500400f590302d40742164686020107444800541200c44007860000c5094054854072800201a902d0390703021007203d0f0f03284440810b11103001c0c504010004e2401c2c0d025800091180e5040300180001c1c031141400c007060100c008005c0000001c410700040b41241d08402d40c9070aa9440d526116913450450034018075041042d4095400c5500c071000c1c035540b604c1c5440c07000c8410620401c0101e2900e96101030281001e800316065004281d01040e01b0090104620070b20380228012400d41d489960308000407181c004088072580e0115408110820010f001c141010340341203000d00082280f0310050381181d00b59100e105a030000140040b8030042d40d441c2c284107140592071207003c0c40ca035200082400075111142840003030b2003850380c040040c58100d41d0104039112004969011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 826758705 1250 826757455 826757473
    0x51206121605010836032203060f0c0203090d0206120c09090903030402010f0e01180b0a030b0d200a0e0f041703060f10090f0311010206070203070f0206070f05 70
    0x4070994084078403440340050415808240b5440180d01c3d4100300e2403003c5003141115614041c10f280c0c0182c409180c04c0c2d1480200524001c41d2800f10f0b50071541002852154445842d505011054407200078009540310310340b802c898040c540020464070003030020340f1128402510f60000503094080c008240c0348d1000c0742410440c00c454030f50010400011f00f156a0811354a4010616903280000c480003408609403541b0751003c0b44c01070a4800046105241905904000400440103a2a2030f403000340c5d0340402050700302d0f10720340600604a4400c0142e03015040725426444011000e41100c0001401d101010303007044040c3c8410420b4030282265907d602c0180c200003020680d0b02034103c1c2c003a20248100d01c86010102e070f104080701c2c00340000a02101ca41d0000d0360403c9001c0b201c41d1480f10030b0000794600001c040300f45c44210740c002c0d4000c0341d03010501c0001d807001a051103801008101150820401000000c8903055041c02e186d13010b490140d224461468008040c0c40e0548000d4480e00c140307202 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 826759955 1250 826758705 826758733
    0x114120f010f0e040507031106042303010e160b03091e0a05010b060a1d03010e0d0203180306070909022a0d0e0a14060f071a0114060a05120612 63
    0x34904903000030544640140d0350b85110450728205a0b0000c04503040410100041510241d031420060780040080d071900344da40d480080700300400c0700c284101120704030501405290070322814a02c0044c100240c0380b15641042c504010f22028007a1102007407020000c144140405c002e032141c207036603c41c1c6940c101c2c8903480f0302c0d2b550b4240740d140c01c41c1c0d250700b04614003081d810b14000b80d80c043d010549403609028000180303180c1004200f2011074240d0360b80c80c16046c0c0342034100f081c900582410740186036542d03400b00d90b003020945803980990007030b80001c060010303099200c1c0110702220028a001a01c2d0084041d22001c5032555142055880c01c01044640d009000411000d00d009038a881c0c00c1d415583c030100744440201e5a21410f07400514142c1c00103c14100b01008001c040b0400400354a0b200140c3c1e502c07045840c00c01c0c0140040043c401c0184004000420f1160001408a03180c80c00d201880303000501e64826100e10364903440601010130110f48840e0710301d0f04214102e034250740c1c1e03550100c45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 826761205 1250 826759955 826759981
    0xc04060f0905161202180919060909020d0201120b0907030e0f0a02010e0f040204050d06051602060c030112050c04050103210302090a150c0c06030b040506060901090302011412 77
    0x501c015189071101003802240d040d494055107107516100c103a80d40041c0800c090017034000c2d00c010841300c076140c009101380350b86034509944104011004080c540074518400741c00c40e04940c1143d42810710301104d44001da520b121030b0307110086d8240303440b04614065000c0800a007014400701504200140e0030320080f1074050b04103400e1120b0311412101846124101d466030b520035540040d0205801e20040c41143c10114210780050001a00152509549001189060b000b212041c0c0341540d80e40700b03010f030202c080421203800015910051140d420000300070034061006115285002c200314a5650410100f4050100d070014020020031440d1f949062405110360700d280c2c58802e501884005403002e6009100751440014060040407407581440344203400342d02c0050305103050217460006100052651540c80d0060302456401240766095401440300b0303070350040c0141e44610428015520141d034443d00d4141101c0d02440c00d40d081400030481e00d0b68502c64581140d0381000c42d401001030007001d1003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 826762455 1250 826761205 826761209
    0x5211c0e0f0d030f03051e0c040e010807140603041103060f010504050c0f03010902030606130611010606141204150c032309100b0a0e15040e030c1009050c04060f 71
    0x1444000103041c0000801c0700c000c910358801404980001ca07100c41c1c0c2c620075804940d20a11460285283d0208010103440c006421201e0305440000014240010803503002a41d00501314000109a001c0c24415203a100105002d00103000b00000f00000e418032026425503942c1e030501074182c0d50141840e4202a0007900c003405543e0240307082001007004410460111a4988820701c2042c0c11640be01102c940607500191110358407050034000300c540c14189040d01c030000c01c03080e200d80041c201000c500600303403040c80d030100d404d00807050b17121481284110b040740c0b0301d600c0e5295800820754492170804c450141c1c1200700425a803070107200e6001507400d07030300c014850304031402c4c51406900c003142100940c1004490664031904406a544580856500800d8441000070f202c12500303030b1561005285000b04a450000030402d81c05110ba441c10f1a100740703120102410044c600d0801030000c244ea0307031b040e00040b8040055540002e0001c0c800140170125007110000c005200c0c40b5036400c54289040054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 826763705 1250 826762455 826762459
    0x18030b190c0f0c1e0203120a02060606030601050403020f13150501080f1e07050c0102360108190605030d0e090a05041a09100f05071101020405211c0e 66
    0x70030103940382940a80c0d40341c01058456503501d0030f00200340d43c2c1c0c006808401c0a0100c140040c0310211030069070284030a400c0c007002c10000c15203410321020300a14010000e00414082c9008000b4016243da01408640a51381c041e10a00c80740f0381c0c480d010440312021420245001490a002c849100195050100880328240d07100c3c02a07859410b04442e943d6000d48208031400360041d901c00070b0040305020658404460b003403050904503140c03000c2e030036070788081c001801c0010b014090001f100c240320001d0740b800001c11941d00741da40d407010000e4682c00c8040c000200e05001e21081503000c0f078058011502404016050700e010207141d1401502d100740031002c9511031522a40018104c1c001d074400d0910641e003100c0c2200e8007180354160352043d0000a0100707a42d50294840c2440d0503603080c000d10218080084002405280180e0000c08403900001e801b83c1a9004001c10481070f03440d10745401c4103600c0c000e00e400a00c0034501c178803458612003450480301d00800007006540f0740d40081c0280010441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 826764955 1250 826763705 826763711
    0x3070303020717150a051306051005010f0e01020607031e06240c0b040f11030105070c120207061227050a1704080d0c06060807030f0615050102070618030b19 69
    0x280d101c5a0340c1392a1403440120420340354800080d185140e9070003840c0c0288088800b50008440c13515100d0a6450440b070349094401e00000800c0a0750b409102d05070031140500e099481c1000b01e0000075200d4001400a00816132202d01400c52503c141e80c900740c110119030020403003075545800c14021a07420102a52041c08540380ca41c80660045042402007603201c40700d5506c6a655550703800c0c00b04c3d1103000540e070207200004520920b44003445104d01074605a02c1d405009801403030624007100c008111001103410194041002c9500f150304404030448014020404180700302e00421851000701d141c0f04880400f60784101809404595100c11600842d1030180b4aa40b49031400c01e03500c26417043c680c540d844000704c0d04007184200c0540803448d10801022030065514a0740c185440c0040d041507401c1210361489608100b194416800110400c58260034518540f10000c3c5d22000f0f240f04140c20702181982c0c4080049400041d0310107140c0c400d85812450030a02c002c46000400c02400d100e901d4070b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 826766205 1250 826764955 826764989
    0xa030302012007020120010b04060806060a090e0717210309061b030f1b0c15180a1b0e0703020415030501051c11090109020a230f0f09030703030207 65
    0x116801c100c400f169011b8480314400400841e08007005030030100c06807415541c0701c510711100d81d00c9004100080c00f0240050900b42082c1c41000f1186010b540100141840e101d000c512240f00400c6e0a405c1740c100000c0110343d034511030f0f10740b424a00c0e5408065820700401c440e0103420118840554000c200007411034000d50790b07144200e01d100c40c4000d602190300b101400003541d508001c0c002c05500c206140780d40c840c03266480482e0401900128402d13411074100e9018010384240b40c1c00455401012541182180304813608450b41701d900c3c070b12002e0101c3c0100c901e00c005d4110b074103003410001c7c40b51030800c0c0000c0c9030a400080003900240140c0740c6400440000d100c1c0e0700e200e40070301c030f0690b00c0c000c0035842805080c8105454059662400b00d0340031000f4080b9904503984c2070002c0e4000c010700c441c0517070b5030034806500070b2100c29124000c1c00090310038490003010340c0082d001d4640f81042134001315a40c01c8001c5814400707009032004c07541e040c4a2110003000b0503901044000071249000200c0010710 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 826767455 1250 826766205 826766261
    0x10f181806140f010e0c09030a0f050d02010b04150b0a140d0c0e0105070c140f2206050a0e070f05070b04110a084e040e0c03040506070e0a050a03030201 67
    0xe0b10a00c04d2101134441744010407225242c1d07a005040c03801004084440f481e40b01d40c1d03407400d03000341c510b0182e819410482e21002a1038080c00783c9405610304035000c00c2400c05401c440302c4410311a0248801220000c10700e01c03100d41c014000e00b8000aa1191040e4a0b06202ca0308400506412483c1400040400c85484510350168080e00c060340d074894501107980c0d04020850411581c4440708d139074085d12200c2c02c0101600c0d04122081580079840003d0300c0950303a110240280c400607440740303006081d0110101700320303c11211036540003055440c00342c0d4100d00401046419000e02ca10181064011001748410420340c0f020b0300303c1008064902ca0101130380e82102c030341c5620107142c892800c00e6203503448641900006949040c900c407c031100e1001c0808031158002c10240071782c4442841e0307000240034404203004031440c40c2d00801d0b40c8407291440c50207030f40d03140e140c0e5000342c0110107000000100c000f15a940c0c4c0081e4010781000b400b044545542c0e07003070081c06814943c1c4200710b9070f145403810303032659 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 826768705 1250 826767455 826767481
    0xe06251a19090807061a0d050c0f1503010612110c0604021023030c040807121b1202010c060b0303030c1201050307030507150201061a0c0c01020105010f18180614 71
    0x8030f0340020525050a00c0b035260200941991000b01070340d0040c101e040180365444940036052035000d0401401202c41070300510860201d80344107a4480e0401501c402c1908402400312030555a003854100502600f003221400078142c1c24209020702500415049025040002d102b44100c1c02210a00051103510005541c100c081400c2d0f170700594814000303240220300c940000c5801c0000800c02d036103000c0e550414503040c41c00031381020404411001d18a401d1003050031035110504a141a8184010700d06105d201300c4500d00d500080c1400704584980c000c0c0725495100200c690b501405583d5a4540784c03040e12400e6020569901c00081d8500001c51981000182c01c403c0e03a51100c01481c00d6828200903106400c81003448504541d20b421020403840d04018a064030307403001e03c2006803520303280000f80d42042905400c00d0304582c980b000410034403245030703004400c0b181144859541519041064006048120420110000c1c030b211340d1010031032540d1042a90410b28079800240392608640e400003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 826769955 1250 826768705 826768721
    0x50c12030a1409100305090d1d01031812020705120f06010608100f0308040e070206160e1305010b0301051008162006040302060708070e06251a19 64
    0x1540140056000d40c2c2c09182c5007010316107600c2c481d0741440e202c040003030820500c584003040082d442e0700501580746070422130303062003800c981010340026010100c80e0700d040240661303840c10191034003141502000a0181070703d11503084500c40e81030741164000a03543c0d40701c40c841d0703d000e48024458010a200b0214110110010300350207001e180e40fa00b4000c41d0035440252801101440d03203030001940e40444141940150720981a4588940c5008401c008031807004026030305540240007013109070072580001140800760340c1880084d0a41500100320002d1881000c0e2212038170f800b00229400b01c4d000045c50484004595003400551400421200d08009880910030300d6a418410604c490241c4000c541c40b10741059141442d040314103c882c913040040e6001c4d0b004d600032100f8000356903440001d05500c41c40c079060511344e568a907008600c5a100342c507808406c2e0010303141030032030f21050b5400201d042034204900360070300c0d24000a00c109042c0203460100c0c503046c034000c0c000580941c500078150307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 826771205 1250 826769955 826769989
    0x20a0209072c0a08120f07030905060a09151b380108010b1207060e15040303051206041b1101180c0602061e01031e06020a02030705071221020106031e050c 68
    0x806c00e44c0345d044904a541080c03608038141b204c50074000c5030700d4462101926110003180e4030310001528004c0c47d0303002e03000c20400000c10030141070611504002c007014000c80ea1980203e0041080900384800025002480c584014444a480d2900914181400d06d40d060382c044000810030780902d00200001d582504110740c8071504884820000340d03004c1e080c00d00d04088041c00030745030b981807004600030030b500503081200401c0780030510078a080550083d241d0700c020143c030100040280b912070385980801e28a001d10030048444031620130600d0a4018007894440c00c544da540300b000b02d00c0c2c420440030503801400011720621000412191f0b0b2851080060481c0d0350030a02c02d6402c40d00c80124085418020440d02040d0520000000e11184002c0c04607a126038051510703200240780480c00d00c0c5c5140d200111507807a042c0d41001155400d00c12208040010107000210140044180d002d001035030b00c007400c0343c80948009844018000c071034000c0035104178161060101294100316640c81059866a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 826772455 1250 826771205 826771207
    0x60e0619020a0602031816210f020405190506030a02010e10050405030f0705010f212703050d1d100c0c0c030b040c0b0a2a06050901020703020c0907020a0209072c0a0812 74
    0x403400b140c100c48c0d0a10070728054a040c1d01d0460894000c01d080d2038060b03600ea0041e60005c080c2c648502800d02c1215007001c800c60241010141540000b00321080c44c1b80150300c01e00303000387da080e0414050703402c03603000382009400d6404980945445540340c41052240f640410340e03c02500c80041c1c0308406140780c290283d0003c503d0310010703021540040c800a400407019424006402880c0e028103154100003030700c240d80c0d06660314450302d070316801c0e2000000d0740d8081005000b121072101c84046008001e8600d00080001c3c0aa12001c08407114844141e02030011819032002205000780001054841c60194100205a9030b0318202d10865100b1880a440001c4105042420000c1b08220043c6018600e511952000c4610780301d031002c82d0303c1a9000c01c00ca030f41c0001c0b080201501480341217000c2408850b0381001e483e101c1400b03902c414110701c000b40300f001608001010507000e60f80311000408208500041204000c2440f080038118442e440e1203804159000a02c540c0b00185400c5e610204e00d0700302e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 826773705 1250 826772455 826772489
    0x9010207050f0a2001111519060303050414061315030506090c091e10030623090a0c03021603030e0c12213001060e0619020a0602031816 60
    0x407895148640c2224100204420a80036101c070411200000c0710002e160304c4801d0402030503d5a083d03a03230030040d403d86410402c1c2000483c0c0c001d02514211543e607810401c02100f001e0000b92540b0a03901039240e00c036070344000403034618468245400441c296171000c01c03041d240c3c1d004000070342c1005c58007103e10341800c00c03a880150500030144441001540c0303085011441520010f50040c69035044540020794450040004602c480d9160380500442c4c07500d20f40c000b90420110392102c60042035500303000d0311003400465041c400c0c0d04070303410800b0030000c2ca4021040c1e441d004019143d1030f10f1210013841410300d481203074a811404103008094500c0140380060220040c1c8a00141c402a46080c00c1c90500150b90400c17404200320b4030120140c50032400461030200700c8403102006070040d10400c02000f2800303101752280360855038022100d1080403595414920100c1c5000d03526070004014a0000c014000f07071002402c0c1e0103c0001c409415107100d4407032003001c00080c000d40d105421005611540c0c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 826774955 1250 826773705 826773743
    0x1f18020d02100c020301180528030c05071806031a01060f0c02010219140601080102130303051804060b0d0c14120c1308031b0a11040c1709010207050f0a 67
    0xc0b2019603109400c243c29800e0594000901b1142d1190f1310400c51001e0361125010000c00344600c0c07182c42101a80003e0004140840c041080c05a620080038012b80314072000034030408000102c020401c1c080101c62000340c50080501500d260b102c107c580746000c01c03080301000c002d03444041c1a0b480554030300d00c12108040085a0000d505602681540240d41d0f510303440340c0403620101001402265050408110160414903046050340040b026034070500502208407424070705174040b290140b40c91910f55030445107900b00252000c0c07440d5485842d102c000280c0700010809040b18a00c0300d001003140142c0c50000396800050516120f00c0c6190802c41c0c0c07014000d8000078160041c10102006040071b50041020760341d010301381c12502d202e61000c86d0340301001c40c2d8001180040107850000d04041c070b0751a5142507015113940309281c8902c1d1110280c0302ea80d44100303244030113540d481c01041042e003080300c0c0d070314000c0d8002d00d0152a54024608001000440042d103200c501c0d0340701c0000c0c0750341551208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 826776205 1250 826774955 826774969
    0x71703240612010305010516080c09130b090403110f03040e0402131107060b0a0b09031509010f0c05040f0e04020916020102120103050d080f010807090911031f18020d02 74
    0x32500d901040501c50140c59410140e103090103584650000074031410524050052420301030110300812010f10b0400c5020144d98060703881b003100641d1801070383c20358201c0c4880038160202050b03800090907002c0100b0b15a00012007d040410701017070b500754504039841141c8030304c194055801428044404200181403100700300c1c000001c07054000494502c070040ca04425440030000b90341c51910b64031800c1c841c0c545148410003c05900b550a8500940200403944400150345030f2036103030044e40c00040c0b1145081d002000308910201e810814446200e0000d03000350024020003080c0c3c12041800715240c84d400705050b0103107400410354440703645d0b040c0c0000c01c10155090b4070300442d5000e01920083c4644002403e01844c81507026010440d0700d07080007000400700410480c800308000004102410020640e201038848409000c1a180144d04203003100045a8200035013501c42c0b401c008480300080790751102e00e1165100700b805000b114406580e4480d400e018040e501c64044144c180c01464850 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 826777455 1250 826776205 826776271
    0x4050d180f050f06090613030507080106030b06041a0a060306090b09270705190602010b0108160e2206050a060309050606010e1903050102040626040b0601021203070203071703 77
    0x800c1c51740f421940e0f4012840d241c01003d0b60740000c081480b01841040b00c2030000401810b1924002c1151500d0342d1240c0f10314510207441207001325501c80b50300d040074001d04224901c3d200050705001d4550750340c1d0700060040115101d0001414074043d6104442c8c60060000c5025100450007a4007440c01310000c00c0e100045104442c0b8a80315007140041c603921600354042c0419040b0441c1420180741c41c1c0c0103401c0d9a0390350501410441000200450750010252a0b03035030784c0c4e0070310700640c1c2844004040340340d034800b90284841820840ca42c180703a0121940014050350030540e10a5030183da036800640c01d90b00c2c1c3c010014400c2e084207000625a510549800707605600c001c011101c0088035004214070541507400035503031650009810300000d44c000500f51160f0014000c10b01f00d21040b000b20782003290019000a207410f14500204a65a10801103c12040103d080c0c0503602d00344800c019507640d1011001722482c03130f40c1c0200c0703070340410034030003030b20f22411070741c0c140f19001d100320400403010030780354 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 826778705 1250 826777455 826777459
    0x1a0a05040801050c041d10170c03010f020c0c1c060b041b1e05040b03040b0403020a020603010e0415141308130617010e0c0703121404050d180f050f 65
    0xd010001d0064024081c003400303204031031080f40d652400e08000b492a02003154035100b5541c00741040c880c0704c01c040d401c00030840701c825494100f036443c2100c50b142420090030300329034150b0a299502e4a00e11260b801403080c00e21007800c40c0c0c005d523400d0b414410148050b00e03d072269540b05101c84030128155400110003440300910000354641d10101d0244110300448032a0001202621038040360081841500a07061003424506d080074609541c81e0308500c00108000c16000c034540100d420940208500c076581c40e8009c19681c3c996840d500c0c04c001e8442c00312821754442d9503851034020b22020900c90a0300d00455125101c100b686c0c0c64801503181d040030314044400481c02c10800c2c40b09899604041d0150159942c3c0444038a15440c07015200d44060300551310000500080c442c0d40315405d81210840c50b8182410f140074040401e84c003000344001000103864103942800c2008000012a00700e109134699202c080f041d4808800c1010101c42e14040c01d2200b030041040cd0280e071038034002c0040341d4000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 826779955 1250 826778705 826778707
    0x90b1c150f1407080a060e0c1c02040b0f0d1b050316020f0f0318041a100504090218040e0f0606061c0e0718020306180603011404080910091a0a05 64
    0xc040b124480d890129008800145030909203c042c80c640d018110040c640040c075810749080080014409208540c1c41c5260341403d104120005c01007034050340e00a000401103261030b0340d80828801c415910860402036280d240c55006100080b400b0125912801203983c1c02d0300b15a070b014415148000d0350b03080602503109818249d207145030704000c2070f8015243e100c00b40d174aa04d04801180062650201031510640c2840072135204004294281c0c18643c0d42101c2c501000401380400b5110703031050381c00101c071180c0006240f003412040412100b4001106030790400042d24500b09032600c546202d4030891140d000000440c0141c580a4041c12005d8400a0406802c1481c0c2c031440e0100c90504c1c2c4c6c0204a03400c0b0007020050650007107616003421401080035491860310000040c41c140026984440610320a40490000d403025806801070007841024030556040c036042542450704081030080c800c42110304121802d9100b041e5050440b4100031741d2103c82100070b8002281c5400010b102c408004e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 826781205 1250 826779955 826779971
    0x140d0b061c06090b0109080604080307140c0c09010e060a03030302030a0b0a1203090e0405120a090509090a140102070c0e1e100e0a0c0e12030f04090b1c150f 69
    0xc0c000c01441141c0c1da03807000004219141010400648261505040c1840749480b000c215515011501070352003a8840c00050f03403175650301802d480950344c000482142c1a40401c0c80908003000080c0d0009070181250740042e00da03038072540c0c8000c00c20b0444402d44c000d00c02805c00c01c00280030b034011316003083c0050303004201d62050a0205065950503446040c3c2d001105403000b041c5500010402c010b80001c0b48416003914207a11017a90b0346d051500d44200d4400300140d02003000b48031b200c03084003a02c0c00500110050828440b11035403004c1c4d80c2816245040070459108803200705200701c0d141c2c540d2003240d0340031240c9003202916080800514140307000c4050b007081080c02a2000000d449024111410f0600c107003001d0811032400802400078a000b40382034100740e003564000342d40c524403610031103c18440d00b5040c020107085015030030341108446004070300071a04488a030800e00c0795000c1900c240d0740d95218808960f440003110301c0301401100c00c2d1500041014120b8002c10411801050b000c14802 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 826782455 1250 826781205 826781227
    0x18090303020d1404060501062a020a090e0d08160e040515030105040c06030b01030b1513030c0603090302013e072916050d1a0418050607140d0b06 64
    0x10f100704003121200c0c481c01e0030031041185a10a80d40500824545000c0d51411001940300b140b0b500c078001070410080c071040c0f5003190b03207500c03080c0c010f000c048a0512101040c40d00c01680c43d01690301c844045210000042c036003181d040c1d02040000c440e5942d44c00249032000c1400000d100141c000c180c00400b52803105e115450074002c1d94000d038810404100c4641c58000020200c0b000811042c1c101341c00c02c900043c49075519407610b26420022851b190303592219001010074549140e0006003048404c01c07000501d02c2c0c01d64002070490b0f0094000348a4425940701034854840103120319503000f104042e010140d52170018440064030010840c2c42e00e001c1c3c554599525440640c1c2d103000d180180802c203180d4118180b9540c503040950303003405ca002220780950191a82c010444151012503586c03121801e4130050a400d180d6081000d0010007a01c00c0d01030b030005041c0103291042d01c0c60310a10010035401c0d4894002c03481020124a51030782480d10035032115000c1c151320411f10341d00031800d010240b104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 826783705 1250 826782455 826782461
    0xf090b0d11070503071505090a030305060d020d06050603210f0307021203010e071106150906042009270a090f080d0b040e0102091f090e041a0a02030118090303020d 72
    0x1e00500085032a17514601d0282080c00c4940b01c001001c0f4100b0382031203055500024108459985800c001c035480e5500780100d450003107020800b82d84461880300440038001180c2c81140280016000c2c0c0310b1480f00c001c0c09503003501c040e54480b01251070401850745440c6141c0003840d044800ca2050300d9031049284012452a0400e1f08264107007400d407020310410603000100c082c0040a44d101810461404090748000d401d00400c0e50390090005200195003640c551b40189900c0000d04c248000550b8900d1b0032840a4000301c1e0006e006410713440aa0719802d00b40a0b50042205001c0d41151841c1d540c08900700180031920030448426006a40540c0050740342009850500031161000a40720362500c208400c1e01c42c08400303003221b130744108900038041e200c1300352000c0181c0000d80540c0d0520341d551811904581c26501030300703120300c90300140410070903081c0d6202074140c012100c00c00e0319240d02240008a100a210300c00140ae2a2414041c211660b90414080349009003001800c00c07400d11040f40076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 826784955 1250 826783705 826783717
    0x31e0b010e060f01110a030f03020f0c01090b060a051c06140a02071b0f051203040f060c110108010b0901030e0c090a0b0915061605071d040b070f090b0d11 68
    0x2107251940800c04030382051815490402024078002881c000e007000d5142d200e0402d0b080280420100b08a4040d106003e9012100300e10403500d501030740e40040440140c02000303040d204490a9502301c0202c0c0e4130340340c5a201203003031340d05c002c1c028001c10141c031aa03d0720452180004684841c0c860b81d8881c1c0c072402d0405560b1280745810000741c0d07581c049140c000c43c540314180c4400c8202181c0a42403000203404d0310441c0958105840d01c800180c100291103181d8011359100d008249a41040803800c0760380680e07005142440341c11040340780c40c2c21000542c1d881c1024040d0300031100040c41040003e40c420340040b40c000020409451501d001e01c000306111101c221040628951103014880c0d842c105540e00542c4000c1444000003124483c41c00502039225100f50b00f0303001052000508240031040c49118020907414003141c05460703014040142d8000c00f201c060343d1594030880054002801a2400e1851b5409650340c0c805881c20110310381c0030b40c2c101648030708007260703149100f1044600450007846 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 826786205 1250 826784955 826784969
    0xf110a03090503060f01081002070f060e0102120108010209010503060f0409050f0d02070b090a060e0a08100644120c0f011b0c0f02010c08180108060d080301031e0b01 73
    0x1a000e402c1c00c05152034108080c0148603907480341c4004000101c008209a151084008005070340e0341468200108140b6078040050083d40c80e014194686020550003031441581042c000da8051f039903003080c94200e001e5007040c1401b06904200084071890001a0381c2c0c0341075001440010541455200e4034505941074030801141d504c46041384100d00c0c0c0400c81403004140140b45149429512004100c074040c0360710072803081c8407000c203000c0c0081c1d443c400c40d80080c0c905801129140d200072440344002c2c292a100e0310310042484603101205a2081c00b03c0c09107803c6000288a0a40450403c510000d0b0402a070042c94050071410800c2410800020614110060010050107461044250844405010040e413142068007100089134004005145181c0c000300c510614003018001601c2042d801d2000401501c40010410158815001d5a00e00c1ca2001e130f07102071103580c8a105014100400050141c0300501c00e100400004400500094000071209600c00311440070ba80c80081e00b45003070300090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 826787455 1250 826786205 826786217
    0x1403191d01180b1803060c090312030901020f121603060806270a030806040b010912030309030915030e0f03041d040c0506030c0d0e060c030c1315050a03110c07060f110a03 75
    0x700c038517080000726080340422509914040c80301000175901d001c2c542d6100701442000c00041e0502030b003035040d0790074103500102283d924500c2c00002640090216030f00d0300007200e002070241c840c501c01d12404003565000700090040b40c075081254140540d0008004041c25205a01c00e81c00741000d001280720b00e4420b4aa803421810140d00700025910f0403072100f41040491041046031050040d0b045007025014100018031200d2810121658500341c0c0090080c480200380d800c80702981584120220400c8500340e9454016058441d40c40348200e10801c2c0c4502048408100c40c003e032900310ba50000e108507194845640d594010039a0780d002114070907240000498003010158190165144400003800641030303030724104420070780b1404050510400d90201140000000d090401c0f01c4014102c5184203255100d44104020702e0b42e88140d4501c000a42061060645884084e0a445007116240050562141001030403500300c0f64921480e020030190800c0d4015074041440b400800c4d601950b200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 826788705 1250 826787455 826787497
    0x6020106090501080105281b0f030c030509030a0e0402091305090d0905030a06021615051e15040c140c0a0614040b0a0c0207031403191d01180b 63
    0x1411980140d0000c2005d034142000c0041c0425600324100c0e44402015400c82c0c18203840301d50400904801480280d050113502d41c000625800c800c5624030442560707014010100e02040c1202682c80c02d82e06d90340550300c284962032081d80500184145600064401030405e000c0c030002500e02216020708843c0159180284440d00c0002e104021402c415400c04510991a01340481d13030303c1c0c0000c08080c0ca143d5011444816240210041d0114a6040a01d10802442440c00080209402e0381c581c0750030704c02001d282040304e2111000d584a1008410300c1d001c007821034401d0101030415001c010042040c0c56001160910340303100039112981c00c8600034140e209030341c40d15608894800d01030210303180e00002003000046900c040b0a600c0307400b40001054024044000ba880e044058000400041a00140310318400c0c00101505c480070344003008040f003284410381076a60604050140550391600d0102c41c6d8154062455010465044051501d03440d40d15140340181c1d0b000301c08010f04071003c4e03486d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 826789955 1250 826788705 826788719
    0xf0103120908120d06030605070e01080a09030c060e010e060406022106091b0903030a121802010801031e1a04060b0f100311070c0815010902120126030406020106 71
    0x110500c601094102920841e0030901000c3d500e0421908080d140100040c1a09101c2000e800550040d940610305124900700101d0140c101d00384814554000f91101d800a08500894080c84214680540300c030004c451450316124003410343d80040c001599211000006040810000b4034481c900820005072280340f15045650030b80c5a0192070301c18440c0400c24040c0382da940d1403110303401100700128040c1c01c0302031396102003880c0940c02c1810b0f4107020108605400c0c40c1c100010340400c4900031780811003600380c61a246482d40142d080030740010f1030180140009480340c40b00c5c0351002a01e0310901c11b00a0076031341d04522882200704c9290701040d05c00034401000b80750b015050b81500c0440300d003404a0072a5020502044071480b8440400d84c990298503202e003920011251020b4121400700c1d011a102d82d40343e81d58400c02000002009205800020b0701c0c50a03100307507500ca9204404041c07036a4070f020f18158250b0103100b948c81400c660640c20b401c0c41e420400050001b42859000400c0703052600c50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 826791205 1250 826789955 826789973
    0x604050f0f0102180616080d02040527040201050a020106150f0206060901051003091502070b191e111b0c040c0203120c070c0902070f06050c2d120f0103 67
    0x1101101d140c0c01480559003030540c4140c4640003410540d65a900c03003c80c520030b031080350301100c0c01405d180740000d0643c8507a8050340050003501c0b006d0710400c500c5601d211406d4508240941038503c501e04200100d0015840385e0014507140d1003a100202d0500c0c0c6036490172030a26001510348010529004003010466014800c45902603004c640c03924040d8507100101300000e26030203d480800d0ba6450140742002100c040581c0c01c00c560420440d00d820030703890220b81412050700c006c2540401c41d40e440b4901310b40344c003e80d1380405401200c000ec0032000001d070006061500141082e080052101c81004c50408000c000355051100007012040800000d000840d5450f00c1c0c103034210740042200d0200c0d0a4540003580d00705410107a080e9403069542401c0c00c590000d900008501400014444240420096502045802044100842d0701c030171503500d409201d002002e8095003509929100b400f4940b51103100010100305400740b81c4400250748000c0300c8421030320030002e50403400044c014032002d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 826792455 1250 826791205 826791223
    0x60f03101803081f1503020c030301080c15071106030703061503060e070203090127170a0302011104051f05130330080a020304291506030115030b030f0604050f 70
    0x8111103a10513050341600313513990410701034521195281080d84290500c241d04484110180006030380d140c1d6100d030745c4507888080301d2448510074007450102c00e8464031001e003282d00b50b0b5030241014001d000d1540620400b0b800082c06042032607a01d1000092105c18900c041500c0c1d1901d80d00007807000d0070302c41c1d0480b80190240220781194801d001510050360048002c0c0c0c5d41c56186070708110180d01407842201d000c40a0b4200354000e15980c01000400c80c000a51203070b90f54426002800035411070302c0c60340c1e254003c40c45040d81c030010303d82843c206c0201c29400040030f8841c5243c841d00d4007440c284241d85242041e4000c4800503104503202641e01b80c0d8010f1100401c07a1366032004503060003840000c00c2118050070210640358000086010094410701901c0405041201c5d8282001e900417501d11203141156040140702031b103030461506e03252603021a81a1031309102a00629513035101c045008248248050750107214400134150790400402c4038a110324030803001069400c8280100c142070001c1c003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 826793705 1250 826792455 826792471
    0xf01060509060708160c08070f120210080a15082d150c070c0e1f0305030415092112020309090613140a0608071d060f0310180308 57
    0x140402816955a4801c580040750451346041d180c1e0b0042c052182d80c4207400c02e004103030b091000030020b0802000728881003165101c100380f41d00130b0f5440c07100000b02c180340500258007403800e41d98854031a002e0701003150054151400003450400b1602031a000c0d00c410f4000c11510b51003240302401d400201f5407240b1180c58495000b020304090b032155503581d06203c0e0914045a0080700c0000c48900742c403825980c7c0340f81c00201c1c55086550b900d41400000009407003071558000396000c6a03042882400c4d80c4021242d2190045151900c0e01111081802d8100040d20030007001d044001034468414660034264400c0802e01201107226103003a16100e50f0031800442175420074015103a01e940c56049940d402441078510800120042c01d03a10002c1801c2c0c6141204200080203200c5880c106070701c0202901c80420840e44525145c094002041907860340142d04240d061380001d803d400c00749044244088064204c94060800001210a517450705034500e6084100052400c1810b0384044240d420081e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 826794955 1250 826793705 826793707
    0x3020d0614030f0307150c051603050316080712050c09041b0305130c151704030801080712050304050f0f100507021e01051605031b101109100f020a0606030b0f010605 73
    0x1170b0b0faa4126460504400d82c203551952080d085a17114051000c80300c8030ba0084807240d038910b5551801400c66001a1050200d0990300c114552515024141d04c501411042d1100000d21070402914005800000c00a03800400148803000c0b203520340d8054120a1100581c02440b20748c6c0c0c0c1c00c0010100c443c01008811380ba0082c840010101d028141041c040d20111001c0c2e807910400303c00c09030f0300300c51014060600d0460b000304000602d03510908050503105008141c4031032a680300300c2c1503800148208080e001e40c104100c204010b241003001800e0301d130703030290090316600304000014810f034590b02ea0b02e01c04102e00049200840c6014000d4a00d003603840b800003a01c24400c0780000380b030381c040c02103d00c901c010b60701091810b001041056070307094200a82801c074044002c640c019280e80c10b03100412081c80c00c0c003590000d103030301880565040c440d001e041d0036482e001d8527000b00d420814100300c92040d030040d0310010021801030b0080c08040d500402c111855800d1000d10404500b00584c041c40030000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 826796205 1250 826794955 826794967
    0x171003020d06200301030f020102010f110a0e031c110607050711100309060c050408010b030d0e0118081b0f0f0102060703270320060c091003020d0614030f03 69
    0x1440d10085501c80d90400c00c00203074800e4440d1216148a00440c221101600110000040044400605800c44d20030ba001344503c6d0000701c2d2801c19101c0c1e80a5900700200b0621011038122300c2a8582140c0b40c400808032840044e45003455a03002034a0b502041c001903002c450760280410402075990807003140d01c1c080b850311030f0584400c2c400010101c07019104442029480140c40c0c401c4c0c0140311955002541040806d0010700d01510b50351041c03286aa25500f4411002106d11b8042030012802c0d5650700e42102d4004401c0045815a004920380e5001400d20000850305241c00c018080c1a1000b81c0348140080d4580e2040102c0d1040c1504680d00c0b50740200c0c10f2654a90380451043d41003151410085640315038a565810300d130110500d03180070003110703200b10300503d94404080c070780050b10000b0307800c900b0a0345030700b02d504c2d12001c64029003072000402039a80340d030410b05620110365807603280c01400e2034848040b56054a600c1c0d44240c1d4a85410600d04201d46414801d00c50b00c3d500100003185001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 826797455 1250 826796205 826796209
    0x160602033108090f0406090b030709023a0c080106090e04050706050d06120b01050f0a0b090906012606040507020d12020705120f120f010608180c1017100302 69
    0x724603401c01022001c02159103080f540b1060003118010390300030000c1c041c040d114110340740140004040544248230380703000040c002440748204d0340c62a403448241380300c0604030038540b1000643c90350591488000c0c0f02135510882014840d8022900e51039407000000d514011008052140903040000e07000400000d0000080001801c4012240c030b5060041e00c49038622032500040c003003640301ba1004040c01058004110441001c14140c40702114070040d00201c507014805080f90324001c1d154a030000f00005c0200740780c0598103540c0700c10b0501d0045002da00ca540c20103503414000d0a50010140c050b0140501c41c40c01c5c0c010540e001c0000d20040901c2c00c1a0400208048465054030b03200740d48c009044000d000c0c00780701a12040310721007084c942d074500c150040700e110344c084c00400e008401c100020480c01810b07142da41c2e0403508036580e0300c8215140c4080a003071500e00c0200d103441034490440c032929241c481584404000d000b584a48030030f414001004549501c005101c6200110400000c6c0010303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 826798561 1106 826797455 826797541
    0x2040b0d0509010606090627080c03010b060a0903030c02210303160221030a3315140c100914010b04051902070201020316060203 57
    0x1039a10007400a080390303400d004010006d101e00a081160500c261500c0c10740d0a080c241641c0c2c041e540c808a00178500841c0e200715041c2d0840b800c80800d0340341c20b104100c0810302c01d071890307460450410001400700c0b000c0d000080a0012002581d015500c0720b6011020100280c3c0300b5050342200c0302003d582e01e400071138080c1030b81503906400b08019440407940c82c014141881c1014400302d1400380a005542005000a80312079880d18030482481800021488007000f029000c03550100c407040180201140b07400c000e11950341c0039691900281d00c140c260400e220346010300c03a10390a071000200d00303203490540c0c00d00826041c8040d9200f4003e5102c091032106090000070800780014005200035103030201d07007440741c4c1c003004007040c0d4112405800401a4920500c10f0700c5c0780000280001c50b202e000c4c0344059072120fa0100401c0007150381c5084c43ca03046942c400f141c0480660400302c7d1032038 = true := by decide +kernel

theorem cover : BRFrame.Cov 826618705 826798561 := by
  have h0 := BRFrame.cov_init 826618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 826618705 ≤ n) (h2 : n < 826798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
