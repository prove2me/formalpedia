-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0194
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:22:58.493687+00:00
-- url     : https://prove2.me/submissions/e4582698-0e3f-4857-b91a-3c7c60511d16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 34712235 ≤ n < 34892091 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 34713485 1250 34712235 34712257
    0x30c3215061c110609100801080c01022d1203090606040b0418020105070507080601080a0302010501060e06030106031505091306060e070801050d0302070b0d02030403020c19090b120304060203070203070e060f04020c0102 96
    0x580003541c0c1b800f605a00c0280110b203a10310801481403000d50001840e60034a00900d0304007500030142849007003034500e810548404034091341c1b0301003510119180186001d049003d000d0501842c0c0401070004940c5038401040c403581c1004012014a00c1034414200c041da02880c0c1240d03a5403440c10031901e020015032200549101708400003031201c0010440410300c2e88a58001d00c1266a900011102c0041d0b002c40e6951200d820001008610702a610800070808007400402816942d0b81c00160517480403100d0f20361a4900580140811031a40b1469001d001c0c10346811495060141000305520414007031240194114403903402458001c0200070001c18140e420705940302903035401080a03400540f011805031180150300400c03480c2a11800035001c03100303150250402d10305070904002d0181c14042c01d4120860061500150f0400c1c40100301a1050382c00842d5500c080e413042c5458010594003140340b054030348081c0100340e030703507140d002100d007038203d034050f07107440c1000c4420780284102d2000070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 34714735 1250 34713485 34713499
    0x30201090c0603060f0f0f0905090a020916030617060103111903060209150306031f140109020307090605030c0901050f09060309070302030c030a030c3215061c110609 73
    0x30b0056050f000310050b20a44072842c01403c5e42c03003490340c840000e140901c408000e00d100090200c030740e040c0d02c0f0540c440480c0d821556030b8442c41e000704050400c1541c0084551000c11000c07034200750035000301c400401e4a9401e41c0407910300b0303014a07915004180401450416026800b00d65070380c406440e000c2140860380e04005203542c900c0c00d80001d511800e0041c4c010900490a42d000c8116201075a01c2001c020300900348070611186980944182100013010503581c80701c107085500b900c2c02106019214040005981c0e003441e003406442c1c5903041c0e2040e010807004004001c10442c030b51082d601e59007020700780707030703172280d60303510751602940210200283c2002011003023040040000030030808980c02603003a0b903001901101810303115282d001c8082c000c6001ca40601000074041802c89000b1140030011901034030030b500264282c4003450003404266480610a14803a42a10b140541c0040c0100c1d07101188011f0444c45d03e28007113000a020b0b0029003811200340c0103407510001c0355440c8038028954 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 34715985 1250 34714735 34714739
    0x5071d241e09040c080105090f04050f070314070509040c0909030e041a040c03180206090a080a0804090e0703020109090506030109080d0204080601051806090702101b0e03060411010507030201090c 86
    0x1d10840d00195281407065051030702e940c0809020b2040c240c166103002d0507807422592146210020540c000e042154503100d500941401c124084c0b001c800550b104280c0d035a0028500c41c1d0980c50090282c2219109020500511000078103180b0610301307d400104010800c14000d00b0181d50846070440c1142e00075060a08843d480c43c604800c18110f1402100c04001e000324110045046800181340b400280d10765a50420160be0003c1c06483d041034000c1c80000007035140c40b2518145494000b00302d81008003c14180814801c6004071b890b8002000c00800c1da4130718580000304801001d1140013400365441010488070346081d0031408609400004240d514064094100025030007031069140300c1c09904000710300d62a0500c00100f11800c40d2100c580d082e240c800402219580241920040d032185845a0018403480d020308850398090b4181800c015540f0000a0700e195080c4d00c0007882030300f10328104030010300c1380d409405422000786005a141c155904d016801014a0f21002c0c2c40e12180b4800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 34717235 1250 34715985 34716037
    0x60d03180f0e0412030506090106110c04060b0403170901050a0c03020c0d05030a11010203190b0315040503090108010902032401050705060103050c0f01050a0e091003120305071d24 79
    0x40a400b6a208404c0107105070381c040c00c22000c462058070340750b9002d05500c004021603131003881401d0808501c0c8043c0e0b1a0031001c1c10000302100c41981c000040d503d00494100240500fa00074944401013103485180745c8140a000241640300d00b10614060004d4107110109044c800c020b410700c02d01c030161512400141c1410440da03650408510302001030b1085010361400b00060094a0080701191000c07044003002042e040043c2605240f03242e098458424024a01441c108071340e8005d9000d04059035541220000060030020143c11402000e80108180403140b508001180c006545000100600303640d00d6004031421710406101402d039100d048008401e020010440454481044a0720050b0000d81c0005640c0e5005c0caa81040c0414040d4844541900b86120b0f801e501078201094999195265a03c001036940391800c1080002c0d6502c0030003c00540001c2c0c546d600c0a40019220180c1c9081000100d00110120021000c011004005041c40c0d5101d8213403103500c1c170400203482541c2c10100c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 34718485 1250 34717235 34717259
    0x9080d0c02150c0d0e120106060206060d1a0709050f010305040305341a010806010e0c0a02070506040b09010906030b0d02060f0f03070c030207122120071805060d03180f 74
    0xc04074030a001b076074400d108011052050300b04461603a0050540360b680c0710100f051525104d4001d0f59000e101005000390008121560340c850103454940d0080300b8207142c00c0c00313101c5003a540502d05140c40c2c101444040307504142a50721038412040b12158840041c04800c152000400000c7c1c05000030903803400401c050440310508080050302d00071aa6a41c81a00701e654031000c3c403a2001544514010400320895031000b010f200140f030049400f002c0d556800306140343d000ea400024891008110200b1940e4001e10200040c070251805010766800000040c1440c4880b40009100703400000c0c1d11001444050b040c0c0b010380711180100740d00ca1404401c09004070015050407801406032031004542c2103076905046032240c0d08140790210700d6007840342007402201d40038400e20501c80c061400309000e00c0c83c1301a40c0b058059180140c507086103411240c41c40891280008601e01d0f09000c1005445c0d203484940c0e82c1c40741d4161070022805c0d51011840446009507810400501840807804600031503415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 34719735 1250 34718485 34718507
    0x210030e0f0304030201051b1203010b0307030e0c0f0105071106041403070b0307050304030305130f08090a050105040e0a05041a07050a0f0302070c05010e060f030a090309080d0c02150c0d 82
    0x2000380ea0340340c0c0d08090300507180e100328003000340070038020f005184642c242031030313481340002c1101c0403203190a260209c0d020483e0400d900000c180c00000040024460349802080c0c400c07035a100c0148928035a01001a10081c422002030b41040000700b01c030401e1001741c0c800c1ea001c0c164054842c07540d0320f4503080c030f6075041202040c13128083e100702d002c0003c2c0241d20004580c0b2451640d5211800d54640d5036046010b0320b405400f80c43e00d402400341040200d82e03000c1901c21090710813900d040d42c885040c2d041c40340704c050302e5000078140070b0140410407000c6111942036070b00890b100c8001400c0c0d41d40d840c0801800440d0044109015030b007030200704801c0d80000040c8610b2402d9158411010b6011104505910501000509520000004210f0380d400740807040c0007884014944c504000c40007031104080c0d002103c83c802d43c141c81c2c11460061641140941c03002d0000080502121446400041d10740e0b503074154000e000e60400c00d0141180510401640c0d801d80650050b128111544c810081003e1800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 34720985 1250 34719735 34719761
    0x100f0f080622110d050f07090b0102030903030301090c031b02010906050105090402031c0521060f06070503160501020403060e0102090a08031606090203030909070c050f01180609030903021003 84
    0x14020682c0703400014a807640c91200140c01c0c801040265458030024400002219003083c105511100003c8007880140c0300640c080c001400c0b41450100074100b43c455010102e4150b40003005201081c0e1004000c41c5d064400354000811a001d100808030011700c0490101e800d0f1010840e156070400380e040d08a6419175004031030a006998851003044403990041d18000c7d410b50088002c11180003802800c58100c10381410010b00302071180d01d02c3d0002d0000c4034a00e51800000804114040c070f40101c01c0d001c03040003520b00c241091640d9803099aa481082111100d8a81c10f034031101c10801e00750110b03005140d101c002409051a1000418085c1d0407003400c0034803925480501040807000007040d140145000e004885800c0000d80b03502c1f000349819142a83c0500003041008090744800c228140240201da4601d040c505650800600b00418000340380340b581d04011400e103030b00d010b03030038416440c0740c00c0080015040500e00e02543c1c2403601d648029006803200c40c4c0140303000e80542c0040c10bc6a01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 34722235 1250 34720985 34720993
    0x2060106111207030305091509031c111605071508090c040b090703090305090d0308190e06040201081e010816050609061e0c03030103050a120206040b070503100f0f08 73
    0x4800c071180d44401061003200c0d9807020a00540c00801c2c42600820b0300a5000c41c00d44400341e000040c7d040d2204011039a036180d81c0c4c0001070414200c80e61561004803004001c2040000e00c0f50200d10b0589441401245808020805a4042481001d005880c000c2000d000c180b0414a01c115000d00000320488a04440f801118135405a42c1400d009155400c03a009080d08090740d00c06005500074007115106804000c0140a80e500584414030007001043c040d80300c101c49071a14880c0750040f40f000003150340c040e5040550018018200141c006d4126074242841c014581c1c074600e0340ca059185143c40003401020800c00061513440104d05010580040c4901030800c03600c2e001842441d106107500580c0200e41003045000000c1000c5200c3c14061100d0001c610b4810005296491900280c10603940b070f030040800b5130308100d100c0d059003040c4111800941018075143d2248001100d0003844142031140c0000014029215908400c01824205206010b261784a5049900c3d04002e40500c007040c0c89 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 34723485 1250 34722235 34722257
    0x302040e032b090501090f02030106060504080a030503151804020109060c05060105060a0c0f03030f05010e060d030e0105130e0603070603050c16020607061e050a020301140906030a0206070302060106 87
    0x340100488403015094000240e140d4009403900100c240520114035010383d46400b100300164080c0114aa5035001d20080480c01c48280109821545c09501c12024094100f204002054021507204040e03a014140399890380c1d11030031464142e00b182c0c51110b0380700304514a5501178582c01c02e070182c0218000e036910f8080680f202c0f819a08150503080142842d4081b400410052070864001e0075001d1452800c0c80424685640e03038001d02400750021400b0948481c1201e4800c44181325050040800c820850745506110002c90b00c0700540f681c014040002c0c510030310031264050412264a0490388014001450b070710400841c9d4840d0036103282e4420f0050120003c0e54500c2802414080c051284805240940000218800c0160340c50226044801405890042110362140314018952012200b070159503a0305d00b031040303d134000d0400810601c10300042c0300400c0c1841c290071802c041503583c0d140396240c550000e0314040307200f0300c000c0d440720000a40604169000c104281290740355200c08080c22 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 34724735 1250 34723485 34723511
    0xc010b040203072a050d1d1804060b010306030803100e0a02090307050d030207080102130915060912020604080d0e090f06030303040b0c0c01050405240f13050f03030a0501030204 78
    0x440305564480010f40e00c0040070203001504c140e00d0091440455025103c21241ea82d000e040c040e154070fa400103d0b0184004034240940500c0717a5401c4082101d10a00074a42d4000300c24010002900262840c0d40d03c408103d12a4000e40c8142e0241d1f400014054681c503150080f05041e00e194021b24101c180c0100116011007428000e076544050000d000d8904903040100740a8410304e1440150111702c1204000a80d0304421b200601b840000c031107400c20030b20308050100d0140c1d01e0200c403007c541d00800703100b046203d6000ca20742040d200c055040c440040f55034000503446005640010b51140540c12250310160381001c4404c0c01c02000f954800c07590f0765203060101c0c00240482c0d1083e00f6030401c1000500240343d480901e0ba1000c00c03c1d032111300b090031004100342121000c03a000c940e0365010380c4c42815810f0b580460f285524044c0740e0a144ac9203806c040c203010349440541880d50116014100c44100601840380c03015841203101125181d245c064500ca0207400c081c4001d038080c40c41c081c44c400c41e80c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 34725985 1250 34724735 34724737
    0x30c090503030301090b031203090105061c03020606060a050f0309030919030c03020d0f0b100305070b0a0c06020903070302090403032004030506070c060b0a03060509060903040602120f040306060b0c010b0402 91
    0x3100c00501550850b803801c09160040c15200c0e400c0c030762500501040c1c488c0c150400d000b07103004d0520b99000207038500d406000c0c089805132520448498807400b6082c08006079000801990001c0191904c1c1e1f1180902c0d1801d031010b01030102a1950381d4004400c124407410004044d02404c00200c1c0c0032140012851031445641e1410302000e400501200412b00c05030030a02c440503403041c41094000800c403807036152448441c10688248081305c240003010800d101040101d10058601d810340a07140c04e000ea03030050a9424007100c020722154000c10072404a5900b03000c0403000f1900600b00c89940d00e0241b0b07005005001c0324021141ca0180800d0b80d03000a07544909031029607030300900420080e11130103001c0d94000003101d0100d072041d898000103101130300c1e0010020700841c404c0402003440d081c4140d0050402c80004c000c085d407540b042c00b0820501c1e5000400a1807548001d40c0e00d90341c0d44000310802060300c610b42024240500304440003400011001c0107010000e0f50788000c00021110008001c26 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 34727235 1250 34725985 34725989
    0xa0203030f060604030c08010c0806040b0a140d051f0606231c0608010c020601121121010c0906030f2a031d2107030c061802030a0b010501030c09 64
    0x164024000a03203020641c0d280306070000401030849081c590f036550f65112900c0300c0e401c08049039440785000131540b500200c500e42c0017941210103002050091012515040c050700c0750740000507071902d24040c0ca40725401500640758200341070b0350031080d0010480071030296400701660002d203080d8001415a2252180c04110f09900700042d01180187c2000c140907000307950140941030b0040d8150409140a2007100c0081ca2500000301d59094601e001a003071680507400108080900901b4000040c41549008541c400844008080303052442d00340d50400d2020811074030541c80c20484c2d080c8203401c6400315040301c0c540c0d07405010901d440440b050940303444a031308030a418183c42141241082c21b0070107043d0b8400514002440d40a0206960500b00c0e84040352072032508640004558a55182c03680110004a006c20a240c10900e81d0020201c0c050004c015000c1c0350f0364007418040358040c615580700301d500181140d00303240c0c15080c60104194217200e140d01192400c003a00000e80e004c0d000001c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 34728485 1250 34727235 34727237
    0xf140d0f05030604050619030c050a05030304030c050402070c0306111309020a021f0b0d0f12020604051b011e020609060108070506090d03270807060503040506131401060603020910050a 81
    0x802c5494050a10000d408080c1400c0da0181c441442e0103a050080c10081c2d00850084660103642072601050140d24030484d0040d5003c0c0e00200018408030700b40340d0203001110800d640040e40d070101c6050441801d40c036030b000101010b0800c03200360344082a147c0078101c81c00d9204c0403406000e641e49180b50480c42014a501f025070010904c1403240788154001d8150071180910104000c0d000000282c082d900d84d00d41240d030f07201001c02203814402c2d01c80c40c003221701d611030006100c1c13420300c0d85400e83e0740d014081e074914400d800c1d0700c5140340c2c1d64481c0c0ca0416050f900001c0d0804003c1e1000741c0a5100c550480f2041014429400005016003001030910111903010300714501e8903040c10140f03e0542d05100090703007441845522030940680c1c014003c0710081401d0780400e40c0600741412fa030305088003503002c801009010700c14440030600108006802840c0f0454298241501d89080201913503219000c20181d46054800507071a0740580040041200465180c04084c000c844c05803020301405282d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 34729735 1250 34728485 34728487
    0x307030b0d05060f060112060e0103050f010e03160203010b04061413150513020f0a0f02060601090303140a030609020c0106030501050f0103050616021c050a0f030b0603130f0f140d0f05 81
    0x213010144455240390010010715140c5080300007254800281c034080c2d4080011104800010010312000340f20f610b50044084009000e4070911030002c40ea030340681d101500303c0c440e40d41c003401c046640c2544140c0d0f0b91080500140300f0316a43c0c14058014031400252580151094420000c0610321403062260148681000c0c0180301e04207001d010940c0c0c00a1601c11701d03580d00b002012000003902d000390801d80c850365071b614422810001d0080c2483d0010b8a1541440028802800080e0700b0404aa80c901320801072141c035a440c4840483c0540016440781140d544002241420313030a06400103803e490007000248041c1c0c45a1100754038400b400d100240c6950072840125034540d00c00200012101c0003032040300c0c10341421150340d01e04040c114195902084000814210712504224285140c01d01803d04011190884000c500c00d448001e000d10a449207603401c0300c00300440038100c1d600301d07500082080090411480c0182084083c0e500c1d5400d1032117802000c00c903181c440c12040140100c6582c40d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 34730985 1250 34729735 34729741
    0x114070c020a0306060b0c100507050d020903150403030b12030c060c090a03050d1d01020d17061908060106090e040309030204110903060406050601080109060f0308070206070213020307030b0d0506 86
    0x480c0c45024094089a1042032080000080b07034950080e04090b00f20404d00e07659817640c6120380b40ca01105040c05034406400d00e0100f1805e560003c007a40c3c180f5154040c0541e595101d40700080c00d200135104900c249140410911003810b0740341d4800c200c1c41409440c00c140001341a06410303501d0241d12400d43d0543e100c82c001078141d094003000b03020001e401510400c0219126541c0c18203109020640200042c501a40e01c040c5100102c0401c5041000307001074451504413840081002d080550411400c0c035507200883c01d03c2c3c0350011880b108455800b15103c07103075103d200090b1556400e01c520400503040c50004203640d2500b4150342d0045070700d0348a07440c1680c515400c1c0800b0b040c030160303602c012220510040180391400d201445c8240d100e580c00141514004001400d400c8042c0c0120f92030615000c810300206030f000b4000f609494012000a8540b0882d20001c3d004d0720641d41d00030b4100171303401d00800101c202380c1c0165010b00c06a86041c010025001c00384204101d5240010b132280d0f2144000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 34732235 1250 34730985 34730987
    0x3070206090301110703030203060102070509040b0a05100504090609060b01020d0503011a0d0c05070c080c10031d0a050a0c06030911011d03030c0a0c0906141e03011802010809011407 80
    0x920742214090b0022a02c3d06108045250b42d402007030b07096003c6600002006950341c0d0601007a0080c040868546a840c10544c45440d21000010078150100e95500003207101420424503ca0040400500500a42805150a401a00305040300300c0b455170a00041600350b40c000304d0003d00304a40c513500c03030341141e01e0311180011a0402c61201401000c04024110051030301c0d0050154044d400d0315090350307038050381c500405071000304e50000003607400406644880365600180c225662a0301c1c030340454403c000e118281c80c3c814511410807041d01c0f611703020600300b0101040c41c11029020303480302c040050740e418094060361030545c0014500c2c40c035040a0400c660160000c043c0019045400c600340380c0107000841e156070b001500c005080da0006603035004114040002002420b04400c0c02c0c02032900c5c0c012251a40c041106a092141c2600c2040c0b00703c0000c95150150300c0c0800900a000f1074041c41c805c41407105040302e041e03000400190008800f40414007031400081d9052044030303210394038240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 34733485 1250 34732235 34732237
    0x1b020c1215041e021309021c05030d021308060907031a0c090108040f020a030c080f0c0d030f02030c010911010f020118030f030609050405010f0516090e07030603050312010807090e03070206 83
    0x5100341c80454401c03901015840f180c2441c440c148040320001a06d60341030040110500300d01c0611032050028003480d600042002c4141d9074400b00c0c210b80940c03964190054000004441d4022402c0d5109000400c00ca482e00020703400d0449001d5000018001d1003100410b044183c1140c4581503148100b041c151554481c10300207501600038028204690000d074006105180306600940d0003064a03681071008540500184c0c4100d1804c1008054465a8a0100700d000e010258090305001380c3c0407203030070541c0c028000c441145045600030018004140780030360014094030940307400160805811000302d8014401c0c20400c078464016200043e02d680d50454030600400340c032104242d11030b20700045021541c095580214410000031569071011860f0800307c030310080031a8180d8100141071801c06821024080c1542c0302040054920303652000c055002d0803942d4001407142c0700002e40503070002100b2007001e040e1610380090b941c0c890f82d1a2804410b4601c90074604d00c59400402c0380f8001807130940 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 34734735 1250 34733485 34733513
    0xc0b070504150e01020601080106030218060406080607022506051902030906070b0a050708040c03030507030e090a1a03031e0d0b031f050603070e0703020901031b020c121504 76
    0xc50014a09a00c07001c800d150308500700d1404020500034020001c4941c0c051000341c1c00f4040718402081241e14540001e000e510218040c42d84454070341002c60300c05e8480b1741002e00981031810490b00d85c0d043c400002075480c00e41d0713950802114903101e212600c0718080c3c0c4410080315101c0c0c0e15607007415444209080600c28410f10031081d8481009001e1441d15900c010703003642c90040b1b1520009190003288642680c0e0010074240070052004101700c002100381c403400301a6901440c200e070301c0e03696500c2d05440345031a2481c01a4045040400c202a07040d458000a074903c480b640100401ca40c8e00703041c142d90b402100e010540f2409500302175000c640c11070014000c0b42640e040003181c0349407000c01080c141300301002e460072069668503280c414101d05000381900444298001c2658601d4040075081e40712000e05030700f0415400040f01c25150307100b6000814829201c9441c00d00c002c0d8410006075403000040b180c20300408505071042016030001ca4031148640644024101980d115134038002c0401560f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 34735985 1250 34734735 34734737
    0xe011a09120d030c12090201020d110c040614010e040e03041401091d160c0302150703091205041e050f060a02030c060901090c0510020c150421060b100c0b07 69
    0xc6030081500c01400c02c80c0542c5020540c6001510700000640240f4140c4c2215003803c2541c144142000140da0001e00030708070011520704488652032044a860500821918103540541411004181c4684401c007060241c103090300c0e5140221507001c14441581c81c443c0c0418960b0b00248400c01018a60006203031464105250164803582c6441071410341c410741600138030000c10105c003000a0814040c141c2c80340e07002a0304101045000ca44d8009541700e00046c01c24036881c070280d021801c09030007600880201ca5201181c10b42c0002c2102c80102950454414503000140c1c0d12004008a00d81d8554101a0760001e42500c0100d8146018084036610040b13640d001c40c802040001e01e01343c07050004c0d5010380c0128001180810344c9081010260840781c00541c07045100721040c690050300054a00503040e030950300880c0036070450034101c14030b0240d94030044210440c031111043d409110b49001000768800c41d400c101d074402c4c0c0303014081218070541c2c0ea480880d401c9500000483c00d41450140d0007086 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 34737235 1250 34735985 34735999
    0xd05131509180f090c03060509070e040602090604031505090606010903050a0b06061b0c150a080a0b040f0c050d0515030307080d180b06090a0509030d0209040605030a1b0e011a09 78
    0x4071010f01103418130b030020303a05d88040d0712003403080001c84e00450750006020310007403500504010740c5143c1110003500081c0a00d0f07002400140d151544c000b540d0046401040070303003884000c0100a400740c80101c1b404003050040d10005000e9600078410001503940090081647c40815507601036440c602601c0158410014400103600c0100010403030312087d0024040d00480e100d050134044480460080c071402000144104c4003103543c007082143e4007000c8007001098101d01100802e00a0501101d0140f03400c0c2000080c2c40095005070051441900d030103010082907840d03141e00d1001c2c0c0c07060a04941d040c0c000300003840c0400d010f40c003e48400340c0c0001000891040303003090900743d00e80e5480100c0d6000342c50410443c503807504181c92580200380f042c0c2407040d032030f20a1381c0366100e104002d00340700b00ca80e0103e94076041e5291a44100d01a04020703046810041090502c50600b1001483d0090940703400b1030041039820509066134100ca1b441c0c0203660301303210407199030b4450760403503840181c004031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 34738485 1250 34737235 34737251
    0x603180206040b0c0c030303060d0f020d0b1f09020702090106120213030f0b062b0c18060503070911031b091003240b04060804030207080d0513150918 66
    0x80d4000082c00202501405259a070b282840d080d8200344901440c54400d0f0002e004009035070302c03840f41d10100a903102c015003800720070500c000380c41404803103006801000c1c0c0508001300c0c002145480f9540101991004140c1e40c2d4400400040e88180d80000303412414100040041301d028001100c1c0416040c13801506001100c00710a23450a400d038403c1d40d2a01107040c0e50001d210f40080344d80d80188c400e50b4100c500000490340c05000c10302600c0040c0960314150765038400e101c00565a0b601a060f92000d59141342c1c04203080d61b01410440c0203840c1300e0b004050000130390311103a2080c602181040d508403811a600e441c01c1e400f061801e80048113121000f0415541c0703a580300b603a00500343c40302d900e0000d548c82220700e90443c03111104140302d40d1528003400620041d150a401c0c0c2c1c01301c030305910304840d40c0d980d035190407070600c0c17200e50216105110b1501003112583c0c00c4000340000c021654003a03103415a44040800d681c1030398aa001d40401d05a8009001840c0c081401d00c48000e500100890041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 34739735 1250 34738485 34738489
    0xa080d0b030a060f0902040506060315010e1503090606030d08070e0d02010306030204050a090303180201020a0b07170c09030d0f05030a09030203190c1502070b0a0923030a0801090606050406031802 86
    0xd40580006401315078884044045107014400d03541c00c980b00b515241e05601c1e20b50025011001400030307580c184aa01ca06014080d03441040e9000a920070420041d181d040c000742840d074614041c0e0384140b10b03003d151b40007080188907400981c400c007019940c003010020b1072028814040d0085005904240c0c4402000c005a10b8070f0140074000c0b00b44d008002803020031070500071704845040c01c40010702038011210101503a070000741016282c1e00550341c0086a141d149095964241203008242507010120402000380b490710060803010303409505680020520a17400c44030031280c890b484010030024004610f0003081c6500503803200740b09004403803401c03c2501ea4a1120710420000900042c200ac1c4046e04100040c0c0550652001021055081044035980c40600510040c1141211680e43d8161024000440758030240e0b9031004030900380c04030210000030384035403003e00008045144007000198100c500c0c403450045610b980d6034242018100f000850103420380221049041021040301c101507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 34740985 1250 34739735 34739741
    0x3090302031e090603041505091f0b131104060201320402030f01020d060503160605040314070e0c03070206070807080109020f091216080a03080105060d020d110310080a080d0b030a06 80
    0x3490003008a2141401f144a00c0415140e004101000030b4111107000382c0a00c0407001c500175104142d0300041900c0800d180071401507810349040c1c42030141000746120b00c42d06220002c0c0260b90042d03000344800b100328484000310503809001040c0401c441c45815039114600300d00740b6001403004050b90155108000d100f0b003641c100304100740605950740800c100754a010403c05482044202d260158503250020240070343c060780c440603180c0500395130146000882884850b02070402d40d405840941002c0d048940c543d04101c0d542005032003040085a10b090280c61418810303081039445503000ea00380700d0b03004040e40082d0950305a1342c4090150303014545d2036041040303031013200310010259041703d0100e5101031030156100300c94540190b603443d00403d910894007415198161451a83e80071842e209034028402c2031545021946049220400651f4160003980605800d03800000100c4e01ca00c50f254489040070001041c1070000c0192a25664141d002401d00c00c000a0a9810b41a8a5111881a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 34742235 1250 34740985 34740991
    0x50a02160b01060f020a050c04180c08100506040b09180705041b03050f0c0706091109040c0302090907121103070e040b01030c060c030c060b040213180c03090302031e090603 76
    0x607207518400520030964040f0390804254204d03c01000303110b096850781910b03490300030701c801c2c01561211800e04440e0010b01c1e9802c0030b154800c0540034442d41e1050000e03240e40c0310600704030141c1e00f04004a401460203015000c121203008000c9000c17900e905103c8500e240341000180c1081c0180400001c041d613451180c0142007080e104030159401c0d01071001011990014030442d401c0100b407040c0000b0900400640d11101d80c099000a4110994202281c901300c403510f80e81d500c00c510b24108010050628500d0044030b100b40d41040c050345454580c3c58513001c0a000d0078400902d034181030070120f00e0041c00445509006020760f8045511000018407980084a042d5003004581004004010700b50504a000700002c0c0f1341212200400c1e680100000c9600c00c1c007401c0c441c1c5410070081c0a60315681255910f03001c031800003610325030351001611161207001c8407070a040d1a01c401d040009001740100781c031a6078940d000d18030300020002c114411400550001c5d04a5400340601046c1d500d5220003540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 34743485 1250 34742235 34742243
    0x40b0a0f031406180607050307121e110f2b091407060903020a0506070510050112050106050303030c0405130902061305030d1809020c03070503070819090b0d050a0216 73
    0x244040800ea03641e803500402401410f19404e40000c2d0094866000c0f48558000060f0301e040d0b0390708c1c0c584510441e4001082c82c1800b6060b4904884805c0072100700740300c032929200780b0500b030081c0c2d021003003001c001e4016490610341c0701200300814280c0b80c0c2d6280c405a0744141c1034150f030b090320065554060442e102114112201580c00070140181842045802c000700954540310002504680c0030940144007031040c170703004100c046884c10070494148480d400261244500300f001d5030351221140042107a00d8015151540b0300341000c111360501108586c0301c4e05039480c841e0b01d024940b001380500b400503840c10740340c0c441d5250902030051355400d000b80100700c220b0140c2140c280c00e2100b054149103008079608180100450240003403128403100b40111100381c000142c540710820f07406801c521179800300600b01e02000405108000c107241c0580320700c0304980f01d2a844444501c600f030300c40e0080340c058a4100701050010083d06111a0811548401c030400054102180c2540909d054101c0c40001c603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 34744735 1250 34743485 34743503
    0x4180f020307210605030304060c03020f06040c0504060608160507020d06020a081009090b0f0a09051e0616020705220504060b040e030f030103060908040b070605060109150806040b0a0f03 82
    0x11840d2041500030240400b03e18004004040c0b50400196881c400c03171180d1001d000340500c01209241c000d100300ca5440e030445050310214503043c039003402134508500800380302c1d620301140841c040b8895005184203c00c0c090f10650700f84030184c8140c90540050345d0480c0d01000c80c01c20380002903103500240190062544981d8040e0a0582c100c0c00780d400390390806039a4030b02e89200d8001081c00000000e0f044003a0310300c1030100341c841401d040003400070307904042c00b14483c80350310054014a0145200b80107090009642054842d07141410428803040314801c0103030701150b014012840e0214140310091105079010804020a12402041c0c0700211030a940d82c0e176955400039094101405544a00780840300603501e01981850152914041800080c001550700c540345410440080c08550180a81802d5103454807510f1400c140607040459190303002a40200d030025840030543c003961100100d0f07031910305042d40e074041800020b00c0b102203a01e900c84000d0743c0005601640200080c0618002c003514 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 34745985 1250 34744735 34744757
    0xc0604060b011b030804060e1209100207081c02030409050108100c03051014030a1a041703010f14031f0b0306060603010806040f03020a0519030f0c03020304180f020307 74
    0x5401101d011031122410311a4020240090101039440342c41190341c1410500100e03241c500f882c40c0107007400d41c41048070740314680c0c01d040300170301c40310107007150701c3c0201c40c080008503141c8000ca844100c40e228840540d0300c501c00c40030140b191942551904803651044900300b680d51000c0340e050318001c0c0e1044c44141c0104000c480312044ae400340740aa02035504052103541403940c45509852103a20541011000f0154084c80607a002d000e104842034000d01039021025801182c801c40e65000c4d18100c40100190842c4035803c1d444809403412209a0302c4410030091804510b03502041c100e9607940ea0600615041450340740a0702440e0610040d8100009030000e1000103041c54014050901403081e041413004102c00b00300000d0542d88150701c5201c002022015150030b914290480600404034020ba107001c140d94080d00c1d0f200c0c0801c0340255118a00883c038403405441c001c1c0b65490190050304108030a014462800a40400c00c0030505400036150885803001c0c8100d03001039540d800002c1d20351444c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 34747235 1250 34745985 34745993
    0x61b0218040b071409040c03090602040915060903020102060a050402010c020307030605090d030501030c050d0302030f04081507030902091f050a08030901021608061b0c0105040b040201030e010b01090b0c030f0c0604 94
    0x24941c0003c0500708210801840e4404078141e0051800c018440e64585401c0d91080c0d220707412614a80e50b00450a54403282c0315a2548040c201503d03801c86115880c040008000b845110040b0031244c041e0098076054940103540005481c00500a078140b00c164181e49005071001c00c200700045006050004541c03e00031180c500b0408642080820141044014408114104e6511084400880e2103095441c1c0b2454180d080d0f0280080501030340c500440d0000c0c0c030500100e1021500c4500c88090300d41c50b600c4440c00c1c0c040707408401d00690808031010001e0031003035052203908280242c50040d2603c49aa030000520341c0340a98014210580000c11440d01e42d50701048401140341c1076070390001c41107080c80891aa5201b000380707a1440414082801e02d2010700b41000c81d02d440d038046000b400680f501e403c10300201b010950f012400207142c241d00c41c52425040c031941555020596880040d103107008444078103500036110111290200b081100040c0c83e00e0b00041404a00200240001c0c2c039003428 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 34748485 1250 34747235 34747253
    0x2306010305130b0f04060e0d17070815041505060d020d0e060601020d08070507120f09050405060a0b07020f030304030308010f0503031e070302070801061d0a0b0307061b021804 77
    0x3014014002c425241c2c8000582c04400c9258403a802c3e491160140e52181041000350040002d41841c600600f1030407103d80d42c0c014101d5460f8100b48034040156110000b00f02d42108085440170442ca00307054444989150a07005900491425170008010035241c400246682d4000f0903135081061b40010b0311656588203010344106501d80001a0807035250200010f91a41240000c00082210a100296003203014809032071800b504107004180306c601d112005403200543d10802c0300801d81e003410004040c500b5000d1584a5180549410b01c128600350710420075400000040f80c7c0100140c001d2400380c1c404102400080d406030703a60031000c2d450510300c8403040900c5d800240c005c0d0020480c0c881e05460008055900c5841503540c0d40d81d64601d42422130800070660440c41995080c284009000c00780807241b030b403890394641c801d8551611a202910100c4035074040094142c1c01607a81080b8060003080201002490b41c2c02c020340d580025030005d001c13800741017080803e0800f180140320038042002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 34749735 1250 34748485 34748491
    0x60b210c0405061008040c0b0403030c03022b0e010e091f08010203150f0619030e0f01090506010932150108060a03080a090b040f05150f0a0309062306010305 69
    0x1e6401c014a043c4080810020b1994555034018030004002290410940d0800c4c01c00403c0e1442406032202d07242e14009164101c5104164018814003100c030080400101c081c0c00036010501c203c00c2c0380a00c407441501c100c240c4000d0305050140e0080c14a6450b00c821030400c0c81000c1480f40070000041c4041c80d10250080c07600f08450a81c81442080314852000710041e9401608403400c481e000c3c2580006501c0e4811200ba00701642e0344e14255100403901504a4001c3c1c9840000740e400300454078000c1c1f4202c600160010f002e035400a40104040a01b540c4103081440e04104120112050520309102081c0220b40010305070394010300700b0549030f403030421170b119821003440d181e401c0e4101200020800f802c05d01018003101c0c800100304201d9070180491000030081c81c80710f1600e490b62005902ea50103024400c1d1030041000ea01d8000415a04404481c00c2c05e1071070f5045800d24400b603100320011b00107544100d500a0741c581640400903050300c1c1100902d4819200b02d81c80f440c009000605468001d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 34750985 1250 34749735 34749739
    0x91003031e090504050604232a1b0115080303060108010e04051e030d09050a1112030a030c17090105250f0503041a07021e12030402040207060b210c 65
    0x40c00c412000380d0b07200d00d041c0c0c00c0b50001c03070300880c1d5500c84000007001090450128003200003a460540c090154002c40c01d03101c1d406082d14003c86912074400381075075001c0002c0071444c0410804c01c00c60103864090304580358136440030000805915550500700a401e91b41c0000c1400e40c0b02004001c82917a11074401d6000d0b0000480340c0081d0f08040c0e41d5540d60f0035502c4a980e1209006080d007021840080060300c0700704081d0b0205105111042c1040c0d40c56505400003500e50803003041c07400085040600b403180201c1c184c04000d52500c03c01c010220001e1400040380820060703401c03034800802c0d04041d0f000c1d00540314280001110304005a0000840980c0300f02071034224200d64444848031303000308808424290a0404c82d40d6070f0388a2405000390040c0702594801410b00400f8440c0d10791740054100600c4240403081c0502c0900e00400d140d661245071102c030410b00c001c00c0090010f0070141c010b484154400e4034082400b0240750001550602030742c80e5040c40311079540c1100036a12040004464221302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 34752235 1250 34750985 34751027
    0x606020102090d06090318140f030f0604020904030207080715031a0321090a060503040512040e2811030603070b070b040602070224070c0e09060106030c050909100303 73
    0x1c0e0300c1c00f150309911001c00141002d65150b130003205050242981c0c2c102c00110b1941e20507101d450b000310850203070b90040700c14003d401c910044002400e00013118451900d50b04010800c0b6a244d601308941c1410042c0210110b008400000452400404c000320107400040003a440210960000404948020100c2840c0daa8040b03a051840e450106200801400402e40d0342c602c0c004d9980c2c0014544210104039801c408460f0001500c2c9502c200610b00540c0719100352010381c0a010000500c0e80950b016410120700c40c0310109905108039400460010b180462903105609116400e9086654410040360343d48400410080c8924042c40b400c2e01602000b6205800c0030140d44403c822100010b00003050980d000850f00c082d561048403500a5241d00507141010000c1e000014001d900642c40840d404081d148002c6000120221820f11642e504001003469a00e041d00403000340c10781d0510f417014410100409121fa07201e40d00318034420100358400e03030038131031862400814080c3c510440d03460041c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 34753485 1250 34752235 34752247
    0x402040c08070c0b060a03020d0c1409090706080703090b09060906060303040b091002030903070801020409110a0206150a09060b04030c0b0a0c030e0a0b030a090606060905060d1d0717010606020102 86
    0x600f003e450030000740c00885104d03030741d035549010034035204882c1c001940c0b2a01c52201c510422090420a01c16564080303010680442c0c2c120600c80d20b95401da85001c00d13604800d9040c03042c10301ca5492035502500301d20b400301c1c107010079403903080320440240c2d182c02d4140c010f1030400038484420020140c00c100150010f61501785014854031546c002e015050b0f1041c500c080d14480c40300d00c20015680b1a0300001e09848480c0c2e5074107141ca00075401031190040080c142140405040340f10001c0d1458052107401510250340c60184070070041c10004c00065001d40c110700041100c0d00c140c401c90014000f020309543c1d98038114100190000610391094030115810445120b43c164800c45142c07213a541414184080402100090035041c1140c00040d0482404403c001d40c421440d04010304080c0100f100308061034445008a42c0701425004651300034404101d8000b0030303a103550240166200765204a240d08104203034144c100606a44080000543c401039020300c0da03001e210b4080100000e0008500e008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 34754735 1250 34753485 34753487
    0x13020d05160507060e0f0601080601061d0603010905040c150509011b111203070605070e010f0306030203030a050d0b060f030402031e0709110c06161101060e0c0306150708030402040c0807 82
    0x31080f40320007404c0c151a0715550503288010005000616070741010744043c0e40e100c0c44c0c2180e0340d403000d00c1010700049080c404401c0c0250707000700580280d1006081c552130f6030f00705401500038280191080b60b4003000319400045490072a030020000e0700d480e5503110355034200b080c001415850328125081300b01d40c0c0020440300060b0441c05203400d1520540d1004070304920355456504500941c80d0207040c050030f1400704414980d00100c0c1c040c0e580000d8039000c1030032310b110707074100c003122039500009405a000b00004520300c3c2c01200a400440c0ca6000d02103400740105000c00c000d074000c100354600b224400320900c81145014840e100603ea0380405000002d600c2486440d61400b051144410b2103950340d210200070500c00c8111000c0d054520116102d07418900d030641200c0018500400c000740465884000204046c05040202e40c20440517602c50303100c40618100716840607201c07541c07004049a43d1044111035401411a030390084032166160325190050006030b03036001081000300040b0a040001c41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 34755985 1250 34754735 34754737
    0xc011d0909031306030605100f0215090f0f010f0e0d080112060204050d0f1202031303060b1801030b0109060f0513090201021204030605090c0307050a0b03070e13020d051605 76
    0x44901156410840c1e01c8000e402401c40c42044400039540400307a501182140d0103403c054100d6400352009040300035422011245401031148d8000142c016001f00e030908180c0b07024a41d0040e801c1825a4181400042d09525205501503d0300c1543d440e030000c0c1c3e0391049648190508843c400c0046d00582c2d2a5550007803d64005001e200c3c04501180311750018855180d0540d80038010203418042d006085082080c50b4070341c4010100c8056500d0442d0b210380031b00c0401500c00081c00c0c440c0d42c8261034155502d82c0050071400d0701c11904039411380c0190401683c10002a4000c60180d020102c142d41046c02c40f4003503c0082d00714000910000c0410419034542158400314040300c0800050001090301c0102d0611a15031281c11034480007290200a000c000c0d0700442c0151810b504a0b06084104003d2588882d42485207540c44152102c003003095005000003076a1000241c40e12403d0740c240200040c0b00403000d000700451555003c280080052080d1144c1500005940002c1d00c10003100b0304000c0c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 34757235 1250 34755985 34756037
    0x15060c03050a090e13020306070207050d11040905010203130614060616060605030105010b0a02010b03070605030705030403020111030406020d150321090e0f070801060507330e0f0c01 80
    0x10084000b0b14060300612409400000d070141501d960007604121490074150041802e081c1d2103030007200d002c280e0240c00000e4000c125800507114041c001d145031204241c10300c0004001e600301d030300c4155042c0060f40078402544103410105032521a8207450170007000301e4110700240754248888009100207030340d0320815113841580700780d18060740c03450610f0010b016104aa11640d00b40d0b00b03000000c10300c0d8a105000d050718800d00d90081021546001c01c00d599018180320b2500401c8003040400c030454861030045500c0760080c000411250110b088804040d0300c1140d0503901c2950100303104400e5022400b4400303544d030104000d143d8560540c3c81c0c2d1002446840340b900d40c0c6d1901d421552030001c1c000c0404000402041203204135520346440881a00d410890300c0c0800074051900200710540500c0075100155080a0354100300b00c5075085852504408001c20036142011108404500c0468000c801c082d1542e07001034014610251480c07850150220b5045050010600c00c042000d00f0590602d44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 34758485 1250 34757235 34757237
    0x20708030906010602071e120813030501020a1701030c0608091c050415170c180604090209030105060109080303060f040908370c06050615041d0106030203160c02030313080f0115060c03 81
    0x1c1c51504030b09d480d81c6036215030786000c4480c80540c5800018040c043d4086c0001c1003140e1640c2c40740e03491080c080701f074815023400001c1070302000913014000c0034880c0b030f185640401c18008950240086809042e01c4041d803615a40011302e001506015482c600b4884200c05c40490500c03030703041d204806280d040c0a1006140c01403030f03c1c003c6551030300c1c468060110700240790080c00c440d80c0c4a4680040130080e61007582054000d60074107001c102c85500c03520201c1c0071116000040e40c15610350908000f071490101c2040b03a403194031000c0030800300303d045004088450a4198001d42d0026a0504064903122050200300040c1c1030b4100721159600034074060307462a8484000112551140e0001c1e031048901180802c88200108001c00c0d4901c0091242148000c00711001015a9a0321000c0702030b448200c0301c000404070b82c03103018041140210100c440ca1440201900d040000c003291512401d40b076940421415800310845242c001028030072070213041c40170601800b00300c2c2046400b42626991250080c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 34759735 1250 34758485 34758509
    0x302010f0c03051b0f01060b07020a180609020d09050607020c060d020f13031b08010207020d020f010903060f02040302040b0f0a06120b030d030c0f0c2301020708030906010602071e 79
    0x104043c8030302c08a071100c20420031a00201c044221510b642ca41414081d25440d40c070300400030074901e01620603110b850340c1c000c00d0b612419081c1030805040461018240c01d59070f0301c1310004244500702d40042d12075490b042e18006800c1a1a0500c2490b00300c010f0880c20554101c444454841d8441000321441c2c2c95410f00e0160741ca4242a4078a187c038492030704201c03110f207014940401080030340700826205100c80c3c0c90315003030729440c2c0048900301d00c20941c00030361108017100d21200609107014007a2035503005041a203215580e0b074540000f540c50144092110980c001010302c00c41c6450700c40c6070342400e020b4a4216425607035001213440192070b40540410300620400d9030564080b01d4021141c280c03406026185403d07038040000d405010f910702c9120109100700000c000c0c80b889040c1102d0195041307034080c0c0d010804d034130401e101d10540c8000d41c050f954003041148007081200300118000e80d07510000f4101c03585030038402400c0c040e10340c01100c1d48018040007402c040481942d03c0040c0c4031315034942 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 34760985 1250 34759735 34759757
    0x10080112110a0303091a030106020c130f060e0a0617101d0a0506010614030601020d050f0409060b130b0319050c0706090605150303090307030609021210060612060302010f 75
    0x2411440e281c9403522940903110200102c1007560007010141191844d0700902e4902840c0c01e80f2401d140000d016420050b8000380c0e21010a281c40684003c3d4140c01260010368003c45103440720580d54103400843c0711030707a040c0a1014003011841420020000c0314409403c42c450601d040d03031241c4400b070090000c0c07034030366040e0f042c08182c45480402c0c0101500484c0e110203924941641c580b402403150343c0105400450415840710300b00200c9125000c141d002e4081022031210942d500e03080380c80d0701d1006c040c00307000100c1d40c141d0910560001d0078200307030750945550464201e00740e24100740d001210b10540c24001e2005801111707000f42e141c40d6220401091540e2818001c0089018102d0040c08070350802100405103c05540700314014400e00407104401607030354003030664034410000016050752000d101000801c109034800c0d40d84500c014008000310806500507071a0041c0f402000c4106a503d641c01c00c0610340205c3c2408070000328900a201440c55500007a01760050145403400b0320506803a6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 34762235 1250 34760985 34760993
    0x70803041d0c1209160905011206090303020408070b04050a08011404081606050f0702010c1b03051804060b0309060a1103070f0c05010c202d07120f0b0610080112 71
    0x3c0c0c46202c011043d20200c2d034940110043c0c0d448035198800b03c080720034001c01080c64810b50086038141c618412030484021172035071710040200206403084d020964280000b0035028010300607180181500404551100c0c240020081c190030b180e03024048503031402c0b4000402600340b0254690064100040c0c80e160201244d566100040c41a0018401841c010800ca83c00c14040711203800351340d50741d0003040345000d040301c2039480001c901c080f80c94071058901c040300001d104030005c001c4c4030b402074280c082002e4002d0103e415142c0c290044990104040704100100c0c00402c00c03941d00541e090020301c100030800282d103000703203c0640300c642080400428203100c9405000000d480c594410001c1002031556400203144440041c0b00b80d000754212146016080000124801c0c110f40c540c03007541e011101c09010b0b01c20b45140c00b82d001500c1c040c1200c001070248152000320b0b003880c0141046c19000b4058a084129108002c00c01d5100385080c2c806240d41d103900c403035400d0544190303c548800111742828 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 34763485 1250 34762235 34762237
    0x105030a030f1404170609010b0112090309080a06060e0f060f091314070503010b120601061b0c081b19050405070309020301050c1b1902010c02210a05070803041d0c 72
    0x3c500c5203000200041c101504001c440000740803482a10250b0300c42902c010b0a0351b0501e0005d50020740c802c4218001762003140c0c40f5000e00c92190401d50303011a52074200d03605210703101d04159245503840e00100012101a048540d00a004190200d800d10308a13000404081c5001c411034003800000000401240e82e9412101070160010440700c00340d030150120710380d242c056000e010301950822441c40c040d4201003070400c13807540b5460701401d141e0303083ca00c084840715110380c448a03101034bd514240740450808442c01015100e081c2c050700840c00b07050ba403441043c44440160340203640d0403d1400b03c04029450600540300125070214046d200c0c4502140504581440654154a40382c20b0001c5a40d0040003840c4001e4401c0100b103640c2204600c913500d0b0700071a403a03c1009481500c02000540c030491109124910040c19401001410226507441901040c914102c5600445c061010301c0000c01c00c4000a04203240114901401c083c50700c1c1d0b12080001007041c80c5140140440c0724135031a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 34764735 1250 34763485 34763507
    0xa0305040c05061b10020f030a02090301110c06010503010507050301051f030609020a020c090a02091f140a02010c020c0306090c0409050a0b040308010f050603010b0a08040c0504110a03050a050105030a030f 90
    0xf0009522030400f54507072807040e50410500710552140c151641c101030520300075a50320102d9a8400c0d13045664600c00d520295000d0b40005a16560300c0d80c0000082c0d0600002d00781381c9a4040007025290f050000b49421250080e0049041c400240b004005c1c03550348841000d00501c0702d00100d09120051882039028220079006181014000b017020000710b903001441c85540c0f541220460005d4480340e40e4002248100800e0580085000080e9628100740300b644210310304042ca0f000007514183c101c0c5ca01c2a80015525a00503516000c0003c8030329410002c503024520b08038042c01c5a401d000007410782d039030300c00b000c180c3c0241d8a07881268180113051081c941c05507040003880001c0e06c2c2a280c0140569824000e603240e60a040f240425241080410740781078a0386410414544004200d040d103524030010000c46081c60704000c003043d03d07283c40c0511840700e00c22034856034461350820303c09400d440f4010b09032010240790000401460f500000c20031034032501811309005203080c0c2c40b41250784179600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 34765985 1250 34764735 34764739
    0x60c07030f020705060c03071a04020307120317010b0306090610080a090503040506070602120a0e0a0308060607020a0b03060f0303090312130f120212010c02060103170408060103120806090103080a0305040c05 91
    0x21846c0140c5000103c0100f82c1c1d01d1050100010322103889d058966160800d4401940640c0b01c44814004201b036503282d420490302034100054584d0a418440034420b1090b0030020400c0d001006224941c20101805c642003c02203880203074210a03000020a5041c3c0181500d0070030342c032510140e060000620840d000350030080c101694402072410048044c0d40306461049000719204005400400384c2d10136451112088000740c50b0513035654501f16400140a02159030065040043c0c400680e41c4008090003821000145502c031b207050310801207452441c16102d07000313030010040440c26036000310780e048061000404003921810f400c40103005401d86a08000f64807040fa94022803651f08042c1d68050072403080b6100004450203480b083d00340ca00040804000d40d00080040c00040d85400b60f10b002d403100380620341e0400340d8a02c01c15103007040a03441a907a014801c030074aa2042c1c0d11011302c1e070744450140c0f8804125490f55032548010300c140b1030a4800c0641c0c40011034104600703511004020040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 34767235 1250 34765985 34765987
    0x6030a020d05090a030f090e01150306080115060e0402070804050405070c02090405011e1103070804020102011e020403140609030d0203040804031416060f05180d020301090803040b010602060c07030f02070506 91
    0x2003900f980d96101281003500895921844113081074824800a0117032000410707500030903440d051301084035030a01c240c4c60003455143d580214980f1024850740303510900150404a0700b52814070098420700400141030f0040f40100640400715607214212012110181c900107000d9440b0002203c1000444000030b520040d000244010f03c03405401084016094140014051004c0a8103c0032102901c0c540c80380d6400070700c00a00b00f20b0003603c80d0f59000d4010700000c00e0603134040660a9002400006450855a01150a105103c1d41005440e001d1010000414003800c144034640d40e40d007c0c02c082e040c0305540000009040019000036200150782c000304070500704429981d242d4648030813517450324088c0000c000000e42a445490200300782c013056111030b03103807188038046098008611040c3c242c0203a401a80c101c0142c40034400da0160340d0041c081c541c0c50307003440d2a10f0341800c001039001c0f6045600c09414441280901e200311904d0603451b007019000303222403c00a90030f00d0341c16400301c2d0380814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 34768485 1250 34767235 34767241
    0x3150a110309070303080105040902010c0b040c030b070210060b040302060304080a0e04020a0e03060906010e1602010e0706030209030d030902033301090f0b0405160507140d0c0204050606031506030a020d05 90
    0x10000070f141003602c1c40b0b030b10b8985d816038039002440115200481c010740022803001189001c60314090420b50401d0281d42c41900302c9450380c40c0c641c007041c1e003595076800607800141140d03005090745c8540b50103001c1c0507c00c6840d0900c0e5800240e56404082d00c0500184c4001401010207400b030440070707802d210060400d40d200c0f034038008054445240ca054440c0280a281c0c0010520f810200c0d005050b9260704d10010740c2038480e800d4403003c012805508800307565842010041c100030400448005040c29036016a0b1010880281824074084890620900d0304010304500182d401280400c1951a0007503043c8207a0351042c003060051030520203160000070000c0021440756140d400410000d148040d0a01852080e0001c0c003080364011264882e0440310b100440e0328486c130820040c00198000e140c48035407502401c0c9400e003010b10103406400808c546a5204045040901620740c4c03280c0215902c3e402c0d8a40726a5598020010050107841124000b002504e40e10460703061303c003689511082000fa601d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 34769735 1250 34768485 34768501
    0x5070b030a0501061b080c011d010e0d02070311010c0317040f060b0303040b19050712080106081602100b01050c0706080114030d0f11010902060c010f0606020c03150a1103 75
    0x192081e60488562410540040752050003480c0c20b800204089005040600341c3e9140d04140707820000e6418410354882c06401d0402e84003d0311140c45481d040000030b000066104117500d010b12142c00482550400101080441c00c0807024142c6000282041400e90569250448030382c201c043d80c2c0c50740650048103000c00c0c024222104000d00d4444c0c2001c21116040c9010550359001e0f51156210b00d1a04000b221910520701c0d1802d40c0342c80080c01c0c070030b0510700300b0380c2c0c0d120340c0c803034030b00c18600c00155100010001d1030303800b071300c919049121704140d15480055450b00035101c202c00030054003e56140c040c0100141d1042e0111801420340c04c0039210040c3d00c400000b4040c1d00207100e030100350b114a496101041c41d001c5209250602540c642c24030004040300150f5411484c007004203401d559800da41000f5032101c80003030486420700740c000107100e4081400002180c5058110b00115072085282c0310325601c00003051910f42d40304421000880e61489442c1020340705950700300548000100c1404080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 34770985 1250 34769735 34769737
    0x31515040207050610140f01051c090f03030f02030601080408070c0b03010603021e03010605030402011d04020d020a030f0b0f01110c10030209100219080705030c0f0f0111030405030a0e0105040305070b 88
    0x1708a00b104094406a5a0503040000f0790b5030606158403120744907140308158010401013010307507150303203000b545100400110800c130381c0c0d032460949089101c5a50041015031511816081031480501141182807440000f461402e0041c00244004800541c040506c401220100010902900b08580d60368650030010041d42010594003803074564440f03a0158015142c080d6416103c840d0759003425940d070380c0c004403141c0600e0b100407226107000e1701300e0742e0880d103482c0002e14111191000150392500310042c000d04031107120030102c283c5403501c3e031030310159580c00c0c611000a1209203490302c04100c8014540703041103048809640e00101320710400c14815010740140480c1042210010070754245090b0a90311000141e0780c084800071003170200d00004a0f907202500b8403a00820460f802c0c0482c4801440c0340c0398007075424800340c1c2e1000003410400f030000d0081000c3c0c0784000da034180c21410199911395a0303001340c0b0000c100f030103484a4001c441c1e912800076600215000f100f240c40195a0b40074640807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 34772235 1250 34770985 34770991
    0xd0905032206020c01170c0a0c050304080606010801050d02010801030204050603190b060a0b0a0c080a09030209040303050124050304260f0315060c1009020406050a08030c0f010b0315150402070506 86
    0x9401382040450807503010b2500380201005242d01c1d00002c1e51000f086441d558003148001c010700610030b00b10b0000c0359080001c1c0010f06410720081c2494140b480015007101c105900c441c2c4543c0781841c1c4040180d034011621811603505650105003038a8100019081299071503a04c035601c111584580b0a0195120303603207010f0a0181c0752102c0f0705403110507280680c46054405c038085a04010136800044460703009200720603075854100d87d041e4807a4001001030300d090754140d00081c0c071000180003c00c0141c01007040b198612100a07440e1442e1440031700280002480a00400c5050301c210121043c0128080800d004158900395210b00302010780049400541e180d25026551200f81041824080d048440e00d041d110024540034196201080183ca440c98040303030031985a90f400039580e22652540750150a030741c0041c64035040c094909034544142103440020030707030420600a49a0324040381c801c5007040303a00507888896a8107680d0410381540e814049400c1440003984a040c400007160b1240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 34773485 1250 34772235 34772237
    0xd050c0f0a0e090a15120c180f0c021f02090f04050103030c050c01090501090b0d0f0606031a0a0e010302090901060305030f090f0a0602060c0c0703050d030501050102150405030d0905032206 83
    0x1150700e8070b014013000c40d0b50841d2002d41d54104540240070700040c0c403c000b13541c10710583ca05c0300d4850321003d200040c01000c03121000c10b01c0e00c1d00c1226140782c18074002c1201398800c40c0300030051503030b0380d501418505c980340300c000c500194002901c4005884100f8000c2490300c0c0984188280c0d607403442c00420324455084281c480b4050051000080c3d80b140c0d52000c12030310305039150302d811030030581d2003040e551020204503004e175916594841044a1805a40000d08041d1400140209101003a001603050208a61b20135002c0031750074090440d114400d14192074060314222141d0381c4000c030b20341c010035080d0404ac0161001041a082c40503142c0001d1000c001e0503580c0c0c03030f0201d1400c6d007407014944890154201680000d40010100030b038040117001d501c503402e42242c99071640c0b03032a11410710b40c44009a0f00080d441c0e10040c00296010001c0e40740700d85140d02043c600d85001d032641e40d02c1e409130b07003001510f20762517085890a20030f041090b2a24019501030544025904555610609a0130f2003044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 34774735 1250 34773485 34773499
    0x5191502030c030606030925080d02010e030708070c09051018021801030e0a02060c030a0305060109030c150e09160e01030b09011a0f0c0d0306050a0b0d050c0f0a0e 72
    0x111020500d0007968065659007159030709503101c210400c80f2075000200660300d148500c00e2680d0000340211400400380915403030450000d4104070801c0d0a040200d06041c1c15a0b041c00041e8407440000411110b1454202d005a40c54511920381102080280d50003809014200ba040c0500903402c1001d440469505440c590034640c95440c00310207038000c008035500c3c1d902c16a100c16034103502a4101c043d160b8412401d86e032604045078000b4460340c0010101c918181c0c004100c401d141505445126040802428001d030403614581d6040003503189805030480b0722100384810b20580b801034000300c01d039400080002229280c200321362074404004128820000e04c03621a0b03000254024810b40e007140b10094000b003035983c00c3c43c440c0219007007008080000c135a01000341c11008015070000e8800018400058010881c221130000c00b038889c1a00498442c2c4000385040101c5050f00040301d003401107180011899950304d01c1d51030228021a1444090140b00080a0220740d80c080017022038500110307001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 34775985 1250 34774735 34774763
    0x120806040b0109080d0e040b10050309010b03070b0318030d0c0203090f0a062f0613060506010806090f060d050d0201020a02010f02130e090f070e06011e09050409020406030519 77
    0x111180f481c2440795040a07004400d241540f240b00d802101284000904041076414290010854400e0490320304400900b000c400d004151001b80140000000120014008581000c81751025840090094817681006562000b401c1c0428415078800320001041084200700c6044003a40326880f00d0056845980c2c0308044040516000c460141503c60942d51515840b440c11800d81c2c0f4454904a03100030350844201c100c0798400204410340c070809100c400318428002e07501e40541907030400b070070340c5060140e0002080955290b0b000c00c95403044d4040c51010310340d2203000104081910340080601180501030030400c410707070150000d001c511810350003040900760100c008402c900880009a074600e40702031040001030400090644c203d011041a14150f03407544030001e142c220700d680442640692001007045035030300008645e2404441c00c00321207500c0030a890051100c2c9247c0034003031045903a14000002d5444907442400610f5018007128101e10a81c45000962401e01c08201c40c121f43c00e6500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 34777235 1250 34775985 34775987
    0x603050111071515091104080601060306050907140307030b0409020a0b0301081506030307021005040e0a0f061706180a020d140c10080105010e011e0903120504060206060d030c120806040b01 83
    0x2404010300d03501d5a0300f40501d062821700700140141c000c0f4401094001c0c4404120703c017091254500a10058a00044891500d002e010103600c005000d0300520180c089602c88541e41182100d6101144d4a40010002c0803600010b0040041400180d007003045900c011600d803810200541c140d6681c50304841500c0135840c40800d441004961742c0b50940c105101050050030b00c3d000e410344074201c17802c1441c00e041c2c0f075102c2c00e41d41274411500c404a481e01c2d215143c0c0c00074003d12411010f400603142c66a07074508404d1816945aa004c0d18005003c0c6981c0030680408900b0720120320381e1075000f4000b0640c0d00c00c0342001e00300f45015101c004507a00544449000c540380030310001d282a50240c07140231040c0e00c1c0800544607003101320b007110706000c0703000700c15054607c0d024101d2108500544503080002c0c110f08069880040c3c8a84482c00d010040005222560300040d5203a032100741291408220f10891400b02c3c0c0c503144100c0e009015000c0702d603582c0c1d0956080f86d44980314280a0740d04214801030200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 34778485 1250 34777235 34777241
    0x5060f090f0708030f03100b03100603110a1e030b031605040c020304060804030f020a0c030b0a0b041a040906090204150305060f0f150103060b03090a1406090c01050a020106030501110715 82
    0x30070507400703900400c03000d04070301c1c201c5e070155501418a1160244403696107000c084140d10454800314040b50044080c06000e07010f100b00540c40c89244941d030705042c482c08001d040e00c10079104200b2020000d50120340860b11035000803940c8230f4081c083d83c6521040b22190480740013580102440f4608045414680c1c1e44000140d03411502d242d500d0b10700030748840d201034540000c8650380a04502a120051b8041080c0e001000c0c021441071656040c145132920f40c11085400d0304105511960804200d10401c0c82c0b02c018038980200d08580000310200c0310728001c001056008030081d00142460b12031184040080014411203005d0030a40300560340d007400c0101d00180450750b404000500401107804500c0904440b24954070606000410f0754455414190350707002161500c500340d110f04407410800a425160046400e0001d00a040e642410a042038603000c4051820b0b04100001c20354040c0507100350403910003150443d008010fa00d10b10082c00c1c00a5210850030785142c200e900a030305c0040d40a02c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 34779735 1250 34778485 34778489
    0x305010b0603041208040c05030703030909050f010303050d0b0a12080c06010b090603070305070c0c030803071803050c0904020d060e01141302100e010201090b0a0219050412020105130305060f090f07 87
    0x4113070032a0b100041c2c00142c64030040a441501c0992149a000c2240e80381042103001860194840742c0a1070f145c84000f9042d910000c02180c494540c04004200003604041500d07500c1225580101d070184000d0040b0741008032940c442c01d0500540701c0c091341804001e800410502c1e4680041d103117036a1303c450711100c291060800c1590032030010800111040c6c401d902481d002100f600d410400701010f92100c2445050f240c0083c0d506800000030b2203206030b0803c03070100c81000e9044020001500e140c840356203400350700302c160f8056094040080c00719650511980000b070b41c4a241003042c40050031440b40242000b50b4000c00300342d40ca8011078401e680a0b640e858526034020551380310328119900c00c540250585540302c0c15036495403051000101856103942c8200d00410006032501105070405480941d542c1610b4144070040205101d21510184801c0c00c0d140c0a080003a6684511040408804c100358006420b5018446c01c1c09006001102918001e201100480d0704607120b900ca0251924118 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 34780985 1250 34779735 34779743
    0x80103110f0402120406060f06020c0102070b0d02040b070b0105011403281811130e10050714030f0601030b031605040b0f0a08060a0e01060609090905010905160305010b060304 77
    0x3244095140c54240e84141021001900250600b104000a540748440558040b13440d03e45580d000d01010a2103d034040042c55148018880150f42d200041c1d1501b61038003c045007a40005040d940c0100141c04945c01410441410f41e40d80d072850406410120003801001d000500d0940d00345080a000e40a82e0701400001c0482d000d00000c01c2090310726044041124144240c444c00882d14040145580c0c0380c1c0903000b964848204008181040f9118076600b0301c01007001c0c681890025a1030000405000001c078580d07000035551281c02e0160780c030300543c1c202c4040c5140d0000c100f0078001d00205003603000c3c0078282c0b010302160340d8403410562200c445c2c0710440e186002a85003003000b450540c10400600c24082c10300000c4103100804144032210703075040046240d00030380502003880da0700e00c1048030f09240d0300000c03c80e4030304210000f0107030780e8188603a030150b68461300303508144482903201d1000340f84e007c01264000e409101507103080824500c025108d039449c158400c80a402c104017105e10944c0c1c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 34782235 1250 34780985 34781003
    0x20303010b1902210d0b09070207050d030c05120c010b03070506030712020c0f0706020610050d02060903011401140a0501030212061507240609090f061d1b01030c080103 74
    0x150180c40b0000c101c0211100c1c1181300c0d14220482401c2022020740080da21104926910b102c4880c0a006441c5400885030061140e20100194658086000b0080d141c0881e030074201303c141070034102c0e542c80c01c0c0d10303015000c3e0142c0d0500100715240c08000380f0150140c00003e20140100c082051707119003c912486801040030000038412794840c40c41041e640010b540d0043c208600d400400d0b142c0050071004400b180e1210806001280e0104a0319612801c203200c51000b545c00c207070114020500b0741c50300a02400012641481564003900200d80001000380815950360351500c5003034100b144be94549000303088046012400d07502c80c1c02201c014116400050b005511040b042c0040d18142151244000380b040c820800001c091201c4007a0b4100b11280c2e1100718011400f00e130b000c8a0881d032103148103601c1c00d65420000740450700c411003959040400040c16025003070b0740c040040c03000a15070015026005c0119150800034070802c54203079080c0c0e010005605940703c20b542c00042808003829881c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 34783485 1250 34782235 34782247
    0x60d1b030b06120415020d0207140c1507020f0d150603030f02160b13030209100504060b090f010305100f06051207080705180103020f041205060601050a0c0204091403040602030a030606020303010b 86
    0x25841c032185c510311003080061505200b101c034403040360015201215200344094512019110070440d6141460f4110346840c203044014050422a20440b04001d00400d200107002c141540c3e001031034565190810b0004046c080c02400740303c01414a400124040390201d051140000c2c070000d200384000c0a0905120b806034104000608150030680d490210100005004001a12000d2040e40030b4040d0000403142a8280402c00c001d490b1143c1165a540b0000e000006803561420383d070495401080c05c0c0014543c403100908844001990401c00f08d5090280c0c1c0003d050754000c008001900705120040c1680c7c59840d82250088070907a0111b000031021301c4611500e003c254200100d00005040042c030380884984d42142c01d400c2036100d00c020365135014a0701c090100c2800b01e00d500003002d1915a2402d40d1452018040c0501910082d0150b035856982c0c5041221940071072030310348001000c8175122075840b9002036482e484000c014001a042520000d0082e0000013901d05840018181301e040c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 34784735 1250 34783485 34783493
    0x912160b1c110c12030108010e120901030504020a0801020310050906041401061103071209170105040203100e07030501020424030e070b070510150f05010507020a090209060d1b030b061204 82
    0xc90040d20518140c907081011005543e8100b0110210000404820303031290726060100307007180c00c0b640d481103154101039040003a40c942c0e03000300c03030403031809003000207498542d8000714040302a550042030f80c0d5880081400040402005400e00311041110081d4080e5105005d0000362101740310f00945550780680148441d90054000d80c202c1106041140d08041480c3c489040c04000c0c0f5140002051200c441801440d41d2442006200003505000b40005d003884c0c4c2c08aa039400c014411400c0c05980c0d2403000c1d545000a011080086422034000c2d9100da4403008900700910400980c4160800001c1000041c9400781c010581303440c002c40003401240d4074010043c0200d0380701b050121483e0050000f80051a0303200d22072286110070f178514412005048c10540c050000d9690040c60501c041030042d900183d6428958809a0340381603809a08d80c200c41c03001c01d03114003814282800c5541070034161011000100d02c400d8101c2901e82c4c003031100c03d4441051105900c91004040c0003030914200080100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 34785985 1250 34784735 34784741
    0x501050f07080703180e160206091b0126101205060c030601030609180312150b180303030103080d0c030504020618030c03070306060311010e0102030a0e03030912160b1c 74
    0x203d8000d041c20081e84495102c046850390003034001c00c00d03035020b1500707200310040c0041c80e0000c1c40c000344c00100700c641000124a035031140c48410043c40460580e45410803030340f00d0942c41001c144080318403d01c0142c615a020152003045642c00c007268241700c40090303401c500c80208035290790464090302d85511158124403090344020220380c14561101000a40001e040c428900611801400c0c9643e50700b01e450001c018008085040c024142000c1d111010005159066000c84d003a01540c10f59440364949200d001ca038500814076894000880000f0500c5000e100610000700100d00c2000000c00c00343d400c1c0e045480a0360080c0d040082484156080d42618042d0911320b10014110380c540c1c070301031000a10701b0326280c00c00c4816036141c08040007003002ea0100008e40c0442400d10080c507142450000303560740514400481007180c00d06800c4060b032424421107a52120280c042140c80b401c2d1011a540d52010308881030108005042c00982aa504002d480c146008801c1d40340e61000310311101310213 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 34787235 1250 34785985 34785997
    0x1110909070503040305070c031103060a05070e0105090a0b31030b060108040f02031009140705090f0c0f030103030306030209060a03260d020304030c050d0806101409030709050604060501050f0708 86
    0x41c80030400089010514400c0224002d5126000112b05440300e5030074542040c6c03004d09171483d01d41c104414490070940116130318415410a186c000d842d055000c4c0001e841c170884d6440301c2c0b890f550000701650020101c0311004034100102c1c8030742002d020702c5201d50b0358410b0603100191070740190f800807072103035032160b03105542080c01500b00d103100415540000341490001d034220451b2542c1c0340030035010050151060f810b0041c2c03d0010b010710500e01000305101200c020f1805040c07103441800191603512500560350031038080d0f0502070b01c0790784900d8041c004040301e001c103900c103503d88030001c1c0d00c9181405a450a882c2d01407500c2d80100c5048080c03e0b03041800da03020019000c000d1004440303180c520b10146100303900030f0b662a4011780c820704040d4245905055281c0401050070100001e60b280d42158501289551602c2921041d01c28442507240c003076540d902d0786c58000d21000003030381c2246810030381c0a150111009c101c1141d031240190f40c107106a008414100d0f00034000100812486805042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 34788485 1250 34787235 34787237
    0x50609010e030105090d0306050a0b07030807020312070e04050108030c071e1a1909060815010c020d060f0b0402070309030611070c090501091802060d0b0f060408060108011109090705030403 83
    0x140c03641d11200080c0c00e40300119030300b00301c1c2c0c0c2c403852200419591501a050084c070003a00c88218803420145100ca03d41b08001c4081e0612a9070004150784074400c1003110051900f4010011070350a140000411a100c0c00054520a074241701c004150b201d00801103c0b1021b900070f004103840e07843d0440840703988410401c2d52492503511400082d03002d85c6109201c61900c0742d190b4580c0d60358a44651300c1005152884250100040c1c450240110b64010a00d5500300402c1104401c4210601c40103c2d101c03516500c000b504a0181544e800c208403050700161003035403050409200284221003440300300c0c000c01c00081c0000c0c1c0740800400c045a03066000342814800d100c0010700c4d1541c0e81e112030402c43c0c001e5110103060350707441004201400c0a4400d10716061201c0340510116602a00016054024444d06900b515070b0b443d543d4485540e540a00c03450740750060100c0703031583d07039601c04240c641e282481962619428603a540f95090200c008681250310000d00b0040581c4607000110380c0303904001c1c0114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 34789735 1250 34788485 34788497
    0x51510030609020c01020702130e030f1303020406030302010e060115050714010f020403080c0d030204050a0e070c0b090a140c030601061206050d0c0618030803220204021201050a0e0106020705060901 87
    0x2c9801011070004216030f11044c0009079840c000392052012901c480217144010929264911042d140040101c410f40140c01c0e24042d00c84400303004d01d8400c103259900080d440b03481c280700041019010b41002103114480001d582c91130707036164a400803000700d040320040003031070400503c800148040307082201c4c02c0450000240c07006410800380120707405a002036038851400f14031941c0c0800100710161080d002d502d42582801d14000201e01046202d014500c07185020200141100e0722420340c000032207410602c0c0000d41d041040c8a2510749041107801d44007400c0d8100401000280029101e0301d00c40701138000c2c04240c1c40c00c54122407004041038240c0c4450388034200000d196a4036508c03608640d000e11001020540707020006480030005500400744021007040402c040b840120550b50301c00204000508002d0f0031a8460540142d550703070081d0700900c0400c0300301d5a51164031810b8140c034801e582d6060b2598540c20482000842407184500581c0030800501030390501c0c1002c1d041558041c1014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 34790985 1250 34789735 34789739
    0x702100f0e070e0103021504080c12100c0e030c0904080306060304020a080703030201050f0105121b060d05040602040302010e2b110607150b01030207050709050c0f04030303020711040515100306 85
    0x40b0300301421640529060142030005000758540950034030b000c01d110322200752074240b500710055165840403c0c03851056030071013421540c201d401e0000070700700140c446040040340010580600010903262250b8003034881e106130f22211b810542220342c010390700403000d103086944800800420b9400103004a8104814a07000102c4000c108072000181d40319400125291801080c0281e83c120160700c410b20841400800b800c0140300030035030900465007515107558a0550070041021031080341400c1c139040f4500300c20081404903540c040c10039607200340c1c0e41401c107030710031000c04c020b100340c803104084c04c5220000000241a001e012070043d45104220401c0b008001f0400240103411142050f10901e402000d50240c030010761140c4183c2c440242411401c0802584405079580b009000303050342d4076600d001137802c030303482d62041c1d51155003050400c0740d0b1940c0303038074000313020b900030340030031114400d4100142c256072626008041c071540a541150740c1c40c00c8094200544032800545000a25540b0600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 34792235 1250 34790985 34791011
    0x2120309010e0a05030706050a0b01081f0b0f04090605030102030618090c06030c0c06010806010b0f0309030f0a0207030501050114061801030b060a0c031103071a07050d050f0118050702100f 83
    0x8a60f026401040a1611014941881001d58600400c1480d1441c80c0c451480c40581c1c0040300e4640102403522102404001d0000c1c0c0120501c05070041c510300319001c50f035507107a81c9030400244145e400c407403001c0c081e0709d035070f02c0234103080c1e01040c3c80700c43e8488100c002510780c1902c200d00e0346500400386402c0f16032040844010a100303a0094501000840300064400d041c40c404101c900d00611025000b0602d562408003040750798010440c2080d0000000004107000c442c0800a540b900c2e000050603640d01e0881c0380b0080d5450304640b0048440d9420704000050038150306590114010010340310381c1c6451011461596440d50711501617040c15540c1321640350315250480a0b2120300d040740c8800000402d43d003409881d200320400c01000551017002075100040c00b0900d10780c0c0c2030520700c082030119203c541c0140c540d4010340c10052601c501d03002c2003000c4011150031842c1243d214890552016450240c1141501c00c11920440541c0c40140d80d15081c104c0781e801140c0c51001c007040000c111a002174 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 34793485 1250 34792235 34792243
    0xa05070816140601081b0307050303040801020c07090209030a080307030923010f05040809090709030506160806010c021e0f0405100501030e031201050603070309050d0f14090102120309010e 83
    0x254125481d50080c01d12000c00000d921480000000e09006010541c50500c4895481080f0401421780034001c480c2c0c8052924100804409401e0050039a500c50f504c6070f11490003500040310100e81c1e841000000241c8098134402c551429a010700a45203c0c0050344404882d40d0014182d441007641c2d0b00700e10004034003000c600c00d0103c207005002507220041c5401380e07820b441c01550106d0032249006e040c000090003000440b01c2406d416184615255141401a1100c508a50000d4100d000c0c090401c01c07007105250031f002030900c0c140c985c0001926071100450305030b1001540250401d1026461409040d00d00e42c2d9060b2001c001041030341298800b0001c6801c2c0c079019202c240803281411070030f028a6070103014400110210400450030078182c860a01407604040c402c0602681c00000440c01062003a0010501a80c00074104d0f916042e50440007040c0909110180c000942000181180180880d04490070200c059004040340540888012020b83c070180882520b590f031151680760844041c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 34794735 1250 34793485 34793497
    0x40b060117062218020102100b0d12090b0d05060a0b040303020604030822060b0a1d1602010209060a02060402091006020309042304080a030e0102120c03090a0c0f05040e0d02120a050708 81
    0x41305407800f020551001a10700f60240c2540003900b403c0145401c01c13500c0300206400e40307503007080c440042c000d04581d040c0d42015864104603448200001c44d001413402903080b450240600780ca58500d420380d11608030095004034000100107801660100c0e000c00c1c816441c3c071384c0211451840700b4001c06507a0018071420042e41c000c071042500c2e000700b10090b00e0b12521100080107542c00003504134905500b17100058800402c1c1c01d2440e0a0f060b00e405900380300758182c440440c400791109a03a01c0c1c0c40c10000e945c8950884089115a1aa0340003c03401c1c035030b16086504942c9150015030170002c0708d40c2000b028001008038035010480e0a15002481c0c02c0651140d4021402115040d95680d02598000c0075a040400d000116a004000c80f12240c81500c0300340d680003840e40c03011034890b22000f051508000d510140038080b8006248040342c90700310fa000a0381261402ca07810040300c2241a1f08507101c485040381d050250b0061918034a48003115001000074084906d801c5241044540c0c98240d990440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 34795985 1250 34794735 34794761
    0x708160602060c0a020a0308090a06180212010e210c03030109020c061005030c13020c0a03020d1b0b040228080304050a0602010b03100e0c0901030605040b0601170622 73
    0x2810041000580600000b078100400d00805031426951500207503540340340103c01001c02c920900000c04004003030100001c195404442400800d160005000543c0e14820f4144d100f50703900c003012254030105200e000c0740c0903d8040503024002510740d02101100e08240108000c0804000c0051821030038402103018141e800801078035080140041307842d24100800c3c54403d082c4014091080d03607400204548111412650003450b40c0242c42042c0c040c0c00782c002c80f18154400d803051705e0201600802c00e4034441d085036655aaa5400400d00c40103989a01c1d00e010b0807400c1c8600106015041607041d0145215030b941c800441525605001c1c2440c0311140d01041e0150008a000e00c483e20745040e51000400301403000b480100a1800000d40751034568150400712980c0303c203d80340161090108244079000101640403d40c1d4a05149010340802c441c02c031040110702c03001400075806072001000601400d82405501d03550720040c048203024208d250b142c0d034100070821070b4002c111070044490b145a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 34797235 1250 34795985 34796023
    0x9050609180a0203090c030a0503180a03080c060f060a03080904020d0b03060f0f01060c030203030601030b0301060f030302030301051201020a0206040f02040b1c02100e011b080f0708031603020a080c0c0708 90
    0x5c0150210300340404400100d120360401701d000310114000000344c40d2038151101e0780d031036041c00b00c0d400180140030381c2e400100b07001c2e00840c01901502e0042400c511455a01a450003103951b80c0003000b0240401d4040100700c1002808201131030304240c0d01604c0c601c407103803c1c0010a41019000070785040c40c2141c0c0d4551002c01c00f400c00040040e241c51032401400d4600340100c1491259402035200d0000030000f5041650351980080955000d420080007488410b000790f100399200d00b4001c1d01e947c4240a0b09001c0c0c21030100c2c640c80c01c1014821518460001e901030b0501d502c45558005031868004000d9901c00c0c0c90320a400d481d981c0d5844050081c1c1502242e0410f0783d181c40c4184214601e80c20680014416000d000000d1030341c00003000300304c15030340782c441e00710031100c1d40b629540724025400c201c80124804074040040204800c0111300030b0340029240039a02c002c0304400c8059115031020000010606004906107543d140c000d005403143d01819101090b895000c201d1070720004048050700048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 34798485 1250 34797235 34797241
    0x209091606030c0504060309050c06030a0e012703230a0302030a0e0a02030705010c05160f080f06040f06050a1e0f060807150503040312050405030913050709050609180a0203 76
    0x1103035003201008201c5070400380084005110041c005000d144159400c1c9525015801d08000040c00000140100101402e403241000c6085c0001007001c0a2921269071910700131012030742115401522040b0900060b007e403082c07658045a00080100689045503145884c44031800380c080c01924008529a070300503100c1c038024900205640c1c0981000701d058000c040c01a01689011070490180d64080c03d041a00310007034036141d4503100612203024000c2461600102e00e5943c400c06910885503160b0480e2144041da0380d425848171070a50f401800c0070720340f001c250009003464010962011101c00001034265010400300802d100c030849104d000c0d550b4030715040350000315206039409881060014070281d4105800d0010104c0c5141d0751800703100c4044000340030144030380300350340244100c100280110304140c604156660002002c1b14031910111348103412041311481a02e2207a00180c1c0c400303031030302d06e0300080c4000b90b408910b52a800c910a44035854903940407032030990080610700c0e00180c0d286 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 34799735 1250 34798485 34798513
    0x13030807020406091b2f07050109050603010803030a09080405060705071802070206090d0c150503091203060303090409050f01090b0103060c140307050d061503020d0506010801181503020909 83
    0xe15980055125034038107641c20300010519525144605c1d0a82488034450100c400c4003044c1c44c2a140703012141100e1040c0390024180041482e604542c0300fa01e482c18602c1c0c0340c00400840b40800d0007100300c6507009100165800c40c0c65040003014500407040c240c0341c180c403103000c10416404104240d81c0c0303038000541080440c1c822103001c1444000017030b0440c1030040543c0015018850031500c544500c200203180b60600071555003800c010100e4000510410180401c05003007038004861071342d41d60007021030713100490f60300d442203d21601c001800f41d8540b40a03681040000d011100c01a036062040030300d4804885400d1241d0700c0024003031606583c280d8036510300201961a04d603982801c07c40b01000915580000500340c0303401c40281d0034880d07101e0309000114401010b140c0e01281500c6842100c66220a4241d0b000f01502d090380c4c801805035685007001901e60220a100346200310a440c030b4035803001040390b4090b100603000d135011441c0c207558070340000340c00e600c0940c0c4505031a000500554051 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 34800985 1250 34799735 34799741
    0x50d0302060f0a0213090911040c020d08070c020f0105130b0c011d15060d14030307030f140c041205010e0102040803120702060106050403020603091f020a020c0a0807031106130308070204 82
    0x880400703501e840241d206205c1060100d02c81c40007041c0d1140b01420811443c01038880303c1d010003820411806801a10095030341c480c498012004c59445004251010f11a40c4400da1003600a082000c81c800d8650044a0ba58002c4c14207040c408104080454000f80480052200380c201e00c0c004a12a06142c0c0e244820100c40004410b050780052020f520441c001e50541d58001c0c0112482c15000889050181403407074416211303c124040081000001501980030940000341d54000b001302c01c80749014600c0414054800c0004c2c11010f020030441070004c1c1ca0340301c1400d4410800400c0402900642c03600b66001500301c03000340c0e0808518000d450001c0381201c0d62003c0c884c0700a2225501d40324025141380710380e02019010f91b00000025240b11400c00c01c0c08c890700101802035884518200303c04d030003500410208030042c06070300b44442c0d1624043c82650103542860010309840c0749103a441d1201c41e243e01030075582021043c072141d907400c000e00200a0013035010b4400f842c0e5901c0c140c8104011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 34802235 1250 34800985 34800991
    0x30f02150907060305130506010807030b01050301020a0207091a0a030c09050c0f0d09020a0803130e131e0201020109080304050303010303090b03010303050702091906080106030210022a0109050d0302060f 89
    0x180c40c0c03020488050000248030b011900c86080000da9a2207640400310040105040903203680303c0d603800081ca40c0000614403045900170147c00c0400c4e620741e000c040c240d10904070142c00590181c0e00a0102c40d00d50790140180308540d181071003191032000081441c0004503401903500c80d010310410440010a03001d010713030100d110340416142c0000200d0b105a280164100e001c20660341e00c01807400c64450440d80e40181282c0f00441e91204142d50860301c820880d4000c15280504010114072111040142f2003501c6c2e90015480b03e1050311816420386e0b10154000590441d904c502009010450b21801075000314003c0001d155258114240603099641d1680401101001000100b011a9000e419a03c079030754100e40c80246525600ca01c1c2d042c414490446403401460b080c80041d4101c415441813040b640309464414404190320000da03256050510442020240c4107151086040401c02011844070b0504003011400e8a5001107030070b0301c100000460169200200348004481810030300b80d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 34803485 1250 34802235 34802263
    0xb0303040305120d23060109090b010906030908040509040506070305010e070c0201050d11040b09090c070201210207060507050a0806030d050d181e121b030e030f0a030f02 75
    0x128041c0307035030365103580c071428100b80ea40c03074150114094032801c01642098907000c3c44011078125080b4141c0800c90000c8055076400d010940c8004001900d6682c0d000340a07104005848003400709181c1038090b8054609408120340f0403004000100d01d641e285d412280c0100d005000501c41e904d0403c8001d81160360681040c5a000041c40412419983c005002c9948940c20318056898150300e40351709004d00022101202100004200455003102840c06000140030896542d08103840c0e42d109005a407180c4a0f01a000684207031910b8200c144004109480000f0b04800500d0280749880b100e00312a019a000740c0018070005200340031592101c4c2481d0040f03800c030060800d014420f02d016003207202d0900320140e00d40d150107404000d1340d2601e182d4a04a40c00828100c540c03030341040c5058078211120310454408010381461003c05d8412880324400d55150204072102440940741560040c4501c8441580341c410301c0050f14000006200002c0124443e84560303410b0050a03101900b442e04e4504400303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 34804735 1250 34803485 34803487
    0x703020102040614070f08160b0c090102010c03060b0711150703030b040c170f0a060803030907152115090f05010f051801030b070221030708010f050303071b090f0509010b0303 77
    0x7401044400c552a54011f5220514641c0c0e00303502e405803051015140c07400391103800500d040189407000000103050380c8000741c0c000c10005410480c158110b031501d0007603030140e00060284000180c450100000f94840062211381200700750510707112941e100e10700071030020b91039118100580c2410302070703003e02140d207050030305201000c0b020b06644401e0042005041c07a034058003041c1000101c1d800708015000410692b680c2c2c0c9090318245640b02c0c441d100700c000d2800c22001301d0180c64401c0d2008000042a0340c4d82c40c0b0081e0340f5403040360142c40080e2506e4214101c0c0b5a00095011451181500c2209002d0012920350f140546082803c03070503034801d500401c00d0074441185c0d5011f076110181500da20200e0301c03026490f0704004900d061000401318000380c000401001001d803545c006103119040a99a031340702c40c0e0701d5070306800c080310f01841250303010f0b0320622204002403054807800d920000c046a245000640d0382c5a00c1040d00c8440303000000440e96002404100301c1c1c00c2c00b599101980a80c021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 34805985 1250 34804735 34804747
    0x30c050a0315090804080a0303330308030403050405060301180b030606060706090620030108010506030307080f0318031803011a030715110d030501050f040c09060c0201030b060703020102040614 85
    0x1140a44048665640780fa03076a184001009400001e4078040c20102c0c0445107801214030700540109000300b401c2c0008500680c124044202c0500322896404038092040542403075a070f140200c50f0405001101440b400340070120303142c2c441c0c101460090040d0740b184101ca00c00d0540d07210407110040102400b80e00090100149d80c0ca07000120381d14154401c1e00003800c3c0c01e19091800c0145403003000d41c440140030441118107529250f01075810f0702c08503402000340d625038004140c0e603403068280c01000e144044c00100010403180b0050350b802001d80e01303840d0443c802c1c80c02d21070641c0e0101c03040c00c0350703034500049418142c14244140500700801001c298145c03622600000e940340d206100c2d05180c003981c131142102e01840ba1b1080f1a118001d035084540c41c840010014014000c06d009540c000c4c081c505c2c42e003050b0301d41401007076207806460f00c1e4004003500b8101d00301c0da50041207100fa818103403581c4200c0320649844009004041c004e0b80010303291403c045000705079224000003219408814005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 34807235 1250 34805985 34805993
    0xa030f03050d1e1a09011806050d0819090303020a020607020f030f06180703020f040504150608030304021c030e090c0c03030c090906010f2106080105100303080601050a0e0904020d080c07030c050a03 87
    0x485d505481d249000750003600404c0c1d8444d40503040b507403c44da400c520590451800c01400c00301900128154200d030800030007046508907031002131848054010390290b5410320140c100304000707020781400600842000600b0801003407810031513618180a6603c10010814416404c21490750100360f42c501400341c103442c50300040c4031858151039042c0700321b0b6143c010900300036001100441c0d01c99110014881540c0d220540368894200721400d901614034280c07a0540c190018040c1000139034151190000e141070807040c441820001046275054003410000441442d40820141d880340400c40030b41c1340d640c01d4403000c7c020800d001920460600000445407181541c104440712000981d03400c8041d5440c01d190100400b90000354060b04240d46054240210322640690420980707000c0e8480102c55101c9000440d241d00c50103184000081c0005035911903464641030703058010740018124090f404058071541d684e903000640109290b800b03940e003081045107908003480101411540c8048079440e68603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 34808485 1250 34807235 34807249
    0xc090b13020a44072003070204060603020a170402010908010e0f150402060d0209061606020d060b0408100506060c010c11060f040305030a05060d120c0b0c0301050a030f03050d1e1a 79
    0x40d03490701e00808a000481241c41105c1820350f0707420112010190b1500110030641780e030301285003607010f6418034a010910380e00a00840e03040c441165508507490801c014031084c1c07024050300480c10082d10100c0050810024000c1c800f101d6800e4001d08124141070141ca0310f800c001d000b030810701402e09810400580e50300f90aa4075600c1c0d03012005a910b030190f81c000703240c5200e2050601c1c3d0600b00c0102202c24010360783e01815144240707600030080390f601c1d03150007040d44c040d42c400c0b6021640a03141c80052040039810050b0450406010a030a0240a000180c00c0d1001e00b82801d000031680060500582c1c030070405d860b0440b01c86c0805006904083c0c034000c100c0c2c03000034004d44200d512500495801d441e03d5000040745e907040a450398001c0810500100800c02140381a6014030380240820840742d412012a412180000c0c006000c0c1c61941d5252003070001a0703a82541031207000d00240c0103a503410b0040000709a030807081c2e000510783c00c54056084442618402c000c0d100180441015512018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 34809735 1250 34808485 34808597
    0x30b1017060c0a300e1e0d1b080403060212010e0903040e0408130f050a050102120a08060d080403030c02040f0b030726010212040302070b070c090b13020a 68
    0x219001c160501c0f0030f00b0212a035004110302140c0314500901804056900c0d60003004810301242c151807001124800081010201107648461b0b600b103140140865805150008040c0d0b4200c02e031f25070035546684500c00340c0e821503401030356141e40000d8580c801114406c0d616014281c9000402d0060800074120703540c900490103606061240e00003c601482245015035924543c00d0808600960b03c2d00d171114004801442814001d00c0c201802007482d41c000325000f540d54441040807814030798886812601c01c075000c5c24030380c0c104445590000201d4407510081000c1c40c0251180700601d100c62061004441030f81d01000b007514034004c404415581c020402c203003240e01e405041d812074640701162006c121070540c5000040c1d071000419013003c0d00c605281611590183e000e41c5c0c0c3e000c0d42c841031102148543c62000b042081e052005200d0034000340c0c8024140c100142c146040e08100e8194a01240d00541039480481d43da00c202c0b605400703240840d004054000e042c864900001820950303c668507031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 34810985 1250 34809735 34809737
    0x7080106051903180c0f120222090203071409070509090411120a0b15040908030a0504060f05010b1803010216030804020d0f08040303030501080c0906060d06030b1017060c0a 76
    0x90089890b02d0b00c20f81280000c0007110121100424491030700c138420512501c5000d42d58542c8400000d0804400007003180d44580103010101c0b00e0b840308442007144d048184000603260307602d0100e030015072000c11884010382141508034090448003000c00100c0b00c4001c0c0424100601082044035986480500c2600250300401078440c0803c41d000064080d4071003640c1c405a4824526900d080c001698100340c081ca003c9240036441c1c09083c4c05000076500040c4000c0c1c0080001c2010031807000b540e5002c01d41c014024440065068100c10385401518004c1e4082d0701d000d003000c00e000303880a016131258001a14200d00131803a1140b0301d015800c06003d00c2a018060101003030000741507484006070600810351100200340010300600d0310710b4564005000603400a803500c0d00104d04130b44001004203c040005284004a990711030410000768072100c030340514107444000000c0010003a002d480d01682541d84620040c5062102c3c04003c035160030301d080025440b03201800541c0d000e0408072080241d203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 34812235 1250 34810985 34811017
    0x110c0a03030510032d061a09010806100302091906030311010b04060303020c0d03110601170f0102030108060408161401020301060e04060e0406150b030403020604120305040312020a12020409060305060708010605 92
    0x40d100b08049450b160b0040070b080c00d814401050303407c00c04200c00b022202000c680b19400c90b600c03a424960390351000c0340c16102085103a04107002601d8a014219030202942034180c00300103502070580301b91241030b40214049035020811400d0f0042c00c1c040c0046424040c0d0702003005610b1910025542d5001030040ca00402d903031849181450301c100c0445c2481d41754041256039559540b40d080d62500c1014058510070b0080900c2c11081c0700e03043c02100c2c102e6450f01c004107816203e988902d2003035445040400501c8000081d400300181c4a100400c1603150351400050301c0b50314058010b4400c032881c028492045d4500308040c40128039500402d50841d800010000d6414060f44000e100d0341c28940088d185100003104000130540e000601e540319500c114421a802c0c0d840c4d18083d4240c4005407801000301d802014052402442d40d4050002c22240b0b146c903200710b10410160b030040382d2158101e015070355101e42d424030501800700010b03070300240b4900d041e1200e985410380040c030901424900c2548502 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 34813485 1250 34812235 34812293
    0x2010e010f1e0c08040810180507030b0711060a14010611070902090102010b03031c0b04020c10051510090f06050a0507030f020102040906060309020301060608070512040501110c0a0303051003 84
    0x40b1412103408955400410261780e261901038040d40e80b0502d00303003104014209a0703400400f8040052082081e9409001001c2c2d150860f5111001c20300000c04042c20020342041a010704202000380c5030240c20b071280d0003c0c600f21003200c0c107001c01e1016003081d41403090061450300740c583c3c005005c104540e014240161150542c0c00100e002d00a00c140300c0d41d00d0700c000304003000001c5000300325103000104030340100b1100f4105401c0c002a4003500046802a82041070303a02c6145846810065211303003110101d01015801c040001c007000f0030042c020340007840e03000061056010041f9920003400701c60420505001e520030000b0103a209462000f000c001140940b0065903000f501070ba0041d180307608082c8120750315000c0090090002c2c0d242030b88a0b42c200040060904e0081045a014405550740c1c0c61034040341d40ca84190039500944202d0700740d9654800b1200c0b1070042030241c1550798428010349100211403e000301961070260900b01c450040140410000d04000403001c010802c0c87c103c0c0000344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 34814735 1250 34813485 34813487
    0xc03030d0b0a0314100b04060303090608060d06020f0c120403020d150e060a0e100b0a05040b0d0204090f120e030c040905010e06070e010f020c0609120f100902010e010f1e 75
    0x2e159035200500760025000e022140340008100c810b50305440103420440310702550200070030788038144005004200c001a040c030200d8031402090b0362140000d4694030f4010f0031659400d0072079008071000b130307038400c1d000c2880803601c9010f010f009201c0b21f6003010706003800d05540001301d245030603107001040003118103101c40b1140301c9500120300d40d14190b019524580340204103840a846d082105a8550040c001140d41c444142d20a074882040080e00c14881c041c00d00040c80000c020021003150300c62585016003005030740394002d040901c0e1217401e20101c504000e10780148640d010301210382c244404079442051035180086d507906a240100c8011486401c01d0800c0783c018286100c0d000c01a0140c18204984181c201000b00c0b180c5c842a69035a50441ca00c2d00200c2e261ba600c180000c0d40008104002d514a150098070104e01e042c000e000c1c0c40180482004080ca05209400c1c1e2144c0151140441030544da00986408807690b000e00b40f00c00c0c0311a00020040803110f42c851440c6911001b5004201d4807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 34815985 1250 34814735 34814749
    0x20319090501050709150f120b031204030303050c031b07020a150c020102060117030313030203090310090605060108061c1b060207080607020102070c0b030c07081204030905030c03030d0b 82
    0x5565102010400088a42040c0d40030f0078045800d10007003595180300040091141c5500c0d10700c040c050303964010101c081c0741d0031140c10b104181c1d80c01800d43c480c499608250b40c28004160010116201e69580d1459887c01600b541e0000300847d0f03800c49c007841081521401080b118036006200c81070b20b0307071740c04951000075070b01506500700407001280040564a85e94026003007000941c001d030222100d036a0384601056080d444602a03803100d8000f84080360110b01013541c00000303203100b801542d09001c41b440110b0320300542841100181740d20b980c44c020600c42c0c28030549412240c03e1804002d1890180c0104249aa05c81403a140780c01c00712185e0414410107220b80f1204034480d00b4140d0485d55142402552990240600225801050b002c42d00e00341c014421114000c4e0702c1503065001300d2818040d0209030708000c0c40010107a604112510004070900c0082c1001607203a0100042070600c0d080090a185003900314600070340c840f144252040e84c002054038194036456001007901c980c4c0e40085529 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 34817235 1250 34815985 34816021
    0xa1d040603080d0920030a030e030715020a031403130209090c040e03071b030c030818030d030912020c0a0b07020d05030309060717070c03030b061908070f0c11040203 73
    0x102d00e50104a0400361a502d40080c66207600400170b5143c15601c00500061103130801d0312103a815801107002100190040d48000e08100004050b0740b407045c0c3d01c88501d03101030010842e140043c0c0090701504101a0071241d4880b0580e510881c0d00d0452501180028800c25941006840307109814005290100c080108841c40203010740305100008d068414075503a500050710440311110084400440380c240250706404032908450307105182469600e40400b1580110000d40c0d032201510400425510b00300411012011a90342c0000d1500880c1040514140c1540b10a4219081010310046e1030b0748501014050303801e0034901d03596846642c03000454800d01c1e180010030310b00000c41040301010002c82d10a204071020384542989813401d042d051481c8208603058004154400703548800300780b00341d100700901d11020307103090b150000302040248106940302c0804002841d00c0c08101c034403540000c01c00e40142c220b0a10103207402c840c1d0f5800881c2c1c509203a016000d070740c2c048001500400c8038402040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 34818485 1250 34817235 34817243
    0x501050d1b03020301050a1202060d02070f0c03030e0a0e06010f0e01030b04060902040510110a150605030a050a060f110d02030705040f080102090a060e0102060703050c0d020c160b0a1d040603 84
    0x10000d066040c0c05000f80d002403140341c2c42403040391000280c0c040e4201114540e00c0d801840b06180000f00c0d51444003d4201244c280c1d0140000300d451400a00214403100146000b074070713680c6c42150b40302d040003ca02000e400c040000c0cac00300000c0c0490340e43c12120040c231100d15030030150f01082084004030024402c90b114154000d0030201e00081007049a801882030b42c60945003010010b0114400740e44d44008400542800d502000b0494046003043e11000c031400c1d160140450300e1550349002034540450807509843c0c5801c02c0b43c05030b041024a100e42c039500c0e010b501060081c55070b581004101030092904a00e44d09400000240700b0b680b00c3c500300e5018000e06441c4110f01502c402c240d03030007500607002c0c060040d42c0101020940038000c591040703407004140c1c024540c99441d500128040c03e00586580b030325810500840c00040221b0024120711244e182c01410b55000c0c80340e940804c805903070302401640d9030403c26071a186034007500240c1456803056900544940707031b038040740040c202c0b0b50005d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 34819735 1250 34818485 34818521
    0x40b100e010804080d021b0f03071505090c0a030602130806060a0524070c030308090307020a1e0305030f070302010615021c0909060b220806011206090210030b03061e010501050d 78
    0x4047c54100c50b94454501120200d8039180c60240e0385680da4803580d03038007600082940b05400c40c0e10b502e58121640c022040380a07200d80958903008111891480d40003104d62980100300c030390344c4038030310703400c000040a800e80180b4a0342413140120710004107a0084ea40500c000380020424510012609550680b0441013607a03100e0560400c4800c1d0400c0340004c50018046201281e408403000040e1500d09070001c01194040d4504a1006032228078040c500c0c030300243c090000008168140003030048400d00040e159550081407800a086814541011104004101380509911f03800203601d03102c044800c02c2c14003141403115083c0e0700c00c0010b42c0202101e0b804c00d6001308103103c103900a00103001f005d8100c24411390303d4080c41126000c00740528049540a480104210980c4a180d242a5401101d0004500000d038006c81e160280f500c0e071400110f902c4006407540350404008040d441401c8861024000c501c01e000100122018411181004004a100d03200c500315075100402c0d020f042c2c0c00003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 34820985 1250 34819735 34819747
    0x21f05070b0f0106020f030307050f0d1401031b0b0408060a020c070f0602100b010305130b060d0b040501060602070501050c06150a090e0706020f1f020310030206040311040b100e010804080d02 84
    0x881200d0b40d00b4058840140500d142e017905120f000400d03680609015282e413070410003002850011500100e080281c6c040e180e2081c0500141041e0a03030340a50701a208048900d400d10520f80c000d04025800ba10f00020200f0040103070f0400840c8184d0494032a51025940e00e00c45140e880c90071105400519200404030030000300319400103100001e08940e140b050003000100300066007107070412100c4100b06280e02180000044130016007070b5100100610806c0c00c0102a00e55a68405046030203d5090f907564505101d01c03a010004080244001d107002440d01055160090b1954409444165401607244004901d980c5804025000e8007072440d0400c80194800690b0303954800700e116800243c00741540c5607600480114902c00104c034650034221404090003400f0b80294802041c110045502450202c0140d892100800081d03002e403100403000d4000c40304120440c2c942c0d144451090301e009804000301d40d00a1b50740c8031080c00909001010341e4590130400c8a9200f04189031030190b01c00525 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 34822235 1250 34820985 34821001
    0x90d08040b070b100602031c020c030409090209061917070e09010506150c0a0803060a08011e060f03120521011e05032808070501020406031a030109021f05070b 70
    0x14001d501e02480043c0503545070304810404018203406404c006810800100c143c05002c00e070b070203a5554400d10010714000d00034820b6030071b640103070301301602c0b480d10b4046400951038501d841c55007101c1c003201c0000c12010009010820241360b8454011031040744044401c0d0030740140140c000070005503800d40c03590300e00280941d0091200300ea0140c032503046040f1610b1100303821016106403440c1000244028440b54442c40116040100070301c0c3d03c0b0380610004100c4400c207000307140d404030722186842e0320700b00d452a005007546c010750083d000f2084d0340101007020925200b03c2c0c9030868841d0500c0344e5a002001e0710b0003141c48000d0102150001d07008000205402c444505282580031803980518007500ca404041d210b440280309410b214082001c500c02940c0c2441007121003601c45c14100340341450710340d1081d00f640c10580c80540400d5440c0600c142d904a104600c0c0c2c0086002c5000b04803032081580012106070741c18041102d03110580e095601d0442c0544101c8281e260004950703441481c180311 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 34823485 1250 34822235 34822237
    0x1b07020904061d0604020102030f07050c0d0b0708090a0302150601030f0518010c020a020a05010f020321010603180c0902030a0209120c030c010203070f1704030b07020a02100c030503010b090d08040b 87
    0x4410b0b884001100b442204000214104c5d00495050b80503503e4111304e1100c081454010410a40d82e600400440d80b20541da1701d02c111699601c10000102e0310f1134051005003081c4001001e4034126000841c1080001394007007249410125207204c0c07080e580d120307100100c0080894200404141d4a86002e00144495405d50b80118040d958028011f003484400103d85a18034000002d40000035158244204d41c02490300d8110600c0d0361040301d080403914540c50080e0a840c01c51444030310f80305401031002c03071341c140200e50310f030504400310b142c3c80101592485029040c9100700101d07103a020010450f50f0500c4d404540c1c0300880100a00700080d9a0310310f0a48449960303c450744288201c040044088d40040142c038a40f640002030f0300c10b001c81c2030312401580c2c01011500b00019804110200006075410801c038050261079000781200c1c0300300d106120000000384001424400c1414003000004e1f8081d044070b06444010115503112403a03100840e0a030340c591240100080030118001c02c800d01280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 34824735 1250 34823485 34823501
    0x30b0d030309120c0b0f040302030c1207060b0901061706010e041505040606090b03180a230601051509040b060405040c022505090403051809070f02060f07081b0702090406 75
    0x81034800205030050b40c00e8070130001c50b04005010740b9054000030342d210600900c0c943d003e03002e401602e1a220040c00703802c2c108404034001d9041c1d50130100d041c40900c4494411003684000c00c3c0c443e06070382d504001d0b002d00108130654044050080c000e0000c0e986903c90001c9014802e0081c00c00c0c0200f045500395082600743d01e015050065142c01d10000301140314a81060888415052052440c3c03940c485014801e00050480b41480c800c1c45134140014100c41a004004010820100088414036480340c1c20408180d000921960798070044a00c02044041180c0034040203d4001541515000c085403150082d035100b641e00c20714045106d0b5003181c01240440401441014403c40c040c100b07804100d20b003090f40a16500031050100080c0001d01550050081a6120301030103000481d4800240f41d001080795042c000888181d80e104080e0b40400807282c1142c40c11000314068a0031940091140000a15007068402a0b4410700e001005c04003c0b90403254020b1f0980441e0f10f014208400980051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 34825985 1250 34824735 34824743
    0x906031507031d0601030f031107030803100806060d0b06040b220b010206240f0112060308041508130f0201090801020d1506050921150406090303050610050d0c030b0d030309 76
    0x19900f50101031004140709043e42d5015290303487c06521503e04440c0850012111039061007010307408008274101c040694403540404190720351480c2000203490070504090b090f207002e5441c003000d000000790072400840c4d00003025500082d0344182e0310000f6102c40c1c14110031201012214811103449a407039040900b00340d4082e001c40c0c9558482000300c16042810904020000c1d131007001c0c8600364548401c01241d8040149450080e48100d00d00842c2229910350084a81e042c2c005810800403c00180510b0481800d041c191003920700b02c01d40c2d9039540c103c880c005203031102922010085a018101003005401ca0788021911800e0807607000c0014254915125000114107400081151283c0c0031524a09006090200703c50841460301c460441c6004641100d4003031600208000010754100b03a100720300441000c1140b101e141030160444001800b214007a160703152410240c9908901200e983d0050018005441c540e40c107002c43c000d000003c042503222079007000240030305030716801260f162405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 34827235 1250 34825985 34826021
    0x1c09050706020f0f0714060c030c100507030905060103020f01020a050a1202072403271a0f1303050304050309040914060c0313080d06050a0b1201060c0809090603150703 74
    0x11074071602e40c1c0c501900b003001409500c000401d0000e82100d4001e20006c4c400900b1050410113074551450a64011217400101e41d4003010315640700ea202c9008154102c0749506003041000003075140d841e15030a050002034000c0c03980070040d50450340301b0418000c0749038200056860410311454610a8000400c0d84e0000510035040d0100d50010b501c440046a04145003000840050144007074000d0056004a0400c0c21074050200072a8441c1002840c5114400e151401522188000c2c9154400010b4090000c840d0090208200b030240301003182a1181c0500b0441c0d2681e0712890648d2a61007001159a0440c1c107042003030080003190141c16120301070700801e03280d01e5525840a1003803400200c481050554034040c801000c2140c0c44020709401105c0031003c9405500c1c1ea005c204c0b000040d40c0070744002100080c41d0510740300d00743d400c28090000341c0b40c01d805000342526002014000d000145214544900c0880c0496904004546003a0070941042c0954908044082c0c0105140c3d040c01d180080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 34828485 1250 34827235 34827253
    0x8090d06050115020c15090d02010905060f090109090207031b060933050f06060a03020d020f190507020a031103010e070e07020705090903070609030215040c0302040f021305061c0905070602 83
    0x18002192205092031130b9006d03414454204200020726001c0c0700142d0500418510120b540d4584c5002802c2d03084040448944d07401044d0b000500c598141c0e84405071182c03042c002c80002944c007050503020070102410310501014241406002800080c00080c4412541802c1008951020841c83c1906c54225903d0020641026002c0255401140e050020294140000720035140920141c04407600a20b00107040c564142500c2080ba4086003a03d0807140001c12113154010241c19403203148950307881c01c1d6060050641c0420031140700b502000341802061401e80300316450961024044407050400c5401e607d0b515600d441d200036052f00c2003801402140004140b60502101d5503000d45044802945824410f4503114020451590110218010300031482181001481c0c80d40c043c50141e018550003629610412084400078118080f2060050109074100440e40c01588111041510040d40e1a1011481c1c11480c0d00400f4404608924004106040c42000030340e031001e40710542c088500e881 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 34829735 1250 34828485 34828489
    0x10506010f05031918150603050d0906020309010507020f0d0323040e010b030601091a03010f06110307060e0c041e05070309050a030c02010c0b0403080f07110a08090d06050115020c 79
    0x11104481070843d09584c2c20445124645682c0410703010178040100c4400460301c0d41e10f886000081d42c5a0000554440c002070003840b03801d10252074a15042d061000c0214039294020307449000301b2240605100303001c2141401c0d500c0c0d04045019810005080e4018242c81e89406000703030807825002c0c0c00d080625140c2006c40e869240071a01602d0100ca611502c585c41c0501201c1c103548001d00a5041041001d000240000c400542e06440210310050540720b40c100394035881c02800303a5105008100340040310070181760300813007103960781500070034003240c40682035032858074050450003010781041c600b4440410700b0068042014211201801c00c0c8087e80345c0080c01c60603a041e42901402c01e030800c03120800060700422803046000c0c410304040403110000d4032002620101120107a000c00c19100802640ba0030030701c46903602150a083c031070001d195010883d41c1c0c50158180080c010a000210031540b0f550f00c00d038551105a024905000960311782d60440360094480c2c40350760140c454808041614 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 34830985 1250 34829735 34829737
    0x30c06020f0d2409090206040503030310080d0f080f091501081006050915012001020a1d0406030312020d060801090501020c0f1b0d020120031b0c090103170f04030302010506010f05 79
    0x1900745000080d400d20a081c40200805e6004070380c400f1041000040e00e49051018500c1168281004144103161284007820880d42845000401003130000d0791000f6608026071070380100c620909048070380e840c044064030707220a030f049503641d104023a000082e41c0032001031042e100c45000c1d002484142d66503014800344000039210042000c0404a000029500c40c010041400340400206948100c8050101c1e00b244d2000c080000081c490304c81c00302d5460302c11b00f02000d00d208281c804000322072071510002d081d0110b01c0d1045240a400090300044120160000310141a1030002009945880c0c9000c40c000d51007424011803602030812500746070600814294094070181c0101c81d105c15480041080b81c40802004134140a80c002090184203d001c1d200f4100500c43c5006565503224801c414504c40d4050304292059401010b00c0d00030394442401d40760440c0d5100c1ea5803003250420501840d00d50080c150f0744104400b0219000050641c1508600d001e140e0a80b42c102c080a401c0c0b00455807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 34832235 1250 34830985 34831031
    0x100204080c0906130c0806010305010803070b010504150512062d010612090506040c0e0c040506070f0c050d05030711040605010e010c062007050607050702010f0309030c06020f0d 78
    0x98116a000900c0360820345060340e400340c0010a00112984c184c0520300071a0136a5043e440010440020040c1e1960144505405007218000460815030700b50b0302c0d11210201406405c0c051511640e8a4000b06480064034001d00b01c028001444c100380500391075628001154079040d40016041c1242d401403104030114109c1c4e00381d416404080e07007810403d4600004182c004000c9581c0c0380b41c6031002c0350003400903a010300e100b01800900c04c0e2800030405d24464024207280c1c24403c04100402c5141d6480d4102c495081d404045103001c541030341004506030000b9403040742c01a049131869801c0000c04002007101a115030b0010301d00424040501049404500841c0d0101c1c150000005003580149007019003940716400220b420a190103159080740c4110b880743d43d6051012640b0010407405101c41540700701c4a20300b413401c045141d00002c0101c048a040c40c400c1c10303078030284402494031a00922a026421050540d0b4566040360340c107080d075001c0390540f980246040f00a008800e42c9043c031501d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 34833485 1250 34832235 34832249
    0x8031c0603030c0b0c0d0f0903090506030106050912030702030a0f06050708070e0112060b0c070501031a01140a0903060216110a030506010603020906130f1a1215040e0105040606050102100204 84
    0x4510550341e120381000401401d0030f0352085c0309001c0120b085170035014424090700c1034440030554001c1e40c0b40c05032804a094000c284a00b03000e04c01030000b80e80c40001e988003040304031243c0c010740a005c08050b040d817041c1c80c400380d014080c500a460a012506a80d651080d204100402560f43d48075000c5616010658110f4001080d1024040b00b0f0f40c880e550000c0071021400300050516078607401929598400203881c00c8680044e10b082059681501c180c250942c81e00c21074001d50600724000810072003c5035007003240841d02045103e0100d01c180b828401441e0f01181c110b41e500007071256038210070000c0104580c2c0c696000205040360500e9410070084030740c400002d001d281d00303184060307000e0340154817501d07084201404010503081003100b4420003009450081e1290b03906000040800c803003184460341100c20108600100c907101e040210383d02c0b01d54903004a09003900c400002d400b400355101004481d40c2030009010074011a0fa00c400c0441d0b4090b000c072010708180558041c2640100c3c071983e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 34834735 1250 34833485 34833497
    0xc12071403040605030f06120d020c10090b04030807030c05010218151204060f0908031f05060a020c0d0f081810020c010e09090304050901060302031012110d081308031c060303 77
    0x2506016011b500c550800300040541c842c1020840d030b910b2410818101c1040142d00001e505480303420500d00c0505c05881c58900000e40d20b0410012461911403480014003236400029011705242c46207020008007a84107000b9540c07041003408510742c0d1184005507a2103403050707800320507885c8201402c468400b40420400b440300e42c0d4540b07525000341644007007003800031386031409540040c0c000f00c0118859129807039144900040c41d040d4843d9140190000c6014460820141580c140c00065509080204a441c1300000f0054a48500856021742c001800303d1800f1030000000e41c4c07140320006604005481240e03180440890403a9140d04080d2020f0128100c0c0740c60309050f050004c0100c1d40321001104036858a599407000c1401071200764460340c0081c2d8003000f03000750803041030f80f404001c04024403030340050101500c0381c01c602c000c20314015116441a010200c00c00501c0720544001c0e81c10000842482e594903c10b182d12030384881e2191301810045480d403045550309114100a030380c0c0540e101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 34835985 1250 34834735 34834741
    0x7031a01060813050102090d030809010606030507080c0a031404030c1101140d020304020a0b070302070819030807050c07090c0207051503090607051b01050109060512010e0d050703050c1207140304060503 89
    0x15a0204a040f0003e0340c96540811009100352030741069240550300c25940e810061600c00e140a0071905c403500075004142c10a41404401c5600c00d00c8030381c015140342c0206540d40c4540c0c00075001441c44401d0980082c51640400c0149604455a04c0c0c0e218044c801107100d0105580c01110070000c50a00840007400600c48a203801c08650301442d805032004d00210b4100340c5034100109581c0091608500503401340605118243c014013079001c50040104001c2032070301171030f40c010700745e464010450405c000020681000030281000380c000104030207001040100003248000b5103418882c081c01e4003440020781d90200c01c0140d04101c81c82011040003905840e204d00c04101c420b90700c84802036144000185c91583d03203241c20300c40d2500800c030100001440614020138020704201f01080140d01c1d9140800d1040180f8003c200d50190345c0e0b1600d8400d81e030359038601d42624240034100d40d0340810710403004021000201e440c01041c0a03402443d4900b880c1010400c16070f902d202d9402100d001900c28004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 34837235 1250 34835985 34836001
    0xd021c05090d08040e090f0c1f0c020a060908191109040305070c0906030b06060306030705040b060f0f130b0c070506090a0e090604031206050a0506070f080a0207031a010608 76
    0x107005801c0300103060b185600150385640e11190040d8100410252446082c002480000c100865040611b8005041c0030048031002801d5010b01078000d05000d41091030310780e0740d180b04409001100780d005000070065504d0340b50040c60305500b0700070280c19219020182c050b00300d140724018903d945c0402c140500455480030311400e82400350048081c070400348282000240911041700c0680f48003040003031660300e107080200b090b490240019001d81000c009120312500c02203050001c0e60426280881c2420a40340441e16074499010502180c0c0404104202120b003190000c20102d981c4510700000780e43c0b110141c400e1849994030303040c85d50340300c0d200c200450f007806005011380b00f01c000e00e0040116510000c01c015400c04403070140322904440d0401c02019044001c09020360081c10b0208506403c0c54082281c4040c01e00429100c0c1b000413907841c0400c00942140c550b4903902002c141d8540301c403518042d5840034280022200b2060000300d04c2180309240f204581201d030559604c00141e103030036072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 34838485 1250 34837235 34837237
    0x50f04141f0c02031207050a14030606070b040203031e040305071a0304031209020d03030b0a0603060f0e090f030417070603050c04090506011215060806040b100503090102040906060c050d021c05 85
    0x4500410340c0410b002c0c204078017007000106481610207407916960f4040100c8010000c0b100d152410b4a00c0400303109100194540c513064445050b0704c00b9090050751100d00020b480c43c096840e6603001c2061540c41007582680e07800181049034400c00442c2d080c6511102c010180540a03021071141003828800200860720500c103240c606001141e0019a990054002c208150190300096000c20b4a5054890305400c11030304900091195183c200041424980300070f01125191103002c43c23900002c40030507042c1030180000c1139582510b0040742e43c5d4070313981d01049025042124030a00140a04540001c01c5e50190140c10310400c80c03981d00074034250515514100901019158034100701e8040c50320904114984501d5605107002094801e1309864a00700401500300101541d0003503003880c4d0300300b090351076036030702d1400350791a505040b41c40b650342e00d44580c02030240f5800070101e1420801d000580710f402c070320104c40e101c0c01401940e000d88036044c0180d96030448607811042001c03038140d80d1b44005116070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 34839735 1250 34838485 34838501
    0x3050706110d0203010e0703090804062105040b01180b0a17150c030a06080c0604141f0e040f0b010207060807050705030c07050301060f03080f0304110301050f04141f 73
    0x99000703100d9640d84580c0c1012640302c1c035a5600100500012103070f11140d6600408070328040c88041d190f230380c81da607443c0140d104500c140140b80074202030400490400c1040b00a80d041c04220a142c02d06200e280c0420078801c409401024600519481003940901001210040c1003184001c1c60903482c042d144180094200190080200315140c0c402c80519460061003c80c5000f9200d050090104080710705583c07100d41c00360300000350300410313854440c103450465043c0881c2c009005908804210341d0710940c50001100300f08008030941c00c3d5005240c10303018100c15901001003200d06044601156081c0f00c1c8540940c0c4021420403035140310b03040480d444501032600d541451419902c140c40d41e003080c0304040070390704401d00620690800b40b103080300502c1c698a00c80c3d140e51071500e0f414454400e41841034142c55002000034140305001d510b004400078081d0080005240030300d6441714444086e181240c1444417600310301540c8400280c079001c05c120b00521000c2422101601c1c90040c4851 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 34840985 1250 34839735 34839743
    0x30c0c030a020a05010e03070201020a11040b030a350702041109030a03030e0c01080714131211090a020306030c06030a14040302100e160312030603060f1d0a030c030507 74
    0x100a0061940424009004414400e4004100d4414a80703490340c2914440c140424241c0d0040c0807a40150382d00195612409410450765003540c0c1000000c500a0641c010341543c1500c0760001310b07000c000a030b00001524907040350650480c101484640f5125001900e5140b04030101802000f015240c41d511500b04804401c161500d0065a100440d080850001c0300350003003507603030941103c405828050702104610900c0d1412041c540508003404c40c1410b40e030303007510700d0710f0108040c080504071184250240041121040444076640b0303000e4514000b94610f0f5000390401e40110321188414000c2c0c030b0056400502a15500d1500020300c805504024080200d654540c1185601d8440748000a4042c1d030096001d48003408103205040203403842d00e854005540d000c45040c4d040d118418983c8000e60b40c1c04040c20103003400b50b103401c82c0a08829003001c0e00c40c0d40340c580f1300064482c40b43c1c01225180c0001403003504104440d8907483c0c03a00c4100c40080c0100b01c03600d00e50f40001c5c1c8660000c1c402c5600c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 34842235 1250 34840985 34840987
    0x308071d01052209020703080901020a2c0306240d0b070f03060e0403030222030c1502010e0601150207080f12070c0f030302010507110616050d0f020d140f040305040506030c 76
    0x10641980c00c3e1040654004035100741d0010345142403540c01107134254080000c030000d628040e0300c0500200420005000580b001e440000c90200001d400c426111507000010b08550890814400d80e0503a02488a44030340700301e0604031090090705040c2520507100f1303004400c0d0005503803545016901141a504507c2c201540c40d84007042a1540c00c3d10140114060f0f0b33401a04d8501010000c00019078603107040042c1d9a1a180070000104005644030541e45000364600c5d003d0784580e0203038090890f074083e452081c0070b1640007040c411140001e007180302c00a90700b29482c079541c0b85611621200c111040c0c03030250b044840c002096950610040886900ca40100104260341c4c820400922840742c00440c0182d44987c14460309a40c4030032100c660805400c05804642008000290141c4c4149110024810b000c101e03030008080ba684182031b61000e09134203560b10031086140c00001e1a9030818880140010303030210700c44596000e141e920440e4035031543e610b41800d03c000c002064000030104191460 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 34843485 1250 34842235 34842277
    0x9020a020a08040b040305071a07061e0903030b03070b0f0306060a050912060627040f11120a0c090204050303030a09060b0a030f02030f010203072a05190308071d0105 73
    0x16540c2c0100024101803044684540c1540340c0a41003041d10b0f406015200366105001e40c20b0600501101c003a181d0050300082e8200b9003140c80a1041101c2c074040100d01d1404503003030305160705504a050104070440c180c5010a40b81e048803081790041000580b103155050002444900342240200100200c909009040451620004460400300030102c14643c008406101c043d003000003c408010103138001c0c00e440b14a017001c1c40384100100400141c10005020000700900c2200c50b8040140c00001d07088656035070b001c6120307039a5000000400ca80c459100c02c030005504015100ba80c00740c3d00c00a01035491a10781c134420030043c03e011003042c0d4415603200180d07441c0f07944503a20080214810880c01e180340281d40101414555000c400815503401041040f100c07580c4141805200483d01000200181e58440c8030f0a80c4080007100521034401d20401c1c031070000c40074001d0607101c1e120b55941c0c3c0c050b80c0c41400c11079001091a10a014820101c20000929801070003c0c1022100000c2c1c00700e6841 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 34844735 1250 34843485 34843493
    0x506010312030608030a050f0d0e0706050a2d080a14280902010917101a0306100605040b0c0c0409080415020c0901050f180c0306010e010c050709020a020a 68
    0x105080e8001c884400364a9403141900d90180154001810050085c4d41040c51118014001c0e12030600c601404000006035484901003503400842c0e1804030904a030041038640c200038103181d100218080124041c44c0c0c4d4906070541b01002c40740980343c02c0c0e4119007031916101003603510300000f81c0440c01d03994076416040501d8111180c110300c0b4819030a1401c00140d036024185403442c208400840c04d0600389803c500150340c00c804c01c1800c0300d511151414480b003030790301201c0c104242416115400c0c1e080507d41c010403040903c3c0002900811025544603489664030444003040d24401c2c1d202288050008005025240014000c5001c4610942d0a24103280001a04846200c20304031140b050208046c0041c0c00c0e00a480c42c3c0c108010700007040c03000d824030b00013600114144a010302c260f540e802080402d455410280ca0308052806a506460900001503100707601f0448549001403421100c2c1c044540c8500d188442d074070f41050180c180c080c00c1a00800103580180c0260042d40b05090301c00c0c00207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 34845985 1250 34844735 34844743
    0xc1202071209090507081906050607050a02090f0906070c020f030f0a060501090b0f0d0503040e0403090503100207120e01180603090507050102030405010914040902060403051c050f041202030a05 85
    0x15845050141c0304015a1900070380100c0854000d126050b182408004059800030304064101d00c5942c0312a507588a6a1441005002c9940155400100100784202003007800a000c1803003920807550a4030f1582d075120b20228152040300e0401803640704a001c9041c0a014500002c6554009000d000c0718100070008245442290804003113558403405080c428841c403403207414090443c0d0346003807085d41c411030002050b100c903881c4400d01c5061b0314005001044400c2084078001c00d0700100c0e01019240c0b906000d4250f01003840358134022f00524100c494a101c2c82d20840d80440d0b44012050300084840c0c01c203c030a03c8549100905010018480641c404c544030104001410541c1d00030445005a14220742030200d207510860556101380024040744c1e1304000b014040e12034050007890000c071000300080140c9400e03030029400020002e004014000003184e00700d66801104084204001c1eaa0021206480b480761000c40003001400144001d002045100e28080d000504a480d03000c3e031070b1500350034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 34847235 1250 34845985 34845997
    0x5030f0c0d0623090a05010c02030a020a03052101060c14070303050a080910050c250c050904080d06151b031e02012309070e10090b12070b0c011107150c1202 69
    0x113103a00c00c40302c5178104442406108003c5501d44060b42c2031070711408000e0b54a0410020003020701001040190035840e032081001040541104660030550350790901405100c00c003107003030343c11300e0100b11070000b54600012202c044a5041d40d8075450f0400d4850121819076002e8903505050103110361080c01200340b030142034000d198a5440f86ea03a81005e1040000c84007011011213190388103c084813012410820041c0125203090b2040409641c440c509903859224600300d80f034415242280100d40c600d0584003001015600f0b84079400c90504107003812800080d545402000101c07810111800d4001c034014242c0080202e00010940c401500f10081074001892082e4865107440c82c02c0000300d0070108806002409411075040d00b5041201c43c14071034818034040e00c04850b80307800706c008072510303103680092204d0711090541c0c80c000e44461020382540e001c1c0540404640c20519a0060342010b00c08407141141e000c6d662001c59903540141d40b000c4c00c8180d0510051003440c000042e900c104500013855 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 34848485 1250 34847235 34847251
    0x40819020c010306050405090304061b0501091506090b150915030114040513050c040513050f060106030b0301020a0c060f02070804090501081c05030708040206040504060f05030f0c0d0623 82
    0x5501c8266000101110a04d0703200510550525040c480c00c4800482114151602c1d0303c0c0141a035980e001000d840000d200000814070340c68042170a09000550240d00610701074100306200301c40d42c0d40c0c1075800780d618070106141c1c0b0a03011074000c08850000ca0040040c1400a0003400c0c0749d140c00c0007400c410b50000d03030101c1101601e1224034440d80c9014070a2562291a1700320420104040b0740345d5a40e61030b40100d4080c005d613559004503071310035406c7d02c8551216a2020803101e800410b00c84640d01d5000070710030800401d0401070034100901e410300036100c606651390346100b20044952912006003159013a201c004603070030443c10011a400000a101422100b20045041d500d00700340d440c034203503183c1a10400307120041e044690303503607010085a8121000d864104403544441c00007a205100707903407189611504d84080000c2a411041c0740c002251012800c0c0d4801c45082006c10307888281d2082c104d40d000c24000c8046000620716170001d0310881c490400d0400224071070310a088401c40c02d41c1c03426 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 34849735 1250 34848485 34848493
    0x8010b030f03040b0f03040f2001030506120a060906060506030903120105010206040c030f0201022517060c0a350603060a06140f0f04020307090303080c030705040b0304081902 77
    0x21080e09081000140d40080440210310f0030386007106000c0a800340a400c1c0d810000e0010100b0b0030b12849801c5600d4064112003900c80c1108148000c81c590000181c5490200c0d08020010740300e4908820411030303080c01280a00420030705603460000034003514070216036407613403071401040c41d0b22840701961080303c01c0c8008503641e000402c0310524111059200300d0465000e0403c100000312000d0001c801c81c1c1d031158442042c80400d10040c0d08056903a00355040c481c181c07040d12a800600b88102d40105d8204100050b45089280007140e100d840407602d09204403410498000114896041c0b084d0b1501420440050310000b400c4510415030f075503030071007140c41c2150140140d42c0703810f01c404e80d0019001170341040451300d40b0f249641940c0c00e28013000d11815038084200200d45070039000c1405450018001c664900d09900050510105c50000703600090321140042d265220010480303010b180907403112410a4508580440c0b607900c028002c84440c0c0081c0000c101c0c109001c40d0000c02c90590790060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 34850985 1250 34849735 34849751
    0x501080a0302160b04090b0d0b0c131d160908070b070b0105010c0f030e04020403080301080102030f0c071104230403020705011206060819090206040801050601031805060f0a0e03040801 81
    0x20f140c141e00c8a040d8091040309481000882d09810450f0b08642c4418004100b0100100005071040c000c80c4028088985280400440c000c03440020400c1105186000c4c0c551f0751a0042940301d01c46210211192143c0315001c40c5c1c2c8100c1c550502c5425048901d0041c1400e52540c4800e030405040d40e000c0c1040388e06c0170441c60708001c5002c0316030780074103428684448400480e4440701d980f1404010050207000740004445425126a0111005960044041552542d58a444078001c0d8001c441018200c41500045011030740d22504643e102d1350424081c6141c4051301041000a218003400004003418100a4544601070565030070b10460281d000b03081d0080c40e04001604001001c00e00456051030508207004036038010014a410051020303500e10501101700c5000f0040c41d18401c041d52245c0041400140030005402c014801d4500303903010701039031880d1b80302c0321801105070b903006207503030014400503500324030801d10180d0100880c50042800e20340c0842d460300b10750068100c2d0032503035114108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 34852235 1250 34850985 34850987
    0x110102010b0f0310050901061205070801050115120c02010b150a030c05040f0b09040608070e04050c060304020a06080601020a0204060801060e2401180506040e01140d0314090a090501080a03 83
    0x1065078014007941c542c0c1c03240c2c2e44038000903140d1045541071050181d031007011501c075110960100014219180d0307003460076070b01818500c0d0b4810b545e100d1429950300344400801c000300c0340ca45d50014a02140c480e0030301c2c90200120301010740303184411481150741c0c030700d03640e00559508640303100703506582c5882c1076441c0342a5030001c0076504010420700900c40c04010130044c00c0c1140d80d1100031110550341440c1c880701204002405801e543d40b0081c01481411000710304000b20a00490040384140100c0381c1c984d1504050010b84c2c0000c44002c0c1d0302000e0407404100c0180241c00b116441070b4140b050f00d0b0005420350004040f945c00c1e800c40b80d05a95245018846600455031658200030103000115080c0c000c01184112120a0014903040000d8030b014600c994034489103400150900400d0346032260748a40402c150780800344079054ae16510410700001a06018180f0b00350a5016038415401d000004448030303035070b404000069044070280c98005034500302d5100d00f41c041c1282a0141642d1102c2e405c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 34853485 1250 34852235 34852241
    0x30e010506040915021303080c0303010f151407050a0f0b0604060602010902060a0e030f0604050c04050601030e0703060b12030d060311031605091306020a08010501020106170705060d06050d11010201 87
    0x15540110700c0e1811000110340382020107401d40b0020600966101100191b004954001c2d50004100020110707a4484e12391011000c2c0d41a182c000e402600707440c0e91015585090301540040c0d1000c50042d2880400b10466036004141081c040c0c030440305c8100d11341e590b030801d00602c0b8001365011308000701444664030f800d0042d0f200034880d5100a012007400c5800080c0b2074410020020240806c115840245442c02d01109032050541401e580c000e2806081064441c1e246034042440790340b8010000380c45600074071a4a0510b50307610001c0130014107540d9940700821000c0c501981c00060300c2400065140100010002c0039281301000c00c0541c0b451408204174a035001da40c0b480f0350091032401204c140c408400804072542190011819110100d0801c6180100708018000b980005a000c0080c2c0d0415602030413034070207074020050590703a00300d054641c0c100f407030490b03c0b40c2d08260403c12183c50100c02421003410040780008515a442c1c00140c2c0b0651011030490310201c00714a500e22940c1c0a00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 34854735 1250 34853485 34853491
    0xc03051c090c0803070b0105040b01020a0f03020c0108060607030c0b0a06050d030201020403020a0504180303200301080c130c0f030504140d021006091122030b07120e0c0a050607030309060c030e0105 87
    0x50011800c21101b599403505407401401440d00496490700844905da00c00c000110f00250400c500c1e406d44003442c01e00030740303450160380902d01148010010640d030f42042c034108c8408a42660b18451210801c4da50003401c00c20150000425a0302c50101042958881c584031034910f20076000180d407540341d807040c4061890aa4005231090b4582a41c0100d0b00c40307001c0498480300d0381480c0008a200c6001540341d00b900ca0035074600030645003c80049110900002c202c01c07142c100329141d40011440d006100240c1c6c0c030391100ca80019181205201105001c0d40145400034460302103a09100b5600e100b5901c0c082c103038003100700141d021140a0001078414800c0d40c000d814501000d020112207080529401d100300c035071003180c80e140d1440c850b0b20018401100c0f8003465028840000e2814150001031080a00550104002d490048006909100001e00d1510000041e00c80c0c60b0a900e030000300320031074206240c01d03428107898002d1580010091301c076020400d95580c40008448210030b03603040c2110002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 34855985 1250 34854735 34854749
    0x50f0103050a020d08041802090f0f13090c03050d08012301020307080a17040b18070f0302010e03030c060108070312081e0a020c01020f030703140408030402010c03051c090c 76
    0x400510100e0008540c4007803482d010380700345114401501d484240c5101e46d034000b040c0b11050302408110b03c065034000b0075130580102c56420307110404000300f01c00c050206804541c80300c0481c1c0d070450302080b160801c40400d03029001c40480e01d981e81d02d41a043c00f1284130755000198283d80148500c603414010b2a0214840000c04400c1d03555400002c0d50780d126121003d84207907404111402d01c0381c030982000e040078214000480207410207203030100c10300f038080d00c1100f40180e01500d055204040042d800e000c442c10701c0305603c002c0b80b0b540c005450154401c0f0200c1e4260001f00510600c50b00c0c10032459000f0560017004044440c034505001445a00d40c040000411200d04140103e0444940c2a01d024244199905911b516012400c0c0028441ca140e400c405500210b10000030b00c0d000340295109544640701800405c0149040c0c03d026003045270300800c288414008140594465020390060520078100b040c501004503012490200030602c103c0b6031103803104980d008010001c41410001c0041d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 34857235 1250 34855985 34856011
    0x2030708010b070b040803100302040e0a0c0504020f0403060506010513030c060e010801060818030405030109080d06050a0302030a08070302100603080702040c0905060a110a02060a090806060a1202090a200c0105 92
    0xc0d0740c52a0b400318000e08046d04100010001c03a03900c881040e904801076034000c3c01040070f08040312586465000054081c2c9004000000003d0b0505042c004c0750295044401014501800d590700d000062102030310860402c1b07000c0c4610b2082c0051a060702c400f460061850304450343c584940204000100000345042050581c010020300e0782201003590083c00140041c220301c02001d21552860041e5400680e1540c20108a8014441180f00500c2e05210b14201800103a441e8003e0204620184c131009415501502c0840c0110341944d000d080c1c8284280706640070750341700c1c3c1c410000b643d003d0380040d10364510000f4aa811458588502c52015030f0504100e402c19243c4000243d90f40601c140f071005011103a060302a80c4c001c10b00041ea41a41c0c001c2070035464160f000750003440c050085c0607205441c4500000b00f411460041980821560082010702c0f05024550900102c1c02e0040c0c0401c0f555920341724018004400035001d0a203c0001c1a09191101c0383c0c1a0554256240503004c00c2d1a010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 34858485 1250 34857235 34857247
    0x10203340f0b1b091008060f060a03020921120708070b010b09040b01080906070e0607171b03070203210705060f0601020c010804110907050c010501061205010608190f0b0d050102030708010b 83
    0x303034408481e94200060411024a03514107002c54900340c08c2d16021940940d002590b282c241d40c065000e020300c80c0040e1000720741811a10460954103505015115071a800a14050010b241940042c04030500c90b200c15810004503640b2032000761001e03008410103150100b402c40c042d050078801c080700fa60003440e02351500d080c0700307000c10f45502010b40900c081207280051301c01540c40f0201191070440d84040400448600107428100540000d080b200fa54003816848441e01003000040e64011900100900b0003061800700000714080b8207a001180c01d0342c18040c007000300380144800741c8202c4140d100b0b08124902100020b0a00c091021481d06111805045c803000c500103200ca006100c6c000e482e415550b80703035000c0648180c01a0140e103401503080c00f00128420386e00201d0540070f02c514507014412640c0ba00820b403030700c8e04211481d000c4184110016103a80c0c1440d00301c17403686070749090006040140c0001050806e0880c03841039036030b69000401d04c50901c1e407044020340140609100182004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 34859735 1250 34858485 34858489
    0x3040c1401020a15090201090609080d08100302100f080603010e0303010b0901020106080d020a051b010219021224010602030901120509240405010605010203340f0b1b09 74
    0x102502460510140108426415034000c208000f010340d00210f40344690b850000c00603020b04003406007280002c5d00f14100040440c0580c015a06440c6420060241c48903c1d9808885150f0010640c2d00030900c4050000090b80f219045504400303195501d01f5103a21071010040c003142d5000c1d200d0340c040c2e803402d00100c1d008c62020068a0641e4441107034942e5404200b00100d01400c0541c005494034015109070300b5515030002201030ba5580318400356071400f040c0c1524124096070754003002d40503800060801d02110a140381001c10180300404400b040c11161fa581460320207095184048480c030300c02002440705000005030f006040318802189040b08120000302040c0001c1d1007500403075140d4010900d00c901c01c0c0885450b0001450752000c24030502146030359580400d5405440c1c6519000010407154400700403940d0741c030600d580440245059a040d145e01180d13449803030f400013840000c160006040c21303d01c2d6a8090190580903920700f40403044102c0303107000d1081c06210305070401c00300d140341d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 34860985 1250 34859735 34859753
    0xf04030201080604240801050708130305070201031d01020c01140403050f0d0f0c050904150b19030e0a1a070518040b01032013050a05030a140708030c06010603050a020304 75
    0x2a950a280c4440e02d80c0f00ca0303000c039000c0d101d414004104c140880392018501d14840790080112004907000b8403080c0c0340e2100c150340805040d100c0185201145400300d000c01e0141d8010030161b481031500040100e94150784000c000d020b00c4040da044e940004202d50b00c01424000e5030701103500031241c42c1103401d140e0b0380034240c1e10410131084a0004041801000d01d02580e103c004125421682448911015040104643d006039681c61060380340030900c0100344170f840300d80d50645103039000492418201c2251050300a40b155201c504050301c031034804185210900480f20100e206202d00c81000d03040c1446140b041c50300a0413007081160600c0364450b5426080380b411480c00e0140d40008903802c0310b200480c00352514031446648521340b81042c3c511034501030010300c2c41100c4081005841038031042000711810031441074941c50782c041e10741c1401140031090322030010100c1c40c0490ba0507a964a0140341945c000d0310510700140c1048004104894050080503401600c0c240c0441c59440e2a507035020768 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 34862235 1250 34860985 34860989
    0x102070509100905060d15020a030e010506090103032109120306080d0e010f110d09140102030403050a02040509010603020a0806040320340305010207050c01031112040f0c0602010b090601050f04 85
    0x143c940c0b1038000c117949464282c413441125411189600d02e14040e200f040700a580306c5042e040005e894000c080e41507050610a00d0b004000081410300aa46141c0f401c803201c0b036041d00c445400484510000c03602500c9031045075141031041c0144d8450842080000d412211542c0c840c0056800c401c007400d1070503030b201203504280c1e5800d090000c110000c070001110343d202e0100c030712111f40c46188452000d9075081002c3c0c03401c494200c0354003c0c4500e000d000490312406031303200050055120b07041b110018030b0301d07810985d88042000c0c00000d01d1a620740000b542d9240070f9000c60032a030482030038003007411fa000700440c08040e4451010300e00e504400c40d81c5996100032184180d01d4807500c2c00356601c5620b052140101c1300c6c00105a80c21110b0300c82c203007a8000c0d88039403000c854900c203801c62250380754000d025040660642c42902c508040c0c1403065500140384c001d0045411400c880400c2000455609000300506940c1d8000546600ba9005104e44498007815440c14421300740301a10246c06520210b4003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 34863485 1250 34862235 34862249
    0x504021c0308130f080d020d060f0609050f060c01020703080403020d0c080403200301050c0a0909051b0a030e06040c0501260a0c020705100302070507090908040302010f021903020705010207050910 86
    0x100404150905002440400b84c0c004c00007a000601d0903183c070007a0b0083c10141c2e25041c000c0001c103580d02000c0c0000ea8440c4900804681342090030021481c10702c0f114080070300c0c087e09030752034100e00b001c030603089070307c00901180801c40d00f00c1071005140e070401290158846a0620030b0400b8215101d5040c5070040d40301c02400c65100518001000c2c17064081c440d40c104010700284000e04040b20000220707000022440700107169a0000501210a8043c1030300403001c980320516103110718500000180d11401d0064285912142c0c0c421612504224040c4940e0280204d11000d034107101c0010401c400344001c001d12400d25202090300342c03404c1003142e60080030508000031900d00408041e400c10030035900131b951042c0030040c07007030310307217406400074031070741d032103203095424040e01c0b204005d0486d5110103003d0032220701400140300550180c0300700307446040103004403448a041c2c611101c2c2c13114400c1c001140180c000303140401a0756010012040949000ca804000c03c0c680407031100140c2c2c0c00c0703101e010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 34864735 1250 34863485 34863511
    0x110a02060414040213030506160503060f06070c08030706021b061b0c0c060706050403020106050a060c060507270611030c061f0302030a030206060102060106030902011b06020d06090504021c0308 85
    0x90082e640f103070304660160f035645003d0485d069a03820460744132101146ca00c01034041000030000700e42d100710100d0303104840c000e11000d2060141c905009040d000808102c401130114403004c2555142000509100c0b4402d41c809a9508003070305610103890407070441420749500000c00d00101c1009042c0810801c2c4405480d03d0711001d00e074480524200d1100e0205811890018400b804c0c0065604011303c20750094000340400f950f0b8500340074545445100c2e1000091600e950080060f000c0c0e00210b40000592801126440700820f0700d200d8a00c85001c03140e02203058500400610303400c0814100354405240145040040440c2000d071100402850b49a03000e0b081560f003600b8042c503401042c091500907085a0701c10b460b9140281d91307110240c1c0c017180540b01d01400091058403c3c012103211a6040c4d60f05141203c0064910041d441d0000044810b640c0a001d43d00202c1c81c070340306e43c0000300000440400d00e0b05060050002d000301d2801d810388080703203441a04021a0b0091803030303508100c49040003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 34865985 1250 34864735 34864769
    0x50603010209060a020105040b160f0c05011b0c03080603060c0405040e03040812030709080604120503090703020411090f060403080a05030a09020612060306070f09090b030304031b0303110a020604 86
    0x1038024481d82d034030701da030005010a5064525034150300840c800e51140c6010343c015110070901141c7d414401070300c4400a500403103d05842885400314041c0b040c4950004900c84070100308104203003546211315000079010304041e130141540450101e0f00070b88203401400d214100200d100c50b69105034043c0c1c601079521201c40c880c0d140001c0045800030b007400d809403074400001e842c403065075a0003a035942000898100b80851031000c0416207501072a03009843e2803420f91070100c251020f400040c90a4180d0040a00000146c0c44d1402030111000c01d50820342d98462002c0c0c20410300100c0600e51500403403050000380700107a00f98040b242e200b2041e081941c0c0702d0f0340307005426000c0e044c13000009400410103d001c080c2c032818040420300680f07088060300e64035a03580c0b00444840882c40d54170400035a0000081110f84955480351194150140c00c1d40e2600340c0302d4a030800048880303941d1000354259000c04000f419405514002007018200181c5040c8543d9000180b56015600941105e0f0044201b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 34867235 1250 34865985 34865989
    0x80a020702130204090b0a14030606010f0c05061602210a110a0609080403060b1e0103050612071d06060f07030e0a030b0703060602060702010b0109030807061e021e03060f040506 78
    0x1000d00b8080c000b14065503542d888909443c050030503c0c000c40d010b403c00314804211003207007000b00b4940704009030007070040e43c1d104801190a00d8541c41075009104a002c40200414000d00501f44908c40c800202c0031035851001c8001c0c50000c507030070380807085071580e841d08907a88114803c65091217294a010701e03d02c0e54000035241090a2600000c0c026460404c8010401c508200034004407401810201b22800d8540148020182502c98802103070300700f040e030b90f0555800f0703622542c3c10503400b0f031052031030030780c0721118616100c03240d0004000c090704082110702c030400c5800a580e01c101c003510594148034400b4075031221400340150040620007400380c0b02c21540c490121410085801402c013581d41d050020b0007400801c99030103600c0060040c100001d11041c014001d103891240103070f5032103600e240345071503440d80c5030440d050841e4a5600c90100840044040b0340d1901c8070490604010f0307642c0a2880e0402820341c814100c10303207004041c000c0103019900c039004a01c1c0d054041d0b0f00801e0540e030b4280 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 34868485 1250 34867235 34867249
    0x20411040e090a0201170106050d0509010b060715060f08030304060209031204030812010605180603130602040303021b011809021b030a050703030605120d1803050706080603100c080a020702 83
    0x1000891a103000300009001e000483e0b1810703500030307220044509205030351642c1140090190001060b410001005c45071000d500c4250b021000000000c0e0f1041c41d0000902075074440c01e800c0c0d800f0203014040f010f12100511031140100b010020300d050716881e01a11640702c0c0001000a006c0035404104900d02351014050510302001070800300c2d544503180e00d09440140c00494828280300c020500104043d4040c9040b00c1091942529147c40040c0070340c02c01c03082d50310040c03a480d0003844207403030381d00040c03024000341000d5486034001c0c007403000d43c1110072181420058009030402c0401d019550f50450040e00340301c2504c02150002da5519070000003604100d01c504c400e41c0c5c5610002944c1a845c540c0030000e00703c81c5120b940c040c800e0b07540c1c48081080e0001506034544207038201203031660300c90f401001d01e40c014150b05501100303450360300d450300d50400d20740340c1c0400042680e260400c40c0600d070902c4100241061814100415045040c000349582001002c21030669400500070f0b0030366a401ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 34869735 1250 34868485 34868489
    0x100c0c050a03120305090a0816060b0405090703030f0e01080a09020607020907050d060b1305010513030804030305030a050603031303020f0604030c08010603110108070f0e0406090203090114060a080a02041104 91
    0x10745044025a81ea20f0840603c40182c40c141c40001d01d4200810711620021030340c03c5103690030411250402030a89456040c1c0564010101ca800307607100807121460302d442c014144103c0006000e04001459030030054000340248004004105000c8405041e60303030840c1d00aa0003441910b400184024144089a1544070700c2078065441f03407815080001c1b00c1c2e4001c0040501d291400002d00007283d9450100d41d0f24040c60201070718035240e4900c01c1c000c55100e440039100600192a00803040c95680d2104041680103030800d0300022000801c00c04444518000c10341c1000e070039801145000c181c113030303c02c2803140c1c075000003840f0b0002100c01c140150b961030b0503203000c0c50304042302840d9a540d55481c80c2c0204040c2c072007102d0b00b502c4441d03441460340c0602002882103455456098403042034000440301c0480c4240728039886540c500740402c0341c2c1f0162015511990200d400011480701d209400c002604005120500c80c46600c07605202d0310720003050782c85281c2e9040c0c40115180403800080311242c0125 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 34870985 1250 34869735 34869739
    0x304210c0203011506090b09130b030a08070605060a060e0f0f0102010209030f1c02030406051b030d1802011206050f0411070b0c040303030606030209010c032003030709090608030702100c0c05 84
    0x200d000f0409400c00c4034200120341c01606c42d22900365075482c8151341c40c003c0d42c0c071b0310350700080904000c04c1c0d001698105c540d200b40018180c5203040240c0e0b45148080c1c11000d03080e01d1195030740c0c080102c2e41c204001b1000203003000341480070510f10380c130740002e030511b24400c40b041c020511f070024024aa4000d4050300c10700d0030005c040c0d83d0541e840c88850751307592806010251904515900d0f119015002004440549885a54041c030b02031403400301d10700c14403200c400e904003840208204c440546442c8200c11001e046620400007180043c000144014062200c44000b28600301e0108001d658062010620030426a00400d011405070300c0c0303203020302072258083c000d894400200100004010b0007403003601e20070f40701009601c1c1c40e110214124003601c20840c2c04074a2481a040100e1301500c0f80c402c42c80c0c4a1a55801382074903a0032010f0564200361071a13008542c0c1000180b00803240d5008590240c1170080003036080c0b00f803075000903495403200300d10b0700203001030400110240b101c6041980058a40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 34872235 1250 34870985 34870991
    0xa03020c011e020903010f020a020607230301030c0608100602030306130f0e0114070504050901030b0406021c0c1218030c1a040516050f090402040f0e0f0c030d050304210c020301 78
    0x195000b990003a510420019220f5481c3c40310356010490365200381e40d030700700c074550080002c1c1e82c40010036150845540d030700480c403c80009281c1d0744891040000d41c065031040480344070552402034050603805015000445090b40d0040c01c2c441207a00000b075a07805002142c851180d8881c0046100c014010381c601d00700d50a0411440030200741054001c1c0981e032240c000300000d00e80e9207003421140c50180b4000c50303601c0044040108003141d174005110790071501a50005242c000510488071902c6040c080c2c40e002643c490360071040168002c001010542c9551405020024031448034446a2a0941c0000e09000106424105010009401c415001c0c400342c020704090526081c21952800c080010300181c0001c95000304190a01c1100380d500d040010309110280d860340c0d07007040043e02c0740d00074501c0000d540b883c040c80c15800c108420280049808040c00c80001e03038906040c18052101500da0a01004106100000310a0000c4c0d28034a8507511242c0340201002d4004c898807003924070b004c3c3d4507600f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 34873485 1250 34872235 34872281
    0x903060f06040b181006110a02010f031410050a05040908040b0d1103070314060a03050c090702010e0123090102040501091206060506040e1e0702031602030a0f050f0c0a0b0a03020c01 80
    0x2590920b40c0c0c0a208109500705d2200d80d01c20301150807200210808095800045100005500820900038046060305000c654945090706c0c0400302c620455000d203411b44002c0c0c0030001c80c14245280c0e005040181c4007409222116103079013000e40710398401c54000000000e50441d55180a40c40740c400644070280c07403540c0e81010039008014000141802d84900030103c0841c8aa1802d0410641100e510002404122012004002c4518002403512082d95243d0380301c030300004420302c60388400d0a514030340d0b89000c00e000e1004103158180100103082a0380f040005010326238119120004445141820301600344035454a0030152030b0590245030403210215000c5540203840070782d41e01c10825014030403180d0341c3c1104021a82e440650716503025030002c002c0308202540013084012000e0020301220490341c0c0581d500901d042112200307540a070084084c158420300c05006680c50b9100840780e501c1902d00b054095003941c4202078541c405d05038001900003200000390031041c0100c0b03448064101c981c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 34874735 1250 34873485 34873519
    0x5060301030b010603060f061b14120711060405090c1b060a02072a0603020d020c03030901090302070603050f060909010e010c090518040c0306020a020a08030a06030209010b0903060f06040b 83
    0xc1e07000c0c0100710101c1c0c184003010505040c0030a082c1f0480d8841e07a1140d84140c40040318041c03001c1031000954900c0f6242030000d181ca8000c220708003126210710142c980c1d0b2071081c2046c800b41a03200803070a204080070441004550780715681e050f0414901c0307241c5a0780e00403c075102d0340e0340b034019031140049004070410080038074550390142c42c184c0d010310f46100c440100520100541d0700c41c000c0c41c03541e6150b405401c0c0a0940b003940074280300c42403941d0051030140c074018424995001141d501c44140c1d1112206401c03d81d040c04000000d10903410103110314149000c00c04c202c0303c4010102d80c040d503040703400642440c41c00d40108240c0e0410800800074049403a0000b40700042c075020300c070700a0b150b000c112440c40c001a042d940c8182e4101c0125100705055540c0d250107036020001030000c510840120314040f920b860001c43c011040c1b1180080c403203140d407051040c4000140c5c015014004107000c0a001520081069070740043e0002c0c1c2d480d455031f114000100109120f030741c503035008058030002189034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 34875985 1250 34874735 34874753
    0xe0601060e0303031b090f04060b030601030e150412170403110601080c03061501140a05070b010504060501050a0c1704060201050f0a0504080f0904060308030906040201120c020a020d08040506030103 87
    0x651110780d15030641c00c000805240d900d101c1a120844100e503600182c034030144030b010240011400040010009550300000a016518140c020701e000410000512000e5078152184100140703442d0301a044070905030400d602503400040025108854218076040094410308114400c1c54001d002001c460605040081600c1202980c2c0c0d036061242c100041a020350025481203c141c006005014030303501c80200c144910000e04055040c896424110810310001d2009007038003040688e6501d07100c1c81c05080c81d00c0040010f0b44030078012407402d542840180d910400701c0341c18040504101324607888502e410b84041812003480200c0c80f101080104410798190040c2d4000c0d20102d07814050b94a550804004a0300c0950b0002c00c1d0620400409a1902d150300151845000c01040059050b9076611107001680c412610001c5030780240c01040110741e00055080c0048445100c07c010a01d80240c3c003a40d1800e032240c000e4490902032042500f001912000c680c0070b844050402d9880e0f5960303103004000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 34877235 1250 34875985 34875989
    0x90120030708040614161416032712050d080705040308090a0e150102060f010b04030b0c0c011d01050f01061d0d1202010e1c05030406020a0e030a03020c010e040515010503090a060e0601 81
    0x50340340d01000401d5184801518031940050423882d10010140d9000d0315180848258003540d0001001e1030100c00741c0c00040000108500000300d2692001c0745041c40c2802c5440280c00c0500010700d0602c40e50310b52140c2aa010740c0d5000c0303c4103503154440f07000200181515404404680c2d402000c01040130014242c40c0c658243c02c1e001c40300c00d41c8941c0c07401e808402c0f0034090030080c07100030700c010000306030381594040d00322000c0311030545044a03903080a404c1d500b118009515030359800002007034807042407052540c0609140491801941022401441b1103125039080c0d0700c0040340d0140d29065540d203a03500e005c265000010348413500c0c125002a000e08001116010280a8481c20034140074001514410f0002140d60707045c9103507a903585840094209180250030400c08040c540e203540c5080181d01e0480c4e0007600203042d2211403e00050a2440e441b160501440c284000c0c0041c01c0c8000d5001441c46034242000d5460703503142c60b910b03840c0c540c02d50b0b4090102400c15a50820010011840700c0c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 34878485 1250 34877235 34877237
    0x106030c03060f141009090e0303100b0a08010512070b04030f02030105010602030a3509010501030b100503030f070302030702090a020309071d07030b030f01021209012003070804061416 81
    0xd1030f07960b9041041240051042c00d00c50000241e11040c185048002c0184910b068108004401d0f00d81039054103d5000e00443c01c40341e440041405038020100002400a00c20136052a1810742580c0300180724403410310503103024129500304021805814444403000d044610581c6859030303601e09000d400f051503810182c1c025480c01c3c0022800c94400700c1140d5203028184c0340c810910200c11190040e1030191038504441c0c21301c211103001008401210715010b005014000311315541182400c460300c01c6c0140c104040800c0080080010ba10040250391070a1640340150b501d40f00b50342026425880382c400005d40c40025200bc000034584c0690140d4080c0d074040c0b040300c00550b20b405c0000700c015241800e1030300d455008000221178030711a42240c0e04c00305015054039104500b140c851409d81e00828545c00c3e40203001810030003810001d200d403e048803500740d64400c00000039100320080780300241c688005c002c064800182400000d0300a00340c10a0701c400350403000c0c03034410301440c401080074041c08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 34879735 1250 34878485 34878491
    0x60816051903030215090a0c120203010c02010e10020c100615020106080102040308092e050403110907170a0207020307090504060c0903020a120609081207080a020c06010b03041401050106030c03 85
    0x8040d0440c03003000059030f900d0340040c0007040540000c044c6260008088202c01d106042d04440051141c40209000b4807c8110000e0398600b144100360948404001c5134045a150103081c044608002444040d0507800030380c0141c0d2194454100c6050903404a800540582843d80001c2c0d0020f01c1d4080300314428881d802007000740d462315102402e034403551001402c412400d120341e48540c0740001450141d21401d82589070502c403a88140024416200030030004a0000b1404100b030016040c0002002c807011a680d80807807604e048054019441151844000404000051100a9258129400b0341c4d0010101c03582c0320755440b4084090242101c003200c0f044e040c004008c003041d00415101041d01e500412304080780381041281c40c0880c005640940c0e03a1903d541c201400305880c07034011300c428418240000070030700e80781102400c444005011082c04500c10032003141001f1012544506407a8842400350b46ca03180c03420004500b044202901000754030f0200005040d90f010342c040c91143c0590f813014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 34880985 1250 34879735 34879759
    0x10030203060f0c0901120e0a0606090c08010b0d0902010c080415090501020a030c0206090303041809021005030915042a05030d0504080606090604110a0203070501050a020403030e1306081605 83
    0x300b011080b05855540788481c0502c00b41c80c007580a4006131081c119a030500185484589440324a400d4a40806440b00340c0d82c4d40d07061146030510301070022144443c1c10300c24100d524104089402e403082c80f80c1e0644850303403507844908581c07050040075400394100882e41d8440340c42c0c245100c00c084d212145480443c500c580002419400407420141c0703590503490345e031406030041c0c090182c1c9a201450341076041c04104008100c1102108100c0c0da010b0601c240021407001c10300c1448503641030349800740306105007401005291580041d036410155a00710050209071224900240744d65800007062030140000000c2036a01180b04002e0340c100c1c1d04c2103044403400d400760101504c40e8416805290559040280000d90600b00b007044550001c4000e003000038480c0300d8242c00c10581d00b14010b030b003005805c009810300910000340143c070f400ca00c40752030851520b890b50343c000e45040301c1a6011409422980104803080c0001c2c0d103c24020f102410aa03180440070f080d404004503000d0192030300c02c000310065 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 34882235 1250 34880985 34881001
    0x71406240607140c04020a020c0a0902070804090b040207080d05042001020d030e0715021014060d120201270b010e040b060d05030d021908160509010e040608061003020306 75
    0x440c421416024201a10b05200382c3c44641000c80602c0d1004624420022611081c0d11648020f05403210030380e01522181c04a84100a1103149a50014829500512100001c1001c5d2800c03601112500c0708001107004070500410b001e03000da4103020301204000b04140f08010625048903105900c01c611f45603a00017003656048103030990001550040c4d0090b02c81c8191180250303c058282c0140100b1102000d40d90400c0c48501041d20920f4801600010305030030109905000d03102c841613050390014030303600d0303c3c3c00070076858041800090201e80b903422855440900070342c040301241c110700c1110b50541e21008070b4034200c81c1c0020000c50300344035a00000070b00440743c910914051913001d1b62040d542d881d40c1040290810303904038140c420340402c010402c04d014051006140146807900301c603c203500420740240600c08010109402e05110880000f50700d50f104044515032042400c0410030741110b43d010400401d0550815005481400b003407204a201c031400800459108030704881c05a6103883c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 34883485 1250 34882235 34882291
    0xd030c02090f192007050c03070b0a09080102070f110f0a0b0a0e030f03030f060a0e0703050a0507021b010503070903050601030501020304020906190b070807060c1e0306030f080708071406 82
    0x201041c01c0c82c1420041c01518002400201045e034014011544004800400281070494641c00303103250060000c2d43d40c4000750425001001482948000c6040c1b44c038945031588015020760000701400c8900100c1d600765074032025010301201000c0c1050b890b041d00c030142c0850540c031a0b602200410790214001c1d1451400003507083c0b4918011021b14115180c0480e094001040505919441201000003203519a55002c699108510030f54000c2842d01f00031031000101c400250800c2c0c1150005410291409200040d801c068030080c81d215130340e6038551504460440c05908000c0039802420000014064150007131405240202d0b2445415220342d400c10042e00303c1c0c070403901c500ca202400100840d40c12000074100080c060060145020340650741e041c02c984034015030030003046043d401c0802031721000d03c4e141c02043c1e03141403c000807030558464a01940510178000d10103900002e91108110700780302502c0d01d891340719030882c1034504060801510350b0b1044038a080c01ea052014441c81000c0707094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 34884735 1250 34883485 34883501
    0x1911060412150605090a02031e040b04120905060a0e03010c03020408120304021f0f09051005041206021e03010e0a061d071e0531050d030c02090f19 65
    0x11800034440c01c8641c2da501d280d008140d80e0141496550030001095101c0100541c41401c0044005a80785000c181e03003960500e10340c00c4211700c11905c404001c00201c0445489402c9504004e0701d001c0316800c1c4200302d03481c5030745401c92904010007007002e9035803503001841d60320b52a10880c002d0100007201c0e4000c038128051803065448560190b1000750419032200300841d0007900207071030045c079814281c02c1c084454503100010320000c1d148c80c21802c031040d4456015806080100c65200800c1c407140c000a003039000342e003c3c490b5403002220b420310800c040d5604940c8040d00b620081d41d043c92030201e00d001903410910560b00702c40b000100080c4040404c0c41001c00341c1c0c4044c201900b160f1009010b150f00390310020500418888101d88010418107003000c40036514040780c3e00d413581c0340f0003807411042c400a821242000080c1400c1d00c402075854a00080c1e05031102a41d40145414031414203c60400d01600044d4100e000c0200b840074000d0384c1f000c220320030300100446038070004100b00c100088900314 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 34885985 1250 34884735 34884749
    0xa06050418020705030a0f0c0c030b0604140601092d030302060f0109090f0807030512090c0f03010506030d1b08040b0711010804050c12030403060509011a0108010303050a0f0302040819110604 84
    0x400ca64006d150246040640110a40c540001c202c1465540c1c190700c451075420940d04804072208200b123902c2c150003445c8070092411141c010505003440041c28443d054001c0c3c0150906900f40707901c10804c40030b4004118000c41c041504456501d04002e034450405440710120307810007000128101103980188004a5486000343c1c181d543c00b42c441d1492504011130032410031804001c405a0800c0c070308119801410110302528480095400700617900f409052654040d905000800009580c00b05040201c04072505110642040c124549001c980303404c0c00043c5841c2d40418003052800391a03001e400064490443d569800000c640103550f401800c4800074901e0b485040c822903141000c0500d403035600c0d00392044a04182d02ca03906c14080c0c13201101c9010030380c3c1d0740e1030405600c3c110b8031403411180b042c2804c010580354110340303008059100d0000100c0511001200d0380c030050f40b00398111801400d19405464840340521049800c3c030030041c3c010fa0b41da408041492031035141102c1103c04480d90 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 34887235 1250 34885985 34885987
    0x40c0e06011b121214100b0c101d0102070302010605030c04110d05060105070206070c030b0a0623060c15060f060f0412020f090c120a06050109090e0f0a0c03120207060509040f09020a0605041802070503 88
    0xe4608900b025203451650003c0f51103081c2b20348000050240050009035200790000700d003040c2024141443d088000500a01c264200740c2c00c0c008443c0b07074404503004014400f03004119940c6680060700c5a20811030029000702001402c00d0a0017100b0b0140002e40e4400d4184800039101c41286805441031350160001e040031500302c29101030003110403034041802c0501494103150070a41c003182898000c0140440003800301e410000070b40340c90700b03c0c02c2807400121031280c28848290390b071211a000b24040c4001caa0050301c070038400e41d6140c5282200041e4024038680d440d00e02000e0401281d008030440c045101d011030041341d11241d80c0e0140c4401d5400603076807106221303e404c1c071a2001c0c0c9891203e5404a000b0207046242500c81031140c3c960460085070103001c164035500e4291582002e0303444000c11904100c80c10f02120350b0000403104141c00455000c83d00d0210041081c0c014402c2a100030b501c058000c1d0300155054018019004035075000401a808104040c2d03264140d10030309031300407c9500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 34888485 1250 34887235 34887253
    0x10509010c020d120f0905030102040f0e13060c0e03060609040b071b060507020307020312090105030408090613031b0504090506010911040905040c0e06011b121214100b0c 75
    0x12140011500e564002090f09207216400c2e01c2e01142000042000000141401d007030211036500824850010b02c1705400851602d8030384502d001d0046010301900345071903140310202d10b544220440111020742c21200400281150104c00350100032a541e0300c038000e000f1500003800501e04000258402d54011010050790741c2c800700100d0782c2004480741040444c203100b016001188503031059078030806554009503911443c900401d03281c246050018403020404002055450340d00030246d07600b059010944c0c0740c9a212500005000340207a9180c1520082a1800001801210714120780c00c50254000b001d040764441047c4419241080d1000e00306d030744420010400c014096220700011a0030944007400c1c252100002e5060741c00030348042d03a04402d004001e00c50103003080d901c650410001d0909000b0700c0c0f10020b2421074500340f03d074060700d8105020400028640128030600107110100c0c01049001000ca00c8074080040603205003800110105e008113400c0d0340300003203c140318902402881d040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 34889735 1250 34888485 34888487
    0x5060105010503091203011d01050d120503060103020405060a020105060406140105070b10050a030803060405070801060219060216200402030702100f06030f0515090309010e0d061805030a08090c01050901 89
    0x1500c050840c0040348030740171424118034600d00c0a03501030091030200404400300e92411501403441a000310f4418043d00f100c0f000002d0f6042c882c440c5a11003070405035140e90301d2200503402070169a00c01600507000040c0c5000403035065203c01e02c00c01d01140c081200d2601c0324400009400c2c020310050218100300085070105008441041d400704051800000803500d500100341030840b140c0c02206c007a640402403040d146860700446a01407000d160144442d890002d0080d41c03240b4840b80040100110140e40301841000c1d0112103011b003c85090072131001d6540781040d152841380b844988030b503e150744240c80d41c0c0341500071a80102ea20703a00811740400c1c21069500240503584076011211b80d507860000010341c020101039040d90040001d400f003c4140038203260195801001404590030400207585140e0300003451140700032040d22800c603660b8061510700b00a1460713241c0044036003c440f030350004016002004046640c507a68541000f074455a003015954a100340301c8070701040d8180030b20b52840d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 34890985 1250 34889735 34889737
    0x305040e0412020601080c0a0e0411270c07021f030f02030903040501120603020117090304090f1a0306010e0c0c0c090a0e1603020105040522050403110106050102030c030a031806020a03020a09090504050601050105 93
    0x1501802f80c4202540e9440000b0303114012003540307400002101c0c910345c83e52040300e500765039110820f01401d51074050654001800903030502803618219145030540d00d16144aa880350300c0c030901e4540110b6072403c00401281c3c1d04c2d0498030506002540203001d481803041c2c00c8c040c0341d0890380d0607150481da15610b41d54031400b240340201102800d2105002c00540707021140110210780491610019001414407030380080c542c45041203600075031103000100512040d605c801036100c50a9524981c803034400580b841c0c1801c07600314081da4024a60020f10500542a41c4030301541032403023088070900d500c4c0c9148000e48549611003e0301040c0107000c2041503003046903c810005171000b4944c41c001f40f03007560407001c417801a60240c0000d04031908e44401c0320804d100e094040e100034001503040105041045540344a4880300c0000c05440e000c0c100d80881803485a0f1002541c0b184c029510f0344801580240250082001e60000680940002440d40c809116082c0610f03000342c05003926a080c50b0042d145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 34892091 1106 34890985 34890991
    0x10f090b01090507140d090501150603052809020d1a0906060402120402040209030703120302130609080d1112160606051005030109090305040e0412020601080c0a0e 72
    0x141c0c40c2c1003001c031021501a0390b14560b136045000c1b001c0c40030f88040d510040103076003404d034195041e440c10b401160566100d03907001c11160350b62900d01140320260203183e0404e0300313401e100c200e011606908500031035800a0540c04202c0c5d501d0b0364810200843c1140a20004078240030300590113824072465030800002c0f03405504011900441000b01c1078040e01c02441140d00040394889074606011100065400040400b107890304c0c0c0380007501941c0503e0003d004006160f20205509004840280035205008000c1000c090588000d64940d841c1e400d2080188c07043c2c060031460030311080010050110f00e0440080601450301d00001030312100c1c0c00182c4160074002425040d164410701340c0781110381201000c01c140c1c1140c20241d41030b1285401c40c2d0b0071311401c1c0b000c0006215561101c520740c4001580bc07254182c1c5e880c0c06d0561034000c5400d94585c0050300500401c0505201c652043d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 34712235 34892091 := by
  have h0 := BRFrame.cov_init 34712235
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34712235 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 34712235 ≤ n) (h2 : n < 34892091) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
