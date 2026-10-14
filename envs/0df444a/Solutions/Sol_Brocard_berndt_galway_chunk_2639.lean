-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2639
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:18:46.725382+00:00
-- url     : https://prove2.me/submissions/3ea9b632-9272-4df6-87bb-826fd24df455

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 474460431 ≤ n < 474640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 474461681 1250 474460431 474460451
    0x31b09060c011805010e071206110c0303130b15100f030f090f0501060e0c0301120305040512030c01321f1823010302060d1b0207050a080a0c05090a 65
    0xf0301ca81201c000d11220381440c49034552401d00e09403066041c4a40300e90300715190801c840c400d00c404140c420f07540303c140013901611305954201e85000b40b0401d40628480402006000c081400f50948620300071820561260340c6c210407084200e138405146904030401000c9444d1460007400081c580c004139050102c1d02040d1946040c0c2141d1103c0d5069030f89440742c454030001d01c1001e20449010b400d40d040c50002914005644207500d10041c03042d14142c00030540c9040605215005450103010010070000b9100558010180e985d0041c0d0003880003546040d0490410f04d50b500b41808281e0f038101c40b040280e180915003055440307030042444c000030b2103400490b038100d40d24040400180500003c483c104144903d82a02107440301c09120400603200e0650004d504009000603045940c100c0d055a907030001303001c05e03070702404281c04945076610100000051954000c9003040035103109641c1c03a1440341d0358002ca03e9480d2195000982500c0c0000d0042c172040c240400c2883d27003e07c480801080c41111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 474462931 1250 474461681 474461683
    0x91002011b0203070308010e0115050d02040b131805150d030e030f031210080307020d0f060e06012c01050f0a08030a0207050a080d02060a0507030603020a230105031b09060c 76
    0x9000074001a000020048105a000341c0c40038098120041e000d2810343c1003111100e03000010000030f2003482000309102d4602c0c0681c0d0129001361074131442d03503070b1580003014080c04965814000e443c5c00100d6a001e21848001603c0b03050f02c15040c040c0c0d42072103400d0b07100038811800c44500302901001404502080d607510708104507142c0030503142c0110307519010001c0f41d00c00118040c01000164080150810010000009440e01c243d0112144580c01c402403030003001100c40709400810703990a180b40741e04c02c0800400d036076040f607a815042c00064210460545c80c1b10030704000901c0b594280c036005220505010480e005103510251103101c10544480200d03107103402a148000059000803810700c09030501c1c40c45013000340b1504c0000c12610101881c080d4940f24000d101e144416681e01c00540c200b41310380c0040c0c0055402409200340350b42c40368011000f070b202840b17000c0e2103119060314603510740d4030447c00c89100722002000345625100c01d074001513180c0d005140541d0301800c148040b40f00c03404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 474464181 1250 474462931 474462971
    0x9090a0f02130b07060c17041209081606080702010b090103080c070302120703060b010801060c06110409020a030e01060e0c070b130b0a0e0c12151e090a031b0809100201 74
    0x1444400031504c441042c078240d0192440c0044a4080088020f00c4a01c080e1240ba486600b0541c407150342913010141031030442d00c040c03082e030012066110350200c0c68544031500c0003041c2079452139034070915143d580e904140e01307856075900801d80160303043e4010030100d5440c8016080200f222001d40702a5a500d0b0000344002c2d07688000300b10399800042040040090034426401c00d40c01c282003601c055858904040d01034100c04d0005822035840d85540c203855002401160040e195985003151511360441c0014020598807100b080755600c2c101c80416440202c0704801c3c85044200c1802d0324113400781ea01c070320044002901020000107900e40b00310000e6081c1c0400361141000503c006818003814980302d1501d001504217138054903208503401d41207400030036003a00e03040c5843c0507680f9548402e40640071240c90740003a01e4070740c04071500340b1000c1c140101d4000d00081c082c1d40c034800351840e0180d03c02d03cbc4007491100204070540c00c0055044904210021000326440c900001030100e2030a020510081c13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 474465431 1250 474464181 474464189
    0x603230103030809010e0a030815010c0503130e09280c09020d05090105060d020a060c1a0702060601020f07050604030201030f4a0c30030403140309090a0f0213 70
    0x24181d83c0400003104001d11400d4034580b07080004107402d42503914041c2403620050184004850119000724442c1d0250901da043c2c540c0c0300048a81e1501c46000100111080e4010700101c5016240441c6040100007070003a1025200700c815110040c0d41184050405e0300701d44225111003a040300029101007500c080c0c660400d91100205061916201190840341c0c01030407a0720503005d41401c40056100c00030400309840b01800c21710007a400c07034140700c903028210b6120012a203c5140400454650102d0154042d2138280c00f02e5002480f08101a912401d00c0d025058014005020400c050740c4a500120502d6408202c000f40041b0445407241030741d5104641e40340750204c0c4000300e200d82c01c2c90144050f030b452150420828000b8040d0f50154031089074500040c80f803100a0411802c031513840d0754240b84070a00303100d440204a400050103880f03405c68132081e655454003503e50f80e0101c0c40401104c1c8220002810507856a0b20a00968001c011503400b00b240d8542c02c0c4101149034a640c1d83c40c0001d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 474466681 1250 474465431 474465437
    0x5060909270d1e080c0c1218150408061911071a06040603170f0f120702071d160e100806091f030b061318150209010207060323010303 59
    0x11042d020016209003004101d0107101c00300d840300082100d510404254021800d02803940e07070b030200d6800a9190000d00c5800e4912000c00089404000c011780c2c0316020940c100356500064000c0403042001c01d80078a2040ea042a000f0800040040642042c800c903100c010031800950400038402c29901c13500004403c413000b9441d03402c64000000d00c04c90f0154025811034051091a0440d600c681030801d00c0e0306220a42240402c2601d00100a00141c41c0c0c0e801c00c2c0030885465201c0c0c440f05203140742082d1240700c09801014004035100e0501515050036000364007202c2515143c0ca04140b18040c0900ca0320403c1001c2c603030010100c1ea884816012600409076100740a5043c1101003201e5801d0141410019450240103400100000c40b00c3d04100c4e900042c0a4150759102808222034000000280750388a24218442036060040c40c1074020f50350080801a0242071503404482c12442b0f101c2d01d640c0942e00c443c0040004600c00c0c0c000403111194032050007202c0c0d480e4107190058903401e030811004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 474467931 1250 474466681 474466693
    0x40f1217010909061514060711061204060506180610020a06110c25030201050f070501060f0e06040b01021b0103020409020c0d11060106050324030708010c180506090927 74
    0x14813000b400f40700301c07030302c0a40c8000c51514608554142030300342c540c85d520f0191001090321018049600000c2e207510304084d1016588031840c6012a91070002203c0407245145490003140050402c80400004805000b022610a40761001040005000c648400d421445041042c0c800103c0d240604640782c0801e42c005038841180c0c0403041e00b071114058840315580e21000585064240d096801030031a6020308185595007001c60400106201d1140c01410640c280500050441c40ca40030520444503080d40d180300d15100c1000300400d440e01c80411a0040e0701c0713642d203240a000301c0000d0415803001410018600f65981c0804001c0e60400f000c0240e86030000f04468500d00d40150080c54949c0c8003001400745507040000240180c04040d01498418101e00d0500d210390b91003d5039042c4044008085420a43d528101540a0102880c0c403800150300344928680440880c052402907580060043c2d09002a40090000d4100014210318030442d00140c0031203421882c421507070303461900d0409003003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 474469181 1250 474467931 474467933
    0xc0a321f09051809030301030b073c030213050103110705011b090f210c1211011b031403060f10020f0111030f2823010b03040f1217010909 61
    0x1800c282400301e00c105001c20f19007008900000801106d0650740d00132001496a220503804030791004640c4a9441d081c500001d0041c10f596850b012a00c0c4a8132000c449442200034080860176802003400c654081d01103428140103640c003e41142c80c03003482c282c00003818020561103180c2035484410070340d06115156070047c00784550052030080038241105081c0181031914540a054007841c9580e8009001c6001c01a0104440324076040010b101c041d09481e40c120b00303030072302005451a040c0c420340030440307102411000107412170104200a41640f202080d5189000c80b40300d06905c02014180c1c007480d0340490111035079618111040c40c1030f0746da000f004003103558200c0c60300310390003c49101c10644050040100c0312270165a45544145501c1040403071075007901e4044101c075411800d0411791400c0a0140c403101d101007103411551404400e000595981c2d8036020361051105607000b62282080f80448000f082d02c01241d0911924a4a461001d400885140e10124202a080855442c0d15803174088 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 474470431 1250 474469181 474469189
    0x1b0516151a0f090408031b0d0501060206060406170c060f040305030a02030406030f18080c010f0501331b110a091d010b010f0f090503030a020c0a321f0905 68
    0x2403100c00300f916041c145081c15150602c1c41d000042c24903499003844242406401000030039140c0307155682c1c80510103547c5540c1c02a460700e508540042c051451314900045d042130000050110b00c0046c000307845001445814040c1d40d81c443ca003503249041007000300000081003000180000c04040c2e000d107031203608105c001410740b04404d48812410381011000000781c0c6041c1c60411913194480445a13030b40b001010810f01520000c55405503c5141100004000350400441042e00403900d40c002000713008070000d0504105254600400507280880e10000d41c02000c60b0082d249000301549014040701400003803d12041d40c111402c3d280c1c0310b6043c03540b9040040501c3d040c0e4480c00c0002d100c1c200440000a00010744e0320190010800c00788a030b81e420901512591026000280a491740c905c03d048010b582d80344000c0d4011300031107138080c0c0001c4142007402d410079125008102d041409010b840c10a040c40c3e0644081540702c0c0ca031004244000701317220404840c0440741d4a64010780c504d0302c4208 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 474471681 1250 474470431 474470449
    0x20703031704120309050c3007030c0e091009080405040b031f0c030e0106081e06090c0d0206040503030a0306081902030604081608040b0d1b0516151a 66
    0x58028010380070510001818411020070064081e103070016402080d41011813402d803482400300d40218246029010b180b0046078030356002603800c81594190110041e0301c0795141000d11028003517042500342404001d26440000da0000c0000084998041c1a03152020407101c200e401114010030028040005042a002c2c032118018100c01030140e01003440019060891002c0300c9821040e80d419070000c1081c043e40c4840c0c1d01000e410020040d06858a89150b5100c03841040c403000300449003554013040c807000034014490f004403030103044100940f00c20702c101914034541c00c0340d005030f0a000c0840c458070304102500000049680104000303107040d002d50b081481940c100b00030f80c00103107600300241c1c4001500641241e440500d965440e0f4040003070b803245601e56040201075a07000500040c40ea00080c0c0a0000030307a000320100300750352555906806c00030858000310701262080c0450900706003511004d1003c64012a443c038888481a4815821910041c00c0da0f40700907040f144000c0582824188 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 474472931 1250 474471681 474471707
    0x12140c070810020702090f04230c0f06030709030b100b03090d090506030c12040c0b0703050a080105030c0a12060b0405010603020414060406140307051903020307270b0901020c030d02070303 83
    0xc11484c04809801051141c00300910007450300c10160702107010807010303038100c030550302e075880c1c80d40400000700440d16200d01400d400075103e115069190340329803514a0803a400340740340c0d40b100c3d6170061940d0b4803003990650060020400414490002940c948000001c42c8102c550201a1810541502020304140100c1d00030304c0c000c4d40d0078402c204615030260102c41c0704108500c181d032007559075403030704040d41c3c07255401515028001098a108042e0440c02402d84900c0c03640f1070300ba0981e214418150b0310900c03040e01d04d0f4801c0e070140382007000742004035008403500d004200c045011501c00001c28260382080c1e01680010794005000c011016100300945000f0034120340c89481e02e8904000280800115411500e042d10004046032400c2d0280f41110441d203d66900c84094003207a100190094004480000c0401c0100710820f00d0420340905568441c000010499030709070070076040e40415000b41011740e0540c41082c090030030f290b9040218084c2811154000d000c0b2038110b180041c03c00b290001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 474474181 1250 474472931 474472963
    0x130f1406100f09050f03071208120109090f080d1506050415021c03020a021501030c090608010507080411010201150306090c0b03150616080d0c030501120f12140c0708 73
    0x240b00b1100d030f480f441d400e040721411513481d0521000781c00007a042020a900030004009100e000a00304003269014280c00158000c041005a07078410f0705c881502ca080c20010312082d0501e070b07404001000d0030082c000f080052034000801501c01c0c00d00c02d45040d070a402540218a0200f07040140c41c1c40c12400515604071031003e004111810310a41d440490f18580c4003051640206501d90f1700c520800480202d00b40b425034200d07095949040a000301d60250007102c0185062020120f80307408140541d0b030040c400340d50f51518aa445450300c811041c0c0c3e4042960440d5218008403600ea412000200080d41c095030001606000310314200c84100450791160400b0702c014400c218171100240403d800100060302c1c000c2e51a4400c000161034000031150080031400302040c0048804016408400c3d40b41080d02d082085988454258416503e078220040940895000b0040081c92041c01c04188000368209120704010007a065181ca420a4404101c10f52112104010025007089591040e54042e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 474475431 1250 474474181 474474197
    0x90515090d1d03031e07061401080a02211e0609010b01050f0d021303081215060d0e031918062d4505030c130f140610 52
    0x110050b040300400c4411424544068a0454494406004551480c208184072104101021148035803640064005031002880c04e510740d40e03400140d10986040e1810310300100410001d81d802c02c0120b20b12800c80840c8040f0031201050075035000c0154a9131460300d080c04007808008107199500d00203000705481c400d42e06007403811000780d03004011601c42d902001d25042e07450f580f214800c8043e10618101000c10b0391403110010078841008080c6c1441030700865000c82e81e031940c0c90004e07184180c1006c81a80304804201c2440d422209034040c0c107200ca0355106490510b0b006644034600c1300450403640012500d4860082c40c0442ca059080c0e001c0d051038240103d00d00307510b40d0186103010002ca83d580818030090150342205015014580061880500c0c0e01140c443e0415000070015001d070242101680c00f4180120b8411035200701425103402078000c0014401000030000e21b10034003414110895039030780d501454003d441c019205a110207002040071070a03c1c0c2c06216041c6810200e04081283e44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 474476681 1250 474475431 474475453
    0x5071e0b070c050a05061005090a060b0322050a0c0503060c030c070f030c0b0103200603061003050403090b0f0a0f0305060a140f13050906070906020d140d09051509 72
    0x10112103600000c0c0e074074202c0d0740125149001d528100e42090090501e119000401044101428403001030764410345ea050b02c3c03a141e07503007240203460540c0a1500e02120500020304040344847c0d4a41905000e00080da41400050f1261810701030ba5420035544807078002801d2080c0d060400003941c001c0e5072110400e28510308040c2c010414001c61a005108410700d003a00070515200300882055207812829081311940d40749096029400c200c0c0501040d620010340c046640d01e03154050380e01c1440d0107000f0800e40848048128028440204101c041c03041d02000890140407120260031204000b02100d559041200c9016040401c8078440c88101410041004a1911507d071040201c1304900c0f44030184c62500c1c40042c9442984e920450342164210980c82c056189640082d07015101da0400d44034036490b044004c07554040207000b401d026901907078010740c44511891002c0c44200d07005034103509110001c1414410b440806105403250b91000340c94041032f0600000c8035800400c8c110003040c4a001d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 474477931 1250 474476681 474476693
    0xc050408070506070f061a0102010c0c02030303181903030e0c060424050c03120a140907061d0604030b0a141603180b01030f0309050d031b030207051005071e 69
    0x20320701a1600401d4081620030420520b0701c140200176521820034882d0346145642d1210201001460500544c01e0406120004d0b016100b802006500580550b10b96680c0003006200c09425800d914011310032800200d184211130240700b1856403007560b005c500900078100c1d07545000300b00014944100c408200801c0718510110340c0c00c40080052100701c010f110076070801c0c0d400e8000c5030f2651041c1e02000a941e902043c81010b540d1241071a0314040049000c907414161041c0021600040680e0007403100748015070081446403001d08003044004c80d00c03400e1401184854000751f02c1202c1081c480814411b015005014032a45110344911040d10340c504064056070140c4240802c000340755481a0300071003c40d0140c0020400e0f5080700141d449540c2d6883d000604071103514054002503035042c40400d4908e08002d0781c1520f103402d96120754150744087d1448000c5003556400710158070540ea40020242c40e40f401031122b030920780d103c283d140c41d21030030070a104100d020744601151080d418841c0018407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 474479181 1250 474477931 474477943
    0x1d0f03030709170a0c092019050c010b10050d1d070506070503070b0f16030b010203030105220c08070201060501051c021e0403080a11010911090a0204091e0c050408 72
    0x2c00d202c07490f0983e5a040d19030030200604405001c400c0c140748041407401c2640c11801c44003050381c402080c1540d000200000c9400380c42c02d999240d1800300c2c403002141d48164050003805481c03800000d42254030130000f070260031030300950001142000c201025031099511a1004122402e003103951110025070920340c51b00e145004442c49103c01280d1b40d001d01004000343e03000c403603004040d980b075814104a03080016508036130f001c0c040c144800070f102c2c2c018468060510210302c1038005509503400d1008009022602a900300340071452150541150305880c043d449003100c42c0d403502e4945040841c402800e4079800c1d0031141c181300040003803506c0034281c11040b02c0000040f050041e1108803c0d40541902c281400f401d80312005c000c1004000d010b09407000344079998058951644110101c000c081c240d6449160280422440214802460400c949055402071000300e0062900748ca901001007110f07020034401d60b0300c12103140855040d400303512070528540590701f48581402d140603101f82da911 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 474480431 1250 474479181 474479189
    0x150f0b0907020c010e330c010605010906090510030b03030a0c0c0b07050304090e03071202030d0b040608030304030804060e16030203070602011b0c0305040f0308071104020f07030e131d0f03030709 86
    0x440c030301c03206414000c4c1c000003070401c107100114080b201d8a0111000c1071b183e0006559110f82d9403a11400140c0d544c01280744904481607902c60200c10340c1703440c04100222035105100c205258440c040c4041c540e60900040c2200111610381c110136210078141030940010359000301d040744104004803804503d0000584040f221500404510421040750240c15402000d03002004424520215400241c000c009484030081400d810810903044104020642d551071240b040aa0410000b24020130f118007042030340140160408280340c3c240074030f02c510708007150b0110341504480d44810320841c901400f9800c0241940d10091000080000c510258011803618180901c03011070b40c000100750040c026180180aa075201100c0513589003031071a007551003036408071210107011040e011545000d2082da000c0314414031007103052842c0c035981038aa442070f90062640c4548400e84d440c1c4120600d00520800c0911342c0d080201c6840340e43c15651a2001040d4840a2500140204150164000f554600711 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 474481681 1250 474480431 474480439
    0x5040c021b0a0f03081c0b060910270f0b070b1311040c0f110a0c0902090a03150603021908150705120c09030c0a030f02010c150f0b0907020c010e 64
    0x41040200003411404140d80803c041c0c040c490350000a00c000c03000034121181640c0c5403c1d82e402e40c9090352100329451207020b25880401807180407494144544c0104000800d401c15070501e646080e5a0030044004075a04440146001c0e4144a000d181c40c010b04001c008d43c402d00c50404440c1d55031040c02140042406404290164181e000e000c1041000c1041100c050030400a0080c0360400a141c0600c500d80c010202d00ca01068014222001408040c51178102c0300d2110007a0414400350003960000d901240d201c9422840070011840c2e02c1090051404400c07400100c0a1540c41030101c7e050100d440581201c01c820410042d4104c049240c5400b260184102d51040c0d507095001e503046e01440c8000107040502d00c0c02c002010201d4402000b10803000c40455000403c5c00c800c01007040c6a070f000c0248030b282010304040c010b5015841c500c58240c4030b00c80800b1026094a049022160920001000e10f601c0c0d41910a15044c60700441d030304042c0920286c4a141c08400019094111000080e401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 474482931 1250 474481681 474481723
    0x12304061202062b050414031303080d0207150e160b0901051b01020c0604020a150509120a0f050304050f0924060405180901050c0c0a080904140f040b0105040c02 71
    0x40c3c4c1c40c400c0860258411041c40d011440e0100c5502200400d02150700300e648102040218503d0040041a1180880740505121040703007103944044842c5c00403c002166550203120480029403040f07205c0c42962208400092001048069a480c00b007402a800704011344a40040c031545211000716000350f0402e003440341c1e4806108801d4901c600c241031441d9115480814207601c1078402080d9580918000c80e0740a08098a17111382c2580b1980d6040450b010403401c100c00519420444180c004d02510f040a030340c1701c050b041d1260345078010111011911500001028072551a009962141c84a000c3d2220240c615000d1451002c1920703151414049505020100c0f4499131010101d501406021700900d1090941101c44004484280c425400f95424200014100f14207402515104810780b4010b00d10100e081c0c0b030b8100c05510540c0d02030340041e25107a68a51040000d0f071042d009003011a6400901c0c5814108607135000c0041c1c00c450303c51410300c8004900580d00165815120401e80034800e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 474484181 1250 474482931 474482947
    0x906050a0c080f03010e06010f0201020f0d1d0f060a050a061d060f100c030809150f1306020315030f0d020615030106050d0f1511070303110c010501230406120206 71
    0x854020f0750b4a50001c004000004900b00ea03600c0c148a01132202030300d038440301c040e020806038280d001d900c1f106040000c003030164613007007161604840320460342803201c540b5215100d0703001800d24550369100c544540c4024248400c0908500c01d040d07010000040400030681084210000d04200031040d042c400b0356031010a0746070303031103124024445d00000c0080b404403031080c0c0060040e0400100583c00310714002c00092245901241302c8035941c0001e13410101941d181ca10b80c90300c40e0009000e10074024241040c40000444510055004142680c06541240c07000702c20946011040344042c001500078130526070301c854000030b031300da0000200e08002c03980000f50800300c0d00400013030744210381c0014030240407020f00c00507040b403446036405071802400007000144200182c40030880d442940d014200040b4002c07a10940c03180c10451108080c645c0342200d0410103d09461081e00f00b8000340c00c400351040007089501000303c0030000b00350b038240a06458000d146d9500750500c10702034041e90780003c42d45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 474485431 1250 474484181 474484193
    0x1080a0c0303032c01060513050f011a0706050a060515070b060105090f03160501031b020606060307030b1206070f03060e041203060302090c090a0b07080d1532010906050a0c 76
    0x808801c82e41006400e1300c030f07021525280a88942d1180382e00424221108180e2950f140c0100380c4644001050702c1e41991800b071032203920b40b108180c0a1640707003045c4a02c60004105000301401004030b0140072951604000070443e403503003c22020b0348409020000d0100107445018016406182403c03c0354440d101c06011940440c040c1480c0c603814050a40001d50340801130607640c1c1a510280d8040050b605450300420b01001e005843d81c000d41c3c0160005811850480011941310802d0314000c00e807103c49501007040d00d03a50000c1458031350080e0041000a075440009054201086e180a0100500d000400a0190740c0a08080d00c05441c84c84083e07140360082d000100210360103806000b491505100340317100c40d0441d419903445001a030200045040c412400e0b41d000d40d4010000b546410f00318001480104404103a5217601203141c0e60009800c07a14a961b0100740c031880040e0b400d400c0c003951442c0b000b6166480a40d0500c01c0130081486800c0d4048256614603049043c4688150440d080c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 474486681 1250 474485431 474485471
    0x403080601021908041e0b07060c031404080703030b01050307140309011d0f1606090519030c08010c110a05070302060f19030e060703090305030a0218040e01050403020601080a0c030303 81
    0x1100c3da03503000700380010018500020812541e0603e5040304031181301c0f903103486040c114030130400880e9081c4a0000031130742030342c000c1c0d19807407580c01c0004901170b074030700743e1102c06408070760584644101048603014181c140c052084070010034a0403c0c0345280a040103040910000c2c5c040e42031500c04030014003100c4d02588030301c50f115880001c00881d00d05000c1265580d01500b80301c0d0041e4004c14481124503d0400d840e90280c0e1100e44031108180c0c20b10041c0441428403d20401c034031003a0f00d40c000702089000c04444040d01010700080380151a0f4000a40300788445c0d0101c00341a8400e40030203000c00e501240d1041901c1d412148155070320750100c004842c2d80192041600428100c20100070b007541c240d07000b064403c3c0d8540a903211581e231482c00f6411280c20f5000035001c110108001a4043e425500806041a0a10001c05549041004070741100d115420051280e9075490a03c400c0c10340401006004124407030040401d80b1550b958498405503900c00101416160a4843d00b58055600c41c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 474487931 1250 474486681 474486703
    0x12050a030c0c050619270317090622020a08032703060402010302090604171615090302130e060408070512040b0706051305030c0d030e030f0708031e0103060501140108040b040308060102 81
    0x80c40c9500c002e2103032402c886c0d00d040c2001c0340411302c030001079422403012240c80341c4a04024009054203565012400341d2400031801003e01d0f244c1d40c140407000603650081d003000541103003002180c0b51603910604280c240c00c102d5007900c10200e4501c119049a60000c4d2090307001c1da080c80c001d600e415024022949500a0b40c2003034000702c12035444400c06680c00110003007802043c88030212a1a990300031042c040e40b10441140002e00203170024000340c20500c103200c801c00d6051000190300d1400c0130b00e003030800405503000c5680754000500c0a06104040100c010036171010b40907103203401e00d04070780001d26200e0b0b0744004210b00e0700d0b68002140060107895141c5000d403c46c040e42d0382d4070740c404400d64840ea084181100420300e42034802c2e2031800c4c004242c4180000e8180d00030f03c0c280041d244c4e80000c4d040104100c6400043d015a42e98004508006074000c0d40f06031008035183d4100f00441502074580b6011034100500501004040303448200800e400642508208100e500e074540100d04144516407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 474489181 1250 474487931 474487961
    0x20c0c0d0f0c08010c0807262e05100e01020316050a02040c03090203012004120602090d03091a030c031504060305010e0a030311030f16050712050a030c0c050619 71
    0x141200041d040501601c05c0c6a071070441c9a52510030581e110015501c20034002c1e0603414a04d00b0001810b046181c000844480f0700300e100a894604036030b4045070030307648241d041e2034000400c002d00346410001c800e401c841c24081023404200c23000035907038020002c01e40c001815091071b241c00e026050103000710362900a00140304a41d2082c81c0039014140c1e42c00c040303020758682044100702181c0400303030a20700a86c5240c01e070320380340c42d0103a508006090b0300c1007514040d5003000318021607a00e585036800d189129484815540b850302014000881c040f0b403106030303880b004000300440c181102c001c60307501c01c003400e2030103d440c035490000c14000c0c0310340c0d04010025841d0030190b540c104000501c85a9061096030240181d0001038825002c500081d45c1d207003201250b0802149242c16029103403145240d0781d10b045801c02c2859103e0503401c054950303414020440005846030090f43c14020b26036408014240414241000c0c4d884664959000f00b24000c0d086000b41c00d4000300c00ea5400c40c030001c4a410b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 474490431 1250 474489181 474489203
    0x607050a21140a110d5105010c06020711193002060a0c050a0813080102070213110409020c07050102061f1509091b02010b04020c0c0d0f 60
    0x840010000c0c51090240c8200101d628001110000c0b0341c000c10040181c100303ca45c0c205a00050075802500700381811b4801000c0d18004841e00000344140314204c41c510340140036030100900b00440041c5c2060450a4855040200510851341c2221403480515031145d40183d4429041c200404001d05c12854558030a031207101168150031012800d8003501e10000700c0e4610041521000708840746403240300300080c90100014009807070401c015018200342402c0001c41034000f41d48240c1005101d2008446a02d8086004429190703466010000340034036170021483c0840c0b41d000580b04401040341450213030f0302c8101e54401c420022003621b0060400200941d201d00c211524203888500324007a041c010b01ca450700184609841c0c44004649040e0325941420316800c1c11b1518101d280c1c10f910000c00c4c08003c1100054580007440341e1354400c189003e00c0d20010240c0c02009082d501640340042c852030050040d50414000880c40e01c0d03c7c2a030803600506d0848103480e00020800c021364010348041008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 474491681 1250 474490431 474490487
    0x204090b07020f1605030c0402130e07020a0507171509031b03040e0f01030c0902161203051506030601021f06031e1109010b04063e1006080607050a 65
    0x303407604030707103d81425514018a050460501d5148901c602a4154420303030241d8018186680180fa03561900659050b030103444101600042000395584c00c0107910401e44401840028000c0078040c0c1241c076503913092030742512017040d5242200707100d038442c8941d00d0000c200f40c440100200c50b070310600034094000c1c0d00b900d2010a0340f80c2c1c00520844100f4080d103000600c6518800a88034140e0f035110010712242030034803030144000d401908446140300340010380c04e000310b820078040f030555002c0d9980208052a08640485400a82d014164001c0741e0034014800c3c242c0e008120f005e24404903c111040c618040d02d0780201a08940c2e00c0600078401a21402c3c04034180340b00011a05401361400150060800092200e601800d10621004100600060044a120700e159081c43c1c00c00c000a203205086043e030303001c01c00740c151082c0140d07400d405036142039070b040a04c002030f580e820000c001c01403249401071460700c851009100c40100140041da03200d030240520b11045040ea1800030134a01d20480e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 474492931 1250 474491681 474491683
    0x20a0e0319060e070608010b0c0c0d0b090c0d02151e07030906021e0705060706091407050a0b0309061602150903090916021c1b060c0318050a0f0204090b0702 69
    0x40605503030103030a2040790f100c2c10400003032034030854204d540c82000580ca0024090580d801c02c0010348114041d401d1448056074450341640c10030350003800300c90300300c0c20b101a42614004010314180e007e50051034500c0e015030390301c5074004000003c483c1130340c0d40c0e0b00415036000940c0a07400004003184102148038820315a2000305001a00d1158084960782d680801c12000241445c00c81150560312807601800141000e501074041d880c801c01011440d00c07003030b60f225030141c09019042c0314542d005500801103880c00140e084020050109001d1641c100761030084e4844a000700314170070303407240f42042107006d40c4204640034001c8048107c1c05081d0a1007802c103522580882c2c85148110b0100d808a0b00401c492200004403a4a5800800d41d6901c0b402c0624019150580c55000307000340c0c2d402c903c1200b907036071107141240380c0b088400040040703194002508031000d4840190046406041e50b00018000080f6088081e0700f28500004550700d501c0010701521403440c0080a048070003044c0003041d030b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 474494181 1250 474492931 474492973
    0x5010e0d0602190f08010e01091508030a02010e06070e09010b0f0c1b01030606080108032a01090807061107240f02070f020f0301020a171902130608010e0712020a0e03 73
    0xf050340e620701e01080c0726a4101d820740000e010300100d080d40000108070850655011040c0100c1c59114200e2840d903607206207055130400140304015035101c90603004501400d00580d031b03001d02d0034108205100d50040100782a000e05000e10800b000c0f000070200340141c0c203401591007035000141101e074003039600880d41d860b541407003600c0703400b01c0c0c102000480d4213801440b0041c1a60031a1004605080e4080d189147e80b640581d950307620425031200b41c0300d050f5400c0c080c04584a000b480e648c0d1b0b5400d0180b40502c00c40300b02c0c43c21088004c3e42440340d100045d1210b24030303034050100700e40002914009600c08000901041d00c0e0002d006100103000800c004150000300b040c0c0e402100d00d0710080300828281400d078814960403000046c2850418540080c09410160700107111218140300c80752072480c01c0040360b0055040d0102120100d00400c03600380e111a007a1301402c1e07280c9540c03081c3d060000000d0b00d0504d00000f648207690700440e80c1602c50b407141070360703441c100da00030202c906003045900c443c02c0e055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 474495431 1250 474494181 474494227
    0x23040609111e0403030e0f010306150c110306280222091409100e030706020c010222030c12031107060503090c0402131502070b0d020a090603140105010e0d0602 70
    0x4075000d84002e006552105540c210780e015292902c004d40d65400304404808400b01c443c0c1071641d82c0b140810165003207030988102400350307120440c4240345400d01c40039848040340340d6807003503010404000e480c0c41c3c400141d4442c017644070a6110368012004071240640335005241e03165045031901c4415400600322680200d83c0d041c0002c2200030b007100c80303030341c0000e40c11681c6030003560000702c1c1004403074230035400701602c864404103507403c010307581d44d03000d09913071042441c00c01d6a0b4021610700322400391b200300030000d00783ca04c985098403440c41d907c81c28170760700701d11400441203400b1094005141c010f0303000381940c0320301409545141340c5900000d4010f0700107480c82411803003022600030750740c20300c0d100303c0360b480fa032404064074035618141121035140c040d41c22000460003100c2001070b40726919000307094600b1031810007584031600c6040c0240880300541c02102014201085a0480c12040c0b003540c1c1951001c2c42d007880c544110030b010450700e19407440d0051000d88009001c04242d09440e5080641d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 474496681 1250 474495431 474495457
    0xa0e0c19030f0b01180e1003050a050c09060306040b07030f0908070501150902040506030a0b0d080c01091203110910091e2904120f1703060111072304060911 69
    0x41c8140f0700442e04e02d036100c4064a60880c1400c5c0500c0009000241194004000300280805544a6803024100f0014440466190303000c02d03210078403840d094840e550711180c154020920791619803a94407480c880038105505040e51420072030240c80541d000038148a402500c0030356684407620b800d900900d0455500e1050281c0001c0100340c070312880c0202c8040701c400030612800c6840c1d11409100600b46220425401610560200005805840941141540d0400020f03e22105081400780c0d031841820b510f0426241034030101c8694094019030381d509006603107580d9005003510040c2e403283c0c01d40d0400b0900085000c000012450918081415a140410707480c07181e03606100c0d20031000c40649404c4c0c03244403003070006110a00005412054290280324440101000350720703001300701c140d40b054003104080300104010503940c10154240600c48040010a0b00510b086280d000003206005d00810b00c006c0e01d1400b012984e0349170000d40291031740f18000c02c900c00042d00f002c0501d601800c400190 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 474497931 1250 474496681 474496691
    0x60c1005010506041404020d0b1c06110f07110a2718020a1a0d0c03060801050f06031209062503090b03090604061113170c0409020a0e0c19030f 63
    0x2583c2403e9090b01d08491030400c1180c1d501c80c0d2041044081d4204854801c01c050340c03007110501c030381d0b141d5a0410880c0900d2704030a44444483c2000b00580e8508031a4410100c0308100700e996501c0c08604842d0010b4201c288022211003010001e0a071440039407007910340908180810710700d84d20421401091341c0d8054030410801581d00c207a241d5a8a5101003e5071002500c4020419500300b0001741c09107280c040c141903d03000346915034104961400c54000000307070b43c80b40e09210040c0c0034407034150098011310342c001080c0b07041c8000035545d0002c105000a0301502140c070a003c0c3e100c020a5800d80c80e2101c00156014500500c5451200484a000e900088080c007001880d28814000c0301c5c01110003001501050b035030f9071a0440500440b240d801d91a0104000180074280742401110240040100781e40e240a195482689040b100c00d401d40e110700d00e46172041c001a80e642c02d05004807070085a0080303580d5110070050545004c2c1b142c21641182d6204100345609078541d100700c44844085c502081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 474499181 1250 474497931 474497939
    0x3090c12010e431d040201030507030902030705060d0e0f1b100207090c11011e0e07050102030d0e0c19030b0a0e0a0f08040b160b0702010b010203070b070c02060c100501 74
    0x1000d4400021083c0f51280c0c00c480940d002c5001c22103101c101d040e003440c0310700500e68801c510440c0f900029040300c01c0900c048184002c641e41801440c2d0130410074503050140c410543c0002c2e481b0800c500c0340030b124820001d5041c03a02005904903d5038103e4002c1528010701c080e800305a198030443c681d0255028015a000c5898608894003000c2000641c2c0100740050a12000b10003d142c0c041c20f0800f402017003201003003100070034054882224005040c080b9110b100d040742e80d0590f02c1180100b041307504032080034003480e6400810303a401007850f07440c04501c81c04030f540304908003a0b0300342c2110b412405122072104284245c8040c0022a481100041c85a9580c41c2c080001c443d503054003203255070001820a40442d90050500640341c0c02603403200d190940d335128010380c59101105102080f60001c00c6c2c80180711005d030500d80d1010041c0024410074081c200003d40701e204014005240314000301c04601d9461242c2400c04a160340a400c607035907a804441e00c81c0c1e40b091102618907005081100200b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 474500431 1250 474499181 474499213
    0x1a0603010504030c0b13020a03120206061507021e0301050f041e122313080c0409050309060c010603050607030504051908161b0605040509010b040e01050603090c12010e 74
    0x203100c2c03a01a500c00c2c1244a542d55181808200a4205003e605203540e808016030780f2076688000951141c903040070b41c0f0b0b0060b10060700300000101828840c110710508003001c0300326007080b24002981118140401da00a51241d0303103225104025a400d0b40c40c001c2002035000f07030801e00d0b501590094104040c50780890481c00510002010b00418008188080c1442e09000744008082405101c0400d04000c41080600303181c3e421910921191041c041c0041102290138820502e0b0700c107054034280802c403c203480c2c86980707120704903499000c1d11f8001154020042c00f940100082c640c82000c0c0c41d00c0781850350b4018041c040c103407029141d50141031401c08140c0074007144040b01e594400811410454000c401c612200c00200060303035032200400410500d4948414600098086616041d40300d50800d0300748441864142c10030724418800308001d010803220307404007504580c81290074503a0303991961115402c0510710104203801c43c50741d070300322550300d241034102c0701300860f03524221060424503080035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 474501681 1250 474500431 474500441
    0x30e10060e390903010e1b0a0b1e0c03041508180706080601030e240c0a020705150f0d0603050d050f0f0703031d0307060b060a1d130204031a060301 65
    0x1048004141e810702031108515a110840c00341c8602240703e05140b801c901103070940f1443e036071001c0d403a008039000801d2102d0071411403c0060342911a40358560401c40c64026a04c1410801709150410840c200c40c01041001260054580201982d4072250780300c0241c405100303c28000b502141c4a4000201968040020800c54949000003488503d2414509032210807020702650304143d10384c2009000c541c8100700218030044401406241074040400543e4448400b9000400d991010001410215800604041514030881d03080300c008e2200c4203007000720300c14440b81c0400e83e003000c203580e044100c2c9680404226405802650311540c803503203089685210301100c24403040000e101241e05450104081d1a00b28401d06001820b00d2015840e228140010700200750755134030010303541c001c100c1c81d4050032800e40b40c256403081c1440450500a0440e4502d00d8800d805a07030503071400b00140c0c1d2504404403503805516001c641d50394803410031002a84000151406107202c0d00c001c556641014414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 474502931 1250 474501681 474501721
    0x90601030c0503061306050414180c03150a06090f020d0c090605300c0304050c1905060c100e07060e090c1215270f011a0a030e10060e 59
    0x3154a035a60340f100700000c0c1001014805d00090b034640b004030740c54442e4800d881c030070980e896070350045151182d401480340d0180e00659106400c0b1441d020700741d85001414540b04100610004225500c401700a0300622042e0f1040c01042d040c0400341c3c4003041d46500030b154040380807070103020240280409450103c040e10581000510800017400845944280010320048075102286101d10341030b4507104018068940301d41e03414000003444100442001000b00740081540c0658162044107c8078440303080300e100b0540030360b00001e2001d00b03010302071000d881180251070701044003050f8540034681c0e07076180307000308004a900098509107501c2e18407807440c8604084104140b4200c4001c1c48810354000180c0f143c0748052082c0348403031045c2d80c0c000c0e1120070740041c1907401d5842c000d9541d0440c824000036200c2c9296412010042c01126000c0b030112981041034115159500c855007000ca00400450348404040d001c0d00919a810a1507500701c0400c88012250f4903156454200200c02510302d0960b03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 474504181 1250 474502931 474502937
    0x12705061e01060c05030c010501140916080a1802031e0706020f100c05070b131e0203060c090a17010c0e031207110126190b062208030403060605090601030c 69
    0x10880c15201c4d8180b1504070380314005032420416117038280d5094075401e8118002e0110340485000250801e541480d50060301000b0130070b0030104444018100d0b0070080c000206141e11941c0c00c41c0e5010864140220740c541c09411101640302004108135942c080c0744200d2428040d8003000180c0910010b00d030b0321060038580141c03000c0390010751071400402c910014501445400d00031280401c00003850288625002e0340c0c007400d003080710b01c0c0001141d005010749102d00d01c10200c1c043c025880000e5201e9200c000140026580d41c43c12000408a1800303a011280c03000368103641110000040d0008511901940c43d0303030741e43c0040c4c4010036071038444c5241d41403081c003014410000802c030765004c401280310060404c5441412400d2200c003800424028031245024501c0c10b00c95001c8030a8805a070b003940083c401c00c10b0000c0d050000305a0310604400000110902c00c4000a0201e0200d203c80180b07280c0b421250760300e949280c11006041c1c0da01c40c09102e4500300c4002503103540240104062031007690b03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 474505431 1250 474504181 474504241
    0x1703040302090c07020321030106140304050a02130f0f150801050105060307030c09180c090503010204180504050c1f02010e0c0d03080a090503040b120c07050d1101270506 75
    0x143d504510758008210581c0d0600c10745000d003000214601d03441e0280000c0d001c0690740c6c1d605081d80900400302000b28081c24540030810000420b00104500100c81e6040315148210207040c40d180020340803030710400c940e2914000121021000c02c1d80802c9801340f000601d0040d01e5501e503040f60886000340310303081c1c00000030000548402e20039441005190314604203942c8480d10b4407000031084001e0341e4a20140c550307075009080900d802c00e504c0740041c80120025868181001400150035140700b020400035500c0e1004a0100602405a005040d0f4040c0c000c0840d90301c01180d000c3c40440301d030054000b5501c0c2c101e001612a0700806c001100300e002500d0007038000075550f001c4903e070074002c14000d255651000000c001510903c0280000c000c45c0e42d1180c3c5402c1e00c0102c48001c000f01400500c65800304200150005501040d440b440c003149003401c40e5000a400e004038003401e000350f180a1000b00c100030440c0c00c0116105444060b44c010b90480721301c0c0c0d035051541301c20148400c0c51134592000031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 474506681 1250 474505431 474505441
    0x20a0c0b0726101a0409060f0302031c021009020d1703010f0605040b0708090319150c0201050105030703060c050417010f0f09150509030d140114010516060c111501170304030209 78
    0x80c0540301d13030f54850304405444c050351100350001302c8801c0d80011443d150078144c01c0003540303420081c500c01c440410140603c41d803844c0802070750b5141e141c070000700f140f51680f4500d070641d80c1e44449440183d03045030004c0000f281d9401000c1d03803507109001d5519944403001002c40c8251240d0300b81d9003910b030002050f925000079a00c2e03000d05500208a0b8a50520800500d40403100072030600300c0d01540304050101d0304540d0320b00030130b0682d00581d40100c110381c5030400401c815170700020f200045940240c000581e0303130b9155004880920407a04002c620303641c1d07c84501d1076080e055100303260b0440d403407000700400d01d00100070074195803200b20083c11704003d005964000c44450b6010b030790042400b0080f03e02e0a400080d64406a6400c621408564815000100303c61a4500d201819508003441c05a00e044164052880c0c0c0350f5041b440540300581c0c4d060311405203801040494002c040480454507200d40c1c0e1a05504200000d006048802e01c1040b09050103d030000180c4085c0ea500600405071176070b80c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 474507931 1250 474506681 474506699
    0x905041703090c3d023a02010e0304080d03140c070b1005041a04060509100b22032004020f04031401090c0602070311010f0f03020a0c0b072610 63
    0x450640d140c01c0240c1c0e00411312130710641040e40040711300c00c440314100040d208a006030816409a402400d118a8400c0c0c009803c1e2006c5c04802d14210213120138034030005600812801072800c0c17010a450b900c00020003081040c0001041a040c0f011580d0902003061511010681c00c0f05c156041446102c05000110024103018505035001d02a81c4900001c15960800642603850303818150041400d02614901e1a080900980740a0003003518400201e003170010082e40126203078496148074110100301199009400b42c49100d8041700039111814941d2a03040c0140300303104c500030210100040d007105000f40e05140c000d41c0d580394080070071982040e20b980c444194103c6d144e20020308070755031030041500103805002d2420140c0410380c020150709040d0720345402c03507074614040c05060110000d0748800301c9a01c4103101d00c8140c09440d0140c0c0f140311b2031030b0681f88050080f00c000c00c0507500c1001c01035555881110841c404030010302d60460080f003403c40c6e00300414250341005031000500c0f401c0c8003640c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 474509181 1250 474507931 474507949
    0x304030c06020c011e0e04060f0f140105030c160b0a020301062706030e0a060e0c0a06031104050d1506030809030c0406080a060b0a0e07091715040b1b040905041703090c 74
    0x8a40c1c20b10746c441c6c212410006007141c03019008100710f16104141401400742d000903c0014101d10402d540d041c0c206440042c029000060422020580005401406203500c80c3c694100580c000043d8172541011030488020350801d001c1c1800140361031101012040003400f1107004e01d000301c061004418100032044028043c40110640e103441800d048000299081c41038048600c1d0100160115184e0a82080801001640440704040c103001103100030ba000c52045600b15881141c01c141c20380841c0ca0600004001000c01402c0d092070000e000082c890950001c00100100718195624542c1060411007200e0682c0591032803075000c442c031100001d550750f008152510b07009080c072504580e6200464607010041701ca0b140082c0500d0820403c0403560800100c45850b00005030464080305c0601101c070400080001d402e0b039000c1c01c04918150010005800401d11400100c0d54a0b52202000000390506840031250140c0b003c104010550708ca40583c1d001c0d00300341015100010f1403400b0025022 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 474510431 1250 474509181 474509237
    0x5181b0907021f1401050901060e04021b03211605030a0c0e031015090b03151b070b0f011a04091a06030106021e0705060d1e0e0304030c06020c01 64
    0x21080460891034201402c000302c600404406001c5980c1070380340c4c151050340c2c0042c1d00483c010b0f946480180b11070380d000f1220582200b01910010b84170140400180036a09000c540d283c542d0000090540403034074500601c000e6060751600d501256100c017520907503611000f41150780050710a00110700f1100d8a40c004214560b0300340b40c00d60b0001340f50800139080c0560070300c4031078116a480780700700c60021030101c4000003440c1e841f40401c0300080c80400f09460308584454100ea4455031000100d40180103e088031248540210b03181d00ca880500d0300300410481601c002101c0041040000744001240d280710018007141680103040500c0c0c042e2030005012070141c2841982419030980107a07854120143d8003c1107658010075850341c8070400b01084117003903c4007480c0380d000084148403585a40084440c00000d20000144020f240100c0192600485220805581c00d05c10b542ca504034002003d04156401a8109008195110b109981d62651850036038046051801c10001e555000c0600d41900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 474511681 1250 474510431 474510433
    0x603040308090c0f30190515070e09060a0b030c07020102010501080303040c030f08160809040b03070f0b16060204121203290102160b03180609060f10090603030305181b090702 77
    0x30905800e4014204854000d004186c0003030451a881404020440c014140308048c03c280c64906001400401090458004a008045000200e50a80c94070100da0740200084041e0644a0400d8212204113074007d00c0c0507801982014004074a03280080112801550b122a000b400140340d5903620120611140003500d20342d80c00d201000c104140c06402c044007600c5071620640d0b0b4901c0000b084201c0380c0381c0001d203019501c06081805503044100c0c84100359000c080c49180c9524084c500d10400d1100e1100050180713001140c001115406007960130112841044031034076445065a08400f2a40b520440e150b06069000342c00221100c00b40920b10281010b1054681003032411042d0030220801e6032100d10385d120b0000402c40300700b401d03003003162141b003190021f401c981c14040c51b415903444015200101969003000480d94101d0340807404002400c240009000c016920308020300184021200c003010501e410703034070412a4101107040082e04c0d01138480303104c66501200901680d0314000744443c0079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 474512931 1250 474511681 474511759
    0x14090403020a0f080304030915080a0b0f03070e162a02060906280518090a09021c0605060d02060711120a0f14010605150a0507020603040308090c0f 65
    0x860f00d5100f808441e42d024108542e40d038145440c00500c0c2a116a0090500030001c1c5011007086500018281d00948118408281d2381c0050300022075101001030344aa140c825a14001010926400158407030703500e03a002c080d1000034a42c0c2c26a01d141201a1511540322035a901c8201d0104004410102d0360002d0903c1d41050b0b03520b00816055842501d0000f80c2130240305600c0c2d2254500a481e1010a5440ca071a50521500404108000c042522407500c1121428000b404c40a03840c1d1090551540013409001407502c00c8655085840e40007005861180c03e02d4002412400e0290100555076809401c45143c201180c944555036100e06c9151940402c1070761402148a40820558910b03a0190507040140d012a01c1c000c1007880c2c0759039413100541d040080c01c000c0c40d560440d041ca40d800c0410142c43da2214072000803100d92258000080d8440310201c280000e05501a240500c50606602201d0006044504210000000150941c3d21240004c903050003003e02c44038a1050f0b0707020500c0040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 474514181 1250 474512931 474512933
    0xc0a060203071b0e180106170307060e030705010615110c09060108060d2f04091220070b030612010b1c060b100e101b02040518070603020c010e030414090403020a 71
    0x900c03070140d8a4042c05c1c140e505002c48021002c2c8035440c020004040c0d0510000b080b41c00b0240c9034095100301078840d558903103010a1b207203030a004840d40d1316480002080a65100c6514591440039042614001006c21040d8601d0200000e51008090b80040ca03c00301541d45000440325240c00620071504182550300d84e20002d11000700071a075101c01150001403945110000c00c83d20504c080050303120703600701030544020540a10004502d00201c0c0b5010141841001925140840a0501d03000500c200280081c01a4004021318040da2046828018000c10324001c0341c00d90f08900240c0340d02030684140600c000c0910305803110070a10541001ca0580c1d440000201112125546d86001c0703501f4404044803450039203140402c254050030301c9041d103118801c442e03026682c1640e00a0080741d503030300800d03107154201c10152260b1030224102c80d9610b4031110002c029422488040c122982440d201007074400020084e41c060355588a6101c140346400420031a4410b409041901940510103410f8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 474515431 1250 474514181 474514199
    0x60a020906070f20090435130321021c0909061517010e06220e07030507080c0105031303051c0b032e0e07080a03020a050c0a060203071b 60
    0x8078420b4013907110090303c01e014203200e0059032041c03e10350784a840b40e001080002050041c0440c6010001840c0c0241324980108402c41c902805c04403050b500400700e40d00c03143c458211940300a59115909a041c0c0c01c110405000581c8594035030100903811998a03800120201640c201c1d2a400b54a0418125960340c54148225013a60304030f4844282c40b810303030b03048a9402002901d8107100c044c140c141250314028455081250107002248506214004150381011010141003403007143c403c104040503030690304903a140424803007110380d13006555002820b0a404103d0b1030340c128060311810300d1030740e640400f171402a8500c8401c03014000e0500012000c00c1c680c00e000484603c0010700000c566454808151030b2240c59025609070440c21a0350380c0d0350003058142c01c182c940f02c007030b80440d44e680c51100580c02c01d09641c2010115205100d1000300f070540c0010501e0001c0d0141003501d030f03008000b07418009884114010f40000d0391003040100b00003440245498002d80040501c2801280c071402e10b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 474516681 1250 474515431 474515453
    0x718060203030a06060f21020403060608030c06090105090d1b050610030c080304260f01050c07031b0308010e04081c0209040e010b1f02070503010239060a02090607 72
    0x1000181d0001c0100541c02e0700d10301c1050007816550a050540e060f4110340101040b2a10403406006190150b80104200d0940c0548020791380c0024188540c54031601e82541d203410000d06c0071841e00c148004911500c80c103200e071600625007480900800104080140d48026030400084898541c2c6111072010580900c4414003401900b8440d40d240da2441c2401229141290040740b03103600f0420040100e404203e074645203148400184581c450b0072a22000d083c0701d126110f80c0515400c000801c03010386d04890051010710f1081d1540d05d5003000c407540110f02c40c41c060100401042000380140310440640340c02603446882880b4091038111381d031245502421441407118403613600894101c010349007500072144070064500007001907807004000034012080f03941406150809107100100d50038401d0010901030a07000d0000e65680c8c04481c910040c0a04505181003c6600b14001c0c192075080c15075240b0342d1a58801c0280040e40368602d04800a5010600490784070b4ac003000600c000401003412 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 474517931 1250 474516681 474516689
    0x6150e09010b0d0e0a151b0201021206090402060d050403090501180f1403192301050603060606090103020c01150806010b0f030703180f061506051e07230d02010b01050a080f0718 78
    0x8040340c606001e0594414000c1110114800c0d64018031209841c08000c0c60078550001037218484559203071800481c803035114400c6111000d90402e020031007855007042e031850403180c080c0c0e030750400250f1420404075114002d008035182405181810055810304404a6619000040580380413520440312607121400c9003004a410450100515134045200c41c000e188405444000344100c2c5001400a0b8403020300618461180b1801b0801d0940742e480703079060342c1c9140041c5000700960900c4200140e000419881120254410ba000102e201c51b402401e0b204da1002c452800360843e10780d06003c3e805880318050440f80108941440e8012480d154114600719010fa03000144201400d9001c4041c0102500208140070341041066009144a9400c002120100c02800d84603c0b41e803600c036640c0c0080e43e40402e13044200104108400700040303000d0f1104400381c0c00030040c400007203005649138080d203421480450b40d44000204d030041ca1007041c40e40f000c01c80c5005928562589030581d020390b01504 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 474519181 1250 474517931 474517973
    0xa06080d0e13020307210e0f0105041103010b0307030303230712050121020607051c020d030b012309010e030f25030f140304030606150e09010b0d0e0a 66
    0x548801600740b88a18503954250110158590702d09038501400b0011020014011034a0a103c22442c51a01d5408842c82c1880c0c0c00c10341703040c803a842c1000d50180800b5201a18900c24440c001c00b0f1710b15051203520b851040160140c90007900c2d40c0c409a00400320a030000701c0c0301c0f0390502031540c248551580030340f0030051500d840c0c80342702c1d604245004a45050b0000000d03042c2c04040e40c01000c48922044036004c0c0d0481e05a950b50480f450031a04040e0f4a01080d00d80900f0901d0b4030400a8010070141d125100568041000414400044445010719985c055100c41c480000b060401c242c40010503420304181804000240b556012910341420a12010b0b950340020000744400030304441750a0f601c031100100d4010035415500c550080c0c0108a00041010190004440c1d81c0d00703043c01510021a046041040001d503180d440350050a040018940003d06d011424106880d0000303813541620f0b107070a121803d08020303860160003800308002e00c46d22072150207000c00018031003c52000120003254 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 474520431 1250 474519181 474519197
    0x50106031d0105090705061c05010308071a010605031902210a0606021f05070903080301030503030103060f0504050d030c020309090a1407020a050a02100e09070801210804030b0a06080d 81
    0x4800c400d6100c0ca070041241503641804103000e04503900080301c00c103a480455029a0b01c0641c1c003038481c19a003c401a28400f24201000002840030880c05840306600441280ea00d6943c40d81c22404075000900504000c102d041c4085204614880381071212100c800e9001072070a04800650140d0380b10190900c06007194503020040c841245000340230081c4924001007110400074800c0c0424140011010711041c0d0396140010781951050f0601c0c0020358000f007840d80c1d03d503140c0c145540c8036030090009440031401c0008191411700c00b071041503c0b0795005400761440c414901c3c4100d01401005200c1d80441c44103100443c4281d51700c001c1c00703005450b41000044c0714460fa9900c03c0721808010180760640d04a400c15401050000c40c0082240383e04031501c8004500040d03080c2c60184003500190340100c2c031001004101900100c1d1241607908103907449603005115034070703180542141c5400030f00311181170000300001030801c008103400088214001c6451070b00c07805a2454141c0034408000024811 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 474521681 1250 474520431 474520451
    0x705031003150501172a0d140303090c0a06050715110c1c02010207080712031103040f0201020f12040b0c01060504180b0a09081209010e07300c05100c0605010603 71
    0x10300c00c5000071a0910151a10440f00811b101c04a40401080c011303804400c000780f600d56940c4401d250b501c2d44e02540c0080410308202411356280c0040f11a1100d500c04d9900c04c89152030402400401c450452341c441c1d140206694400321004030045902c12665100e0031089182d12400000d4000b103001f60005000c08a50868444131800003044404156441042104081703130307440303088940441c5c01c0740a010b1200005c1008900034210082c0020390b808c2c012040c8030400185050080c0568000d2f401ca07071004034081c000f9034440e000741c8503407050050100b108000421011001d0203001c62078400005d20b043d40c41c8041010744003511b1091a0301d403404064841049010b00d48150020103206080247c05441c2d07407030b2401445440d01ca5111700388040001031910701c2c00d40011091010711010360f84507a641c4d20001c3c114144400042440108042c240d480d030240c1c0b003603586111500590005012481d040c1488405034012003400e041007681d100d803102003603041c080c16000704480d9500003112140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 474522931 1250 474521681 474521699
    0x3030f06170a3f0905131a011e0e0f06040e0103050d030b0a05040504050a0f08090f040902030d08040c091b0e0f09010e281a030a0b0705031003150501 66
    0x11a10848944480d028620324401421480d2081e143e002401c55500044020038141e642503030b181d1080343c2c448248400441e82c908150020311120800c2041d04010000890054950381c08009207080701c01402038030100d02e1480303002800c1088001520342003001240e640030501c0e40c0e00c00c3d000206e040d02144d00400401c401040260203180443c0340402c40260528005140400781303204081c4590303220008241032003420f20440da00a58085514400c40310240b600300203d80103421481c0c8100d80c054802401420070b03000d0035035800e40c000c0240c000c02c2c2e500b11003500c0012010b001500c00c51007100b0b0101d511640f51003540480382c0b050341c0000f00c0c14103c4100401c7c08000786889401002d0100c041c94840d29010380460569030711242198450703440000500580d459030102c1d102c10b4000d0041c01034044920350110002e880c60808bc0300501d40c1003418165240d0140c0703c010502160400007805861142c00a181c00c40c01d0381401d28807082c1c1e01e0312489103802d149000f10002c0e5503114010882150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 474524181 1250 474522931 474522953
    0xe0609090108030903071508070c03030e030304060911190504110412030201091707080316020c180901060e0412260901151e1707030501060b03180601050a0303030f06170a 75
    0x960b0785030700190f211010000804203200a0040700038402b80d040903000f018061381044c42002012012281c407454070741800c002600c407072141079034034615000c0c2c082a507041ca00e0700403480819205c09084520f29220500008004100e003002c0b0480c0c0c140400302d526903858010a03071080c043d50010450b4035040c141044000000c45606029807020000d900c002880032050340d60113a2041070310b01400740c20f60401e034140122070101d250712641a41d5903241801c1c03144040c9000b103101c203000b00001c60300c4800384940c00809903400307400e40d40502c1c00b84207072074817501068000f07980010a1103900415003071ba0381d61030081a9202c035084d946403c406100ba0440602d100000d0450f1046d5001140b0103a015413140c030210700543c03070304c030600c0380a8101c031180800c594401154014020420a83c1e1500030700c0c0310707130000d071454400f41620042c03c0a5039540061758505840009241001842c5556400d0b4014a42c04500c002c5451710750000140380c20000d15940c050050036400384c0008200d6282851441c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 474525431 1250 474524181 474524189
    0x12c0a06050717070f020d1b0f140d08272205091f091a1008060108010603241d032116050703090b0c031c0209030d0e060909010803090307 61
    0x540f0622440c0d02007042c1000d088040c54041c0e4076a40c101c100c6007044640341143d00d20b842c2d103207040200005520380c445010070702100c650030710b6240828015010061310348082c000c05404920b0601403a100c02441d0002140c01e0b204144823100d6030a040360101d40011580d000c2c5400d03041111040c0303a508007160141c558003074211005061002c00124400c240c55400e2115203e815035141c2c01ca100700541d1300c14a0380c1a20541911a00d01e00d080e180e120b8a004a43c021001c00d030084030f000003030f1714205000f2401030f00c0d408003600c00810f40003014041e418803480004281280c8034840d811048010b07040200082403036502a5598000c1c030007810b00c00004102c140d000c110003c070100180484c580e098000d07920303c0e81c5803550792882d40b8102103440310510740140c0340100c00000c0f50140f100c4004024a5446c0d80300020012594504092030103d006010040350117420000e180c07034107203101d0183d0404a031002040b90717043c0713100380000c561000c200740c0190b14550310025a444c060301d0708100c004014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 474526681 1250 474525431 474525473
    0x60201090303061d0f0c0c030f0409110309030a080601090b190201050106050f19050c0601060c0b0609220203010e16090e0a0203070e0a0209150d0e0606012c0a060507 73
    0x4d0085208030388204e940206440c207016428401304543c60310f120100d0303242c4018a001c40b40c4803404d5400510041c2c0c13184c03003000c500c01d00d40540c003004190000b09a80c4a80003540196041c40e0b00590240c40d4954000c0100e07040040c441c001040301244074001e0102c1050503100020b41e4030b81c01401900715001a00500d05100b0103019144016025100711040c419042810702008040e240701503595002d40040f512143c0640b05c0089549944418070485450050400f100d45443d40c1013070001c2188140c1e40d100b1035054010365420a0601042e061220380d00c082c0c0001805484484068107085180303091400c1c0c20f03113001c010000032406001e000d544804200244c0400e01c00c0782e00180d039640203880b5000c40c065583c00000c1d10801254161a414400075060140a800002440e103195100b11204071100d45841c07007100a4440c0010000e1103050180c42e01440e960b9684c960608464903680380030a0070000f80301d241e1141d1150481c0b0b000401c401d444840c0c5880461034641800344080c0e114880c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 474527931 1250 474526681 474526709
    0xa06020a1a01051011150910061e03020108180d050d060512210409020d05060316151b080c060603071413020c010207200f0906030709150e0106020109030306 69
    0x199611400b1a0004c0ba0302c50400000c1c1500000002d03082083e822209001e0910030010050510b1011540058070303490110100303c43c546800ba04001c00100c440039055405e1030103014401940220603c94001402d1403219511b40b521030403042c9815549080780001650118804410b60a02d00840016040440b030b441030703c2494108165890b07035840c910221010f09210b0124071503a000048601400160b001591303204c6094100801500d0290b6002d0301038815400c5500300c11155805035800e440340c00344410a07049841a00716a0192121100155010030076681c4000070718002c001d02002183e94064426441e0140403d410189550700244441d0240f24954105541c1c0d401e90000da20f4480300e0060325608001540d174024001e418005014601c5035100030403075080304032011341440d022110b4140540c960428008505429510207805601c540000d000001450b0004100004080e0f0501c0703501c0c0d03070b41d070030985019000e0b400302c00940d64682d459014558103007d12405400d14054000da = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 474529181 1250 474527931 474527939
    0xc0c010503061324030b010e130b0a0b03010f090501050624030604180510090b1f0e04050307020a0605070b010f0803090f0a120305180301060308160f020a06020a1a01 73
    0x1c10140b01881c0043d00c0e699a103401140f4002c500d00212110134216104000644a18240034404028020080c85c04140700010740380210340c0005400c00d90b800226000c0945a00c89400050030346a0603069165484015228000300b213441102c1500340514000705d0642000300921603260961b80605005c007a43c0a11641c2a000c1c0100700c90304410141c0300041c51141c6001000c91126000c14010700e103000700b926101c041000c0c0c1d0810380141d03008071000c0301c0946598600354900a0f902005007000c840342481040b49049140701540d0290140c000d907442c2020070703030005440562a070400404900c0116510080c401000b404502402c1c69140590202d0f0910040350703564000c21413642e01c0f0706001d42e80d01c0c0700c985035000e06c24000c02006509090012092502908582060f030442c040031451b046c03d03040501d4140550012a60880b9100740360005e0754207190601860703103200b511042c1251150800680700d1046000040c010b0382e014040300d40052420360301c0e0b0600702d88925012454900140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 474530431 1250 474529181 474529189
    0x5150117011e17031903060518040204110304030801030308060105090a12020307090e010e120a0801030b0406020f120601110d14180306181002040b0706020903030d09080c0c01050306 80
    0x1906441d212011001c1c540140e0000074154038950700f201004598001c020a01c40f10004003502c1c402404034415044a2011602103044a00500c50a40d0003604a01c6c4c01b042000101d90381c513001400030308045800060915148600d41c01542d04900040c0b80d03000410600d54012241d640045003442c0c180d10f86084200010ba405080d400740001d412117244860b01155420482c8000034400c2d48000d2184202c9224020300178103500d6510700c12400303150f1000180c480c1e6281110340d0041c058641800590030740c0c407820030440b00280100d82c8103600f0003180c140c0b01a0030001e4410704c0c4110001c00618904140018102e84120b10a504650701220010010641100400e80000300c01c0c025640c41b1030119517803030b030b01c02040705403540c00d0300940c401d00000c6420701c1b24401c6141041c00031030310200d0a10204104030b12a1f0b00c114290300b40d040c001e010016440350003c2c11118030040449042c80c1500e016202100d21404044624400001d14280b0658080c070081700c6454003420041d0851811402003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 474531681 1250 474530431 474530477
    0x62401080702030c0f061501030e060c03061504090b0103060e040b07050a09030b0c070501110a14090a031509060e011a040905070b04120309050d083406051501 70
    0x6818048000d00240d02180708006a6250020400c00c84100803008003c0c01d03241c010665440061800c4043e0583c02540613000d01541100c002008100c176540b14403800c1750310b42001c0d10255100050042c1200c5180c45000a0030180650300800959030707940000240448105504c0b0f865141441c0c004c100208503021451980042d42d807c000e50340320071640d000c45103c0e1907078000410003c0c1d400280030b14440000040c00307105200e00c00803c000c0b0340301c8080c0803883c01035409000010707410903c0c50500c000d0007809045501c0020b0030b40e4286907280c1e95100b00c07201d0480021218666140443c000f401200d0050b80d2065a0b0b007030082141c03043d050a81c0c100c000c0140c600b980215107030b014807010000208002c1d001083c409003c1a00c5545401c5560160b42840d40142e0004214420114051a0458080a40f00c0d44840d080d4a0078072200d1900c4241401d42010180f40c0d03505d00440040003d10903009a4134501c50180040c4510f0b10b40820350303002000403406410050013501c4160304103491020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 474532931 1250 474531681 474531751
    0x90602030901080a02090423060a08071a0d050f040303060906050f0904150c0c05070911030f0907090507050901120b010905090c160303020703030c021c12021303030801060206 77
    0x40f821a0340d0307400362944042e10a000d070301c0b5041841c2030040c007150008402207913140100d8550b81c2a90703486480400035101d00c14081c1c926150050380e0200143c1ca40b64842400c00d946502c5000e040c1221100c41c40c048840403100c132845540032a00300400c0507418030906001d452040030800080b420400403c81c1c1c0285411218021851000803c051000102d11441d0018a001e400c2c0400c11075460014201c2074031444c200d5081c41107020104083d00c417405a4900c100c8070000e041d007556101414007a1f1080060920710361402090004242c026890107940e1040f109621403031b80d038403d518001480400b07600618402c0c285004031580103030780d201d042c40c0100d89048072030a600740c40745550840785106081c05982d50200c11041117082607019000742a9090090301c003044070420020040c1d072148240702029200c1105080511940342c06a00d00b00d40380c1005030001820083d0015003c4e002481c581c2040c3c0214802e54010400c1c554104800c640c0290814111140c62030214041d18283d201044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 474534181 1250 474532931 474532937
    0xe070c08030606090a1a04050120210903070608070212090916020709020a0c1403030f071b05070906030b0115021225111002010b0328050303040c080d090602030901 72
    0x41404c0c1542d5042401c001031300c8294400300703451440400c81e1046038400d22503c0d020411a680c003a0b00d86a1400710034030030359461805080c0c00d403a0b00c00409005c1040102e0113422490500c288805030300d04010050241405440e03030140c604001034080c0c54145010f84134420507104221707141d100e0b242c501c02250481c1d0424181c1c2c00700c0000f82c40a0342800c1c0c481c2c00c411145031001c06d1607407610b035002c140f0f5500c140c000d100c1e0048010741000943e03101e1208540e0181c2d10400800880c509034030a03803400c0300c1c03041041361031040307140143c0e5014101180c07580918445510b4079010f1050110310300200e0300411280c0342030b86100c2c45800d00070f91170307a0b140304080001e001d020070b11805032804450313240f495400e05510381d0705086662514950100e8001b220307134062607046140303514050051140c1c141e0068000c0c0100200342d4040489941c120030003a1648800304170741400c5000400402c003075401203100c7c1641000c0340d030a10581514090300c0d210741400700040002e0800038207402004495091a083c070b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 474535431 1250 474534181 474534187
    0x1060311153604090b040f050106080102070305030405071403100e0115090e010e0102030c04030213110a021e0307020a03120e03030406020a1b0509160201090b0708010e070c08030606 80
    0x344149403540202e400c48035440e410394030414980e48215811203210840c0c05a5a4120303454036003400100d420058000308851028800300d008602e074500704c4544035101d00000300380f00742c441c4800c0b8203a03001110101d01103440481403004006092004202400140d4001d00c80710461800080c1e0381c444040c00e80600c65034400c06031003908420b400810784c0801c0c040301c0d10403940d40c1e0007e4070000c144540c18681310b94a40081e030007180f40d060007181c1c041c40e19040124200b40c00c1d502040303003405040c0d0414484035a1000c0c1c1c098928070690250040c540e8540191100c16040300d01c803c2c400d008108401d8142d082004030317000503660002070760107490f08201101d0441e02a0601a509455011262541480042000621103900081d0344070024820b901004240455448140031110540125980149070000080045002c01249070009881d44004603043c402600c0300b010000c4117031840f000280314100144a000c2818960304e0308509030b8030302030050752920749034140079002c060300d0175200d41400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 474536681 1250 474535431 474535459
    0x2060307080a0b1f030c0207050f061305090c0c0607110a2a08010f060f030c0303030509031b0114090a0308011a070209090706110304142202030709050f0301060311 72
    0x40d80000c2e6000c00103072440b40e804c1e5031180c0c0300b1010300c80c0e40e800f000028100048800c80d41c0c40410013500304c1d500503101794072940c980d901700300494100345410b051007603031441c00083d00e54030b101440c0e0040a01d41c82c402c0d80da06201c0092400e0400080000003072040722010342441840000c1d10283c0346802c54080380c1c50303851486100c54500e05550013204045a542004a99800190710a4240c06181781e010885195100322820010311684406403460040c000c080000c40d0194012961028411003a00d15050401241c4080708190055005440c8c0d91860307480004481d900b6030703c0d0881d405c1c200604041d0b455980082214405010b2a69807410021020400304440401d849000d90300510140c0c40f4a050b02e0364903070700c14452289100180b034142d8420301800c404070484080d18040d500340828140324100303100183c1e012416061452080410032140030449202460044c14a40c2d04c68000c54601420049000e0340c0701800381c807030703450b061081000a03440c4030181d041d050150b5a81d840300540c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 474537931 1250 474536681 474536701
    0x703090b0310170c0102010c1d040213080307060f05010509040b1521160b040807090b0307120506060307050609030c0d0f060203130b0106081603090512130e130206030708 75
    0x180b0f9004698480043c1040c1241100c0441c102140301c000783d00800462082c81030803100b102c0c4540054824040000300c2000a0400fa0000c24807091000325510031aa40c0d0440d1502c0c542c00208180c0b401692107031104030510583c064903004010441d407103030040c2001e0701da02e07041e000e01400400000030107506030f1409882c0d040400d035107440d0741c0c1c810062003040744d1003503500d80c0c480743c401000021f50000e02017580c1c00c6240c00d880c15102e00324010a981e6051011039001407502151050341842900e00c0000c011007a00320f905039082c42200a4042d5045c0b84091602d007055a400280c4210018031000384161400904070344504000c44403403014408604100480075020800540103900001c02c004070076a542c102035440b1440341038100032503a81c1d5002114859026140c10b40e005000c00e0030044200d1103900180c1c0c01a0203134003034031901341c220015030105038005484020b030704542c49010030000c10313588145503210750f460541d0125420b60340d0006400b8030004010405006a1101248448903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 474539181 1250 474537931 474537961
    0x102192303010909050105060301090809010f17160206160f050a05040506040f0806010b0a08010e07020c040624030213030f0f0b040614070509010c110d08040e15060703090b03 77
    0x1114115075680d6152010751014188200d4160344542c00c00b40403c42508052041010b296045080c40b801c141d4060011034818401004d00400c0060300c444c508100104041503a001f50714104003072502c5c0800d150080d04089006082c0c43d0000b04030082401e1150700a121080c0115035403511550345d00240d04213907414091034004c5c6420520204d00030986403400002c446c242d8400400b10390341ea0b0390300d043c460079504c5030202000c0014028001080a00c41160701650046024010b5640440990000c24100c80303969101c02c0300110011029214035000d000040368002c3c0d54941580760013801010b0600304402844010f00c255003050188041c404025130210081e41d200c80e03085103604045c246000078000411154801c03081503404501043d00031000c41e0302c001d1041e1144000b926094440506001e40c810030150031980000d801000200e0000080014004103e10b40d22603013069201440c5503031811a00130700401d41000050b02203600440c00400b00c1f40e01c0d204041d0b90754ad8100c0a0800c1003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 474540431 1250 474539181 474539237
    0x3150712140103060905150c070f0213090c03020f0a08070e0c0c030703030c0906051206010c060b0303070c030507050409150e07031208060415151d220c02010219 71
    0x207024900110800040303412450449000341c1c200c62000c0c29904170b40c1c3e166541502c0201070206c040040200007081d041c000e040c500c4c002081d040b514400d01c07c110060300c4000c5402c5443c0c0607084014801c600c0c2c80400101e103e08155100c910383d81c00d00d0b00a5598007054011301c102442150000f510521607035044512b140c0c0103400707498940d0070611740500640318200140020a52115000c51242c1c40340e025030300c82e00800b5001d4041901c0d200010341d0b000c1f400e008140d072029207564501c07110780c4081006008092095081c1442c0c680340d801c042c0c1c100403954200310322550600720040f010881c81d102d42010340000d404002501c0c00da010025242001641c00100181300c1d40b03504c1418541c00107400ca105180c265814040107110180c04180c40c0b075940641c07080e9a0001182d03e512074403500c4c14541030400c15284090b548803d00001d80e059a900c080c00091004180d0707080c001c41503d003d20861416280000d5050640b1810f07408008101c81a2620800400a0b1605656101520b00003040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 474541681 1250 474540431 474540461
    0xf09060f03160f0b2517130501020705090423071a0a260109020a030e030c03040323190501140c180d11040209191e0503150712 56
    0x10344a050458001e50b2603a125403410007400a0000400355401011580e00b0b25501844424105628801010a5900c01019240303400f552465440b41e0611200804c014880810901005850000020314042c01c0e03030001400788402c0800d22001500c11104503c0d040000410003039420007004601d03182180990049000400b81041e205c2c0020303d0000800c081102e90342c41e17080c058540d0b8005201c07c1c40a269072456070120304010014011294060b1440304103e1401095106d4102c030740600e180c015501e016159080000c08004020b1844400c2004d03010f02801c0d00c65202003848d10b651a01e450901a5034035024120104040180a500c07260303000c5d003c2c010805c85402c3c1202c141a40e9008034212060b100f5107500070245500d40b0b003103144003003075108095544816844042c000a50003118001f43c10400c021260b00a100492041c14060000640c2d15214080c1e0b01281440c482d64070381c0102c0c0607800c80c80741e001c0e0720a800100c00707920500c14141041012203040080700284400c9406640c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 474542931 1250 474541681 474541693
    0xb03130506040f061a010f03050603240a0606170103060f020706050f0709050a0b03190b09091b0a060c0209071806020c13060b031324290f09060f03 65
    0x304410f0b102e82a9085018076400c0000a40d00c02100105050520380e82d800318640d1484a6041f600c80d80100750b024034003030156250b85600b004003030150040030f07288083d0076244000f0007021070003900c1204000d02681c80c22540c42e0703440c40da8420440c1010b01014001940721100901048441c1e01102c04c03103a8003047c100110f2506036409010140d054031541c1c00101d81c550001081e10f040c0302c0103030944030f10300790071445d41d140e403003c515050540c00401e0f10042e45840c40c3c03003ca682c403034112600c60010807003e4101d103010304403941c03400480c2d010070174403511343c81c8070038010302e40d2002c90741d1001581550b072134145858040f0306441c2000140c03880d05002e4920400031640c903901040d240e50880c0d0070368408821800003400d84090390014012400740c01760610010b40c0703600c803c60095400500038280c07404406440002903004640c0040042d0455441701c0f04c1c1603035061b10014900710400307400302902e0340c061017100160003994a150864401c00002c400700b03400e603071500b840c007004020040032030386 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 474544181 1250 474542931 474542933
    0x1d09070e1503060f07020d08180a030909050105040c08010b160c1d093f040b030930090319061509151701021c0608071e0b0313050604 59
    0x51541d10032441c1a0183c003c010100d612415050040c3d805078940d174014024030f8004030300071944440010b00f00711003807003031465078012045d0902804107020f00a0351900742481c01c03c001a02601c1040c3d115600035403902c6510b80300c0f00e90044009066071466088a1703540e04614610800c904d00503440503000780c2d880c000002d461880c0075842201c6180702c44490a043c0c2d615080c03245c90319152040c0443d00c14004901c02000304190300418480d01050000410810a6442c20301c690741040d00560b011030000001c1c003400f5181006203001d00138071700d403c0c40e9031001403003000d88940000b008108940000405d4050095409005c01c001413106103111205110842c103252015141c59458000c12a80c101c80200c2c860145d4080d080d0503140c1160400015413422003c64001105041101c20955003441002d110b040c06505038105e200310b040b03011900c0c44c1000222400c3c6805540200c0400360741504010000c90b110b01c240c8100c0741d2041410b41c480d80c3d804010507421119510080c02c9000c4c58003040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 474545431 1250 474544181 474544201
    0x50c100606180e09030415050d0c02010b011130040512100501150804020603101d06100504060806040e07031703041e0803130512070302010614010305011d09070e 71
    0x707007403034180240030b100d07070756100300780c90712004280c51340071454004000500c41100c2c00291107002d03c1e96868581d00c0c12101403002401c848450308024010303516007110b2115503034440d048000c4131540801804000c401d410055101c000085014503500c11410008100c0902c10300c160b030014280138107100c008030b086207105d54440740607410b40c200d0a440c4c82c001143c4220360002024071440039460340c0450380c481e5001c01070150001014076865004c100c6c1c012a440004500c4040004c0785040c0a4125040541c1000071410208014008008080c44108421603219030406d4000303030181d4000411036180b0f00c102e42002c425400281403910123800203a0b40c400130344000c6105034000e8407044801c3c40c581a21101c00640b05074040e0040b0818008620302c086030108038032035680314000310f50001e00101440d01301c0381c00015058000d40d6582800b000130f0141855110300d101d609190030446581004400c421012000c4035a042c115440c4e40003070840744042100700b01074110001d469605141000c2d00d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 474546681 1250 474545431 474545447
    0x5061e01140a050d110403052806062705090d0503040c1508070905100507060e0a0501060b210103020102031611150903251203020109060207060c110d0f050c100606 72
    0x31044e19440c042129070014060016141900d502002034048001c64900820022010503003608560b0b201c851700c000012014441c9900400f00350b9290300300b00d40460311440c0d01c4c18025180c84600c0c1d01380401c0000c1ca52000c0b03610304248005040180e22501c1d6400d0245859600d80c200741c8000a844201c000070300d8200d0726880c4943c1039a0f9800103440d840d017003400030f40d941e100028804500117100e280c0c0041c5150300605103450506045038145500c68841a0a45403142e00521000f41c00180d03138460b0040c0c031194020345888462700080c2e44c0d403641d03000075a04e10404c0440b0400729401600311040040c80c0c246014000d8004090040c0c0c1d004190058501e03034000d00480d0310a20603c2c0900c0c400b1901d4401ca42c240044c0300851140c401c0c0f4011501000100c6214120119580c44500300000741003440079000950240300c00041072102004003030803018080d40307803858944c0054500b00106500046540c0034034060314140b91140105903681e850003140303031804e1040f1818213201103004c690040207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 474547931 1250 474546681 474546697
    0x10f0302070203030c06040b01090e03040b210709061101020c121b07140901080f10020c070b0f03060a0b030411010e040e0a03020609012711061309050405010b0405061e01140a05 78
    0x6608050b42e860302b02d0f10444480f090010700c160800e020420031800d07520098101221810300d001c082d02c0100958080000080306d554001c2419100705002243c0d002015190300703030070341d0b008502d0100f0403a0b055035544200600450100400581c141140c500c91212000c01c0744450301b107910030b58039558007400c004c8401c041540030303400d1701d4000107900c01c0014040091500d48400b0306003000c1c0d107200e002c000c0d5024030310800c034a1044c82d80000700c4040d04e2000708000b803a002c2c062074a9042500801940301195400007030424400e006020100f40380340d90548540700b00b4202400500046000b04014001a491236000c90144032010000e040c0c0200d5101e1080100c6002002540414008800140b14260340314088000030301c1c0b0f110000d242291104d021400090090b0300342442c011b42901840c680384c0103401d0031601d500500040000c05d0085034039000c0219004e2001d451305902080243d104c04062100c0901b4149088440b039028801540d01000d202c0c9115a030b85401c0c2d400640309601610b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 474549181 1250 474547931 474547943
    0x10b040c08150907260a060b0a27050603010b0c0d0207141e04050403050a08090a020d0f0303090203032a060621101b0f1409010f0302070203030c0604 66
    0x209030804910504500b8440c1da07800326500510341102c81480f200a0005005106100c845074501c0c108075090704418501002c120040e907075a181c082043d0042d03c44030b500004003143c0901130b5030401c0340c0003480004c2030405008020300300c10380003195200f40c1803103a0140342c0100000001007003600409004021006c041400c44011806e50302080741c1e140c24510414080d00400303807100400c1d1074451403102c0011304a4244150008a250000d411200240c0f801c80200d07000162007080280c008440c1c940c0091800b02802c00c0007070680110342c04007202c01c1e00800101c00d01061204150003030b0b0140b01c802c0c6c1c019080321380b500000e101d4248018039080201482e1100008020051100000c08070304c82e11014040411034070843c00000e15a090005951302c40340143c100c020490803081c412106d040e00c091014060400d0b2204010b0010707004282080100010000c51030754050804040301c41e030758001c2c60812200c4010b0b0908600078010b441000f50305000010796030084000001c4d0b0b640c01103005407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 474550431 1250 474549181 474549191
    0xd05011b1d09010e07030e01060305240c0a0504150c0b04031d0301050618040f080a05031005030318090a021e130e160309030507060c02010e01050606090607230a05010b04 75
    0x10104074101200340320b01600f0385802d500140c5c1081c402e070484041d180641c400850400d4481c0d075518100701420840720003030500312480d0324488428100e9580c200058164081c604030482c1d0f0002d04c0b520685c00b031000192038000a00c0e101c1d600c03880b03800449542203183c0203031a0505140082c6039800d44800030740790b810440f40312035175868184201c9016a100604841a20002c000c00c140030000c024000d40c1c0b25040d03802c060703010400400042c001d00c4813503691503640c1c0c07420006045100a00d500090f000b0313807090000000c0b66135804084000ca001c222103c0c502039607182e1501000e841140c43c0d0002c640c15030003410003062103000c050650a200f641078040707003548807075507640c43d000100c5601c0c20740304200040c114014080e07840b0700442e60292401500e4801c040e110300c0c00742c981020441380141c5d134804042c0031151080c0300c2c1c1e40d003241044941920707200410f80042c4450141b44000f030207000c15000031100d000e0494881f13804114500054440c140424208680201500c04d074041c0034901781 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 474551681 1250 474550431 474550487
    0x9150c08030709081b030601031103070e0f0604060608161103190c0b0717041707351905030c04030c060f02060f22050c041506020c03030c0c0d05011b 66
    0x17001c3d002d0312058003d00208260b030300e1910b41544c90b000008220f505405240c001045219076515082d00c99000503540106030f080a0092004413241c40d4000c2c400c12105205200e19140310204400c4034400520340004101c0020001038214802c031a03000d480e10141502860845800203802c48a00b8007444400005558502c000e0340c02040404d92100601041000240001c040c01d41c02c0c0c1482c001041d035941840c10a5680021107081d2500c80d8240d128002d542804915146003100442e0180290f41405c00c2c0720481055503628005020400741704010001503034410139201a6001181c00034030074454255604400380c081002d1201880040c080d0000040d21841250b803102d024070b404642410f210050b403024030500a800c0341c42191180035040b03200c2c2c9503680f64026414014158250090000d10300000646017003940300216000b03400034404505c444c0c00206903030a0b06041540d090b00d44a03042e1601a004040984950206d40010007544c00890740c081c1840340800351510b40d640401e090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 474552931 1250 474551681 474551713
    0x906030b1f121b0e0d06090203030711192303160603020304050f0105040c030602070303090c35060f041a070504050f0319060b06090d0506041e0309150c0803070908 72
    0x10380343c5507002140c01c4443c9440ea60030b00c403581941e041c0c0584800a032a074055400241540c0c4540300070350b0102028100c1c2d1415240c14011301221096056501c18070b44d242a03440200d00b5400ca4035821200c0307241003001c080b51028030048072180000d181c40c06000c1d4580c00040e00940040e201900c180c07160240d06c82d800b460500c5614003c1c1d82241e15849090300e1662090082d500420b401c4003019102e4010000207469001c1080140c400050f401c204c840c18000c00b541e40400341c0c03143c41c12803c10360341900410240461056000a401180124035543c2e81c201106c2a401c2c404013040d820051030100800103030702001070801c1c0c070400c6960043c500414002c00d81d4904145100081100d21103041900041c4140e010090280014001600b080902000241d07200a8004140c07a150400c004100821510382428009140030754520003800306591801030040e1254000d01d04014140c500100c3c02178020390b0300d4804d0302d5200c0308d096a64645207800a02c000c5c0039202e92103652040302421450006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 474554181 1250 474552931 474552971
    0x210d08010f030b0c340213060509040f02040e1b01020c010804121d100305090d03020f040909050a060203090c0f1f050d020408190b160906030b1f12 65
    0x242203030300c564413038540804c00e031040c1e8420f0480c0044a010300c103d21450918030b0460031010120345030701880000e00350050083c4d41030418600c5c02d006140c01002d204554138400e003950000e80020407280034400328400314005080c01511114135110794012440d00180740c000e00360340001e0a07030a40c1c030515015001943c010f4801c3c0d400030a520042d0120f214210310035107002460586006180140112120120b17917102c4c41c43c841d80c0c00294542c0c0c03c00290030401c000803c0e908080345411850b1428071142c6001e280540d01030035034841d840c3c0382180e042c401c0410400c400030f0f810200843d42c0b030a1420185d0b603901d4006403500d0050b011100420700d180b070f0001200071031038200901e90000c0000c5034403c031100d510a00d00d10902c680d0034071005c18606800c00146110607800c442000e291200f5003031203004808014201c00b1280c8900b03031450070f0140d101e0b8200c0201e030b54038100403e900c01e24600040509040901010030031a400c0c07180c04680d43c0c400080900c6603030b1014100503010440c0c00c14140c000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 474555431 1250 474554181 474554183
    0x1201030c150804081e0a050d1826040306051312031b0e0102120c011e0605031507110604050d0f0806030c090601020703050d0309020a150c0201030b210d08010f03 71
    0x142c0c0a00000c012400400041840f085240320240c4503001003803022009402c24050b8400240f4040b80c68659200d4621425401501c0c4820070100060540e65503034040424403045441c0203c0301c2104100b544198043e02c01665001006004d207180006180c000d800c020802510100c0e075600c00c40c03900600070310400601070301c05032950f22a054000710540300c50b411513040e1411441030442c60f140d00c0d0800c0020f442984103034000032941601c0307140741400d000c40d40b0700010019881c00c4020810355400080c0d0038044003440c2828442c0341d03100074040d030701d040000200420034010441007104101c0c0100719200004407540300c0d941100200c800480300303004210780c0942c165200d41f650303801916069102c0e940c4144148100e070340141d1a80d41e41303410840003403030810102c3d8848904100310324141e0080c01c080d00412020401c040002c0350002e11407400030f20b001e07040c1941d030110000789460722041611048015554092040e529045559403519440c4010b030004440d02c0000c00c2d501c4890308414200c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 474556681 1250 474555431 474555437
    0x30602132909130e0a020f150a080c041203020105011a04080307081605030a031b0c05100b040b1503100803030403050a081003020a0e04020907050408030a12020702061201030c15 78
    0x703100200c4040441e0300060304168840c140c4080050f4228442c0660600350f49444040c00c804800d5105104404142c80f030b61a02c43c0340c02c0e99840c0c0303113180c0100642e500241c07140790000e216102c422a8009612a075004031045509241c2888141501504002e0403a8019030b4200d48240a07188014040d01990041d0030343c40c1c00400a00000c05c4019002d0b00714084c2c1e90110a00721416561036500e107a1001c909100820f8441240d40c40305110341051041421031420a03061520640e0b1b500e07074941801814845010b503a611020400d03858503440340703c1104000d44904550151884030b0040d941080b2280200281071040109001e200031041c0c9015030744c0758407040d05118400f0000d42d0a22401131403200220b000700000405a074400d1a0300009041020f03404205040c140148500d07144010010002d0040c100010026118000100c0c0c451284500e0244625003000708590068880d048001e0341c4400d011401e00703000c440303041109040f00d104161040c001070f5a10042003c1c681c16100350008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 474557931 1250 474556681 474556739
    0xf121814040b1309051614010c2a0605040503060604110304170705010603080d0e0d0801120305040e0124020a0305040302040f1401080d110c0a05120f0703060213 71
    0x38182034004840060b4010494124040d100a1650403a0380c040000ea8207580009080410030000902c0d04014040d44540c00501c092500006403595064107402061038550501004000007980514031550400602c584070b07255584000400710740150040b244240640d1004c503034149041e1140c203001d6004503540c141103a44603229808889040c6002c4015182c3c10807800c00040c10a2141001031441768403229203584c8010f02c010f040350344d100c0040318207074420403c450143d0780043c100c0e41124030204907060405d1051608440d0f600540d4010000c24409c08004a8600c5800b803600e11130300b8a400f00e030709055005000c04c80c0d0324a0001c10242c0801e8040200780003604040e00400c003d8001c840300411041c03403c0c1090310140304268400c0215800c1410610103050b401240340d403450301150020302c0ca901001c0009981101c5030720a0b94403580501710b5807584980306014044030344c074082c02503500041c2e99081020103980652202c01d0f00b001c4494001c524860000d4187c3c00d4a8204000548 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 474559181 1250 474557931 474557969
    0x3010c090e0408031008010608011506050915091206090a050c09010605041503140702070e09031c05070c05190302010f1b0e220b0405010b0903031204020a030f1218 72
    0x21951000c0e116800f0030101c480c021881b101c0902540c00180100d400005035403407481d080c28103182c80e540024040000820106410fa41e40b9884440b001130003008055540850304001940114040300340a101d014031420001e01501c08034010394214090400d170f80c81c9101d070208105200109000b00c2001c00c50070301c4180b00f14240050380e02281c6410382400201201658030804950000303d81c2840140c2c030210051118050204034541c1240c4030f840190b0401c1e03903120107907a21010301c110781001159114000355a1510810301c415807650020141c0300b00031500180c1d072104450741e81c401d034099801c0c850380200d082110700c01d41450f2817025078458240d000d00002280c1011120645d0359101c0d00d41100030a15103401082140101c1c2c0c01c62002807141c281e14140400d45030305034481d0380612814013940d01d40780c40100480388442042e00c01c20406070b4072440001c5505215400160010102204600400601c0c1510302e0000d506512100ca074001c110016403159101070045402c50944102031003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 474560431 1250 474559181 474559193
    0x20c10030c140d0b0f040c0905060d0b040612170a0e010e040e0313050415030203120c011808090111070506190905090a02040f06020606011e0c02041a03010c090e04 72
    0x103024800c052601d4500036052681d40e104640244051040030f581d510110356040c45c01c10b8082d00d50410a4509118038002070360301500c03000b081c5c455030b030048000003800b440c05da500b0390061a08020040c81000301d680c807551a1500f110540e0000c407409a04d0444c50450303003084006032610f254459a902400006030303801116046c09a8081a4001c2d8403045022208001400540508103d441607610940d00e05010401a50040d003100c4600c213140c1c840030b03c05a20003040c0115140e45a11220f85c1c0c4080c0010150300400003031181940030582c8a8a0708100441440140141c00090f03940f9440c0d250040b50940c1c540f0064440d213503002008124140403010000c000a286100e00c2c1440205295904081000b1503401c45070b80c11140d900050030b100a070b401306c010074050301c000d1008200512349040007038070b0030808042c9464030488003081000c3c00c5102c0e91a041d000795010b4402d0180d80121841100003580e00d56407140f0039400c200002c0c4c88280700781d5040c0d00b1512001800c8555444e90b41f240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 474561681 1250 474560431 474560441
    0x9020703020f1b030d23130b030708040c080f0a0222050405060405120f03060121020d06030605181b18100602100b01120e010f090609050c01020c1003 66
    0x210305500034800c01040b144401d000c0d90240d24803060504403414a0034003018113142501d4100010310140c4540d8100703441c8442c840b5050350301c0c098001552000a40344012942103180d015450000c8004100040240d020406900403031013030390000d01c07107625500d038941c40380e808649107000c51744038030170040145c80c1400180b403117149583c00708210880801c8150096900c1210f058a46074403900600007007041c20440000100c110380401e80c00c02d0140420000725110207007a46040003100641510b19043c0c47d800d040111321810b404566416656618802038a407612041d80e00c1d80c13800c00040c2e602282c20708070040c1910840701801d40007155240c0c10524601c00c01280f504107189850440c07650744c011628a000e5400350b46001c2d20a441c101000b460012100ca030100104c0c02e180c2d070003501d41d81080c0b1012031240c40c40000302d0120710203100e0900509107e04c91031125400d0004102c03d002c1030754000d04000e800b80058030356041d80940103a0303440c07600340d02e25508107410114480c0040d21903882 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 474562931 1250 474561681 474561683
    0x131a100e071107271d070e16030b1f12020424020613020d0615060c110301060f0e0703110d0209030709141801020f0f0a030b0a0f0b0d0204030f050d02060708060a090207 74
    0x3045a21746600859501c1c268482d04490300d0200c450040c0034100ba003c1079050341c0d00440786030500829202e440854245002104140115064000861800c600500109074101801c0d070701191115610f84c107c50048155103c00002002503100d52950a880420030500c280b24041d003103510442c01b0b9080c40410160044d00b999800c0c0d44000400b83d07012040c20030801410075688004103174900d42014030808100541d0940b20340c5c50722000b00080d00101000d142180c0038141548020341d80d502d41075000c1d008d040391a14603d0f1001a082c10b003a1a143d005e0b000350030b429030880398030b01d0f1038088a9007101d203400362140008851a00003120400f500145004200800c030001d424058440d203c81400d410104049403c03003404a01040361a43c584100e90b41c8003c21906170070450f00c0c0418201240c00c07140100c030400b24000030017414469841d011980110b034440c80c01914000300342003c50320f48070703c1c00d00400140030341c20110320f461344100c03981401400e000301788245080c90540d2040c000d40c0b100030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 474564181 1250 474562931 474562961
    0x2114061e0409080a1d0102060402010806031509060118060803090d030203120c03061c0b0c0c0a0c0b040806070f020c06090a0902070b0906131a100e07110727 69
    0x350050094850b80600c2c145907200ea80100c0e01c2e8807403a04c01814a00f0351044912070031840440c814401d070303400203650707420a80a08103415940c41c2c25010a0901084030079048030701c2e030013906200780184000380d134504a61001103c00801c03184142000d041e02c1c10b034481d03c4555813003448840b03414074282da404001a44030740121f078641588906410380c00342044811503c1c110010040140500348070048030040307043c0000111810046a8910641207005480d114440d04013041680031203c1c00c1240c0c210303c641002a0542e20b40c0da40034038041590007401350318003c2c001e607008944800d0003410080d09410785900a0000b6081c0b4409001075500320303204040d4040b050410000780320b0300340c2c07004007039050143c1e05556007880e06400180c90035034003415401440c00c1c0d00c0ca8260128802c003103405040603080c800c1d030740140c4540e5041054a60180c11141d14902e408051004454005814160700b45902c0103850f00c59680b000d195101c2c249500005142101468003c043c0d610b284d0312401c40e00000030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 474565431 1250 474564181 474564229
    0x21518070e06031e061302060c011406030106090504020d081c0e03090301050f06010e0909030c160303020601120201050f521e03021507211406 63
    0x505554a0592150721030201c50300c00006110701401c09000c454038408203041c0088044030b11091060b40c41900410203074030311008080c0b035011075035034108484c51040014001d11841e405000010040441a240d9511075880d052001413100014013503d403155800409402900074681c0301c0c000640d1080d00301400f8140d00c174011800405071403280089128600d002951910644000e050031204003a240b200031040d02c0e010420540ea201840c20040001901c4203801602c6480c8418694096106040f40030f02a240000c0c502407c0200540b08490080e4220765059980b2418000703224068100640041c03002c002058182000c1801001e080612006107182203000f50100f10304100c5541d030003807464191800d0901c050304500d5189840064141d000d00081c0c9050751181c16440c0e048004950044003c00c0700d0050500a20089541006101e445180c500d0701800090142d254502d4200190748802c1144c4c00703006451103003400c04a8400181a5141c42c2c681c02c0020a40300c22403006a482903030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 474566681 1250 474565431 474565471
    0xf0e07140607110a060519020f03040612020904020f09100905060a05031509040b190b0307050d0c09020301180501090207052e090c05040e190204050a091e02031c0215 73
    0x1200344c4030003000d555031056203c0b51041500580c540b202c0c0b12a034110351241140000c4000040100c0f8112a010300f011249224072450307002c045c3c000c10b200154454404078a065115001200a02c2c00e07140440b0507690494010324181c94404080c01000d0308694240400c00340180660001c680000c1112545580b803070135040002e07100300044804490f0b14104805000d21b00c04500d50180302d0f0071700c454091260302d5645001c00e942d4449c91207001c0c031507550009580e06000c00c442000c3d000e4125000c00b556603603111142080003180441e00d10252514181c0005044078040c802e6400e42a40710014008800c0309200c500341c0700140c18a111801a4803458040303000d8018454802564400d0f82f610034030078600010401120300c40c0000c04c2c49a00100d450741d404034480909c14103c541e0403540010302d5101e08480500074140d0701c0c001024005000101ea20400a4205c4042198822822902ea105050104101c034450f011000e42c0503902208040c40022070740000d1035445900154100701105007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 474567931 1250 474566681 474566689
    0x2040b06090d05010b120109032118031d04110d0b01051b0a020901080705090a0c09030614090601060912030e1201060608090d020601031110090302060c010f0e0714060711 75
    0x7030901103c1d42e0303641d00c540c0c411506002c800c071140403190310001c01005415403800b402900910300c0d0fa0f1400e90000185a8040500d81e001c4890003840d01e800c07007504982803401408140452510005200c113001240010340740500a000700c01000743c4040b070410103020003a501038201b0201d400d0612405105c1c84e0840000c0201c1e5401c2c070803502d001410480300714010300c2400c25041c2c001101603000418140b0072070325034841803030308842170010000346005542c9080380c0c00f10454200602c01e60400f90010310240c112a04540144c6104068a18599a601c01581c10020710300c1601d42e50004281d540c1c021900039600c5014098020b805415041142070040d07003154850341000e40491148030038041140070070004d8403e109800c0c00140425410740d03c80f41c0b500028480320303600c615282d13845e50765280d114411040c000c5501420054884880b000283c2c0a00035040000f0300b0103150030a82051600c00262240c101d0f2841d902440440703000310203000050303108000594035a00d26a00d8a01180c403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 474569181 1250 474567931 474567949
    0x510030f020a030230040305071b0905270c120102040308121009022115030609030c0c010507020a091805030c060103410a080c010b04140702070302040b0609 69
    0x5450f9401640c440000c01c25152280a0344803010a40485011000002c401d05060300e4010380c050605648850041c50113640b600742290080d0250300321040009940001070700654000d0702402d0340981000807143c200000c200070b04280f00c030140d0043d4280d40150426950351001e8041c084000b40c500364481c1c580180c1c0c0d038400326140d0050610781e400c1100007010041500040d060618085d403900c18240510250407a03030b1441d04070f0300a9003a01241c00c0000707810300c04400e034802a06036410391038540c0c221603c035000241780c0031140c0105030300d107056076204104541e01654020102c00800f41403102d218000c1540c00c0307000700800481b946003030109404002034014035460100a10b41c07981036140c0402502c141c0f80c6c502c024a0351a02282c43c65210701c0b00182c000b0400003001e00b0340c000740180028a015506040030340020400265548504010742140d446800251003d00050003182c242034180d030011215400183c02c1030300c040c001031406400014109100604650400d118480040d000603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 474570431 1250 474569181 474569197
    0x20601151704110f09130816050f0d0f091a0a021216031407020d022215173f030f07080108060115200a1208011e0510030f02 55
    0x101a080040c0f05150024104100d84d1050702d0044940c24000c00160b07001c5c82883c40203054280104080c6840091101f00c4100705811400316494401c40d9000c040e07c3c0c4001c450440b002501a40039007000500542c03080d0100c82508a2854040200d220b0070143d54015180b0102180a60b003075800d01e206903100a00440c0c4909850302c1c1d54044249005000300345482e850320303104a42840781d640540e42d0343d940d2030516601525204240c00b4a400d2503950000400d10f000240f515004e0002802240709035200240c1d000809007242c80c1d13141140f030540c0c0701503280d440000303000103003103282d0081d410010000309100491b003940180000d0121885058208503a0310850000c104200800290700130740803401489407001402d21941004d03100c03a18140c1032800041845080d24000301c3c21440301182e840d014000d0b0f0180c80080c09589054001001444000342c0040c0721080007184205d101c01c0030300e05801c985003500c60103a11b810140030b0104252083c940500da60354440700f15244042c00201040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 474571681 1250 474570431 474570443
    0xf0913080f030708060a14060304050a060509030c011d0a14030906030a05162c120a060b1009060215131a01052b0b06060c0d02010212090c01020601151704 68
    0x2442c0c442002444c1280082281c2d205440c5100100911140900640340d4154151a0325560382e1310f078180140b4250061100070291450302c400c0041a100c048040c100d007915000081c41181e00c0c1d400381c541c054007841100c0074903401c54280103001641d800d066280805410042c3c0303040528600018540d0f420403200c3d0001c5540722400c0091061840781511011200c50805c545806c40302c14000000900d0300301907140c0c0b010100d550020300c0d5252040400c86084c084215079001040e49000341c094600d424250b8000c581d05000c00c04054060410382c026540b86600400034541c00c2400911903280103011104402d815403942da001c9001e2040c000b08540e11381024903e154036050901c00384000315107080744040344a804424003a13403616140c1c8541a0000300c51149911034000064051007000300f1031340203104e000404211a038064002e4101803c2c0d180c0001080d5a0301007800c0d4484e00c080803c1030040c1c100c600103201603103c0b204c1007004090940f40c152406100d42220382c1c2443c000340c0702aa81 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 474572931 1250 474571681 474571687
    0x5061309030504031a040f03080c0903160e010614030f15130b01080610090905070504080304030b0609010b0a05070f050708070f0f060509130c03020d02120411040b0f0913080f 77
    0x14000c2d1005e80001e040550407030700c1c40d90715280d202d0103100140c05400904000e01c8501094140c002c800581e210603400500792080d2070034642d07980388000014031901c00144100400040c0f43d034098038104030740201522030310b032031a914104104010318004003410854021100c07000d0541c0c6070704003500e8000740d5042300081c1c21400540050481d08006150030300c111401c0b881540e031a075000d8003080407500c3e60500800c0320348652030160b426020310f0300b010206120108001013406100048107004000c165440001380c1d88640280000344500411500455000c000e00000107901801c03042002c1d000d036055401c242d03280c002003410b001d2142c0c018541c894031080144000c5078a1144c81c001130009042c003615000c003040c042241c00120140a00c10300341d0355494821858043d03012265405c2620004558030304c806040981e141d203003680e00707490144000d6540c10f0a0308040c404c0b1541c0501c01040034181e01c81c3c0c24200001000700816403e00b03164001c8042c2e001032500d50180020001c004040c5072 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 474574181 1250 474572931 474572933
    0xb0618041109010b03060604030b180307050607030e01020a0516020f04020415110c01020c0d05210703031b1d181513060605030402010c11091008070902030c0301090506130903050403 80
    0x506410307000690a03031001c100f84059590347c0c0044400b100c2e0711035500310240d030742c0001d9202138446440308071205000026883c400c00c10003182e06031140d50252070412941040c05540c60803030040020310000300310100005c8400c1e9000480300c0101e030b4401400e035110740414402140681e0066803000b00c4101c45d50310340c085c610360013124400c01c1030340800041c040782c02c510b00002e41d1160141c2d0b840340103d070180c03a08000d118050041200030202c0c03468038040e00c40344c816503000d0381e0302c840030035800649458a281110305903140041402c02c041c2d964120103250102d00081d003a8254150380f680300900b01001801031001c0e9000504c20040c074040c01c400081498103000151100d4207a82d4440d9180c01c100f405540d4000060700e820540a1070034810351021850700501c2540344140c40c0e07a00000074404c01c0381c000c1c610900c0728107030b404941c161411039030380b2014001a07005c256002d84400c072050005110180150f48440d03070180000b022249820648400c0c5412200c0c40101600050f00000d410701c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474575431 1250 474574181 474574189
    0x50d0815220f0b0904060c0528120504030e090c130f031b03050304090209041d060117010b0105040b0a1803080301031b060c03030e010b1206040501270b06180411 71
    0x2146840e0480d41400302c543c03880d00044400000400042800ba62070b0920455a4451401da40004035030b50403001c0a480385024595003071848540c241d0008101e480318802c1c0000a0040c2805654140ca81203c1c1140b828204590088014845124150180401c1107500d501403c180c008000801c96655100e0640c02c0090019912504546001c00b410208100040002003240c0071981035a10060f1030703001c0321002030090f000c0d410305880300e809100e65031201c8503c0490a14120703190042041c183e024100e081e1070036101c10303814007408102c050008001e05400b2100a02000001386046002c0d500e00440560940415070070039200d070070000c00140108540100200010302c203200104030f8413854080c0c02440081859001000c06468a42e9003014200940005c45111030080002252070020001c0c00d5680c07004031410350f115070920860041c0188005442c024003414210051260701003912a00290303070b8050125a0021205206131b4080003040201502503072080d15240018841c00b4100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 474576681 1250 474575431 474575441
    0x509010e030906120a0b0d0b0a052401050913050705130503030906032a0c161401170705090603040606140109180903111902150403050d081522 63
    0x240d0a10360040044a8190351590182d45118043c242c2040c0f5070f96413451500081c0c00c208944130380000c0583c6900040000d409841403050404072000c000c182d0340ea46c282c600d50248000401400080003013510440d5118400804421001516074078018003400c18500482d07108950000c00158003041c00741203a507001220b0401060101c006600305802d0034005019484040c000e810241c1e071781007548500d044100d00d80b40700007004000c07a58903419000941900c402e01840748004200e40e10b040440c900c003880d103107140b03c5101a954038610400c800c09403c161003014001c00b06001050007400f1060340c80300000c5210b41d214030360103d0b40c20702c0c00070303400108131080c0b200506102e014103040c000082000144044984502383c08240084641020b494502110440c04424000c4139001c01c64641c0c030444c2014541e1003030b01d031101d00305905901d04e01140600d000c0282160041c4640c880e003c1d01c903400c01500281000d0280515000d1140000d040040c0940031b003107514240c0080c3d02030301420f4403407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 474577931 1250 474576681 474576701
    0x270a060305010602030405120109050a0605071403010806011e0f0b1e161b0302060301090603020a0515030a09140a0507080c150702040203070c0b0a140114010806010f21050901 77
    0x140110b50401002945a018a01416009130319101c03851204000941040006a41150a5410302d1901c1d0400b90040c040c1180d00e0800314100ca1071103a411342004d001c9034125003810010b000180d003881c0200c81b498880c0341d00318206810701c030408031341101240c2d4900020600072407030641c0c03032000ca51043c204459400070b45100e030b441400700700f0b10708000150381c0710070903841800221000d0341108061040c440941020b90452808000407400b48034580c0800282c074003c64501c1d002e01c0ea03c0d0104003503d0403c21724100404030600100d0402101d9802603043d05103d51400c9855051008603a864001d1694050714194040d07441080f42100a03c10b001103000256600c50401d100e060488140380b18500000703004560000000300d9061180c10380b400301c83d40c00a541a0203007001c1c0e008502801e0a8182d04201c1c040b4000000340307044450304176813140b43c03040c0c41d001d801d41c1c0c034080107448a00c0e6229416043c008030545101c0b103001d280308510440c10040d4000140da040c2150314a0842d400c07045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 474579181 1250 474577931 474577937
    0x140d0212060a030b0f061f02010b1806100e040f141501020106081e0708060907030506060603040c053708011506020601030b090f0a08090102060609150103020f270a06 73
    0xb2081c408a1450920f05078001c00481c01030003543ca4410120300d03c1c101a5421003201c0405100340c3c1191641074026005188040703031344100c1803021a4042c02a14001c1d259035511540500c0182c900700d0003980f08100c030f034400a000090b60010040001c0035690110340030080019444200200c20003103029481d44080c3c28402000b2140c200b40300c2e50340e05d040b0514080ca00070030701c0300d00005580c4208402e1001d840c1e00e405891550401100c00342d503c0666000071603482c0100000103619040a00507244196000020403900e03030b180405020841c45c48100a4540011888449684920100c08a0241c0c030000304021105482c0c400c070b044c01c40d41c00e00700028100800311000c0140360b81c005041410749030401c56038516a10340b64042c615111501e035000b907403030082c0f800980c180b01119000d0461120b080c0c00f5500d550f03030703107500304042c01c0310484032440004042c14107626994400d90140c0f01c4410303000086403070207002840c4a580c0d00400312400409003581400d1100380e00b4607244120081c5103030b00b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 474580431 1250 474579181 474579199
    0x9120f03180509071d0a0b0a080c0306030c13090b0c0405100309050d0f020a0b0703060e150307090c090b040806011401020613030c021f0914120c06070201140d021206 73
    0x210006940000141680e010400508025030340342c017400e14884905c0d000104940d0f212940e81d80014010b070401320071000420002d400040030403603000210383c81844002c0c0030304030b0601c140d82002001c1903000403c4580c5a5500b00000005100c02c1c0124020485602d4484e101c629041c200440e130071950029804160170689036030001640001d15041518003400c2400e02c04d0151a01249084050340000d44040b00e4102401102038065120b502070351800301d0003806c1556002e020140c044403103000903070035502000080100c80110b5200b641c4a400c585040c089080d030321400240c8541081e0030403002030300050f0042110340da8850703ca00810000b80040d01281c944240031060000c5684000303401d021150447c4000c42d61244005071001400c0c1c080102d00082c0544000c00d103040d64004d0003140440b04494034007a25104842a00c01c8030860000c05680e145a824080c05030401c00049041c000307565509095044110090040700300f030f01c4001a101d0440c12a641c07629071000c1d000c80c1c009d076402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 474581681 1250 474580431 474580439
    0x30c06241e0409050706030504050d090302010210050c040902071a0a0b090c0703170f0603071a18040e010c050d0f021206060a0c0c1203120608190309120f0318 70
    0x1000050700c40e44001440c44020740c454012501400d090b840041c001d00501c640401e40c0c54040e440707640624003400843d014460145c0f0140c41062140c0400780c050b80c001001c1c40c030000402d401050f800000c0080c06c0341055610003041043e6040900100c850340f02c3c0e00c00ba09443d681030b002c42503200e200c110701403080c5000903010406090002d0305a4000960000c0c4020616018201110344402c4000c20307103110f817030605d042118115081d00c0b214442c4c0200078000441046a064002000381c139800b01c0391902e0a142c1060114110b103078419030300540c807110141d42080c804e106d200d0f030700075554854a81c2c4407c80349824003190301036210401d01a1050180d10202c107002010554080c80540302103941d0343c0c80107429200c107801070344018400001d4403404034040c80d400718030f00b101078802d446682022900600100c217a84280c010110707180d02c0480d030090001e03101c9c2941c5580c0d50003414142c0c00951101820601c90901080503506ca0024086400425a00043c240c3c00c414115030360444003420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 474582931 1250 474581681 474581689
    0xc140c0a06050a0302040503030304030305040605090d021f0b06030f010e0f070f08040206090409061e050f0a180501050a0605011b0f11190f0e0c120c0d020705030c0624 74
    0x103008072000c000001c40ea1102e01d5009074120380151600500303c07178480c6490701c0c00501601084408550030760400000c9401d0000c00210702e400380c0c0c800e4014284154018030081007445007101c101c0c404507128540c03507007103440305801180145c1090709080c8656040c01c89661007120040c10582c04140072004100c400b5a01020160156000740f1703040c580c03900e81d07000103056401812a0070f640a490504107204110080e80842c012000c01c01304145030041840c480c00c01c880b000c0b62030031040c070500d000003455001e02c0d40c01460b805582050040541c0c070300e511401e007115821948107500fa6038900c000e101941c2c00c00e0f1140064100d100510100381d80503500c041c0d5060f81002c00411200d26042d403400705541719000d000c00b40303644040004034269591340380c403014650f138421032200750b02c0c01c800f0414107540d000496000105150742503007640c84050f1240100e60143d40c00048096091140c080010424001071440800140c000d14040c10321180d8070148a0842e07440c841030810a003494411a11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 474584181 1250 474582931 474582949
    0x907080a06050c1c06150504062109050f0105040b100b1b030906070602040911030c12091606030c080f090d031a0901080703110306070c0210030b0306070c140c 70
    0x544070901080c180ca40c1401c80f81140034108440f00101c0050504411400040c1d2001d42150040110070401000010050340d41c2e01c61406a00e002541915618403840c01482a80c0040c0b81c0c1100300051101c035503200d0714100985207a0500141c0d440300d0a200c1440784030780710290402c0d200c10402107618588099004039106804d09603030440c0ac00b442e4440c040b0018400d44a104002a1190743d80e540c1c239141c000300a502a00412809524001001072980c1d88201070300d20800c1000d8406184c44554000c4074000c1e01c00400011040c07050760f40050700d6180c0300c00c0820040185403000308014001c440003426501d8010302d0041070034203210803c1410800012091b22400e9107040c002000c4485e07481010b08064400000c60f0810a10300c0006400c00e00084c0c0541101c2c043d481f09115200182d0400d6110041600c03860300140400780c6007000341c90f08540c003403584040c5080000e1210701500110741420011107840307002c5014a14502c050141982e1004031000400002d402250070b450300081d1300314 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 474585431 1250 474584181 474584183
    0x506010b191107031b0303110606010c14240a0b040b010210091b170f0102090607031d03120c0f071d0712110a140a090603050c130e040b0907080a 64
    0xc4403000c880c848003080c04903e02858000350001e032948120004401d01500c2032100718001420b02c0e5412541c2c0c100411103a0107544141d42d041400d2850b030320fa0540020304d07001d4450032400ba884440d950240702011728060b885420f642028940780c0003940b801114401e41005000b9400d0100d180710503a408602070001550190000500401364108004001c02d009110b240c001801200811010202004c100358180640205c640c001745c500c003041d090307000301442a90024000d00c80040040c0c01000f41d0100084141d039100710b0130440c000000d103000c040c1846051205800101240c4040f004c1c41036218000c81c12004007401c1e0f141104110701c03e0502001d45100c520407102158005119982c075a1361080008005d000740300c035199500d80658030081e00940030074041d4540009488075201a240c0804ca01d40320100c102c1d00e02502a0050700c0e0007041c000c10765200704541104941c82800135409882c060382954220300d401d103816071940d103010b00130900a03400041c00b008a001d000030790006007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 474586681 1250 474585431 474585437
    0x3060c020a020402030a090b010501110a0305181306060e1207050d02030c0603070e0f041a04050c04170303040620070807020307120b0609150a03080f040308030408070506010b19 78
    0x2488100104a081021a0704020340c400d0000003131260007406500328078a1503015a8003405140d9840300155078400ca02c03031111030325820002800022900440142490480c1e01041c009085070717000001d0b80c54041c061a481d1000e54448050002c2c561007001c01c0d20b20034041d211501c018240b01c2031230399203004c680701c0c4070310034451030100344110348062040214420018142d55140d081c0300702e01404040c0b81c116401e02070350502e918040717540742c54042c040b400c10210041500e56500042400064a0b00800c1d01440c940c04010009a0080b80303640c120305c815051001c1c54481c01d01345818000c1d12042d141004002107055001500c40d04020122904968401282541c50b03110348042410304203154801008241142021418840d0410314644203201c1155068415a02c0c4d80445d501d805d105c00315940c010115482c00d00001c0c116a00a04424440758085d0b400d0170b6880c1c2d00e007602540202c400b21415000440d5070300400108101460141112201107800c001040c42e40728140850241d1030020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 474587931 1250 474586681 474586691
    0x36060f110c03280209010321080708060909070b0309032508031317131706220201050403060c09030512121308190302090f09012904180b18060a0306 65
    0x40120034219401e400e540c05417251105682d0b07801c3c180418503100300c004014994089a42c10014829000d00d44900c9082e00c4480b03043d220a02882445400201200c1241c800c001000c11011003190142d4414005440250f6803a58044550008940d1040f440300c40c28104101c000d001a4030b0000b6254403001d0304502c040900d4080c102500700e802e0800c83d104115000188078051ba9030004c1003501910b00030104c014000b440304c0c2100d03554200c00ca81101c2d94000e2002e41d681200001081c001340e2500507d0010704141d26901d62504640c3c0151412021130302e48ac004004203e010320101840700d07405885c450074010040410300301c9000050040c4d41c4403180313180d51070420040b02c09075486482e591407003038240311804102400035841100440c0c0314200040c0f0084107890704480d09416640309850001502c401305442c0301d030007100035202078686402800042038040d4001c120010b6128902c030003207072000c40c06040c031900385010313031840c41256a9401085101d0721070126620480b5801480012 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 474589181 1250 474587931 474587983
    0x80f032a16140f06211f090507020708070312080402010504090f0b281503022b0c0306051e01092d0503010204050136060f110c03 57
    0x1080804041c4a1600e0403000311000c5841450480c01c8540c90005a43c44891103c8960400c01d150207041c03030110003080d080c15080303003081d4040c10082e080701840c8020148a401a80000100c8166800c9845440d0303941c0104103486030704020030700c0213101c3e20000c1d1038100e0464540400d00943c3c42404028060048081402c5900c00c00c103c0c0e0042c03200200400030044441202409061099491442600c1140a030f001e54420b010891881843c2200d0070760207507143c8940409040008240d66043c1a82481492003000c4041000040115401e42d0b9109040a40001400b140c054200e080109031070326209101c00e80317591502040c0f00404280d1960280c042c3c07001241d40c403a20350420341d10059000181d081044807412240e000b40e49a9084001168640d000e1508030301491246a000588030460100c010301102d029012520a00c3d540d1826001040111001e0303519641c0a00300251324610300d032004039808100321719070f81c01d05409402c0c2140040006a9650540905809455503d410440b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 474590431 1250 474589181 474589183
    0x40b0d0f1a0628050a030516050102010b01050a0e121903030f0203060a050f040f060807060e03061003080313080f0d150e27070603020702010206090106030b1302010c060f0204080f032a 81
    0x4004c05000b80190344103600c1e484c005880b164083c0c900c2d00e00e041c80103400b081560041c000e1015001c03040c0e440a0a010100d0300c200c0300202c861201d90341003522170b42e403281d200500303120010980650303070189002e4841c18540101110781220090b9259881803091000b00d988641c0420101c4108450392060503401d840094010490034005c40c222034940240041c1320349000c00c04404035402c6448402414002c0707002c0c95100d110880703d0309031510070401c040c00002c1304107002d1604100100e0b0300c07294244e02503441030000e600405650303600400204600b00140b00c14000c120301e010b100307040003203030720300e400342e144c60114000d0002c020050b400303915084884020075020304003540171000c4585095036200090002d5104080680c0140958800076466001c140183d20850360301203030450035540d5444205030030a800c2c1d40224104440408480041140ea00814980c01d007680303001a507843c508940f05244c2044030701c1f0222540c10622007420380448030741d000510201c03441d40c0500c08001c896002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 474591681 1250 474590431 474590509
    0x3010f031712181002040e070810090501080a0b130330050f0601030c0807020c2e11070807031a130210020a0b0c09060711040b0d0f1a06 60
    0x1c00e4201140e58100030300448000031070f038209040b1505541104a219000e04103902c9103000e102468884030300801d110504c00c0240340c0d44981840e80300302000b82c5400500d010741e1000c1e8460f6102e070340521000d10600408007141034111240e50f0401030442c27070640d8090b04407041c844035284001c9624001d2100c644107002d0f010040c1c4d12104041106242c00b0404800d03421040d1041400203192400224003107002e840654050f0105030010444100d40d4403c10200c0c1d00031100382450412000d911052280794110a4071100304d064980d03285261102001c1c40c0351008070b0380103558aa111030000c001140d5407100c103d08000b2240980100d6039100700620340c1007010540002d411208640f500a18507901151407203c40d0301c600c000140507110342120360000c0c050720840c00d600000802c41c20700020600d40070001454400383c8041508503541c00010f003c825826400d0783e200e46658004010041648038980c0c40c812140c80088103410f29002058428002c10180902034910010b142c030320712001000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 474592931 1250 474591681 474591697
    0xc0c0f11030a06061508070918060b04080c01021c140c01060f030503070b01150f050d0609051815040804181107030905031504021e0f0409030519030203010f0317 71
    0x1c681d034442280c5405401000c1d00c0c4203800e03461260090126900f441b40000030b010700e6203076941c80d00c09402c011090400750340b5030090170f00c0150342e504001003811480c2d0192006000d03041c06010600c3c102000a030030940f099010303280f0078540382c41c0e221602d50801d05110620007101c510030346407030020000a0060205404c80c00c41c0340c0b41c1c10360000070080b0000051040510490750070320f03d640e0365a1060304103c00e180c0301c0f20101d120703003258025262044000c6c3c041c01a1644011450980c0d9100313100440300305540100d40007850021008121104001444903181e801070b03010b900340f44c903851714606c50181d80a640d005101d0b1442019a203081d03500500c404041000f6696500c802510b0081c141c0c00c4644600e0f80070380620403049046441c1e480d4007521842d0060280d2259a59803019100d134000164046035000059201c000c0c4661a0741c4500c0c03070b505100303071602a5210221f05201030705030b0070184074408040c010001888403040e0510040e00720303030740001494610500c0454040302070081e050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 474594181 1250 474592931 474592933
    0xb13050d0c030c091413030c0b0405060106020730020102070f0e15011b030302090a0b130812160308070507061a011d0f0f0102120c0601050307090c0c0f1103 69
    0x3010414000000307140012684241c40d2062001d541c4c100c4002500c013158410045d51414000080c11007011242011509100c1c0c64004281455650345a000705410341d41034076168002001804415010001040900740c250341c20042421240e0400d441d0340711002500f0442c4800d1030600c011a4000c00602c400703408141482c0b010591500180c488819007111022181494002d04503429400b8040c10401d86500014440034018039840170f40180d0f0100d4001c541003080f00800052001c42c2c0700107001e482120940620002d032501074920b140280b24116251303668410807000d54440d071902c61482905900d1304281009581e1040c1c2580d540c0940c65003e02b00d03d04104041004580e000c81b036090303151003601c510080188030300310105c003200c0d040b00f0b042d0440c0425500c1c40d124a0301c07402c2c4c241003250500c1110340b41c0d00705100d0816550000d41d4410560307481000140728902d01032008d500074000300340d400c100820716420001e100b80388841024010034400c0d400b800900652100080440368090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 474595431 1250 474594181 474594199
    0xc12170a03020c07050f030604061109040c0302180a060203030112150e10060b0405130203090304320105090607080a03110a020313140604060f030e10051815010b1305 73
    0x340c041d000e07501191410040b8002e013000801e20380790401c041404c504011f801403007540e031103030740c0c90000300007420300300d80700c01010301005406035a980144240d01c0c10b10340e00562100348030000740b80203000e0b41c48040d10411904c0814031400760b00000352411038007101e082509546890900e0180d0f03841d11071010050302c0c184462041d0300301c00014120034400401108111403643c0710004096401140100c580c0301f841c11036003040081c2c1f16005550080d080c523003500c0c80e15a4440320ba140085040f003000400e0340c021442c0070070362880c80384548d500390400c1c201140350101c000f0006c3d40710701c074404005005e102c000c1009007009119038000142a400140300c56511440004080c2d900d800640500c002c044a19002107140458009000322a98000d440c240c02d180c100041511541c40581800e001c0554a8525071001c40c0100203040100070446000034a80c104841e080c0f10001c3c0b00140700403654400c071048010407076480c1080e41101c6280031380303e07102c02070120050006e0300c9a5004d513074000040307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 474596681 1250 474595431 474595447
    0x305220f0e0403110f060c090105090406060e1c1a0901091502031906030c060e0319110f030606030a1e0515150a0803030406051806100509090a0c1217 66
    0x15441480c080c601a4a84180d40100204031301e80d68401c01009030040e41290022614507101d55015142d110b1050420074100710748840840e0031202643c1c0907200140c0f11688150070790606081d09011a020005060380312016600c5404000c5031100c0d000303040c1e0000c20000f030001c0c2d00a40c00a00440ea001e0a2200c804890001c1f200194005440b80040e40c036884462603100309140c0f00b0f40c070881c0e07800a51040364601d031217400d030b034000030750003481d82c050080e0501070360030751080c0c40800035941c40341d924254100000030504c505902e03100400340c080d07030010342880340c241e40001c0d03005101c1d40d00c030745c100155240500b2103800e000c8019400516900c518424100401111514148200d004080100c3c0404800080205003900c512548000740c000b0404680411003603000030b5401004204c950388140400000d1320326099084400000760809076405002614200740c4907504001c0340401000c1c4444c003910307000050800362181c0140e04160011a10400000085045858101c1403205032aa006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 474597931 1250 474596681 474596699
    0x140f0103170c0727020c1006060c020d0b070509031c030b01030227120a06141f030b07140d020a03050132210a0b0702031305010c020415140a080304030305220f 70
    0x4d00000007d854105080410600d201d42d000380b41d030f00d0b00200080606407142d180c445984501628600402100300802c01c80e5490402c0540301403071054004070804000d1a500034110b0b080c11301c0860400d80104951741d8a00c01c43e503e00f844e22010304840305541c4440e00002541c00c0150b034025101c40c0602c580c0d5200380802688424031003090341421350106d43d00d5503802105002052101a61942da20a00303002143c1d400d516113500000604000c10001e06a20384074102d80c100c010186c80789031b000604452580c2c1d1501174140107100e04482c82d841c2140e11000320302880070280104480a0450b03c3c40d04080c0d442c03002040e003001d40c1000503049801d480e0411070720350703425100c01d0b10006840004981524400400c4840d521618104221554144401160b280f00c01580aaa00c66121031080204107a42488071b40246401600140041c134048240443c082060740301c120590018801000800e030840c00310707800ba8060b02054415018015a966064015a00011007032412080c0200341101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 474599181 1250 474597931 474597943
    0xa0c0201140c09031006060f080a0905060a0207060b0405040201270e01032d05030405090403021e0d03063213090b010320150c01140f0103170c0727020c 67
    0xa0513816507801c0e000810503c0c050380c0c0030388107200018100780090703130b030a0b441041590b80220383c070b1102054a9030640c031031600d03209041d0b9501e0061b030340c005011003c001080c0701c0e60305c061609880521461401ea00060711070503541e0046800c4040e00300d0f501a043c0329011283c40645013413901d28029503101e0804500c00c1d1002043c1568001d040c40b910650519082d4141130f109a1110085180c5030609041c014440e40c044c100f03c081d1700c5003c90b44c000004640012b5171132010380c44000c0035000c03106100201584d0080d84081d81c407408045504000c40f0104004100d090005c41c40c56558428000108006402d0440501c80f802e02d4082c90504204040c001281200e01035240d18050f9038920720040201032507001c24a03804001c0c3c1e2956062034880701e010740540124840000f41000b0780c2d40480c00b1a07001101d5503d80d40401200510400050024440480d1381c908580c50524044083c41c40e6624501e02800c45aa03c210000131360b110368402e614000d9007031909095490f52140514550340314 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 474600431 1250 474599181 474599197
    0x203090c041b0e0a0b07080706110d05070905060f03010e150d0c05011403060f0904020f0a06030519020c030d05130c12230c061803010507080f07030b0105030a0c0201140c 75
    0xc1c00f501400d0781d092903c03140c10000e86641800840c40c00d55140c3d1501015840742604544090722100c5422019107404040c240041c100080072460f45001d03940101b0441494000501c00c18040c0080c080c09541c2d00162819a5444a20110341e500d400100c00d4507003507000d403440d42c40410f0480004c00c2041c0e1030594822240c0a032903a030181c0c3d1026825180f180000c84140e904049040094506403614515858000f400a0601c0c0c195002800224003d04410f40000c80402e865000344512124650340e00c152008103500110305000d000c030310b665201c0c4101180d800701c0c1b0b40c580d800315615220410f5a040c4503580442800344d200d03030701c100d0300c000d00290610684020001c1324000081c40c01e0900b441da4030703081031009422114201b1040000e00c0d040001402e04900d50030999501035142441054002e14464607800014607100c0d2400f090700d440105a4400c25090903201110341c0d801100b80c1e03800c180c01a5010170b00d528000c00c00c80c01006814000361003207401200348584440c036100280411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 474601681 1250 474600431 474600437
    0xf09030a0503130f080303071d01030b1306180902182203030b0f0a0503060714041d040506090c010903030e010314010f060207090908070201050c1207110a080a11040203090c041b 78
    0x1103950345d41c4d15460b804210303410804210521741560318a403c0044450403035005050001c0c4031001140444e01649804130030408243e6a0350042c0032840c0e0200c1c080e12880c1928509000c40706480d80411051580c640f0111021610700c40400c000f8500030380050900800c040100b211443c00d82030050141c00d92246150142a1000c000303501400c040810030207071000600204819101d41c41c04a5442c0c00d17075400440b1415051002080d545c8100c100104100e44806c3d11102c241801e0500c28106074010f4040d004030341c0280750500407640c000e4808400c4a815080101c0062102c100580240890750304034a00d031602c4a00110b161040e1300400420340c1c002d03a007110485034441025100312103000801030200d00b000e1100000546c0709900410004801d6000d0f9100d100c0e034040310b0f1000e80c100b500101c8640341c5441414810382803600c44c0400400ca01c200404950205441c0e02c1c10b0012a1400306d0700403500040058050001002240380000c80500104041c0c1c400044042450706200804000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 474602931 1250 474601681 474601709
    0x90d020a031a1b0910120603150b09070c0c0b03270105100609140d03051303061a1509010305150d11040c0f020d0c0c030f0f0c060203040b0f09030a050313 68
    0x20840f0003800d4500c040c80240c40706607180c0945406442016410328041310154583c400440020b401503101032400c40c84080118861142004108501500500b001c04200c0200042c0340821640e0203001c08a42000c3c514035034a4841c1050b040381c04070950382a411601d0002000340113144158895485100386a61100207942c07113180841d105440b5200b140c0a03004041e25100180ca0003413096045940300b42002c51074120f000c80d819000c454141c0c41660640c0d82c9101228509003080b240d421111b000300c6403c4d00440700d01000c00141d001d614001d504040d500c400041030110000310400d4412030040c0010944041494409104514400d01030301480c2007150101c0d0040c0650308640c008503054002d44140000c0c0d83e011104e1109a0106640506500c0300c00008609050902c01d40c80303004400c1d082d80142c0ba802d010007819003940c080030840d07000300020007020460000b61000b2450f8014101e50700e021207400286130102840313015002c0d001c0015240c04406086100800b01c80744156007a003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 474604181 1250 474602931 474602971
    0xe0a03050303180f070311031011130b040e071b1b0519121712190b0d080a03020d0b130c020601060e010806040e10090302071811090d020a031a 63
    0x340381d50704907101c082c10758014501400003400d920344a9021f0754020b001c52742031402c0f100000d000d9a900c000e607a408007c0000c0c24910701e035900c44c0050040c20104c10850708d018a0720f14159100c1030028041c0c800c1140f04001d18040c4074100403440d180f1034000d62140d030b03000c1e000800100060054400d85204d800300030f03508040000e0411112084075400008c03101c2480040d11507541050210001250800b000c00011003402002d1149501a8200594004461131781207010011030700b00c01e800a12031071500210000085030703201101c0c0c5d10710040c0f40160301c401d80041802d006d41040c644440d0301808540c03641d405c1d01903560041914140950032580e480e66200004c2c0c0d001e03400e141a140c001040c10b400a00a81065084110764480c20340c1101c65000f07104403d01c049a0801800700c1c0103070010001007020300e8900c41d500c0256442540100403241301e103864680148a80c011960007503507018810300556030382d2400301c0021074001300c4080c00724a44c00d00b6850305481c211088000031404624441c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 474605431 1250 474604181 474604183
    0x50306281d04050714150a0903030e09090d11010b030a05030703081f030605041a15010206071803110301150f18020a0f080a0b150309060903030c0d0b010e0a0305030318 74
    0x20b4020358001d00039091301c1d4288500403010f450071044003034200f03e41d40c108040304070020005114549250340c07500f15180c15803600030903d41ca4108007501c2000c107001401110341d03000c00c466441040600b8600c1070703000c84d6080d0a001d0296200240d6142c001e00d40b201c0305200d070202c0200b00c01403080e699100180d80d62898200c0482807412600584018840c0a100080707183d8020b42e00071b401038161805189180c0344240902104481c0119120050440c4003500e507010058070381c00034142d08241d0500100385644066908161201400581ca131007603009190701c080d03020005a5452101084102d619882806514580f42c0b04ae1503540d10100001c14017403807603101390780326882d195403001d2800a0310304003100c280c40040c01071005031341e46150f4070784c20f55900c407406003040d071820061607201d290400501341030910003002c2d1042c9410400810038501300c80e108440342240300c0e034070014040014400480381c40a000d100c55400039042c46000c4148440040030b5031084084000e6000c103e03400009003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 474606681 1250 474605431 474605489
    0x1030606020607080c090d031d06030105180a0f1d0709050c0909090f100b0f0901030b1b19050d0c02010b01080604090512070308010617010e0705030628 67
    0x40401600000e010981c1513126004854200c000703841c40c00d00b0a10f01d50000f403145071074010b0450226646101180310180301c00003118101c0001c441007801d43d890407012400784071507a040b84096840344000618074010075444410a2402e5100810030b216068004c0c841c01500e00c800d84a80d4403600d20002581c081303500405100c2c0c54810000c90070048440c2c18481d581c0005000c0003500e000310403009090351380070428a40300c81c1400502003a80a0290140103106080c919103074018261000140007090250a1107908041018030703001c4540c5900300c401d0010300510303a022016203e102d8402c03680d16440400340540c0681c21500704401e002461b000c0c0d00700d41600c01c0e058089049240003540f140340540c400b0380c02c54083d05c1503074206100c52841150981c441c000071800f09800c200140241035000c1403052040d090320004d0905941000800c20381c0c101c004000b5800c00038000001000760715281d43c010301100707041c880101103141840d421340340110503000c3e09804040000080300007080c403d400f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 474607931 1250 474606681 474606689
    0x1030c0e010b07031d042322050712030c1709090c03060a0306020c0705031009110907080402040506010e090f071211040308160b0f090106231009090c0914010306 71
    0x161a1004960b40c50115038617204c01c4119401030342d5265021a000103110061041c02d146040c255503440c03c1e954000e610769203500801000c0c3c0340c604050b000140d0016000080d01d00005280501e25098a0115091007070068010550449a10304000d1904503d0161141c4d1104030342d2094942c2e01c0020b106001d000c00c4400302d6000c2d0f003c0d2002c201207242c5038000c100c5c083d03050307050f01c0545490310003181c501403035401020403032555420744609020f0040e007d06000c0d00d0031201c054003800e184000420010019101a01c01c5d66503401003800e0740c0c004c203891040c100d405451010b40d4640000500880c60b8115650008280480008541a0742c1842082c4201501008032070802d030640e102e42c030341c64100b402c08060150036182501d01240d09540e4032482884403030260782c040c2ca0080d5045095500c40da1080ca5151a030001020a01150307038012080ca080c19508034101644849003200d6000440c1d0181210358600f81c0c4940e08107501011b9001900d4095541e18020061791004404869051203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 474609181 1250 474607931 474607937
    0x1205070f0e01090f080303011409070f0e0f090f070f0f0f0c050304120c0303020f0109020a050603130212010e06010b2b090813060e01080f0106030b03030c010501030c0e010b0703 78
    0xd9031000840c01845035840510040c034104225035250a41030f83e00302510341002d050b40d030000c001001140720042e0b00c0c4034021402e680c100554142281c0c003403c4000140d13140024040c01e910000107a86401fa100586424000d10301001030a0007104050007040a444280c00540c114003a040c445d4000c00c1807447c6034685544500103041e080d102101c0c5003080c0c800072a611b0104010010f2200200e2003690007281c000c440c2c01d20700a20710701d03020f4501540b14000703112690514a046d00503036142c0750418121791043d2212a135030356030001072038822440301b1302c001d5000158255000d0800c405500403142c1d00c0c0d07207504440642e41c80da40039a0b0240106a04490701e000a410103030f801000824180b40c03042d41c2c400000c51068841d0b0396110780c0f60485102050301100ba12030800072541c0c058007007000b513002800e0005180c10018104041500140a0307081410f40300c00c00c202d40c0d0780f010011181040d42d040000c0282c1d50b100d240482d15084031340f080d40c040600708000451001c00c0103081303135040f07a8191 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 474610431 1250 474609181 474609197
    0xa03050309040b0105070c03080301050a08060c04121505190c0804122006040318061b021207051305090606090f0402091b070c05040608070501082403070305030406120507 75
    0x10701044094002400140d041150a0020200040304055a030000e140f1401034561250b04000034880354031425440400306030712000a205070340d42e10300120340c03d03642d40c1801011040d00a041101c55080c843e160002c0413483d140801a03140701c0403034910100c0300b85400c1800220100b40c0102d500345c4045d6000b501c502140200040682e00400c1181c20384040b50850f02c542c2a242e000d400e0a0610498055001c20b800711018404030101c404001c0c00340c1030078284005080c50a100c85441d001081000a0050f0664012000703030480400c00700d0010320005100050480c110702200b0080c10007641c51800500c03031400072800601c0c0c2074043c0361140c624901c0c400c02c19a51902080134214001d00300d200b404010044c13a1000c5006400103210150061110104c0d061420f418041203907001d40c00405241c2183c20b00b48a542e07400401d0300c1d0010300200b1110f4a42c00e804185295583e01407804903418401c1000002c200300d4040f01400480d00f094946c241d10744011039100050b26811100c401c00600e5038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 474611681 1250 474610431 474610447
    0x40f020c0309120c09010b0a020105010e0c070b09100c0203040302030d020c0d1104090816020f060a0c03270f081510062006010603240305030406110a0204140f060a030503 75
    0x43d8040e189492020b90884000c0038012011030b994440a1b0480090510300148140340301c0d40900a1a0040032050040d50300c51130a410492142e01403840e000380300c541d542002ca00c00040400002070204070300c440402c098005003101030f589a0007807004078007078050000354468050010400c01150a8090812000340036266940083d151047c5000d40e4003540c2c4501d40c0700410842c0c0c4c0130b0400058101a001c6a82800b4010050407148889a051140e031040280c03942080d88000c40510869060528590f241c02d00d0030414100503081203038a07561004103000080d414250202c1d1400c440405040d51842c080b40034000001040840d1040c000c030007070030800c00801c1c2c814025083c1d10b99407444c1e01d549000b0200845404e014081e400200001d0b2100d90741aa01d62849081032200c14a618070b150410b0f00d165105a224001c1d4407a00e82400a030b4105910403030418054041c9059008004110346190000554810001a52030007604040307600087c0803070a001640d03c007aa500b0000560402ca40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 474612931 1250 474611681 474611689
    0xf15050406050a0306030f03050c0f0d020c010c02040603140a0b07090602030901122d0c0e090a051b0c0607120e121602150705013905071203050105040f020c0309 71
    0x1c480003e00030141c4c0d503940000402c0c5c17525a0961420301c40e9940c6640c45c010030400d68500180794800100c160003d403640c142c0070740c0015004544030000c0c00c1100302d0602c9400041c00420f065480503004001c003440c0400c00000c04038040c19182d21580788402c0e641c844420444541a0030300810026038000c000145081d805107620f519516078256000c0360030502c1e07a00713541c03043c0031040750220500c4048030741c5000900c49002d14107070b12a061034a0b601d5031003824001240b82502a051100e81c035034400120f0243c82e0200c003216070f800c80003505070f070b03403051003103003107580d84604884110010399246250007060086015002040785050000d24070b104c10048503900c070380e01c002c40004001e0321407120440180c0791441200c03400c4c03510036080303501e07242e0b1800c0040c00e40e04000202006000003401e1244d01c0300d01111041010615803400c0b00c004643d0300000c1d41e061003020805400b004181180440c10756046e00310034140c0300301b65400e0145c400c00c4e1306540c061b07002d69800700a054105201c1c200307141c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 474614181 1250 474612931 474612937
    0x70210110c091902160203010501090207081804020c060f010503150103020d1416031b0501090f030f03020c0414060307060201271b0305030a090b0406050d0b040e010608070f1505040605 81
    0x80c44000e2402a0407054150000702c4e8040c5e102d251a00305c5641c020800d51500b07229407401844c45c804258a0400d10761794240c010311904030119002482c400018499480e540e0580e030224091744226026414001610b411007542403040c0c500c2171082e04251500c0ea50380081050403a903002c0c1207010603d040e40d031102d505c0d141044a43d42e2500c1149401c038005405407240e400111700880a40d1048031500024400040040c2c2000e4184030b42248100000c90300c07840d002d012280c100540d005080035a15080f810549034071000ca501a0034040403072020590740355501c0c0034240c03c400316003400e6681c402c16401d0755000c45401c28131100c50340f6580d150440198130f010f101c5100e17185102000c05000f0612404241ea0780003a07440d581b0200d0312924041d00035076084080d04040f0403480c01d0a1030842d0007000c52080401e6000b02c01d0302c0d940f0002c0c071511550000f08030b0744070303101c021700159031038001d61555008035106103810680d0745400002c1d0303044c11380e2000c2c1e150345c410761f9007a10f0b140c24144180c842c1e80c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 474615431 1250 474614181 474614191
    0x41a04120f03030b06190908010c021504050312181507051614061e0c09030a030f1107140f0607020a2d09231302040b0d0b040602070210110c09 63
    0xf649410a00029591340c000a1101084022a1031920009881d00030400901900103601c4e03030f80341911210919030000b8402e01006034840081116640d10b00e09581580101a03100a079480000140710418800300048256020030707000b00c0d0040203481c40030b999130480c180c4052000c42c1c01000089280c0703001041020600b13004150180b10311001e900d0700c17440c00b03008492110703208882e4250012206054007645070000c0340804c50509081160300060b882d5001c00c0c2d17004040c00030320010514440e0160703d0b0140400707001c6041c0c0e548695100c1100b8a01c0c50341c2d00400e0302c200d40c0c041d00054245003e500b034994181c1c000d81080c14242c14044540c01c02801100c039541c442000d902c02e81d403560b6680f02160050070000d50301141c1940b0f03290b80704c89202001c0d514061802d40e100e080094a600f40030300428071036011180030078915121804610f2404070048081c20484409003004140b16054004000b418800c0c0c41d503010350344c99880210b03050320620501520503049101a10740500e04201c0884d042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 474616681 1250 474615431 474615437
    0x60506040914060601030b0a060f0518030a053f07080c0a060b1009030b070c1103010608070e0c070f2d0b0415110f0c07050603010605041a04120f03 65
    0x1c020036880d0481c0b407030700725901c0d2460355104000b00501d659040c012820060703c10742d02c43e0181828000094600d4080b03d504034208840461506c015452207500e4010755035010b01640c00341d8116040c610349a401400c560020824541c00f0482c3c00e80d404070000c10540198407001d500344200003001c213500d034050b8900b42c900038010b026481e03140c42c082c8061903020b8403815002503a0494002400481040b03072032004103000030030100300b0100c0c4c0403250040c0c1c820020303e82241c000e00342d4071b04158000c4003262003a425600e8444013180c0d000c1d00040c41400c2c2c0b02c410705141e0b010707629440b00803868494104001d00902d403040d4000c00242680c11084c180e0308007040004040c03014200d01c0300000c0710700035058602c4441001070005203c40c0e442c0340003c0d80c00c030300010702104a0300d00e4081410721507041503929880000911240501017448070384050000100002d039030707594640c001051508130b409000c00c1110000790101e441450f100c11503007240c0a0b0480c100c0507170160344aa190102c4044c80c19018 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 474617931 1250 474616681 474616691
    0x270506090a030c08100f1404020d051218040e1902150408030a17062d06040306020c0601031502030712020903010f050702100c0804020307290d090b0705130306050604 73
    0x514012010f0080d250300402040748001c0b001420095030800c1c095118042d01c2e28035100e03180420b02d050700d60303c650140e407042c80c14801850b0191504102070780c000591780c0007003a202c2e60010346d031402d42d011401c100c07000d00c10a200f91903803680300c0c44961503001c010440c1d0b5000c400141044200d00c400320480825030b60400f40e0300d004c082d007180d12a41c944400590185502c111b031303841400d182a0052425103c80602602e51a28441d4090403450403100907440140711011554401e4200c9002d1680f1000c1076460b41c1791411007e644401c02e00042350301d8860344012044205441c0b090b81e120380380503920500c0c451070307490b989002075109988458040d500d41703d00080b100a1806030394050100c40d80100030264500140c00112445038045008022002051001580c1d00203112030580d40031f00300c0d40340c07041030389590403d545001c02071501d0002808504545807510543c0312040a50155182c02c5466640d0314089402d407244c030454a00c1b903502800c083c00851055880030f40c1c440406400099 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 474619181 1250 474617931 474617933
    0x3210315031608070504061d3c010302030d050c031207030204091506080c040f0b0904060f03030203070308070905030604120e03070b0705011a01080f06030106031202030703270506090a03 82
    0x1420742d890300081d600741c0c018003040265003030070f00c42c4034000c0281005a0003c1c03140c04089125011000d40041c074807100761400700e00d008001544480c0c0903031801d24203100b84141a905690712840912040e482800744001c6042c18900a4081b29030500d040d001451424082910090802501604010416600b40b00c00301e214500380c459054000d41000c1040100e40c90100018404440102841458881444100003019210f0640790a444180388003e0716040d0100100707000b48115800b00244c5c0b50a00800028150040000e01e000c034000c1d074500c0741554410364250355081061203502d426500000001d808100c03c2d6889440032003082c90840001c400020020f07203000e03440e03004242400d1000481c2420404240b045c5144007407125090fa01501050002802d103102c0285691440f6440c4400038031155401e50201c1c010310b0348030140c10308080300340d80e000707640e034100c4201200403030b109003002502000c2d030307151000700c9500d03514014140c5800c0c5014040650090303140075402c44cc0602001c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 474620431 1250 474619181 474619213
    0x60f200c0918060c0901050405040203060d050703030c050f07030b061c1202030a02010f050906040b09030f030112060e071a0a050c06090f12040b0405090601170a0b0321031503 77
    0xa030080b0124211612084a0070b10024205640502002c0c103048040000d0800c598211040d982240c400301c03801622035a940c1c0100715160114040103115000c1d080e400303c1096004110314000700d002d04d0489a450b8000d40001d42d591941e8003010704296140f000041c203502e8011078418100480600c0d09444e080e00ba40c90304155644800c9120140c2c1001c18021800703642441541c0f05180324480601860918140080c1c458101601c054140346031040080c0340000e04004480701000720760403141e520741e561103070032040200068045492070706150381410780e418000741e02e44c00d03110311542c0c82c07600203083c806032001607008100324401c1c050140403028841800b030000724070450084025000509800121a061480491950a102038180030501c0541080829174080e0340066804041c6900c4d18001a00d030440488640340d81d02404804009811040745c00030b00303205000360101c9107040c90107099980b40000c820214417081d001440011040f04c0c1c0f40308a400e4a030300c0642a40c003400030701c00c540c5c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 474621681 1250 474620431 474620449
    0x30818030a06051801050f0a0b0105041a030103060b030604020a090b0a0f031b1a03010501051b0115170a0f0b15060301080a0b010e0402060711060d0e07080601060f200c 74
    0x58944a0390703282000941d00c400d00b920008600010006c00591901d5040100e4011014100f0135407159a10102c00c1182d001e44200c40203012692102c5c0307040c3c0e80b5102034100c198000d0000f26101e909220445503a41130011b5458019613009203441c8527030742040050001060f40c0700e1000d5000c0e540740300000f408a603a10910000d18085c0325500044694010801c41c121040e900c540300c0d001001002c5000e0200e6002a030303040d150240382156071a0304661428407440070850b4840001d520f0101144800b5250240b040c0c21541c1910445081c0780070000341540303035101d0f08000380c6810540004035000802495155034800d841d800e5006045030303108042000b58200760410300c0303958004542c031001d00c5950b004160051000a110405518050780420000d004004000382058144184c5030b0309a03465006803200c1301c0880c40108041410412425500d0f605032140340d0341402080c00116456124a00b4000c0e1030b002a01c440741049070040c40c0d6495200510302e140c0f01402128a00c40c4c0d2565202c1c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 474622931 1250 474621681 474621683
    0x6020309150f070c05040c1806050d0f0615021c0203040605160804031401051605270618040e0d0c0807030908030307050309011802091b0c01140106021207020604030818030a 76
    0x400012904050920046983c7d806101c3c05000024520428030500c3c3c05042c0c05550360740c40d006454003d0502000041e01c03840c040402e080342454004100303141d1070140841d9940c1c03954200c4101c40c40c0e0003000490b00220420070700068100300003d020b00c41c01040106007140700c1170210b1216113001e440701402500315400807158080e0351070715005469001d0146541120741100d40507020040380402500e80d1040b03525414504030001110751644104013101d5098060203000140e0f900a54010307202d503014130540c0031340b10300e20300501c50346d0090001409680d42700840e25540b6458039240c03110809038000341c0c012020020700c0b0b08080b401c00320a001841c02500343e600d5054903410010030040c2515514113a81d2021821620700802607510004140c0d00000400d050000c500f0052001031541e11130104810215070070040c40128501c0d200203d24126809582075810002a48056400714450ba0002035448001440203101080030040107140881421580c0d0002c02c10701d801082c02c0042d601c41c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 474624181 1250 474622931 474622943
    0xa021606050901140c04060c0f1506060e04060602010b31090303050a060b09030c040c020a0804030c060e1f0e060403061a011b031d030a1505100f06020309150f07 71
    0x711307140c03c0340100070719800903801c03540706080c2401d103100108005000305014212600000da808d040c03124007030004010543c0440244000c540307501020f8807000c40c00000302c3c0180d1030000002440c80c8103119220400c0c0d00203000d030b8014411010281d2184840d28400d85009010240240c25101d81e849410318451298030041141c0c03400840e407400312240c562140f42d090314100400c940c0b0b0758005c80d0303081f943c450031500050072202a4508910b01078030050010814180040d020050204d0040860f085130000c0e664800904400402c0c40012845541d80904012104042880741d5004426210003400080c124078103140e42d940301d039002d0350003c4498200003a4095803800705035034885881e650803103a2030f0700d44c40c015031156001000c0d0f10b4066a5000b003140700071442441c55400707202c6001900d4104201c0700c12003000c001c8600013000250f0743d140082c5071100f000614101044070400481e03540e07401546c1070204220600015040281d21180d0702c0004102c0032102e582608040d11100303001704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 474625431 1250 474624181 474624191
    0x60302030106091b0305091c0503061f0206011205150703020a031b0e0d0204060510020d1e05040b03060301110c070620030306120309030a06140a050106080a021606050901 75
    0x80189402c441c21034115500850401020411039078003c9861020601140790009040d0b44000c410707030a05010906806004d810046080141d80d40f00c005540181400c403440814840c1c0031b510320b50b40094880c0d03d00c0258010300d00402c040220568240000e030301620682e10240e1300d0941000902000f12800d0740804c0e0301145031000c0c10f81c1481662020000300480708807003c070a0390058412107081c500f051140101c0030501c021900c030354101d0307402803402510b92007265014080107516504003e084000240c0c08d5000807200e88454002c0488400d07442c0c549274039060030252410203e03440144941d82540d210761041d421840084020040340840c0b0020b0100c05080c100b006002c4000400c0655000d10010104402590040304581d0404003c9809000403001003c030241103000349003a43e03915004104500060020a0700070400446010315419016500c03c01d0b1a0304844080c00b8480018030f451000501601e20b40d801400620450500031030b2000032540d4803020742e00d046aa000703075039441d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 474626681 1250 474625431 474625433
    0x14180a06120f110306040e0f0604030903050d020718020c0f0708160605040f1217030901090209060603190b01180f0f05121504021f0306140105070302120f1c0603 71
    0x240b02d0301d642e5218100c000d1149500164084209004c09044035201d165103203803614819400300b04c20400034a04034251002890b090a019042c04590300c415030b21806034481050440b4030100e5040c1c00d6540510071246842401c01841e0700942004404000c54032902201704520213080110308010b26103840106504c01d4160088090345196034018000d00105200501c1520f55456800c400c0e2440101c50790203044181c104414000c2c010309003044c030b6510002c00d104d021365040d0420380c0d02c0c60080e01d0214441d264131003486164482118500d400c56004040c400589025421101008c1014540614101844464055049003590004000c203002c00810080202e482407374000030030003140d0480c0c0100e03a0310101c0fa01d071410701c0c10748100184040c0015046564098940b001400c95218018407500c4034500500244540d008200080c00c84000701d4007150b00c210100c41e03031154140c0c0600541000318000c482701c1d4110150784000b107442808440c2d100790003517625100040443c00b01045032465 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 474627931 1250 474626681 474626717
    0x90f010606090302030a02090c0f0415090e01140904061b0c14030c031909030c060305150f150f0d1b090801052403010b030709090209010e040314180a06 67
    0x140d40d22100620589a00400159802081800600f6016990100b899880f41010310140c8543d4078540c010140c007003008145813002e0070030040d01c84c00b103407a46110152225080c4c160954240b0034140038000038411800c140c03d1503803180760400c0c0300d50b00129803000030108110508641541510000310f4440e000340a2040f504c10541c100c3c00d880026600d4901c18580c02902e0340b280c00d05008130751250310000101d9910480c0014015604041c003407110f00c1d110403009000c0c0500351070007800a000c0c079240c0015440c1c030304a444c49072540100b444013000c94100700009641c20014000544a409015400d00c1a44501428000001e50803440350f0701c1160300d802600d010900e030443c0c2a140e14090404c148100c0038440034440460020040d101c02c1004070009014103002e48045415008a0b20009010380c0c00750004498207101726444c1c403250f0380340c00e03c2d03001c1d180c01240c0c0038001424030070580b46d5002444001b040300301c6881c00741c0c039114501e0b01d010942c1040759500520005105400380300703032000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 474629181 1250 474627931 474627941
    0x1e081b0a09210b15011b05160902033301141c0204030c080313121e060b031009020901060c020d060e060f060d0308011413150303021504080f0d060905090f01 69
    0x840c6a804d02c14091024000810b55249100e11400442c61841b000c010b1000810040c5400f184002600b4602d40e00d4440e448080d4000b960201c4240c0284c036600e030f00b680d00d01503a19440c3d0b0403013100a40c401c4c00000044400380e05000180501c4c0c13000f004004076a241d41d021a411a00300e43c3d20150790b0701d10710b2525414507031880d0311200481c1c2051100c0e0900c280d00d2107021003220501c1c643e03d110794900e4109084451055490002c1d08400c17a07070078070200310554008914201046040c3c0c0d0301040d0360900700b015075441c40c0f0000d51028003100180002805807085442590002e824103000e018180d42c0e620844207007282071034207640040100105842c2124106500060a58948105250350307607000d0200e28040c000c1e1080f610342d0f100a05102d4503070000240d502d00f480c2d030f401d202c0f00000c0c50441070b10b0f102c80d01003900113008200c2011644800c01c0c641601840c0c3c011b03a0300e80b42000702400250542c01500703ca03a41103898103030010340003229018250045508402525507100c1c3c510035903084034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 474630431 1250 474629181 474629191
    0x80106150905031f0c0915030905012417011d010f06120503030411060f070c05030f01150b0a031503110a0905070c0308090a050d1e081b0a09210b 64
    0x103800200c02681c54013011028001e500104031000c00c4000302d03664181c0c1c1c07150041c1c102e080020641d01c2640c08290380741d04151341c050300900082191304069810801100d9942e20440d140201405042000440c903801e0480300d40202d400008130744400085d0b03001e03003860808207030380355030b4461381018060440c0d84600d03001081c06180090360b6107001d64800d40c41c0d002c020006041e1000ba030403908480d45500048a01c9005141211580c0e0081403519881d80c241034011903029103d988440c0e0b68002c2d05109124510f402c0540d2525014039240719060380360b0020725840c0805880325549210000c808240101031440b07610012101d201c800300740716042d481d035844500c040b801c2605000129820029040704181c05183c01010360b40c42c102500d01d001d0490b0b900400508c02c01801203000c03940485428444400b40814802405407184100c948000c1642c141c03444c548200700f8a5070398400b01c2d0043c03134000c0f414140b5100c0542d9441494000300300d040a0076580c0c0708106c400d40204040ba000c1c440d800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 474631681 1250 474630431 474630433
    0x801060f08010f09091a010801020d050109140f041401020d0c112a010c021002010209101715041b0917062a0d09050a02040b010305060906011808010615090503 70
    0x1e9031404002916030072003840343c894180d5a82081405001c002e000d0400100160ba035992003950b0358012560003503000004414050340b5100c00401c4000c0140604a40300400c81c2070710307100b6142c04554261200028004541142440401d07840c03001081c00035200b503004080c80000c0715040078002412210103401300d004039801c2404040706421075196114000000600d801b0051603481005807050001c5c100082d5008681e040840e5007181e054000340306040e0160f61680721060140360565201e80e0707800c507003400c1c1c46503900058050031162522084505000303002050020410329034075020021203100800040b4200701c14014001c800d250101800c200800800e01d600d0528814000c030034000c5241c5034902c0203040e212090a40c020705483e10b00b040c83c2c400b0080030505152850703880c1e0307065000f01d001d9804c0c0007108819600074426a80b003910b014000c031509603a210011110740070800308032803000e01c50142c081140502407103114040c3c06007446410a1540c0100054848103243d4000307031203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 474632931 1250 474631681 474631697
    0x9050c0a090506160b100801060b03010302042708180910030201080610080a02091f0203070b06090c0306010c02130e0a0510050c0f1e030c07110f030a02012601060801060f 75
    0x40301c49040c454402054020340491a552505104011070311407d5101030b000d903082507000b280d07586403000158102ca10884040014010f2408011042c200141d40446580e10050300c0d00040b400c408018000400000c040b80083d0801c203000413122a825035188403100c0725541c09004558100f2000e942192040310380505443c07010340b0040199500500342000c041d00450b50358070a40b18400704c29020300342d0f5481d02e90200d08042c8000d40d03a81091906941d82d100c0003000c94028200400700138014064804064034540e56800151040156010202e0708003074003501c50b20202c11584601380d2840d0700c14010f03004000280c1080e9140c207112182006c007261501c801d0121515580d03048402c500f10074880e00da281c0000050b858016440c0111224810760000208030380c10690400030f1200511030680840104144410b00c00c41c0c00120f00c0071501a40944185000356000b4ac0030211150800b207814428403410101040c0710120a0b13002a02085c40310006202c01500400280c07103c1740c662410f461 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 474634181 1250 474632931 474632947
    0x20703080732030d1505180a05010b04030c05040b15190806040b03061314030a03020406030c0305012105010207020d030c03021510090c022a270406110409050c0a090506 74
    0x1031244034504c1c030052101d03900d502c08100100c110803010001c010040c1040c0f682ca004c07042c6800c1403641110100841c43c6081d001003081110f040c203a40030b481e00050600701035410042400020000da150250744600000700d200480c40b6024024001400d088d200314034a1001141c002e0a00701c4084d080302c0c80f0b2070400404035003c1d1000602150300001002101c107030801c1c0b500b002c024482250750003a82c03074000029001c0c40c40350590001c1040300e90550701084510307100c44040341294028018440000c00305c1c1c007480d580f1107041c060740d48142c0c0100001442c0080c0c9900040d400703038514070110042070a028449050640602c080000b41103140c3c8000b51078603210054510f02066400b880340c04c2513032400d5982c601031003000040510007980039003806113400e030f11080e80c45904030025244166408002d007c01d002c40040c0c16503829094806030507070303500d40d0740d15240642600f4410884003c0140000a2101000d000d005d0055020000481c0d40c0d035201907005205020743e0300094011a001c1003020703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 474635431 1250 474634181 474634183
    0x100e0f1510020c150418020a120204091508010903140d2315060301060c1712040b011502010204230d02100c0b06060304111e0d03031a0306060a0b0a020703080732 71
    0x441306d40c070704400043e0741e0b0306580c2c0c080d1000c1e004000c04001c47d906c0401d002c0760310007543e8440742c42c4184401e01102e11544d43c0c50820700341c03a00b5440080000d01c0203010789440005031005004020700186001c00c000b10b403044294150200382d540d010b040402c074000c1c04142c1071a0007490b000150151000341c42c540c107003500034124404540c1d000700104071441c10031a011200030140c81111041014a1070a400e0904100003100030070b0284802e842c00100b01081d890b4014401c4400b1a440c0c81121003440c070111149042036810f40201a4201c0040440b050069030751400b00546081d039500d4000c1d140c0345c1802c0a07104103130021b0505000702d008000744000703d012241c00a84804c0d0440700e1406051004040c040c4900e4041001908407100705a040e0402d030300341e00101042c00c1841390507404550490109945c2d807005807841900a5800f00d070910940c49620010000c0702450300403107071410340c0c940e02d0404981c0807000a881c105625507944030031f0090900c2124420788101c02507481302050050741c3e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 474636681 1250 474635431 474635459
    0x804030f03031503080d0c0201020a09050f030115080307140705010c060e1c0e010806030105042f1e040e01060b180d0609030f08100e0f1510020c1504 66
    0x1400595031011020100340c402c0d080b4104444000c44502c6000e980c03071a01c0e00700c0e60801907070750510340d040c0814404068814801c2d900d86a030541e4901c40b80a203480240400d840512104540654940b208054422134040402c00104a001e0046a070b0b00d40a003003269401070200402c4240342c0065204010070780e8046904039810341c001400003011540e004000745400007a060041901112500b20850242c101104044041c02a25041e015a4070780e0100740c22203500311401080301060750b4000001240000d00d0f81000782840c1c003900010780030540090b03051300f04406040300c020100400b0b60581d00b0300d070160f0542e10404000130b200755410000007100d940995100d4183e00c203040390f6084800e5a5a8180445080c0c00c10b20801080115080050502d000801c9005c08142740d84080340328034501c0a0160101d980c40b11307800340d280d01e840c000510745042c00b03400c0600c0300d90750605544040d074610743c140d400b0240c150020041c001d1609c0a02a569500d40124007010009010030440c2400325091 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 474637931 1250 474636681 474636683
    0x21005040812091011041422050408040306060305070f08010b09010b0922050a0e0607020303130314030a09060b150715061205070509010e0c070b040309050607051005070c080403 78
    0x2d00c80081d0b03550583c0b0307441c104d40ea01c03606804601706140b02d080600e01100900c00c1e91515076243d520400381d50144082c3c0c6425800302e51035440a131280030450b0b401640000c0e0024420a4158581039030791300c2d0481558404d8000350f405412145080182001b04c0c482d61008040e07a5000b80141d46140c000074040040500c07954001080c00180f10815580300d07140c00302d9038121010005101c54100ca0f42c0b078001c082c22903500211600e000c405418158001038058498506507000794511303030f90b030301c60b40c00a5510b07010220140700c2108a079451006070f9202a52081000a600107540b0002c0c1c10a0419503484e05141d41c00f031071a44585d04003002c0030000321040e2940124404414003060a000c3d0000c20181d402688000300c8004450204000410008100d07034003111200c0c1079980705c0e01d83d11148902038900c0300e01075030104047c0b00000d644400c0240d0141c06810300019150b682c3d00424456840100101d03042d40180b00d21801c0c294441c40303003640120b5207107080c4000191315502e541d172038420740c08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 474639181 1250 474637931 474637957
    0x30c032c010f02040905090c03070b040b13150302030f22020103051b160b160503060d150e011d0a03080f09161512110d0b0d0209070e010210050408 65
    0x40c0c2600e48440940114141640e440401c6580c1c4e503a07480000f00030003003912103c3d11405140460340c511b150001d001c009503072038952203a20381841c020078030380550300c6181100d28210340060f00180c100711001108402c01d8036a14007699038075004501c040307540d400821003a5031019000824100c1314040c0c070145183c990a08002800c3c0e2140d01803905001302c1080e0302800301000040098006082203202c54120f840380080301090b4461241c1d12030320072010b622580010300300344000784151070503244203a1a14003034203407005801041d201d100c0940300c50f40da030080300340e450304194824840102111074141d01c050000e8100f2020f41d9400070110103000e003241038200ca10b103010801c600c0d000d0200c0d1140090300c81c221364030381390740d00c9903220900b2940c0800000308120301518084070b8840c5c02958100400340e0381c11450680c10050100c0100a0441166082070819a071440140c0741d82200d6800382040da1141444400c001000a2400307880081845801d03091500307010000310403170155000741404078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 474640287 1106 474639181 474639251
    0x31107060f0c0204020a03231608010b0a18080a050703060e19120e0a0b0d0e2b0507020d0c0f050319020d0c080f0d030c03 54
    0x7498440209850032040001407410b9030040105c0491414001894201c3c00141250300403a000510903528a4006100a602e400710b040e0409070694070706603003a076040c20721101a60055181000900a803111407000d415602d920501c00741c106d82d03044400d0300d001403c150b0759880f46403000b0348605107442260000040c001c100c0440000312426070780b00c0703030801c0c0d41c2c0e60740500b40280c00c05003048414240040c0566070600e2002c003c25424084984500c1e542c5102c10840b074149054450541c0038080d03c0074400700f40c25004c0d4150281c0b440000d40e0322810316081d101c5200e901c0000b5484070101e480d10040140410402e415141e00c03401d200202038840c0141559079000c1c28400800c1ca260340014801494007148008055104010241d051980c603058249400c0c080d5a51b01010340114102c6104964541724840d501e0322a403405002001001007542c900c14140c8255600e040865 = true := by decide +kernel

theorem cover : BRFrame.Cov 474460431 474640287 := by
  have h0 := BRFrame.cov_init 474460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 474460431 ≤ n) (h2 : n < 474640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
