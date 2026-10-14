-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3213
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:52.279975+00:00
-- url     : https://prove2.me/submissions/4b7d48be-2bb1-431b-8c5e-ea8e7212401e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 577697841 ≤ n < 577877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 577699091 1250 577697841 577697863
    0x8180319060615020a1b0801381e010e12011d0307020a06050d09051c0315030b01050f0112020c010501050a06020f0705060906040e01080c010305160c031b1202 70
    0x105004964880202c0e550f80404208a4801640704590b9000400c40030206c0d00d00b041040c010100190351100c0c081750a588100300301442c580000850b0600507810141c040c03103140c85030907100760441002400119000d40c20842540c1c600070084100c01e680c1e014580b440d0200300c000d0008136508400d030003402e0003000c450001d000d4110780c600c4d00380303c040300110440b42810342c02440400b40a0401100319135540003240c0320404e086d80c40d43c5000208408010380900540c0c5144210360540b80c04200405843ea48128600d10001240041c000076945038041415a07000b5140c2c1000b01680c01d00403a50b10300071700f0842c601d9501c0003808660140064000ca4141c801c251070700804c4035920b540c104d9884080c201d8501661704441c0c3c050180746484401003050b808020030140c10b0a440e100154070545e4281c1c403501c03141d03110348a542d00c5940c1600449900190000030341e4003004024a02a1043e194021300400b0050118a5012103105044170f00c600b1a801051000342690800c0000e0340d22000051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 577700341 1250 577699091 577699103
    0x203010f090516030302150403032a140405030c09042420090d030c050f01020a02030d060b09060d090827040e1612060617073008180319 60
    0x7010f5031803456602c1003400c0302c0e819402409020710302600c184460802400071410148ca645c80e110364450860384003007280304032005054607102c0704407002d0854a00c0040ea044039039000e00c000c100556000c50310158030300303003519021240d40ea5884c10911054038002c42111031040d80300c650682007007650100005c40e0000c0500000111000340701030a50041ca1515031303109400c0c416101c0000c3c8244510503026105808540c020b6080655071030998104044000041e4070109a2844a1106009480043c032007291400c1c90305220b480414030900c00e400d20b02e104507031070740888800c10001c00d08a0b0080107108280c00740d000c00c66100403d100300303d0740c6070f280300e2428820709200200340815119004105c3e6090081c803180f403e00707041d01122240038217859066454000042890f042c040c2192007110560280c000182004400018500c0c2061201c81c2d42030342001030410100081c1c100384c86560054105a2101002a0341a64007900300c41d580d9010f014141902d030420600c000809100c502c40d82c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 577701591 1250 577700341 577700353
    0x4091115070308060a0e0411041d03090f120d050a1b060207230304090b0402120a090209012702030408070210051e21090a0501090b060a08031c0b0d0203010f0905 71
    0x4000c5c852040e07018030049840b9101c00b14002440d00310340041c0486010300042102c7d0101c40084514100740550740280c0d0700009071043d01441e050a0040c5800012114450f40c8a02c9484084d43c4008140c4a45d052000c00600507556038041c030041840e10443d50700b90500c0003018a44003000c0d400a22089400c800441d25101038440c0c01107a01441c070088100841c100317450a100300002d0a583d90300310790010b500300080540303580c3c540589803282c0201d68005ca04200507205000340008164001303569000c10402601c00a01c86240881906113680000351702c90301c6a040500307643c82200d00003548001c03900194428035810030080d02c0b001d0003841c1c1e400607042c5245280d41c450701c9070ba0724801c409030740c2d842d4144141e1441c1e40819000301148080750340c4c404e00c913036850742111344248040c1d807040e41071800c02c0154a0440c40c1900a40310780300155080484001e6005010500c0b1140b600c2100d07161083d80e44a5198524440700e0660000e000340142004201e541005081c50141964140215 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 577702841 1250 577701591 577701601
    0x405120409060e060906130b0a0b0309010903020d020303131704360603050c040203040606122a050306073914010207030912020619390204091115070308 67
    0x5c054500c034550160512061221000c425001000d60f03400701a407220750100003107510300e00c80010790b01c84c1041ca000007491110906001c1e240c01e0460280504544c41003041264100f4948403a04c20310b40d0110b041e691991508110300a2806140c000700e038500c010110010207600100610310f1010128003842110b0030112401c5004c0d24080d0101515a9010244818483c00d05600a41c2d1003030049500080c0300d40c82d082c0000101e600c1d12001c3c0c0d48600b4811a00e502c80000c1c05100790342c40c0104002103d19864080402d4075040b00a01802c180490bc800002109900c3c802e80040b44000207554407141d2842c4e80080c2034007101d01d02c260f0f80f005010110300b40d0307031a0510031242d029070103446203244a403400e8a070884507201b0102c100c0c2c00420a03c03251660000c00044600c545c803030b0382c03515809821a14085411002030902800300000410920b09645100c2d0003807400c1d03160161404614400da5040540c01411800350813904106134100b071508294045014000f03191295440039a1501c0e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 577704091 1250 577702841 577702849
    0x130c02060708090c0a03110f1507030207090510090207060b090709030c0e010308090607080c07030b06090603010c0801090b0105040515041d01300510050a06080f0a08030405120409060e06 82
    0x1810740303017070b0000f54010040c00850f0907480c00201a24008101c542c450080b20081205511600020000ca510128207841010f80600800d0080d04c200300040003645441080b84044500d2807040d54070847c2c2c001010414422580c211101e030f03040c0076140b5040c83c24001d000500c0204030b44002c1e21111b58500001c503070800c1010710a8103e0b50070101c0c2d11b003056058810040c86c0d601090045a03800d0003041400f00c1e0010610141d4011401031002c440e00e450014240102441c0040800e0300c02d0345400d10800e070382e5802030b0640d41555201300340091780000a1005aa1a1240b90007255000c01c0f800d6900c84014a008000d0054a11111240486910403465000551340a00500c14034026124030240c2c0189024014001d01c05000d030302250740030440e1910b904115240c440c1403241034a1fa000c0154030800ca0107024010244440200345040e090b45065844586051000305403180002c041000d110042222190f49000486d800342e40300d549034106001400140301d6404400742c001d00090030382c98 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 577705341 1250 577704091 577704103
    0x60d06150e0303030f181507020d080703090b1519090b0f030a05061b120f07110a0c0e0a140906062e03050a061203030b181e06130c0206070809 63
    0x21041c0103200e2162515a40690481c07a03009a050080c0300303a103031400404845d000306034080c104913000b400158044035001400c480004205000b0315040203441d41c0015007425085620495080b10010003400200008502d803111c2054000c03e460159400316140352550301c03001c070601003114072007064550322003031640351088144080c0c85078120400143c11010000078501000b640503ca41d446c2100005080300c5126080c1c0e10580944499401c10440709d41001c4030303c1c0c03004ca06030010b0403402d10980d500841e40c00700c0e02501c030384d003101113000c07420f00d407150f8200c8503890f1900503500585252400b1021390f1000201c4542d0b2181c8504051005000414605c0d10305100c46000c0419540500d414140c02401c3c0180064940980ea4400050b070303810001c0b00280c160344295000b18540c010700c2c041002400f00401c0062160170f1f0b150a100c1c0c8045008607050290500004040d940e64070000002d00000c20540b004c0344c054105142c4411707855000ca1882d04c03595003a10b50440544900c1c2c1540e42e00c80c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 577706591 1250 577705341 577705351
    0x110a060e0d0c08030406020304030c060e01090203070b0309030a031128031802060d0203060a0503010c050a0314060d2004060b0301150915200304060c05101803030506060d06150e030303 81
    0xb01c804c00100c3c0100e003141d001941d000d4002c0c00c028814040c250b035504211020298000c0d0141d540310000f0046150070322400008103402e5200030304500317145003416282d02c00c1d00d1100c0d050582d903610401c80b5107078a50560701c4400403500d98a40f00d1050b150307010307103002007041c03400c000074944041c0b12405955105202150758014280300d060501c2008501e009600180891b40d10000050000465641c24082e041076074115640e02034680040d040c0c05070035159003840301c520251101040200588030b1210701d00303031540c00069400d0426480c0d05110580716480c50400d030031074102500804d03410794240c0114104c45459a8200d001038041d00e045078240d40300c2c05140c008001c00d44c0c40da04c92601c0b4100d02c1e40d41c05a09140020361180140e115851940b040c2e04c0a004504d89004000501900380900d244050401500303225144402e4100e400c110051500102415610404100280c8844c0f003900c00025031000200046603c0b11640040d0301104143c02c0700045003030400040c1418048142c90184c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 577707841 1250 577706591 577706603
    0x30126070302010509131d1b18100905010803091c0201080c1804021c0605031b130b031006030c12080d021b120315060a0816110a060e0d0c 61
    0x5030307086a004407016400054201d6004c40c0c801e9403030452903000d01c10201104607802c0100b6400a0f070b95611030804100c0302209041d03070711960020480e0f8541811000d900420701003580103039650f609080a841c643c581150784114546000459041d00000c010441140c0440e100b00c24000d981c4034401070720300c800d40000c0c009514103000c00c008081c480c1c0505101e910755800b5070002000b4901103001c9800c0342d02c506c0e01c00e03c810200c0040d030010911889000e44415400340415a0800d10f81c0c0304c40a8480341414003916690091a0000d1141d82c44800c1ca400010300b542c400c0d164480b10a03002e0405400241c4910310b000354001030031105070341e45c859400d03806661141802814200c0d01c00079008540c3e0b629520343d40c0d2500700c00304c401c11b01c40d540c001c4084e40d01d240d450307040c180c00030005030541d414005d000798000c002910711182c01c44489503102d45000d00100080213030540407201036080e500c0d600d4091050070210010000b081d000035501000170381c1152000d0382c0605044416181c00600980760f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 577709091 1250 577707841 577707853
    0x605040318141909020f0306090f13080c030d06030f031701060e01050c03190c060b030106180e0a0b09010c180b070b0408040506280c051c1e05030126 66
    0x105051490032800c2d84012584910383d00c0d5034503004c41d01642d2120780118100440001088407a00c1c0c03201f255a008010110b080c0c8251070405001c0b4448011050040c01c10900425200318000081049441038844103070188807035039813403910308000c0414000440108001501d4242403200c9054100d040340c40c280d80d0b080c4041c0550340123484030352122244025600042000030000da006020f500e40000700b59554400c0140e150400d507040301c102e4684944603905040b030400800c42100110041c507024601d0020700610381e083c00314034260003840c001313007950200402c0203071200c010744c0f21901001098486003145040c0003100e10801c2064010034001d4207040c0580300100d015290b44551091181c5545131070192580005220b640000800c540503c440e5801185007a03482c030b0481e061f075480303400c0407001e42c3d50941c2e82d16141d10302c0c840c2400301d001340720180c902000c0c0b1070386480d0036405030590191140b011440c4018841e5000b40101e0f130328040e90f00c2c04054034240098800100800748800303002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 577710341 1250 577709091 577709129
    0x90209060f010201020705030c1623090c0d060b090406050a0f120c0e13121701031104060b0f090a050a231f18061b0b070c050a0605040318 61
    0x244840c1501c4440741150740c06e014000001d0010001001044040d03001040780071454079004150700019003040300802e4014598110208445c418500d03503250454014a00f641c50201d41c0081d400303104584080ca904040c000101b803049000100361048007940e00303100241d19071044c08113120092044180814801a08103c004001580c10306002e106842d503000040d80da43d601e02d403200303040d129051031250704400c0c4401c101a0380c0765259011a1424403c09107403120a00c036900050520015000d111001c1207048075954550081d405080764480b041c2d00c4040f0604075514070381207040c00d1030040b90018000714075880d00441241c1203d27041c0c00c00150303101004051681d003c0312007606c035800500c0081e4000007428642120380428003d50b4840c030a007104000c4d08140d10395594032000c140300124004214070140e44c003071001c800750044450755a9484041080380c40c10304035500a03200c6d000303001009040280e17035088680224081d42d100ca0340a84880307040e4102803002d10511910b5544488205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 577711591 1250 577710341 577710349
    0xf0b070302070e090304050405010f0b070f0201110a1b050102030306090c070c0f03030c06110f0f0f0d050103080304050111090904030c02030f060c13080a0c050d080408031308010c0309020906 84
    0x42268403901c1990481a903075400c810302510242c4074543d540d00301107003d009600300382c4034281c01400c160356010049441d2510743c4003584500c03000034114010115640c429640100c2c0041c144199103011122071013806d08222450703110b21100d1011041d0400000076680d88000103485c0a000014031001240d140c20b030140d00541e1081c0070469014004030000115007001c000e0b240011b500940303800d08401018605403044901030342e2200c10079481407050840e04600c0c841500d200400109030380780c1d141c600b04141040ba0040c0316080021508100c0040200030b041406540903a00c220024044001025000d0b4220701402c0c2c080c0c0c0d00b150302100000e010038418a207922600b4000b505a404002100103804d04202040320000f0090100050394803800b501c07108050008d00c03d40000d4440d1225955640045c0006d41c45020701c0388010490140030b0101e4181110000d001d040100c940d207042011962503c1401c51240e0540b55291107200c40c0762501901610803c1940100a1450382e03030b0f00070402c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 577712841 1250 577711591 577711597
    0x5180915040f0b0a24030b1314120c0706080c09040506120d0305070e090f070311040b040801050f061801060f0c050f010e0f160b0703170f060f0a0f0b 66
    0xc1d1422071182d41d40d440412200700c2e02d2030040c0f140c0c0e000401c01c0d4004144461280c05094114540654000b80400c08200041c810a8220a10062140040300c150400c151040780d1501642d54502540103a4150414068001d21011072020305a4408694651080e6420242100d50740d040d45800c20901c061454140d00695001100510000c01c81c0d50802c400b61400c4a8015408086940d80f4180301c0c10f80c0d0000c0020340c210300102c0340b01c00c00b4a00341419050030724000e090722051503120480035105081003410f42c1d01900000b011940c5650340e50503003a0280100b520084070300c44904012868030b043c10b2031400c5690079002c090441991034404c040f0382115500e1403d20800c5019000c0100040092103005401540c410000c1100344072800b041d42040c25558060280d54042000300c007101342041a520b085034132203111107444800368102030361000c0042000d0312484d00800104406044036012650080800b901c0d0160301141c840300b4002c2d48011030181c01c0790411401d00421512040d8002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 577714091 1250 577712841 577712843
    0x303010521060a09110411180123031006111506030712110306060609012a0c03060c080105010f1205150d0b04060c02060417131701060518091504 64
    0x148a90112031042075504065003a100d4a04013a00c4d40004401d0094990840c00f526400701d80800c03411707500804041041c803841188510311070142e6120281c07070303019458404190381c400c10020520b80d000ca0742c10401c0e500c103c60b4804941510040419a64030500e82105129031503402421001001e1402186500e4001c0c8442e030715204031140801c20048110040e40481e00c213045844544a9820405080c05801010f05003c0c160600c000d182e280e038030403000c0252408000d1004117803041d080550702079240f842005005180e00700c070000108003183c0d00c00034079121036584803056030b6201d0b80111074004400d000d550004400c80000544109158080f607001003a540d94400750544000125010350090f41301a590221148200024401103011381000034903e4400760441d0b29055450b250b022425665034000355102190300c0241e5010481160080d00d40b8407404018811452000b5001c0c00301c5010b158000c043c20f01200740800c407004081401003c02c4806400c110307030070702c818160680e00248 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 577715341 1250 577714091 577714129
    0x6060904020c100614030106050906012307050a0c080607090e0127090605190603050a0609110307030b18010e0c04090c030f03180803091e041401120605070f0203030105 74
    0x400c8010380d1200e04c80c0f8801059406000369094071a5410142111300ba0762210303009032021010044203a0b8030039041203078045e2040d402c03000440001c501c1e68040c000d1010007803561161140c0d107014090411100c504030350407113040b91181c1e51065011221099540725002c1a00b02030401403040d0101c40101c080780e030441c0440d24030b007051446014410350f1002c103020ba80b50f42c1d5503424460400e0580407254042c03203407901c0c2030083d540b940e030b2131365515060080e002d0300040c1d0741c5c49014100045071848181c1444014111044151203082c901c00100d420f5658041c86005420620344a5606000b030351885040c0c10040e0400d04003150130b10000d06561802180c600180030000300000301007040014a07203021395034104001d0b91654220804040980108450303030700a000da460713140e81e10550329a20084505105039043d950714049006003d1609070241c0e0000e07030800201e00e170111281d082c80a9030007201c1c1802252074082054800445446e580b0006030001c00040c00281001412030850b10b82e201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 577716591 1250 577715341 577715353
    0x70c170901170a02030109180c0504020a171005012304120c05120106060e0d080a2f010506210d0e0a0e070c030228260f030403090e06060904020c 64
    0x64881c2ca44080100d401c0d40d006540800140900d0000d880380c46c0614a4083c95154401815207400c00800f80f03a01c0741900c03881e00040c44a02280c0b00350b802400d07042c1007451200c481c1c24140e044c44c14000060240d54000b440060310710100221009440030108541054140780034103005180403803881d10102079454241d45040083c254461500c0740d0024102c4400004000b41040310003410300075081d0f0451b10420f12180500080f0f6440001c0302c42c0d8458900300350300c5001002c949404001c0e440c000e40f80812003501c258180c0724174107402c2240b041e00c04440c3c03402c14800100d06400d984550038002220f42d0301101c1c1d16208640600c120000b241c400918031300c1016030702c3c4c3e889020f0383d604a9121002403294490002016010085202e4210441078000000001c03d000c2c040c2072511410040e10700010308282c101c001520400f60480348010f81c0303001d942e80c1100c0103140b180c1da00030768007100001d02c03402c00003d80c1c6950b004244c1c00f500f40103101c40d03c0c0014410802000c0d40080f00401c489010314 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 577717841 1250 577716591 577716617
    0x804030b0405071a04060906050c0c040c020d021002030408070b0a1e060509060d05060712020c190311030313080a1106090705040e0f030703210c0512070c170901 71
    0x25940c003485548524024403000e400c156041440400700102071300f1005040c00140a038a8003d00250181e6030f076442c0c0b0903280c0340b140030242d141c100c400c49982d0700549008000030a05a000c80c840c190030485070200c840f42c0c9048a0308904911003210042c00044003032042d54002040ca2030300d142c00640c203600c0030801d115600b0b00d02c0c0e07000b640a4600b1500d5035503800100010709000e40060341c448030403146d0f48880c07181625640d407035540080880e81000302000560003401120b505403400c00f20480229400c01c40d0303c3e0240040450400000d40102d2603040d01c43c00c014000000f1288544854a140701d80c02e4101e80c4c40f24055045030b0300780400d208020907002d1050404000b103500c2042d042008004c110b10740014002140c42c5c420300301c0641c1e000004400700320307480001111809585450b1540b22a0010744080a0a01c0350300d816031022424508150606030340034020f082036800942c0004142d848520003500c007640d1240000b44010a40c024031905681d00c1c401070659043c0c181000074400303d030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 577719091 1250 577717841 577717853
    0x19080a0c06111201060e0a1707080105041115160f02060f0309011b0f140a17070302030a06090501060e090406060909050a0c080c0303120411040903021510051507080403 74
    0x205115542d060900418001103d440301c8203290300610b42c0d0300700350b4410b0003c540031940c0b1150314050b869040c00c0d00c281303c900e40710b8100096002446000001c02181c05c0c2440c214040780a80c00f45a4070408014808040c5100c0c40700c100c520820420090240d40040c0780d4800c90051035203401640d000b1024403140214040c8840118411203030000005183e20100100e4040080a15a504100b004440042074540e030004d030414504020862a01d48a4048640840f082c128000d048100d9003031047c103000f03100303405070061400b0b44030b03607102070104548a40c401001c586e0709106200c00640d54640c44074803418014203041d001401440040b0b00582c0b6014841c0665451a02c115407960024000e0400d00c0b00c01c1d40801c024140250150200d000b010002070364074081c2d14801071019500b600441d00700011030759a402c2d81200a00107000d0114541400307501c07072030b14841c0714000311421800207000c010360300b04010949000800e2900034030b510505201403031b0045001103400000412010001c100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 577720341 1250 577719091 577719101
    0x3004090207030c030f0905031218041b17040b0105060901020f01111305030d0f08090a06090b0618090d11101805100209011202030a1b020706030b0319080a0c06 70
    0x20280c0c85071007202915184c01000d0403171100d000402c010008105208558021030300b1116455464103c64a40b0b1925522042240b0100d08950303020713140441c0004134065000c2490541c4201742c840300d4599080e41c0344000003102c1101d0041450f00050014080e9280c00e00190404400c18070454904a411008080c00c551200b040d401c1e540b400031510a451920440c40c3e4405054294043d2900b1a02c800d405400054440980418443c1c04800039080545c2001000323030131904030009102c102c0e0b981c01d100c4032281c0140c62140c05007406122a202125840d46040d0103404410020f0500a170102d0085406443c0121092601d00030b9a004c0709225546000d411044815440035401c50f8100d880d0451500e444039020203002d500501151141d40e8200c1541149440c01074000742c0d4a513100b040c000000c04034030301c10020422006540a1a840c0d0004101c41502c3e601e40b02040800c0741001019170356081010385448518500103e0360015805030007402180c01c2d5404c0084407480581d039810b050b94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 577721591 1250 577720341 577720343
    0xc0702030d120c0306030f020d081c0219081302062b020c0d09140d020d050f010504020405090109021f030621060c14190509120106050906033004090207 67
    0x22195440104814154442c8500f010481c4c20208940d034031703690b0390324043d040e104400792180c5803103126201841503000440d98400440c1550030068020a0fa0100003034202105c0e40819501450280301d400c0e0048260502980d203c02e880040d0352500c4d400c1150030f500028084454540c0c85000070340d030741292601411802103481000d0307211001ca00c405841c003043e5094407000c10000381c00c2007040c4e160500c50801081400d0300d5440c90701c4060b001042c1c46400d5150300600603c55010702d50100c07178040d0f200d039005030f1088030140100c1d04e4040d0a20700340e5449981c083d5008034400c29103685100c00440708001d05440f801c012411741d55969803039041ca21641007412801c202c42c2c1140b001c209040c41101181d5080b402c1c10141016035101038512070081c140c5d4640044445000c0715000e601441c25945000b9004000190034101000707024007070603c900c42c51303001d00c410a0120b6040c4c40c010415900509402c0c0090040386400e000c01b0034490290003012001420401002c980d070161800185801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 577722841 1250 577721591 577721597
    0xf310f080c060a0818150a1505030f03090f0f041e060905010b0a0e03010902040609020405040f0614060a0c020306010608071b150f0b040501090c091d010e0c0702030d 73
    0x12890000340508220301103050368414841007061003205a08000c0503034000150300840100100e040301e00b180362940c40003404409403461002c021f065166038103d6084030040000106071281d647e01415584d0100c08800d0b4900e410071300c8009128107040180b411441002480440750844141c046011980581600075192408084003c0b404081b40941c1c0f00521104c00b04219941c501182d40040d8040e0820500801891206030441a6802d401c41218150020006c22034150340c1d151100095101c3e206c1d0310700440c141009034000303900d140b0882c2c00301c400d00390201c00b45d0550351082010340c0d880300304d105003480300f8100380d140540c4040203454042d000544a90500c1c0c00d00e14000350880c5044d030380f5200c46075000c0c61070100081540200e50603403142240c001c5800402e05e41140003405a4500d045c1d045072820000155003011600112282d14281d122826007540310f10030301a00c141100713031200500e01e1140040205030070b04400380780d201006030070541c1010456070000c0d080c155154840000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 577724091 1250 577722841 577722869
    0x22030b01080d020d0e0609042003090c06040f030305071514040201081501120c051e071718060304060b03010e0c010905060408060406050c0c07030602030118020f31 72
    0x20506080008960002c9a8002050715081d440e00c01041c0010740c0c00440e000701400700300612141c503940c000011038088031407200b40c298138416040540b604100e550002078030603402c07001102d0404000b110180c0781010300301c590b030a066803003c2c0c965070b00241003200c010311400c161140044091140401c000b09100980d80141000c1c000140754106c003a20f5595801400a18005960303000300341074494032640c030382c082000f130001c4500783d51178018040b1168414004240312160003e240004003240f46c8100118010a150359259041502842c0c101011120710458a20054a040c0b000342d80d119219010106404180101180c01e440000040c030941380d020951203d0b6030342c1c012512201404007919081d050900d800d055660302e000281015100584c0c480200b000b04094001b203400490041c0112045203580307260102c029482446021008094000c0b04241d004090080710710b802c4282260504008800a141c00b02c2c184485500c0d1800d6540c841e8141009400304210006200d10038007494 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 577725341 1250 577724091 577724099
    0x1807020c010905150307110c0d050a0510020301050d1103031c02070b0f060d06152115151401120e0a0203010609020f19050903030d0e160602030a0522030b01 69
    0x7001d0b00c41e0000ca10030040210700001d40b0102205072544009a440d000110014680426040a00f02400036030405800c1c034181e4140400040d03d018000e12560803111580c15070301009089001c2801090351001251f403494000c510900c0703003a41440e4008041c1ca18004001041c0b01441110310f00800400350007090b44014400d08840150384038101a2800c0c000f8a40f010008a03031f00348039000103003401d948883c0014005840c000d000090400b89a8401d2400c4603404502d0703000c0c41c221021102c03100d60009460700340c0c405008440300a000c581444100c9802d00110100010520200314100f20030290048012001801041c140092a0300500840c841030b00616003524425041416064010400c8001d000f514408440000a2200403005440b05500d030459007440b581006d103a00d8440400c2820b00d50803240c1c859a409400c501c115840ca41501800e08040a024420907000d42c0041c04440325080c060710080405c00c0e21011b40c007510100c01020b80a284050790000d07610699038500600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 577726591 1250 577725341 577725347
    0x40f03020f070f062309040f0b0405010305010213120209010509092113080a20010504030510050a05061c030806030c030a0b01060801060504030b06010e0d020904030c12030c080a05061807020c01 85
    0x345817100c10310b29142c40c103602210219a00e102c2c010310700d030050350b840e5600541c03115150720120054400500a020a59481c10464082d4110140f40e080e290f007a10b00c000341e0b00c107071b4681684415030301510a0126130718040401a403690010014403090203801003a04682c0046039405804400720205262914650901c0400700d03841030300151040d5109000385030110700c035401d10b8034100f406280003c58038603020700102c079240107a6000074007502c1000000040d01d40f490300000d00c101241b070340400a5584400c1001703a5034082c192401051120881c00030080b030302c640145603021001030201c4102c0700034800401c0c90040001800c1d03403c40507110040c002c3c0e65001b030206004000f2446c003c0d00702800d60b110440c6800001d803015043c021810305200094070f90003140120240c00400040aa150504000e002240f400300125a004001c9004405203030080c41001d00b2070138103940d01c51950b03460f040c001000b0710028024682c002228414061410328803501640308000e00d5014003954503400d0005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 577727841 1250 577726591 577726607
    0x3070c06050403021f0605060d0f140a0501150c120f1112040f05010201230702011805060f06060c0d0c050c0d15050603030a0519091e030312050f040f03020f070f06 72
    0x170039040b5041203010852aa191019240c200d0040c2c4000190140c02c420164010030101003031402c00c140800c2040300907103460b40018101e80103104030080c044101c04040300c9066901d42d004015402001101440c03901c282c2c0400046c00207070815662155141d0021440c100d00201d00000340710001505025002d2440031880050200780024000d450b0b0210b0303a000391700700c0003040f12051880301c400540068030035049060540301102111601c0601420710b00d465100484488040400c41c1c80820583d0904108843c0915000b0016002410200388116103400440d24145c600e882078161502c040d944642404042520581009403132401a9940d0700a80c0c4009015a20a400900220031515007180880f1040c00b40c0d01c125951303111070014151004522500b10286041c5102088881c1f02503461450055a001c0e0326000381d42e44007603238840d058810458044441b1140c01c030100d800208150500249640301c0d00503603100d4001e608016140200c15446481c1c50b06c00c000c0c0c00c00c074003a000401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 577729091 1250 577727841 577727893
    0x80c010b0f03070b0403080d0209060a0e031c120c032403030915170910060f0f050f0a2133092402040504090f0317010e01060503070c0605040302 64
    0x41c02680c1c0c42c4c800c06151900480c44064103602c00019000881003496040b24007945c0020000f40d00d0321103007030000341881e644640ca01d000b40b01d09055071115850300020300d101e406056580c5608080c100301100c0150042c20f100c14141900c1c0c0c07824181050040004030702951403084040710b0240396081c010511501c0e82d04c003200e107100e180c1e41c0303180480e031007801d11301d60303c4900c5002e07040354441504081c602414503039090112450110081225024000480202c404080c200310150761030708200301c0d86d1a100400942d00010800003008100c1c0410001155443c00107030800c01c0d100e440d00d8908a241c20b811034000a802011502e1401c4040342d010a41160003524081243c00007076580e111444034102c6005c110340c0c00014814039160300070340455025202c0a001844003080f0784c03034200d05555513080e00b02c012600105051034070a043c2d91601741207a92180400c09140d10b82002a0f4180c0d03c0600000100002c0b40f56800201314640110f80c081c621980c02810305000c0b215503e1508068540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 577730341 1250 577729091 577729093
    0x403080918010305030a1b140d030c050a1d06090d060f060b0a0e0f060c030c0303090d030903020d080406090c0621150e060d0c06021e0a02010801031b03080c010b0f03 73
    0x180b0111320008261400480541400000c40b07440c0a07404120710181c0c0f8008011400d41d20a1000c032290224074100e4040c1700e51000c0c0140013400c501a100b9015100c0108002141d107203500d40a12000c43c480d10f203990002e00000d05c0d00b20944046a4000e08020080d03814540314000000484034078802d42009100410403181003d460020040c9a050581d10051081c440d41d0b40541c2c850382c03941d049801546844040784c0e40c51110b00841c43c1c4a070030840d03811615008540c03400d0b140d90b00034081c04c001181e16901a03c9007900011042c1c2c1d071040040c005881c80e55403001c1110000e18059101c8000d070149448803100c50017001401e40c694050790b1001b114950a004c0500c103407070031b101211750680d4440800101c1554501c0c000c125492210000600320054007000042e03020307000b207030140d08010f508024040c20060704d6502c4d03503600b0400748000c0c0011000c100400c08648161451119950b440d030100c141c0300e0380d0307854a0009400806600109035074500c050189454820705d4880c2c40c4400798 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 577731591 1250 577730341 577730389
    0x304060e060306060904051b0a0f020f060c0f0a020c0d030801150c0c05040903020f011805100204060f03020703020c03060a06091518022a06010504140f040204180804030809 76
    0x940825054024050174501907030b1070b040401d1001440290f50036501c0e803000349990312214580001030440011020b00c0c40980a98a480401e40002003580c52203400c03100740807440c0101303c4001a16903800030700e0301400c500902249442c0c0780c0e2407403d803110080c020fa031091050b505200d0395507074030341c803901080381400b00c0c103000d49000850081c0f100c03048a0b0102c600291010702c900f820f80c20105415001d0115501e06503d442d52000301d081800c0059004100320f80c01d01204200d91400c9105d18014900880c003905150950288217800800c201c030302c00c1c0706440c07035500c50401280c64807070259207804a6580f80c0d00d0900c043d076000d00c1f801c0c000207004021440704a190003081207040c40c0c5c80c005a40020f80002e4064140c45500c40c07690703a0340c0e48440300e01100a201c00032558403804280a4588501d0502002000704070380816840d0042c00750582d003200c981c81d1942003000404681954003030902c00d110040021405400260008500442b940c564810303800e41001407401d01402540e0b0144186 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 577732841 1250 577731591 577731601
    0x50109180201020a0b090111070503031501080735190c02030703050f130503031611040203070827070905041103161e03060203091014060609040f0f05090304060e0603 73
    0x241390900307260002880c50303907070f00c5880345c4502405040c84e1591502000044850800000100039440b541c03214110014900032b0000440713480005441050014040c200346030200641c00c060041c1501031140505103100f00444822031200c400ca0b51340314020075060450b440c505640c00b8030410000703c1e00c051072401c9042d9034081c0044c040c2c0860301d4140540401c010301401d26841c2d90364040e00300101100e4503200300341da251003503952080c01114400104a0f40c1078103800c1c28000e684c040c80050701c03071205c40d54507240c3d62260452510049910030311034284001c9207000500000020301705c000c03c007240794541424082744203c0a2241513001c3c0d40140e0544500d4200f64074140c5c20b40c4c44580d02e07003401c05100b941584c0a49020b80000c4d0045200000b40300716607900007101c440c2120307a5082801003901e881c02c0d01800883c220b510030b0b0020030800182146203081d0780f0000e20310360b0700c1c400082c525003000c481404131007080340d0501856000080c1070201c2600301d01400758a28040711210b180d8946 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 577734091 1250 577732841 577732843
    0x705060913020c010905150403030b010306030b0a0b130509010605030f030408060606070c0b0412020418150f0e01050408070c08011506050706021e04142d0a080601060305010918020102 81
    0xe541c03004501e82d9001c9041000d4590a40180c0e085603004401c0700d42e46408207840740300040050b82c080f008a813404d2454411035000b03004850407207801c9680c104042e0390751034880029100f104d6503140c0c0402c100c140503d01c0840c034032403035004903450000000d00340d007000281803400755071144803c21a4000d00040040210018459070b00040949005840e20345601d06070a46481c0754000300100354000c1804590f0248590022041a000b20360038401c0080c040c1d504203100851600140126001c039901d194920703200d80160300480500440028900c81044070345084400070345040760b05401c006544e40600441d0148540600013050003003200d08100b0000142034641407040c5401c1c000c01054500a02c00d0a40c1628160021440858407004082040450940c0035009440005c9041300700c040c020700340300d541e084246902d20b0b0380850180a20310f45e41d03443d42801c48100e50186140c040850300003030501080d4001d14a0f40c6020895506210030401550f03500301108409a0488482e080543e038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577735341 1250 577734091 577734109
    0x31e111b0105040525081005220203100c0c020d0804091401060912020109080d020f010612081602040e031204020102100b1c17070c0905011d010902031918030207050609 74
    0x214400000340100d52840d0103a801440343e0024a00b07021f040c660000c40e01c000c0d00014820b02c0172075202001d4804c916800481408501d20103500340d4010700c035030901700305a41d2150300300405500300f40f0203d446c07607030000700f42401c61803040b15001004203041025a2250203900d2411245806280702c940c101100140855800e01c039562181084030b4510b81964050042c0c81d02030520f03c0c007a1500e1204000003e543d402d81030001d6019503291540014080f10f02c408460310450340540010b1a0440100140000541c110001d81c2d10980c0c41c0080b003101c501c104003c0607036002e90041d0080c01d1a041c000603051007401e0520160150a24000d18901d40d956062004219840c080d42c0807000748506042048100c1c080b401040618001015030034882c51f50700d0f4604951805a0a201e01c1e0380382c030007030030301041511644030074106410014085000c09401869000344c00f0101600208a0190201c0541d41b111804400c2e0247d100300c4c98040c513a040c04400007170001540c2142c0f4040d5a8804281009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 577736591 1250 577735341 577735363
    0xb0109090f0807060209040c020c0307060f020706120b03030412140601050f090a060e0c1b07060206061003110406110d09050108190b0607060c0807030c090303031e111b01050405 78
    0x5680003c68108200343c9905603100c02001034001c006c0740305940e5019580c1c0d803c00800f10310a01c200303070700000c50500c20807924001080700d5000c3c2040030314189068400c2c0d0104c1e000b02c40a1901d403c1285d035030b5203080020340002c04141000d00e070054800d04114050348440d072413400c0329800041c014800d540b510039502c50400001d5a0030400c4ea035030301c01d03400010030050f0400505400701000340008540d50390040d208150150b207044840d000195441507440185201e0724000d6008540000d0062900c1d0710b1001c04555142004110403022490701401a8841d0300103101160340c000200c56008000c01584813191020300b0301d802c032a0304100c0040c05903c00100051350030a40d40c04141e903525059009248070710380c098000f0303444800920b4038101810160f106080001d40440c000f6002d00d2207402001000d035501d441c0e0740a82030541d18120050000300040b2a9004014001d001c1510814420451513040c00e8100030340350030200485842c90340c90003a0721415a8103260911000c95000329281c42c41c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 577737841 1250 577736591 577736603
    0x2107080c0406230d0504060203070215060d1407030c06020703060606110604060b0d0b09010203060f01090e07230310140102010204030b0c1605150601081006050703141e070b0109090f 80
    0xc0c0060500095a41c0b144c9089901d4507410709050004002d00c03a00514010b5549809441e040081d501d0000d0031150101e40d802c0d40310f2800b0f442034020410104000c45200e40a0040e508100e4894480c40c040d94003070303030011005074440c1c1c0042050212910561002d0081c9240c00b06036140c1031300d15650382e41005040034050395a2050820050342d43c0d821070303480803a0312842521652a014400c0d40c004d400c2183c2032400b50034441011240c0f0f40c401e01c00401955207041c60910302d070710b8050040b2403101d41049042445561b0301c3d20545645081805140b190401c0c1411000850034654640310310010008120f05680c01440140006001c00b540b060b03101401d8941c07e40c42e1300e80116160f0032190034a0002c0d105009001c154958180201240c510600b07082e2a1044680c903000c100000b0303454180b14001c009542445454002440344d20602560401250220305014103901c00c01c1402d800c141207121480b90000e2003038100103145200a0060911040811140e000340e2240e540e4000300f440000c043d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 577739091 1250 577737841 577737887
    0x60e030c0f1f0504231c08040b060a050306011401020a171b010501050f01050f040906061d0102120d0518030406020708010e010c0c030f0504030b0a09020f040b130b0102032107080c0406 81
    0x51a03400304000c1000e5108a615454400440440031f003907810240c600b5580b182c40350002900300e0600c0d0280904680c03000c1c0081205a1800407620010300b400d500050460081c025200082102c218a460303051455144880d548c0740d80d030345a04010810322403c0e00e10b91741003c00410075070b030301c071035400c0c03011002801c01c60307581c2c07403000308003800b520858010751070f003038506000030038840c4d400140001e00e032200480b40c2030101c00300c1c001660380e07440e000e400d0341440004200312200341d2100d81003a0307005150420000c0300c0d5400205924116041500f01e6801030380100020020040309005281c080144a00200007900d42103c0080900410b940e0140500c00412070619030580f25008840007107401522219403400c06520324005440307928001da200d11491150a40203250130300c14504a0040101804130070360701c01d10700c000508060300411b410350100b44600500d00d0740000380c2030000400c0c0c00307001c61140fa04940c00343c040e02c000b4200f0070851005000600544e900420740841a10f15a0708d1891 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 577740341 1250 577739091 577739153
    0x1051501050a09180501051c0b06010e0f3c03120a11030415030c03141f21020415180203130501090b0708010b0c0a060e030c0f1f0504 59
    0x70780502140c1c0003102d11807040e030107078900420f260712586c103a440407100710780345c03d40301c035144580c0d16007105000e0010741710700300841e10305d42c01040c140304114000341040c1c0705141c002000901600040104000640b05510038007035121300006954440d00301814005030318941c81011a84d24800d00d88174480d1303004001005400940202609108011f9020440c0c2ea034030780327076080302088650141b000300c0480d007007035100d08055000b40504102503800300005000b03965150107100351094400717002151880841c0c3d000c140b02d0f4120358081c415140740411001d1105252043c4001c40d2007040b00d0a0f2010b440c00740910110520300c2c2d49200384111058050703225203484070001842082480003c020390300e80301040040129624006100f03034010b0300e07644420784c0d0702e50b414040c07482003407120509070700302c41d403010005042e07540a0b01a01010b20122400d1448001025140862945402607981d0010080d91004007880328611b000c0741c070b21030081c00305d401d290741c803900310281c00701c0c24203490740040d01300803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 577741591 1250 577740341 577740347
    0x151a0d0809030f0c090c090d020f120709061a03010b1b07050a1d0603070803040918060509061501140a0813020402190e03010c0207050907090b0d020408060901051501050a 75
    0x280000c9008040d02c014001180a60382c1c0c9803501388009005030720020018001d00100d50a4981c03606001d410b06418510607401c000044010200c1c4650103000b45109001300c0e401000101c01074148804000362403820030005000f01000c007248503660107420030041c410301000318107994003440c000d201c040800400c410424100f85a0350000c9820040303040c0c00142e43c3c03002400800c0305070400c0c5040546610b41c8820b05450b100d41c0c2c00b54118a0b1700421041100d541140d0003485003d000f00e80020300c0768099138601c000c2c3c44055940240f203a006c170b01030084003444082404804502420116030000c80481070460034015008030b642481007542c009840281700740048280a5801041150341d03914848410f103101d003840d1290000148910300904107800d052040d940000c100350024400c2030301d08010400d282200518500030070000220004882e480da201420b621081841d0242e107a5007008180e13031528038000c2140600707a05200a02482c4801c1c4041010740c440d0a00e05150343c0c142d466001d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 577742841 1250 577741591 577741597
    0x3070f0524150301090302030306060c030409020a02011d03090a0311011b0b0a1a03030d0c050705030d0605091f09110715050411030303040c0501030b0f0904060603151a0d08 76
    0x9034070004860030580740c00c1d54a858254490030058400e00541d00702e0b5070a06088540034500140560310800c0450118646103020700b440069074003c036071500381c545007010f080c0d030814540c10026079103800a1401f07001c0d00d0242c01d078000910794011400c00100000240f0301c20400d100c040c00a45444401c201e859200d00c074801e81e03e41175403000c4d001881c002e180100040300200e620034001460000750101c5040c481a4203030001c900100258203240d952040f41e80180142030000c001d11000304410340000b14180064020700c61644e100007801860701080c8640b02da0010f201c1e80036001c07071014810302c440d0004400c4040c2c8410000001d135030514803070710400c075225039140035100480200d0b24142c140e1075504064441d520071072038664452f0501040c590b8074001500c004003080490355092000d03511035802048104401440011280c58120110b0240700041c1e41c1030364865280c000034001c1c44645001f241c40c0528404080041d214000c6022214140395100144542c43d00b513100400d01c4180029 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 577744091 1250 577742841 577742863
    0x3d02090109031b080d0c0b06102003030a06050103050118050910090c1a07120c020d080a080906061e0f0a0305070f14010305010e01060c050a0c260f03070f05 69
    0xf841c4504030489400340041c5601e80310304e40c0144110401108107606c42d84250043e80d034049840c09040e1214000c005c0941c11022811081003e120600100420344400f031140e00005103001d140d070b03410040e0320103080d22282d400241c14941404010040b40443ca01e26181244900d0380001d880e45489942c5803d0801e482d01c0014000c1c14040d0341c000348911000801b085440e0400117004010103100d50842d24040c0c4c0c10060680914910720200160064101d05145440107000402c0c5016a64a050680e0010351581c0002901d950070041d00c40010494650024403c40e144095000241c0344803e0307105543d19564011180009403240d00d4071742c1d00300d110103503038030a042c1c0f042291500400380a9441902c2404c0e814600c0820214030365001e07214443c140c031401d40300000b445c0c0c02c25009036a80f6900d5201100d96103d50902e00000ca1103040b800c501401c1940c09a42e150300390f4203070740d401081524455541d550800ea807085207801000040743d480c56402455a51200c01078205241001c0c48010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 577745341 1250 577744091 577744103
    0x30e030706170906071b05031207050408010b01020732060c0307020a09050c030c0705031b010c020c01050f190c06050702070905160903020f0607143d0209010903 71
    0x4007252840e000701d00d40d02c1070045403540c0c08603940e40c0c10510750354040a65940010644c1010010b1202c3d40c0304490b840300354094000c91349003411805074450034031002c40f00074000602c0807805014420080c090324414403024402000c1803410a45170b44c0603418070114140c40006800710403119808040c2030394480c0c2030300074000d0b030b100d4050015054030307a8803062003248100403071000483e14a0252150030300600829a807a8110307603982c094082c0a5006403070982d89848180325501440741e1959800540700e40c100001b0a500c10746001c080e207801c0202e0009414003205021381e102d829000010348031042802c9208600a0716031040c259506103014078003811280c02d10003000607403500010301c5011100070035410401c550f10400b854402c446001500e40001d0b05d141020405842d013202a61080c01004001034609040759403507a000060179031503d4903580000c103003100e100c0713440c440545115400d4030400320140c03001500030344a0182d00c24002e010a0b800300e1358210f564460b03981c1a0103142d03c06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 577746591 1250 577745341 577745353
    0x2a01060f08030318030c0c0913060e070e090c06070f020a0302030303240a06170a0623090606040510050c0304090c030218010e060d022134090909030e03 67
    0x71000396241d61080301c844038002d050f00010139840c1c40c00000c64404100c07000c05040001c0883d4108550b009018190038803034581100048003045040c4030710824000362800601400c1c0c80d004105481c07040081c9401c1c51500106041009034903200f04886041d0750005140c0c00749030051001801040c455000071b9054400031007000004050501b204401d44a031105031703d4912110381c10400400b40074014100015a1031020300441200c0c0c01e10365400144000c40819856100c400c00e203102260751048001e08449022524003500f041400f007038020206641d202d252509000101c3c1c02c0c82d10408483c010003c0015940703500d03001c24815640540104202803014025010000f0040c2d040600c4244100c0c04a0244d0021903000c0e1071030888041c0c1c003900c403074104803200702c090b0001c0d04903000510500091883d005480309910300b185200e01c040210190800d040360583c030140346c1010744c40f41074068110401c00f5005810208010403a05000c002042c2041207140c101c8100c041d20242c42d415200312 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 577747841 1250 577746591 577746599
    0x31b07050f071401050a030c210b0f04050405030a0804060f06030321060e010b0d0e010e0102030117010603030206010b03092103180c0a140105160f0212032a01060f 72
    0x1044607603841c02114200d600d202d4864002e156500400d2a040c0e005c0745c0308020000a96002c0c0d00807452110301400c01010450784026241240440303940724600c45641c80c4030600c05071130300143c817007484401504c04100a1600741d0b9090b03a80d00c02c05e65042c0c00e004601c0000b908211003600302c4250318040a40c140714840d0703030745006858482c03840104425824071a428002c003241602c1050216202d0188002e000d91070310100e400b042d48a6101d45100c070783c45111302010264240a801080811040010f90329850840c100c01d0300702a030b44105140f41d0403d0000c00200f0740c0010703910b0543d03020f006207030341c0c1c1d0721407515491414403440b14080c6902c10007890302100190402c050b40c4141d540c45850322075009030103107182c0c40d8003070840400d03071100780a8003c1c8107584c0803207401000d0341c9043c1441407605155404000c416581e1800c12901d00c07034460061720071400c2100c003902c054154070000f1404d0030300f9140901c072460041c041841900c4503141452640060035007000f0010700961000e980c00c0741d21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 577749091 1250 577747841 577747843
    0x2717040e010509070806090f062403010905010609080a1b051e01021204033203030a0501080115180b2b02040e070308030c03040302070512010f050601051303020402031b0705 76
    0x7445290f1040207800000790210740035044880c441c0304000c1c41c078500c03943c41d880281050710014003d07540001c014031540100118503100d4001c40160307004101c0e16580740599510139a40140c003c5400c100c08030f0400c104c20704000610181083e404a4020a0394038070b9403601001c008680d0010751300100c011880f03c14035058000480003030341c00307030b00351041c02d240c1c0386280340700d0310561200400d0006803414600380c4141c80c14200d4031a01c0300001741c0e01c40208019100cad10b990021b9900e620790541e520010040c09100344503000c801d020300b00420944901c3c0031100803941610048540000c2c0d00d400e500145c945c1c41d12000d40403000d42c903150722502520410f0000d00c41015140c00c030700940c03030702d0321110070043c00045040c2120350080e4014a55940c450705192990000f500032019481043c00102d900c5d5175a680149a040b114000010104013a400340b005540025040c0382c18080c1c00c01a0800c0790300c98840e060103032901514017581d00d0b207420340a5800b019000c002030030601d4001c60f4400030440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 577750341 1250 577749091 577749119
    0x627011211070c0e100902030405010e030301030b150411090d05011d0109030909050402060301061404031e0b0a063204020a0e03240a0b040902090702031c271704 71
    0x40910b0f00302c807090b074841c0c1c02201c00140c2580ca0000c0212182c0040140b01503c0c0c0041d1351140c41a0000b086070083d0700c003501c0ca0740d0401c0c0c0080b10200194010401c0985060f503550070f1501d811202405051000400da050912452400d94001c1c0444031040c0b0a00c0000d421900201c000c42441d103541a030b142614500900c80480210001600345a00048803186402140c0c003030ba8006145c50300d96440e00381c084e511000710b42003001d01c3d050309010000c00301d00c2d40b0321188040c0aa823400100e080d2424541032210b0400104012410752901405110a040503503e82d0003403018100500e250188a8428001c00750b0340318501c0d5440703400010480384c0140c0c4850410145641a401c0340c2c402080310501c01000386040022215401d45140098802d000315003001c80c08010150002401c410660007041c041d820403076090b000b69100140c0c00d5030507911b2a000805031000101d08115103019185440d5100c81000601c0800d2480e07001e04030248404100c40f2011f031903074400c415039200e03641e034000d0754005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 577751591 1250 577750341 577750343
    0x117070801060f030b09060405190e070303142803020c07170d0207080c01030504140d180f0501050301030b091507030608070b1819120302030304020a05062701121107 73
    0x50b01c4041605816019001d500b900c0e1700d0092803e030140e0303100001c1c00010b060051100c096010603085018000404e4800c10081010100c0504010360540c203026000080c03000314461400e00030040f0801d801e50718106042140341c4403a5034105c4841c104400c40103070007410303c0e00c0002d0245c008000341450304803a0740f0040d80e04203000d5400e0780e640c0c41d005030388034840e51150b10510342007006016075540c4a0750003250b005101700d0a0021008001c0d104d285014101094000841d140c0c078104c01c4001e8400c4c800e88002c024400362601c5450501300000c001d80010300c0300074181d131128004240c0481090080294084400c0c50204a030301d0481001006402d0358415040280900e07100890032414800803500014200680100d4000c40da6013400740c61031042440750001d1420000109800309040b1205400501a50085403642080d0041104000b4a03905c841d200780c0003081488220b0420701e0b5071000141034058100410712407400142c81c94a0000a01c09141d4a040e540c3c240e00f001c1e88002d000a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 577752841 1250 577751591 577751597
    0xf0e010603111203030712110d0b0f030f07030201051305031501090609020a0c0210120204090b0316050d0209040611030c22210201021018020123040311011707080106 73
    0x141c11400611540d901d500f0404001500100009800c10b400707090f100562003c4068002072019941510b003602d0341003001080c0c1d5840e01e403003a16416142040c2d00101c0e0030400c030040c10241e803080241681d20502440001e060020108a0b00c900a5090584200505024003603440c0c84801481a403800314090042082c4240342003c0460b07003c1d00c40c82910850740a684038801104a00e8003041110066400b0350000c0200c0b550b0407035200000c40c0090030080203180000305080c0f01a008140c02c00c00180410b20091a19010802255442c0c0c1454607900d43c0540e0a48015259800c240010f442200ac8070102d6600010901844103003820043c8840346100c121807407030103458511050544894402c4280c5094483c488812040d1440f00c041d2401e88140111001301e0b041c680003c00b55454800901c039080d03076070a132840540d600004011281c4450303401000c41d825041031a1a0f20780143d00001d0001c1d40e50320020b0101e64045c142e001c0c1240624040c030f4500349000c450080040009000720400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 577754091 1250 577752841 577752863
    0x5060415140a020714060705010e0f0f010b15070c0314060708010608040312020d0e0f0102040303030e030301031e020607020619030612051f0204031b03060c0e03030d0509010f0e010603 81
    0x22400904152021902d03a0740c05440f00c42e180610740380700c1d00d810502d0242c4c0030004004e9000040c8092081c41582880d25024014018100d1603003401d1a12110300f149099040600844481d9142600c0c2c00101c210240c2941c0c440820741001c62910030103410040031000d4000c1c5140844000198480c8510860b80d03907081c040c1c3e251042144c07060010349008001c1000b291070500040f03415000341a0324080684009000074100c11080e117401045021004c85941c000740602c1815410b0103442000b08070100103511b1545140d951075034140744000014040781502d11264119076409040b0ba4103e17800608094071480445d0102d020030030004040c801003481d022000404000c1040c003443d1154115002c1d1a085850b05904182d00d180090b00c0064544e0800c1b0202c00a17911692034140d03030a43c0714910040e2410340c03502000700c0707407a0561401400414116001a0b58000003100d52141d600407002c1800d448600000e805884e400e11140030640c101803034000a2070f4151b000c901101e010b05a2120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 577755341 1250 577754091 577754117
    0x3050604020a090923030d061d1501091403010b0424091e0b0316080304080609060103080f07020f04020f07060b0d02090105190305010c20070b030114040605060415 72
    0x3c1140e0415500400703a4940342442c078640000103580328200400303003090303d20388565201c070744040304d10580000503180c0280400364880c0c00ca0141d4254442042418507065000344000640400c015110b00114907030917060000b9141c030213400c8480c07002d1011300140310800c0b102c140d002540180004c10b1501c207810a000041500003402001c0301014440400510032400c032100758081c000ca032144c15014421100d0702c0b040315010f030301c080f802400582c01864540d42400d04032410490080c015644591041c1c00510114242004032280f030100034110341daa4002c5c0340b020903401b5183d000600d40c803a101084e040c080714180b800a006481c07007600e080203000038038800c021400c2c40038580a5080080b0800603c1641490740d0301000d08028401602c0c1034035070341d40d50075003504e4880c00540300240c22803607102e0b400080e10000300c1c600b11509014041c0c2504120402103180814498031700c1c51840303441000c55a454940c003100103000301906c0305650b95250300300c800c1d014091214400c009141850b80725 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 577756591 1250 577755341 577755359
    0x909020a0e0103450c1403061f0608180a030f030b19050f010207080a0804031e030c06050a020c0f01051605190c022b0c090c0801050d03090b0403050604020a 69
    0x2e05110340718400061848110b0b201c0c20309400c4c121040c80d00d1405119126004140d40c070344000000c003030705900d60090314101d500345030502801811001090550000c0c040d04421100317500c01c183c8010345468000707561144243c200c809210494808036001d0503ca5100b4140c2c08140313410b850029442c14002c038030a24003880050400d40320241f0140c04800e038288000d01d80250f40b61203c20051040b11513841c1ca135146039040c07501d55402122a0f0000080410401c0840d01c2091845010b2050500541c07102e500c02070074112911ba4000c201c0e41d80c40d40004c40f240f07542d905550000710200c0466002204046246000700030958200700d175400b0850b601040d1170b1261046800c0038040700341c40d4260a4050900752a46a00c01000b00da10003805003036101401884040702c101140c1d840c4000b0003900300c1e82400e218240e4103400c107000882c20070524020741600a181d46045076001e58060f40d2400e45402c0803260320296400401c040140001d0000500400007000d81c0294000c0390701404450381d8198a13 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 577757841 1250 577756591 577756631
    0x30a02040f1e2c0708181216030c1509021801140f120a08041d04080d050a0209041112060306061809070e09030d0e01090b01120c0305030c10050f1e070909020a0e0103 73
    0x8407002800c1000710f04100380303405043c003080c18272a00300b80410f00d00d9940c849402c44118180281c0980d99844c0e5002549800d5004940714881841055580d50408040480400080d0b281500030441030011004948807540c84018200c280300541320780350054034080d9400d40c064441c83c202600e64000036400d118010100380d001d641e012552900e84019440010b010380030007032505c150503500303100d0444517441e04d0090220068003070300d0441d5218648004482e68107400382c00c0a019501c490b003045425104d05807010700080b50300114078a03d40e41c20b03101c140f51a800360090310420301400c00f0301001003000000f60040c0d032000c2c01c040c4140c5082500c25400ca07a41801c0240180382c054004100b40c0c609030381d2501102d8001c00d8030841c07032900c035120075185078442012598140d04c08503111540d8011481500e811030080b2000701e006041c481d400e805152061032007452456260030224400e68000c0300550024121403205545540c000c0d240503001c02e0703900a040c1e002c20304043d000301c1e03040d9004200b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 577759091 1250 577757841 577757863
    0x40b09070804030c06020d1a100903031d03070302040e0a1415010603020c03190504080c010c08120601051c050601110d120e03070602030a02040f1e2c070818 69
    0x140308596641e070f0714101c0700c06510300c509640c410f508029100034102c00d40030303190004140000031444084000e013481028014021701c0001c10202d003106000281c1d21150110058510f408c40302e00302c2c2c10000010b81001800c1d03000035846854900816540e84001c41d001031811b02440d0302d040074a00c16804941c50701c00c4c06619010410314070340140640e41c001da0241801207007120849007429031081e9490b40480e00b036603154000c40d802080c200f1041004210240320301100b0303e014807182c0c0141c2ea03400c1071070180c0002c1c1d01780d2034551800100e150344100e013a145800807071143e143da04048416001c0003060140d5000b40040c00101d9a903064440016000c910b08100c0e60354900c1c0025030031701c0440105421a44844c00d40405c004c4080407450500103580285c040c4c03c40166200c0c40c2c5440041c0400c1d86600151046000781c01103043d940746560410100d81d0b14191005e45a2500143315045182d0b025078034410803000c070f050001c0e10303501c03050b010f104500b040e000b580111200302c01c0307035920507203958 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 577760341 1250 577759091 577759097
    0x1170606030601140118081009060c05070809040c180f03050d08090a110a050a060207180b01020709020a0e04090605040b062d120d020d030c1d21030f09040b0907 71
    0x39050300954418100c0441c540b8080e10000021b60302d580030a030030a0100360354002401e4036641b0400601586118552680e039440c24514a0440150394410083c00750100c0c8600c6190350305040740750540600007000036249243d841c51040c9460b0a0b01c89078007900e0307000550310f074481c564094200500880032540102c429030000c21001a195440f594103030305078291503422500807240051a6140c0048440160183d50042e102d65414480b000c04402a4007081351400307801c200815110b030360003203410400d8980040340580e842e21030050903030303c416604001c2a046458660b41c0da0501c1050b60120380928440c0d11502150303182d2004010040c0c43c001240800e84602c1001042042c50420415451003c0907100f400c41d4501e00b00c0c1e45040404031802000903800000e0751a914960610a03e11710244c05d0405202d03002c3c05200103001c04100d4448a4041c0e00030408440402c0074194140070841403100c00c603582c0392403c900740700b09038002500c8a800780b1b05107a51184d15103824085c40d80b2034541d0796 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 577761591 1250 577760341 577760369
    0x1d0c040606120b132c0d0f1b15091b080309060d2a0f03061a030403020327190513020a0c0c0806010312080702070302190e01170606030601 61
    0xb04640008118100c052a800885034042c803500c40d07a28090302d0100740b0800340b15000c1d40300107208201c1c2d080602c00200d041d90410820304200365000f441c4140c10740a01c1c07a1143e8440320b0355000310032150020320054421103480f002082c890f040d54100011f1244070300403042d0540441302d4030382d10900403402960140d82081c000d01502e41401c502138990f52020501c00324046190201181008000381d00c10441c120540c00d0f481841900420b82400421151904000c0d1901e040e01074014684890901413115200101080503d407080068032402c1641e0561842a042600d240c180d28401c0f610000d401500900401045540031030780707050448a020304000701d40c03c03405071924000c0d40900040c00512581041040c04150503070804030141c40204c00801c01e55045003083c100b07120070194108201701526041100c030b69404148503044075415100101100301039102d400ca08652504400084920300c1d000041d007032072011840080e81400340a40b100c039144c1d1010315403991000d0184600c007010300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 577762841 1250 577761591 577761617
    0x7120c06030c2303060f15120112030804030c020f101805030312011208040e010b09010210020301140f060d1410050f0a0e10090e030304030f020c010e0910091d0c040606 74
    0x4440210b6001710000c0c41207014060b0080017810a0b40d198410030603001d00400c40300800740604900740c0c05080c4141194002e02c1503958001d242c030100400003003c00254141000031921365555003240000001c00d1024103140c02400107045000000d03810400d08103001000444c1e040202c00c581c05206080d681e41d01d2a030803d0706140340360744c41c80c604071000541044000b41e20310010741924040c0103006400ca50714180c00c000240340ca0500d0304004491807040004120854000802510300340040d10700c0010b02d03103a0f8002910350701400c422203142508005940c010321490700c1c01d1b544650a802990b03554140c0750001c1c0120105c02c1c588594003c44486001e000301013400703524541c840c007226103141d9125100c600300c1056401100c4425003540c00402803104054200d0107a80703a811080c402011000651000240401525400c40b40100c00d8200420010081c1000364405002290018081100420309c0820b030600701c4400341c1d1460150500d01140f51400780182000c4540c141c1e50f0100b84075007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 577764091 1250 577762841 577762907
    0x308190315181e020f070c05061206220507020106050118210f02030a0812060907020715110a050d11010e071703090a0902040f0e1902070507120c06030c 67
    0x1a8940200c10100501903010f51018030740000c084e21840701050a44480840c0f4010128070900d801c2070b84201340600422041c00708003541079500549c01c8641e0320f54001c88041c80304d405c40003040d0240840c4d0070241081000c980541082d0110750080c0c0ea1507610f6910304200710300700701d054018000800b40d136500d8440c0b20218800034008050140500d5412003c01303500087c600740403650122151040170400f0000712003000b40e4207610020030f9030000303802d02c2c2900c030003501c40d540ba000f8809540c401304107a94080703108031000001002c0c14000c0750344c2590107052840c1d40d0440650030702d0000b86001616859201e0600038500428642d000030046c00382421064050788208220700a42484180486d0910b980c50400600050216050040e9030742e0411001d2000150035402c03281a0036440000d104034403a000c006400b00b01080301d801620b4014500c2c2841c00c0c14010f50002c0c50b440d660400741010300029074002003c0340c8054600300800c209152060383c04140c00003840316404a10354184052543d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 577765341 1250 577764091 577764101
    0xf0111030604050903162d0b01180e0303010e060306090a0b0106080a0f0507120b04060302240f0406020c0307050406031a040804080d02030d0b01030b0d1506030819031518 75
    0x100902641d040505552031028062086901a42d00c02050041180140600704018001001c034040701f00484640382c88050200304103125030446036a00d408a83c103000342c9548030f280c1440c40303030068a40d203507520140c502d8a8001901d80600c240140c00c08500a1400000c001d9406a441180400f990f0300e48403042d81c802c000103201e01c6605403620034280c039441070713445000c0c0300d50440d8580c908504003004200d8101e0b420400200d0083d0714103281480035a588480b81c01c140c9003198404100051101005407450007085206100031401050110380c540d0041001d04c08200158225402d43d80d58004000543d2040d02c0041d184002c1c1a00100c0d04510303181d50300b80d2050207407022600e000d5445007a1840c0802903005140180c10114941c001c62a0b41d014032b4800c03030001d2a091100074072243c0021a034503a0220000c140700c0004038032081401c2107401401c01540c2040d542c41e258a040c0b5240300311000802501c1340003c6c035240707810403012284401081950000110280c280e03002d1800e00d03000389 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 577766591 1250 577765341 577765351
    0x60a0b04050a031416120506331801060f080c041202040b0d050708070501181a1b060403031407091505071e06020c122b18080406020f011103060405 65
    0x20007440010824405410194001052107035019882032030035003403031422302034083d0400485503141694a00700303a1041c1c1d140c2e000800c0701c1c141c032101820a00c000039200c1a0b25144200f54503818400050555040085003c24102c00d0306c1f22002d981d1001542030152266004088030a08074455200c05800d2941c80000060805808100f103500305440748c0d4903240d40c5500c0820582e000f44030520107944c0c00414010303184039110141407002d0900269500340c035003081c0420303d40040821030140000a004a0070280030078081600c49038241402c0050103000b13880c1c189400d018220010500c054440c0c0141002c544d000d0b0800032140c1100041100c0c02e900c0b240003a00c110150b01c0b82000103011f80000303102401d02c9004010381e40c040034511282002d51180e0150000c1806003d190b4102d6104c1d06603c200c101c0c02203100c20728003003650400c40140b1343d200117410301c2000201d03010304100302e0304000d0081c0c42c42070302101d007505444503035582039482c440b03c0100b880f941030004c940f0900345900419006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 577767841 1250 577766591 577766593
    0x7150203130b01031101031104050319030c0b090a030e0603040209070e03070b121e040b06310f0e240a0b18150d0f031d06070b060a0b04050a0314 64
    0x40780c440c0c0ca03155140c01080c0c1054482003425000d2019039a0107204142d540318420203a6402c10f403072b00e800031707845125200302ca09009075450010400c06110300300c14644694400044202d600b41098200d07920314404004030f003c290381d00d10901d010f03d08034066900c1a0344c020b21720301e825a5003000840c2c902d100da00c22550188601800469111000300203040740d1043c007001c03004a49804481414150356058007603440d08250014000447d16024016078040c60079650f5424001c624402e0f08a10f20f100d031450304d03002401d0300542c000d04050303821201190320b80c0c540a20511400108103620394420400342078044404070103801c1e45003580841c09500c0490541d000603c2104a0041200080c0c4e24240f05002d00d8081c04107c01403140d001c6041c141c1c401a43d070f1504101c1c1700c1d03589003800462244080d05005c001c14100b1503100c0b040c07848103031082014121944401c011b28024603e05810b80b0f000340300c0d244030300c804205440d042d000d032000c0f80c00c01002d00382101d01d5a01c031555440030340a6804a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 577769091 1250 577767841 577767871
    0x14060408060613150b12010909050607050703051e071a07122f0d0501060306030b06010c020d020604061205061509090c040e13050d031a0411120c0c060c07150203 71
    0x1380d46829418008200f401c006555503406e440001031901d40580114500c1403401d84588040f0304002402680701100c1d05105540f001281415125070280341090803042840e680740c51600c06515015140452240381c010910711840300191641030400c0398080c0c0001c031308031074001e19103100340c205205ca042ca13501c202d9030031084a10f45030303032011003100e00c038051600005001460340310740d1240ca401800c446c85c042001c070b42035696907848a807020309014100540a4092030a543d15542c9607080c00d503000f00540c3d03481d941d660300038220019403140402003502c3d0400180690800012641a400c80d840c4002d00d4900030104001580b40082d014a0320380302c0a0101141040b40205080c4c003a21802c2d10790794400c000380c9802413508010b50311440800d8180050101c01e8204c103051200b40c3e8000b181d0200c3c1d90050982c2c0512203001e440c0004036030b1003180d003d10058501c1a00102a11040c000556400d40d80d120750740b81040c45660343c01071114810544404103086140e0166402c2020820100c0f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 577770341 1250 577769091 577769111
    0x2030d0e13110301060207060305040305070204090510090b150a141002031b0a0605060f0a05040506010302162102030304030f080c090415062a140c0604060914060408060613 76
    0x80b19810340002094031000001444039580401c03828004028519091280e407600d5503001f80140039980009002d251540b90b490b0070800184504085070741811b008100750320380340c14103095a507020342c2c0c501c40d07454280c9405151824009006001c0d52070b00c01c5031a52615016052144d03200107002c1100071800300344400d1004e801c0071406441c01e0100d180c01080309541d1820032000302d0701c0240007070344900d1005064003101c2d01e03101082002c0f42d00442c2c0006055440c40d005030041c1c401c400300741c0714403100c0d04c0003201007080301e01941030003246d044442c144280d071801082c0e94920060f10050042840082c01e0f03170080784644001a80700c52001e11841c04d1051101c0850b0640e081c500015101c85040c050a000541e0b0010045031b14140d580c54141800141c2c154100001200b000007410b5103d01d82d61410640c041013200386007414018203850f940c1c6030f81d028002d0a02081d40201c00030301d013403c07002ca03a10b858403005440a8402c0200134102079241d1004101003c400e8940e0720007115101d8900c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 577771591 1250 577770341 577770379
    0x6110901090b03151002060702010609050f0412052b0c0503040201080a0902030a0210030e0606011d010c08091503010f0509161808060a020901032003070c030e0d03030b03100902030d0e 81
    0xc1740c881d00e4009110b103040180d00030382559441e800020040e4504400c000800070708180840c4c1164010035154807501001c40e00b01d13424400d410140001810a80d41c11500c000342c4240c6400301d44140c2002c01407071001c0c440c200d9091105841c0640082c01100200e03005600341d42c048944184010200d40544407240d021501090200f50038101003030b91107403003048121090164a602010928100f0301c800c0b401c402d40c641490b410045d07181044104810841000850300c22a048900d0003083c0d51800e032804050040c0310350003405108940d2144c80f000150178103090381050301030072002001100300110704004440404121009095070350782c40100003088241448401c1c0155154800581e503400d66134005015286204515424a00040407034000d02e1140001c1c1c0e80c00103c5490034260726410350404070743c00c0d8480909543c0c400328aa030340c0e208040d0160300c003001001050b0255a00e01d8030186260040b03400d001c00283d0160010860112490310520f244ca014480c01010740c00c2c0145412201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 577772841 1250 577771591 577771609
    0x180605090c09030105091516121505030d020706050f030601021e012304020303070605090a050706090510110703080921011a06070507050906040f0e010906110901090b0315 75
    0x440c0000c1c0e0016080d5403034203080c01110750140c001c0b001000d4404200403844c41004008050300940402d070302500c42d900c1d202d04609041c41c00d221a0034881c032641c40c4c001506110449c0700d032521900c54410010318807800440c08c9000c5840f907843c0d050502c40f0100100c03501e40c0c0002d10450440c002c501d01c0d22542d280390343c1c100321541007420000400600380c404c0b18140640c8807258a0090401104000040e07030000101c0341d4807540070501060740d40750b2640700c42c40e00b5891080108603004500d0080345241d80142000c003103480890391100301040c5a00282c0381c0848001c505400360300007280500102c0c0440004001c81d4102400b4250399079050014044070441c040103094540c0d4480e100b03c0b40d030088034007241400c480125000c5207440e82e69034030250354039803d03c5990b0080390008001810750382c640d0710145551034604828422809030801d028000e26001d00112240d40c075059100580d01e50720010340b074000f041030315001005400c008544045410041104018541e40380c49018681c55003810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 577774091 1250 577772841 577772851
    0x5160903120c0f0b0609180303060f040e0a0f05010507030908160507052d1c06230c0c060901150501080c0919030b060103150b03101a180d050718060509 67
    0x444d9180c1071100410200c528060a03015514251a030315032540c14000c401c40344c10450031155902c070450306d0070200c1d002e86106007801605e8081c030710307c003003e000703401e03444411344c6100d8802040155500b40c82982203407203043c0c0280070b024052200f01140086d203030b8400c4541d0300900807161700a6840d000141e40c60808040c3c0d2141014000003901c10a00380221405800d008503903105030030355502c6030500e034418034020281803180c40b20070b0148515400e0040d0304915400140c1001145482e01c80d00810394001400d0346018403030000040c18480042c481d059202d00203031000042c02d4500340c01100ca80201405480d0082000c10000055030b4800d695280710b6058425141000c62a508003d585050000d010310f05240c1000c1d0703114042841c0740e800700144da00c04a00340e03440740c448149415200c045a04000504406040c00d0035500744244040c1015240140b128401958100c06000340c9440e0780f10020202e42c03012034244600314011020540b0a10a5a800104143e40e50002071000c081a54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 577775341 1250 577774091 577774103
    0xc0f07031e020d0e091b07140a0803010819030807031508160e070305130303091401050711070807150e1f050d1415010302090d06060b0d05160903120c0f 67
    0x500c154054104c075400c4507030201201c1190403071402d4018880d203812500ca14452007000003034001d04220014200000260040088580d140f05034030380210130354403c2c080c07203595108040608200510300082c9001841c0d00d81d951441c0e54541d50000da018016002200b000300110b40b03400704000c07608100000340034a00400601803945090003100e5010b20142c400020035041c2420418100c041c014100120356151800084040850400200700e40c02150344140a500f040103101034035078011244024203404400b500d03001c43e075400007140d41d58a14070500c2d01d400ca401075940180c034046c000c521104a000350074684000e0b00103042660345c04402072140d021881c08150140f807a5290b01c900d410b0703802852415055420074428170310301566100a060304040d0000341151803500c91a062901b010741c8803d09000b25503c2d2800c0900a8001410810009182c035001a21140a44800c0104100641c661110050540d254055030391500d80703e84050000d070845400005010301c0300f20103070360701600b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 577776591 1250 577775341 577775353
    0x1207030f0b07390606092a0e010905040b03160e0115140315060c0d080108011104150e03150109050615190518032b03050c0f07031e02 59
    0x903809000701282c3e8804400c3c0d45a104482044060000201030028200d2154006503250710f04c0c0034005041c50340c0112891600388201c0701000c10501805031405013200800c0964812510b40444013015020754084c002030300c42c0c00402090a0580c4040c80703995001e0300ba500117110801100000001c284e109041a81d000300c01000195030101281c0c18a07046850300d95291031544c6c104208501002c1c26041b0355900c1000c18001a644202c203e0718007e03100c005840034000100c60181c5040c100340b003201981e50034a001c4201c0310910340100e0301581c80c0711700c03c030070000101c83d0200c07031340b5404180e95a054801d141400c200d001503405414000d005207007011480d441c024007400512030080b615511081014864040380780d18240d0030169220707052501d40d4650ba0410007408501d0201e082d9140c1500034610030340307105840e041e60603040303002c100f00c181c1302d6020110003141110350880d0320001c402d0b02440490081a000001488035034000d14066800800480f102c4031001030158003240568402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 577777841 1250 577776591 577776601
    0x902091e0409061b03200414030f0f1b0409241103240103110a0c0602090409050a030809070e04150b09010e010f080c06040501051c060923151207030f0b 67
    0x51b0280c3d81d030700c9001c0400000d034501403c2001c0c0c4640282d000f4400901101d0160302c000781c03010401140fa00d00c6020845460ba842171a070b598035200840d45180492080301d41c08009170405004840c0c030300b0303804014030f0b82c0b40c83c00b0051000049124814501616282c140e583d01140120010318090074950070b840c4983c81e03414001e4201c081d89603200506040c24905000125181d201c1610940000c900b00621040c507a454440700a10a4004c8907900c01d00e00f5500c070040c4000011900c041d54800d4840003c0c545078031404c655121900d1142d406400881d400180000c0c0034a0360a01c00801842d2010801d2841e62000550741e142c240c0000c02030911043c01003003041c114058100060074440094501000b1000100340c0c1131141c4c1c01481d043c001c000400010701482900e1880b01d101190404200e01c3c1d407100314a5020b003003141c00b0f0108080c01804410707100743c40c511040f40500216552544511800014040c084036644482141b500403008000080fa00c56101400382d144255500c800c1c0e4030300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 577779091 1250 577777841 577777847
    0x30a080717040b0910020c0109210503120a0605060708040b0a1b0b06090c0748150e0d0f020f03010609020c0d092706090f0905070902091e0409061b 65
    0x4803c01c005c0856000301e26030351240e40c00054140c01e40711014070320040384801c4041d01c10011a684e1008020388030002c1e580c1c1418681c6d035200784c0100010001489959946c1c41089401e020740f080280541c181000b04228408160000380684800341c10800c0e0050300101024514001c428815a91190510204001490950708540c0c0c800800004141041d220b901d82007403982e520405c1000f81c3d0501040104d03c1440b6100e0703030385502a56854200e428000c1e01030803107405890f126280c007445003905034508090154030180d102000c0a4504020304055807110101c000000100b03a801403001100300300c140e1020300030000074150385440540e0b9038034000903861031300e454009200c0401003249001d01240800301a00380c0e500e805460b211807200f0000340110028206a444051101e01e000d560202c41e120301c0e0050340c1e4043c05201a90104c560390300c0c88106078480c00b008198008042c05039148004000c906404100c1c1d00500000307071420766a501c1000301c441041140040082004040040c154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 577780341 1250 577779091 577779109
    0x1090605071b020618030a051506010804170313080d02121006050a080c04090603210f121802060f0309060c0406020a030f02160b2502030a080717040b09 67
    0x2105107014140400c001102c6900002003410003442250002400e03445007800e2001408104d5008041d00c40e81c081034070382075aa0703040e4450510000f101c4000020159801544078510407070f04503038041468042d1001d00c119a03403004000006056484118801040301d15000d000040c5803540c0c011b035601d241490f40020090010302d42540b04000d81002c0c4002d40d400344c140c800404881c1490700141e1244090951240200d400c414403440c5400000010300210312070ba0310550801c0307601003600d44c0b00d13450100c07041d495100511020030800c0b13901489583d0f103a0f100f8034141c1c01c9020380903065400c03907000905652140440c141150400b000344521040107000c000d8210f00094180380c6468545100a52200071441025042c00b00040001400f24003c1c030145490a40304a4080340103030f19010007110301d4100032505a540c144007000d15200d106607001c900c5045400030000c00304c40fa85540c07160001d0740301c1d40046980c2e408400c02c0340d4004c504103000d000a4074545030143d0b1030301c0b00f980501c2101c4e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 577781591 1250 577780341 577780351
    0xc0f0115080708030406031805030c0309120607080103030e04020c030d06050103062304090807020319060e010b0a23090a090501140f1308190806040513030815031e01090605 76
    0x141151070204030f01c40c0700000710b07030459030b4074103001c2910051025140200ca1318010090300c1c0d400006070501c40010040020041e043c0e00303c03484082044a40c0034140c6e180340858134180402c20300307801480803038040c54800b0349070480184054502070341c3c50707c000c0c11034100081c401c030060f4884009021941c0c05006050182014000c2c0075003041940d04c0c1007880c001c21080d5540519511074201061291000072103003c44d40243c00c8660420214024084448117107209a604070f280040499020906009206003107800030404d07103043c2d080680900a0010300e001c8540b60303050b001d045503440e48600c603080d4890007808134001a20b527201c0c01c14500b551400a48030039855141020400e849552082180d081581c2091491281d0190318150015101b00c140503554900c810f03502d6003842d0380c8950210f205220a680501040c0c660304440300255021410042c0820b4214001507120014082c9035000350000508840349244900c07040700b58043c02150004159441c1d061410138403142d401019046 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 577782841 1250 577781591 577781593
    0x10f0c1106131a1f120c090c020709111204030203040602010f0209060f070c0503071205010e060601020c09042a0905070e01090512010617010905060c1303170c0f011508 74
    0x200000f81d03141802000041d0040c1c2c004014100800c0840f00a10003440c8004601d002d0300209a03180c114002e0880c0d6580002c9510322180c003800300e8901c6d100e00a0200340ba038943c0061030954240400500640069002c411401000b4816034210b5482c0308a07481c0510f000341c001c4d43e56941401c800034251810610211091f5004200600c42d5440e0f902c100c42d4100c81860307034a901c551243c64801000d58203544415814800c200740400c40001040c094801980320360006c1107c0b40120010035150281247c2da2070142c0c10008094240742820442c250b8003502c44c42c102c071203205080642890550081e0442e414101e504c4105015003607852240c40c3d003043c02d500388064060303030400000307104907524092103005241c4820f928109034000d401800242940d072502070020080060458000d001e0210b05644a03c0342038041039850800d14221003195444e207000040c41030860b22170081002409460080f501c00400811000c950144031411602042000100780107031182604d604402e0150000006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 577784091 1250 577782841 577782871
    0x5130201170f010b03040f1502180306012904082a01080f010b130b070510060b0403030c02060a0c0f030905090603123903040513090210030e010f0c1106 67
    0x100700b050b486411640e00324104d0707a0700e03600c070302e080c806080e0324401c002c0280724010034152107455650050407060300200120313140300d1000b00405513141030031303c17400080254590700365400e203880179240003503440003914103450203030380f00d520710f103841240e04054201101c0312500d100d800000d0f4040321040802464140301e00d0801e0380c89202821410b204081d4a40c00024424800e43c96241c100b4000382150061540c98942c20704050383c852035100840342d030700d03403803c1c031301140a5039898165401d49800d47e882d0814280c05038240314459010401c001c040c04000c02691000410100c08001c06610039907401c408549842c06004481c44060102d074400c0d0002440d0342c43d91312215055078040b001500d1224461618003a10b01d0003402c008104d0398150302c20314200720013210000010701c2141e030151030b01407089c002c0310003200c00c40d143c190009600254091901d5041e034400d401060504943d1000020303403032a40c00c1e2480c22a40d140d10b03801c02150303880c0011100c090302030000311741c4540d081446880d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 577785341 1250 577784091 577784101
    0xb010504050c0901030504050c04090b06040501080f0703060c022805010c02030c0307061802060a202b020c09010f1a2104150203040303061401090f14130513020117 72
    0xc00d406615000f038101a0380342c00260a020040002840c0280003802c1040449150b04001c00740000c00c40782c1a01480c00c6c800001005400000c400503c100d003207016082c4c030b0741540d90b5180035250b490310480461240080c148000741441c00f50589056180502c0c1c0e504400e44e151031402d46050000c00c0e801d64006004640e005107001c401c40340819448400052501560706100e500c2c4210b408010750031030000b00705030103941e4108c0100703250911102c0303c03105200004000c084d0344040c03090349810f842c0100404110240c080b80303c102c10504045c01034880440343e100111707180360400d034029103510b809603800304880b0713414000c2060342c600410b1446140c074424200c01c814124030440c3d84403200741044005014041c54a03111030b1592410300c401d56a030b06240c140200a0300c2c45d4003445007008110310030403502d5070290092100701c6002c5814854030038681500040c440c140c5400498202c00c07210102c0940800c00c2c820f032481400e003114070881180c83c0f4000148130b60313903017010400103001e80420700c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 577786591 1250 577785341 577785361
    0x31507020316170309030a080108010c0504062a051006060507020f1908060a0c0e031f0c030b0d0f1106070f0803130204050f0402150708030c0706060b0f070b01050405 73
    0x210402c0c0200410b9000249a10300507500b980c88500b51284640003000b401002c0c140803004000e050910741e110090350743c889000c0e9088410300f41c11000850b00401c401c105043c080e40b0030501d41110140d007690071001401c103900c80d0f2810000111f07065001002902c0308054280300704005004140b0b409401c0400b10b50200b007041902c0c00d84284541411141e2010054003095408084c3ca1030b20306652540c01c100307203207802401c2041103203000710740b071144814140d0030001901d001d81141c0741e607140e0007080311a41d00300007000098580b10404d6242c4290001070f0300c80b5010740d00c0c15446180c000c82c01889a0801070018048022003d21640082000d400401d50701a07030102060b40001803d540e0b0348603609852120380704e80c0c0009400a04000410100443d9140c7c0c1ca48140e00a0340c1c0d1038100044d013a5014a5071145820044c02d461301070000c10800e01110016100c018819400000e000ba00e2b01c8034182c1075002051002c001e94000500d50f41080700b901101801043c0640d402d020034200140c3d07007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 577787841 1250 577786591 577786597
    0x2060a1a1e1c0602070203011a0607020922030c0624061803060e1f020a09120206160510061e03110a0b03010f050f1207030308100b1201050315070203 66
    0x9031070010008500c2801ca56030102c1c004503884203848506898002860210060340200c0d0342a0302ca9440c044c002c15848903c407451110f00c92000300024076120040d0300300107115a015100b0f010b075028500247c00801f000c031070280d0b6418007a4070780350802a90f074039040098034280300c640c1511008000c07844034402c0300403e9401c2a03c42034200801e0030410785010081400d110b0f8009484c503800c04c442c1c00200000496452a440c10401190340d0075a04804020164402e095041d0005214150100003e144034940e510405100409040c601110390482e5005005800e030103494035008489090241156842000300500300180101054842811a074600802610014050f4014818100d16a5039112400310241000e0500c1507202d50311001c020050781d0f41270103060301402c205c1c1060b03a210310301030564051403500c4100500509007540e60440700b040c400f5007a10500d4031103010104800b01b0180c0540b22030421068003c0007036151108051625038070404003481074901c1010b104405e5030201c12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 577789091 1250 577787841 577787869
    0xb0921130503191502120c0a030b18130507080d0302121503150a150609080d050c0307030c02030f03030a05040b01050607030207050909030706020d09110907020a170409050702060a1a 80
    0x40050211131040d108020348a90314400060b071315207804000044605201512641c07030140c1d01003110395101001d1050951103001c40d2000603c00c6c000282000e0343d81041040031910400076140c0d0b240c2e644003424034045080d0500c00100350041400e0350100004c08409038094000c0303402c2031040420101281c0c84881009510450000c0000040d000f4038190704145815259540c0c20081c9943e515070052440c04940500c4009025044114038018800d0050710218011440a1840c1c00c40e2079500b03132050300303025400300d8050145c098041f8000400b480a035201c0d600e0440086014074007071401c2801340702c05070407503031148005000c40d8011940c0000e580f0260b07441511a0304250329285041da1842c0600d03400180f01c64000604412200003c1e00700b050004d10591030201d1540d074170802c1005042c411030745c800040e4002c2c920385020481a980c02460360030b011b000c0707078030782134582e4941810fa40003210500c016070711100c1072046881561250300e0300c0d400c215006000c410300103000100c050341d485030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 577790341 1250 577789091 577789103
    0x30c1509060d0605030a26042103090314010c02012a08090705040603110a0602030406050304060506130e030a020d0203180d050127031202030708040b092113050319 72
    0x4182c01e1030045503000d64050032008084415110080c0341011161801c0700c02c4c05012a03110b00300d1011840320300c0036034043ea251001c00d816500001d100340310040c0e240010035001c000041c00e000000c500110620001c42c101784002203006254501d000e800e5900240780c032405041c0c00d040107403500c5001c0c000090002a146401601c42d107070b9440f00b500e0701107640c0069500c245895000003c01401903640001200151071111220b59034030300a80e241c0c0642d01c601c802140080001a0000d0010ba00150340280c000300342c0300428a030300c0740705003c031148500308062170b07400025402682d540410484400d02d50905c011458500204140078200e80c00012203401038031000040b04c100402034102c00301c481003101c03821403134071000d081a400c40c80015209401141031020300400405490086074410911903c0c4d800507a01c640d55158008800181140110302038802501c00c888031548070040c07640c24407480640c403110100000d0203c00013952146109034032946110380b58000c4400043d10703d0350040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 577791591 1250 577790341 577790347
    0x12080c0f010e0102040801050c0408060412020307060911040f061802070f051506150301031205090d06060b1b0105040b041e0b0f01030308092a0102010e03040b040302030c150906 78
    0x101440c600041405108519400e29a03050080741c07055003d042202d140d200248025201c014516a007841180101c0402d82c20000c00900802c0106200100c40c0c0028411603142c00342d1b07a291f640464000f400100c030400010355100da1946458003079110800e100e03103410401180740c03002440724607651481d0b0401140c1c01181a400340b00e10b0201100c0712a81160a8849060080701f1049680408984080c414544042c0302c01904208400392030690707034090400c0894005640341070b1031540248803104da20000c2084c0710400603d42e400340000400c0000603480d05c0305080320504406007101003624035941c1c074110800002c10000a49030341c011390131080e00c503c01c410a420302a548000242d000e41b2851004042c49040700c1c401d0f000504a80c002c6c4e0f14480d9923140c44003415210350104000c42004012078024076420f0030034409681d100e42050000285031b00214100d241150030070362103800c181c403000c1030410030742c1002e20440c1c151072012204103060421113003107519503000d20050640128004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 577792841 1250 577791591 577791607
    0x1b010218190923011d04020f0621070e0103180b0a0608030f07120509180601050d1d0f01050603150c090a090c091a04170111220f1208 59
    0x2a030300318014000228040c880b20081d070a001055110340410314010f54144000014403052034010351540f201c40142d8050300c1d8540d9000c022860711080c0c5810381c402410000f101c0c0001190400e491441e08110142915151404000d0a07021101c104581810706040c1c0c00680f80b052121040711080d031207450130302c1d00d445078140c41001f0021a000000307540301c000382c1101c25940035006000d0b29489000c0030958065491000c42d150b0040ba00c642d83c1048c64800b042c01402100100b903a0b0203441071406904024034080d111043e5601d10390282408002030142c15034180d420301c80c80d002c0081c014000d005600305900032903a200742440c81c12200c0410030000c40c50350400c3c074003200c5046400038201c40c010b90b260300261008105110f01e135008540c4014001614500c0751812085842480403d5401c00346401d0584010b0920360009141720355072020031482c50151680900a440442d80703801035000c240c00c1d0380c0190840150030044411a00042c00c21900b9107086450074510790200240b601c0c9c00403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 577794091 1250 577792841 577792879
    0xc0108070c1b09141f080a081b121206150405090601120c11061e06060f130b04051309120c022d0306070201022506020c0a060b18221a010b1b010218 65
    0x41c4904074000740c020340010300f02045502c0042c06452f050740da040c0c9001d88840c010003841002102c501e01b071240d010310080045160942400f9031000e4103040400301d45a9442000c4120382c0c492030351002254a8400c286c948080c104005a0b00c141d0240144551084040d810320400030020001c034840d02c1c0011341c2640828904040e1400c0300c4030241454861612050710626a07003090040d2802645e10b103220400168060280c403d0664005001450b400000d01d82140c0c0302c00a558140c0c0c114003c0c0342000084607000d14060f03040ea60000c1c69155a00480d0100f6040901c045e040200716030052045882c452000d030540c2d03065803000340c2e00c0c100400f000e00c0d00001a0040300a6507565018000c1083d060160580140c5d4050f007080311a051002140d0907420140d800c10380d0007058102a15504a041c0e43d040080c801c65680225000c0c00032200060300e0383c03107510007604982c61310310300881d210b404150304112820b1400b002200039401c2011b2540758450f5091800f9810b445040315910704030315405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 577795341 1250 577794091 577794127
    0x603030f030c0d11160204150f09020a0e010c170319050a090204060816030b040827090117060402040c1b030c02030c0108070c1b09141f080a08 63
    0x101a110098072803502150a1206800c0815251102400c03e80030494421100044916198103000c00001c40e101d44c1d02400010300101280c0b01051110315804618031030030300000401080c00c05d030302607641c0741c0c40c040050003d40302d1200036050000740099440081d00503400c8400d2000312885440d166a0f98030050310340002804003283d81d461409007880b0000313045802c000c502d0303030080d5004d02c0003543e03540c0d507030390b03200301c2c1c100e070030001ea0354602c000e00024a9422019802c1802000d140e03042400740c1e031340480f414a000c564145070100c210744011036800c01c00001030041500c2c48054294024104140e500c442c0e00500080c4950780d0350009800c40b5015104001d42102544c441000c0c0300c415180250000344ca404d0164841c1c801d040c048030040d0320a2074111305c926403d5441035000501945c0d10141400000560302503e18458004100c0c00b0131481510040440c81f10f881e2003a0400c0498034041d89046520480340c035007103142c1400748a40000f26548103a50110106179102c501d154a625003103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 577796591 1250 577795341 577795357
    0x1506100f0318050c12030c030a08040f0b09030301180213031b030b011d0a0b06160c0504090804090506180705090114030709080709290301140f010f05011103070b060303 74
    0x7100100114041c800c000800c0300e4280300175a0175000750409048217594a010fa80f00c100d51030f620030002240e0180c0b0036a0b075290064410494001900c05070f41d142812414111943c1c1904ea01c0400100208a00c0740e0940d034800030728000841c544208000d41d800c01071868000903000e4042540c0b00c0d00b9200e00c01000c0c500443d001240d071740031540c541c60b56601186c507030041021400601c2004c14002803c41c45654903070600288140d1500030030740c5030044810203a21090354020000b07180002d13a5203550054004a0b44100c9034650344500744015401180c0b07026090314021003140d016249104180c00b0915002030483c1007440c0c542040d4001221021290b41341030409078030200a20441075040a00e900644820800762002a034a580055003203c5031800309107004c90680446810240722240c2031080c4010240010841c415603420000d288a404d41d48026120711080c0104107030083c00c0c4114021700403d180007190000309440103541c86c01050710141400b4002c00c003042d03285e941001115900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 577797841 1250 577796591 577796621
    0xe1e060d06031104111201150504080106060203040314060f01090b0a080a080d061203080601081806152b080a1106090c03010b0105072f04020409050402031506100f03 73
    0xe03281d250054020140c83d9400c0e00403401e0030011513066140030f05444e078004500e071140038581e192120761010203051442c81c20510900b000041814602805443c0103040160002c654941c03075440c003460706044111090440360056014000c0e070161041d032040c115210f0000118000e20540001749401c8844da024900c503200340e050220800c28901c2c081d11203400080020008580d45100c0d03425100b158110090004201d1400501e07590f001d0b262030350300007001d00d24101010b070380490194a40300b4203450260b5007542c014105d25240c6012501000048015051201c0400ca954241100c000d0203000c0102440e0000c600618554401d0340b007895132190885c21558107040ad00042074480200215050007135007026030000300c9502810454050303d5010a24807400c00f40075161a01003100d152410700b00c0f01490200c01e105503501e0002e00054100860005903a05043c030406151200c07924010b0120b203105001c210882d900d04e00c003030030003c55500700f914440030400d40440083c940d4100c0c400035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 577799091 1250 577797841 577797851
    0x80a12142a1515030c0a060c060207020a06111b130209060c060403051b1f0f0e06091e0c0f1306090f020d05090f0d031a0a03140d0e1e060d 61
    0x492119201403a0040700b103100300c0382caa102d07083c041c140c0302d600b040075898105904940400c1290312407002a100301c2d0080d040142071074410342c0080c1d0b00203107960001000078803505007402055001c0c480c10700c2040ca44070550f000e441100000c0f60648a440b4076548980b079011a03000007549689080b5140d9111900603180c0618180c503018003250080075107620450b01000d0304002034000050304500f00ca141c08140c0c0c0f5a40c82c10082c5802138640e8040e40680b40362203041c2c2d407899400400805008446c050003500e00800b4824090391846102c2a450450f5400701d60702407216155203101c2c1400b00d80c2510b403a217181c0c070341800712406401241d00425002c0c0c81d16410709550012030740a08810070203070780d0070300554548449503981c070240d802000c01281c024050220f422030003a440000046644c065a26a41d00c4080000f03141851b103601c2580d940e4240302c6035841002003407103200948448ea00341568404140404107844540038010038081240c9902603500c566180c00640311139103006902404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 577800341 1250 577799091 577799113
    0x101511060a1d030301060504050405150a0303021c0305150108100f0f030c0e0415020901230a11030a081504090203030a09150309023601080a12142a 65
    0x4014030000303030030074400024010202e01d00341000c400c8a04881d40b41d43c1d445c2c02d040c141010800240000362000241150740b07100180e441e22003001c01c0300194001d4000d130000c0c2c113180901090780c82d80e41100b01d042600d0402000040010b4054100e580310b0301780380482075035417220007001800c00590802c0722000c0c0b552500050120301c40381a6400c0d61b01c2800028800c030703540e410300e820906040e01e000700410580481040c400f491035000d841001c80500d080681103040600200c2c00a00b1810009001c400000e01490031030340105040c04440d000c8001180b4001810900410b96400036004440c16020f4880d4000396a40d240c000f40c42d0305400409480d61080351142c003401c3c044092081240b0188601001f0800c18000c2c031801c00038540281a40d0b07614040d05803440148140003802c45030340d4041c2c01c0508014122030a109010703101d5200104600105418984203858400307504000b000450600c1d809002c0b1920107442c1840c0d145804442e00e000e41c11465809000c980c40e01010900c40c20b10520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 577801591 1250 577800341 577800361
    0x109050a08071505030601021b060f070c051509060d0e011409061e09070303121508060411061306080403090b210901090f0b1e070c02030f010510151106 67
    0x20211803030384a1225110f1881e50b400d84160004803403050150b04000c450300b40030411054000401d000c02046103103803400c4d130319480c0225008008207907515840400240560b0500d00c06401031103480384583d6003005401e81c0042c0d42c0d445000c003019034490701c814813245045425007105622510410004610b40f81c089101d55036804200c940c07408000c81c507051011141001105640218801c0025004450940c0c0b020b554000a0002c1000c0c02595002d000d1101e000e44016480540f40c00e401401090500b400e100c541203014124691080108000514510001c4000e0030212512400c081030b580d600d5040a0f28031608681c400c07104401c000a05ca185900e1000c561490400070910000180c0c954011103800c80e0f1000d50024102c0805c900d400340400c09040d4800e0740001d503800038000030111008070314140f000951345600410a041f04140462a05009c012054444600200014503041d03040c40315401c16441501d8078032000041070007d545c4189c0c6003500100d121408c076890b500b4100814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 577802841 1250 577801591 577801603
    0x90f17042319150309030e03030a201617031903060503010e06041208180114010504052a0f12090c0901051806100c020d03030f0e010c080c090109050a08 67
    0x901d1042c803208007044201403440e150310055807918580b4409810340c11006600409241a041c1e00f44075403040e902c05d01c0e80e01040240321641c001c3d81c034940001d00c000c4d502c00c901d00c081d511200c40c0e03801c0000c00b01d800e8190200c00404541c04403043c40380090900d00c0741421449034214000c040e0102c10364a9811f1034058010004841c02130f03008020403035285040c0b54440d07405460061140e203c0301c5804064034070403803603680c00082c125910b00c4640e0204020701c0c210f038000c1d032640d414908000e004100030301d440c3c4a0554091191001020325101e01c0710705014880c941400e41200c03a4000c12070300c02c0c81040c24186c6903440c002138600300d124208280415641c1d0340c80c02d8458880c0000b0400411107041c100c011100000c000215400345c0e44400e4100f000e14625040038030f040029503000b480240ea616150408c2442c0662800504050310315400019203440d00d80c2c000b4568103008209503c660700403400c42c1c1c0b0202c1c104009440b0006040101d4244543e030340500e030321070043e10001c241d400000c40d803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 577804091 1250 577802841 577802909
    0xc0218090606040612060504030e0d0b0702160b09010807020709020403150b040b03031b0a080d0213060e1302130905070807020d0f08040f0609080d06050a0504090f1704 74
    0x200e0700155211401c00042e0f0341c050081d15094519140c50100052164004a03045440303802c0c080e00281d0f401d00880c445400b4100306407440c0c0c0b4400140200c07590113100b1f5140701c40b004014048082d00b445026605846200380450400030f0020004055601c01d00162020b0301070359405550b110b42d6410003041d0cd000200b1040000c40c0391885070707655480d003841800000754018000c1c5d800e02061400c1407502c1c00b00c4030500c0040d0700402024400103800345000f000302c2c0c0c1d9407000044e110140840400c0721114160000c3c001d00c01713181e403015030302d5840c00c0f082941014500005039507503101c00155020700e00c4591002490b24108000d2080c410b42141c0d44170310400040e8200c607841041841d040b80c86030010910000450072000102c1c0108d404850f0802040d0301440010400d400c01f50348034502c550000040c030400c603542e0903043c0510710300180c0b0600103100490342403008408549580d541040e008200500009176440d40038084108031083c4c800402c0750380c240a5004d000c4c03c07044081130a514078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 577805341 1250 577804091 577804093
    0x130e010608030a08012105010929190f06030c0b0705100207020609090a0e07061e08041221050403090e0a0203090606011206080a1a0106020f0c100c021809 68
    0xd011807101800001d41e4150005552410207907464501c0d200c0c52194200c50003071100c0100e94000700450801d0080140840c030903d000c041286a12044005844030502c0843c01c0c420200140a844a1083d03001c1c440108070050001d401d503526020200146100c0d44010a40d40000e100010b2002080000d0400c16020b181582c08000c94400808124890000002d42c406018020f2000509203a00b40940c0120381036000550000e1102c0007600c1e20300d00d54050030000c2c5110102809180811104408a44e13003414549079a0070140e880040340c0d00495001801c07c440350900741e08500c07201d19034080780b0060f04020807280c185424020004450303800368a590030f80082c080f5848904500c212441107403c90007611454448100454000035001001405142c540c0c90210f0b0744001845106800d45c45100f032916a030742c0f4048402c100c08016030104041d508500300080055001290820501c01d08458803441c08070845810b03140282c07040d00c007a400c042160f03580d20a00d41845285400f13152000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 577806591 1250 577805341 577805351
    0x1170a0917040f09020702211c020f07140604030f0302010b011e050d150506040f0905060d170723060403031104050109091808030f071803030905120c130e01 69
    0x500c91080b4480c80c8200d511401c8200410844e031045070340a400b0b120720080071413400c2296560121043d0f1000010f21b035181d0040314100103c84186195441008854006403121200c0311b00c0290b11144244500f0a0044076031100000030f950388012500590b0303002c9101c080c60030300c80c01c00034001d0040c04952804107041007018a03805041840387d40031345580303a445524001041240c8805000000f003030580200c8440e801003000d0783c420025201510140c4a40d10b40355141000d54819540003401c038a018144040401010079800c07950041030a4558001c03580d129054a06a501c5025041c08032400b920910172100c502800868000e000758020780c3c080c40410340c1c1e8072000000b40b040b0320805010610041c0208a040c1040c2c120402c8100b40424205500003292180700041e40b00701e50496448054508000000740c10452003070a02100701c00749585603003565009000c075507080c01450301c1382030104c4403088045c0c0204401d100c0e407000501400c42e01c41d81900e1000c0a400403440240306035080c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 577807841 1250 577806591 577806623
    0x131b0902071203110702060a050c01060305010e0a11040e0c0d15020a0806180108101d0604030203030f1006052704060e100803180609030a060507120f090b0a0b01170a09 74
    0x41d0183c42e041c3e071b0010101c5103000c1d0460360a4404d03a01c291088c11081d521740f180080494401e11681c40003028100160105400c03071b16000c8541c2e5083c140e1036125070b140c4408a00300d6400005c011000140c190f5409006050a0924901500001c6a40790301c0c40e0001030307019800e0f0b41c0044607500030b41003682e400d00403400560525210a80c240604290382d0701c044550030000903240c00400410800130074101410245a51050074000d041fa800e0340941d10000610205a00305038075a42d0216100c808a600d19007005402420341c4102000d07200390303507402200000c4540364030081c808003900007001003005941c3e8104603440309070708880f01028407140c0000041d04480200840f80707000e03000081c1b50500b12400e410001240c01a995003170700341c85484200e80c00103500d40b103001e0043c8a180c84420f04040c0030000030003600c012100103a40d240c20412114005448224402d8124400e00750119041c1441c400495120300345101c4540c644003a4001c0c007168880b141d00001880d4098010203070103c0340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 577809091 1250 577807841 577807871
    0x608071a12041b05060f04170703110904140d020c0102010510060e06161703060f100c020f1201020d050f1008150a0b040204060224131b0902071203 65
    0x201c0e100414025000000540024964000703209010410300002d46540c0c2c580c0045010758100d889000380e414000541841190400803034641c2c4400380100400b1814250b40d42c005c2509a0402900e000d01d074450040340c200555103111f01c2e8603201060403200d031b12890840c025030395010034107000e0155191001180c00c07040f01d80700707160a070b5066844030741e0066200c0041c000c256200d0b00d6403111030040b2035048000a0009860b0051040301030340710503103d05107541080b00c41c0c5440c0712a070740304024101c0b500312041e07013110080580e9038040360507508a00403d000b250184a03901016a01544002514814500191300850040d079403202c02440680d80e015403070400d1724a038000d044495004207107543c440808a042c00d540a6004280481e61008204c0841d040e600a42c02100140e0001d0b038082001c50316401e00482d060030041c00c10b0b24903040207411006500020107028181c042680d03080301400b80c039640400010400c0003c115a24a240c0c2041402520f03c0d0b05010700081c10034448102c6102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 577810341 1250 577809091 577809097
    0x602130b1233150c0a0b10080a1104020c0c03030309011e060602030313050106050d24050709060309060905031818160302070218010f080f060114220608071a 69
    0xa000702d100142d281c60400b08200d00140c0c6080061402c01001902da0f010400c1c814040b4141c031441606106080050804400c000580c0220015030700500154000c2004401d0500700800c0a50740160b0b9403d4500c0581c0c28581c40d01481c03a09803000006000351090154400f034814200f002201049502d400c003100162002440b07604c0c0140e0080c001300d454099641400490648249c0c00002d8003603841c1d0114008104c0820152079100804414030030185043c0c0b020101805c0c401c0301000303030340307000c10014241141f0b90041c40105541c0720008420401a030344800c45950700b00e0100c85d11000400098140303021880e10003030290141140200003030b0b491032080b6004003a1441407400414141e00120300070f400089040e0391007d0410362000d2055103030280720f40600707181c01d51210404e00706425240b410f905044c202c509039000d440100030001d1056180243d40c6d0040700d00e03241c2c5441d589005021b1402e4414905462464200000348000001813020111340700d418140b5a00303c048452005980 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 577811591 1250 577810341 577810411
    0x5131403030906090d05010c170a090c0308090103060911030405010605010c2609181f03030207090f020415050a03050a05040b2a0c0102040f0e130602130b12 69
    0x250050103203149a02d0910f002d003c0b14500546807800840054440c603095440c0b0113002404075400b44542d80704041001040c1750710150703a0f4401d02080c150b65030744190402c05031001414001d0081080c0103a41e01c250081c40007400d1a070000d100b040156003401d01d450344103403005c40d242d41c80d003000040c0300d501400407800001d40042100b14001040750b080c01600d2001e962070010300701e00300b101d140d890341d8032703820b082c0b50f512203215016582c41c0600c0880503a40c40c10004550401c2842800c0001907030020b004801d690001c1d030082004911141060049d000f203811141000c15525a0801035580c0480a000f81d071005075024099915030221300e8048540503035003c0d054010047c000341110250849880191a510304540345890400c034840929810412091304a030b5000141084a04215803070080038080311040742c43c1c00e0414a0414852410b4107030020191a004200c20003400000481a002802ca41a10aa07150101400ca03d100081210114005101b05d0291910902e100c030310a41c1003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 577812841 1250 577811591 577811593
    0x1290f09190504080904140f0a0b1e0d120f03050f10150210051003050c03010e030a11072402010c03091502090411070b01030308011721070b0705131403 67
    0x9151440c00c01d40078040040c403d5a1102c0100240b28680d1a20b226030b10102c001405844103e040556040900034409491749201a080c030441e0006a5a121080401144490a03061035002c410010444524031284050000710219003c00c0046400c541e50107502d440c03c3d0b8040288c0d6a4142c0c080d001e114081c4c450b488003c0d4880b405221044145013000003215640c012070301d1080643c00240c05a070003c0317825000c44400740302c0410030008204032110382c3d100214000d02098809104a55590050000034010002c40c007520110004062049601800c42188000d0206080b0310440c6e5070711480d05040f100640c0780c030300c481c0800d62091203940c88540d80142200501184c0d40040406034200480e6250311031758802e8044141d060210080c41c01038420034601d0020362540c1006040100140d00c40c60b07841d080215151428000810840c4a40d02ca400d4181041346190b241c100480c041d02c0030050180c40110b0074441c44070741200c06401c001440508410600e616004035207896403615a0035601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 577814091 1250 577812841 577812871
    0xf06130e06040f03360503010902100c02180901140f13020105030720070311010206010b030c0d0e030c0a0c120507150507120c0b060402040302031c0201290f09 70
    0x1c2c0030b0104070a0f07802c0c041e20f45120460b00c076003d054880203040103401d000e481c510740c248400c100312009880040c00c04070000c000b1700d00b103900402c800d1030301c001d89202000b070502240b804540d198031641184002c2624103021a241c103044607030090500c0710242c51141c200900003035480b40d52100c1c15100e0082c1c40e00126128210382d00644041e04003601d00030902043c03040000842c003451400003040c9104600400440e8594241960811048800d090464101ea4014056080d10500703ca07004603070081066034400c08464000f00070400d005001ca05400006005020f0301d600203000100c49000711a00302c07440d9502c00c44044150100e00c0c0c020b000d500101010040200450b50501c6404114140391b0b02d4000f09558400c4030b1000301001001003001d11041d86c082c840313007001300d07541300105071000c510341425500002da0781d0440c400391109654183c3c00116180f4800c2d040380b07201c03e440e9020a0040b0701c0030460107003c110030111190151215032548405490820300c810700030181400c03030304a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 577815341 1250 577814091 577814093
    0x3030c020909030412030e13020c06130503090618040522080c19030c050609121821031c02131a0f040320121c03060b030f06130e0604 59
    0x4220703000140305403182c2c0014040012065050085032040380c2c881da6420400e10b03803a00420100028040f003089001780305001000000344006070b1190046080c207400449140d49162952540c0315a1418039040080031686141c0702014114022490a00711400d0101d90f8a1421800080400790141c0f40390055061105011410100040a5000240301030300e00e071084d015010400040540011000502c42190b88400e000d800d0101c240c0003140080a0261840c10325480806c60003100e0217680c0d4150700347c50700340c240d540e040c04000e880c2c2c1003e42840c80c0c0c1c20303003040c9103a1079402a440c48505580301c1c58800c04c1c0011603100b2143c001003000c00f0301c00280d0510001045040299070442e01d0080204842c4800308010740182c8005c1d0b00c00c14040c5104480d2013107520f012030401c44c0290040740c2d0107982c41d601c81c20102d00021001c03041d400d40039400350820401c0340940820303400340c0c0c0d441500109001c2070f03580c103200c128841e14003564405c00400d5038540000484d0710310f11000740590080c01c0410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 577816591 1250 577815341 577815349
    0x1050c090103020d0b0a060806030f0f0c130e0a1b05060306061210030f05072402060f06010513090204080d05190302090409060c0305150102010c050f090111100203011e03030c02 78
    0x40384e403a481000049100442000c0317880c00d0a0b41e001400440d0707a400c04c1001e646420031450a0ba00c88071700103012072700f145d90074040c0d80316601c1e40c4003031144c1c0d4511070052122440b580a1810400020215400b203c810305194019880940001640c4001e80401140904103207040f00c0c05486c6c003508103450100800c641c0080c0d880090700b500c04400c0300e80400408120554840c2c1001d42c0240e0150201900c2c2c0140e9840c5411045111042043c4102c20803d42a03008603819a01c09a0304815080315a12100100e45a124449180c400c40f98a40700c081003d2030b241c1d01800c141c0d44c0f03076000c42e506001803130802c2d917082c0524620302e15603c0e03405050144062290300a06019a005440800d1050486c0d0ba05000d881141b9a00740001e56148100010b4000f4804a4810741400780020411104d200e0f0000b0598450201c0c100ca4000c400114841176904c140c4110442441580c181c580c42800010716501940c02071081d0341c440c0348084000b58126040c8116001120350588a80303d01521503800c1c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 577817841 1250 577816591 577816597
    0x6050303031815040809090708060f0f031f09050c060306061b150c0c0c0f0a03022101060b0a0f0314010e1509181020130315050106030b010201050c09010302 69
    0x1000070b80100002081c410800743c21140c0100d20800c01140c4400188050024030b5400515007020841c0031814030805858070481055011030540750380c00d2095280c404285002c100d120b482d40c0340c0c0761080c1e40e424185443d030311481045200390b0548140d0010042000b985010a448a41c1c1c80700d010080c00903c5001c0c400302888007001c1c1010345100e4810640c03007441c040c05c104c489250441c40083c0c0402c182c2c6e028803000c1000d03c8202d86e82d1041e07004400204102c0b510b43c4c00000c0c090042040c2d07910303010310003410718000055a0002480000c0e1a03440040d465000f412030312010500200e112040303a8041d000d080d82641c84017001411680c0381c1400c0c500034010150000d8200f0300c500402d08940d84400c031042e40b10310318940c0600d90f2025075880740762400502c041415810b41c542b04c9456a17501c00102489180a110460315895507201c05110144220381e50008041403003000409a060346290032240c12201c2541f000c001007000d581c016801c1c0c0300704845424a0b07003000c11100049601030307405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 577819091 1250 577817841 577817881
    0x105090c090c1b0307060c020d08013b10080d0f2f1e100509070b210124020a0c090203071103040e040615030302070e04060b091e0702010605030303 65
    0x602c0300000014030f03d582580d2001100b80c40090b21000c814a14a80412550f0300080c840e181041856240400c01c000484d41040c0d900c00080c0ca03551802034a40e941c1440c030303108500c10b0302c0f00441d50601902641c1041b9161240d01ca19004064410f85814040c80031f4400c00184d545921a0022410041e15901d900d00100e02001c0d29103010f1070004c4440030880300c1e0580c1c40041d1180304205c0750100c900d2401c4007621000500600304400c201500c10041803c4003251800d2800a845070340020006240001c1c110a02c0c1ca8400b0900000170020f4480c008100459213108100c214101451012a01e45181e50070182ca0201c010300f0400868130365070b0056074010f40d03610b01180e00c0d00300345446c01d0441d40164040705a50403000c0910050201071300c03c0c20702c00c0541c82d0391207501901d1a43c001c0d450785400d110b1240c2c0d1201c030900103030030701031140c108006524004102c4080c030b182c000000c4196140798448084025050800035620600511a080560708010011429a550010031084c4900c1547c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 577820341 1250 577819091 577819117
    0x507150908031e01052d06091806150a1e141b1612150204090905030703030c090f0509131b060e0604180f2a020105090c090c 55
    0xc10600803a80c204081c41c0500d10700f4000710164a02c0e041002090f68040c0c00180c4104401d1048400156855100000c01e46044800e030034001d07402c10001d4014003440b01030b960042080712400708100e01050080d0b03c01d640465118880c6c41241c2c2903a51a40180040480481c0d2420b1a03501c1d40b01003214199030081440c40c0215041444001907900c0390040c988000c0720002d00a000010040144050b50740d800d50341ea440d854036450298004014103241074090030342840320010340900005601200e02500c0b07250000c1c060303000549802070b62a4408142640002c5c80c2c07104603403c3d14403a43c0c00c0402c03108440c0c0b89242c0c0d20f0030102080211751014151024010052401c1000502003002d85000b40e86003161600340d840c80c22001030298100c4844403445410104411702100764040b06a000c10700d04400300040d884101c1c0840b2000308110030109a8003c6400c4041400602c0707181d922041c0e4105a00a02a07911211403107680e9165007540715030700116800c00a400c124180f00a442803118000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 577821591 1250 577820341 577820351
    0x809130b19030507142107080313140109030507090f0905060702010c300c170a1a030a08030a0c051905040e01140915010e091302040b090403050715 65
    0x10004000380075900c480c1c8040c1110250030001d00200b484000018080c500c0084e001003640710008441a1041034204d02100c5060400740320910104040c4025114900032295100001c044000322840b2620130340202801c2d60f841c05809510810200c42107903800001005410304120f0740c01c000d040002080107009503501001804200200821030107442c140d00006018040c0c0c00f00100240b074041e107805c060017841d10034981d407001c400070003070000380c1c1340d81000852140604017151400e159001310360075425000203105060070240d20140145140704501124412a003042c107407a2070603c003000c2c00c042c4041c80003c84601040d000900001c00c9454450316101c0c410362420880240642514001a408241442074503400d0115602500c8500d151304044110300e800202c603140c0050040c560807405146041c0141d01804c41c41c00c6803800180404100d01d050b00340001c40a0351014207078400e0781010b88078a000e003400b0001c00c0c0603d80541e9401e10704501504d4420000901011511b01e4560b16 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 577822841 1250 577821591 577821611
    0x1020a021309020616030f020f06070810080a030206180115030f031709010203011a160210210f0c0c02010f0c050705040908030a05010807050616060e0708031e0403080913 75
    0x40180105c00039022008032004503401c00130182c1340210544010341d401210001e03031038807000800d681c1c000c03400e01d01b40c921a55025a4080100e480f94002d04072f600c178540f41c40d4101a00400c0c202d110302d10020800b0300740d403940da00030342c281d40700d404640440710400301303040c404129000880302c0110b003e800e140182460704191018101001c42e4030840d43e03540800140020201081c140c03000f0300b0b2610b1701ca81050400c83c01c1c4410400e01d003030002c0c0b2600e004c205003000240510300c46c400c0401c680c00003003150701a800840018062441c07038000759134903042c809000d80e8054090680da0700d4041e50303800f1000c0c402100030b03220103101c1101500d1314461401d00188540d603a0091660307c4d0310030920f180e22800c1990711a000e484040c0c2112416030402003040c860380c4c681400b07031074a1050f400b440b40c04070303201401e05030300800d03582010340098060304201060680001004002c0701a03241e10352003400765850907144c5940581d0000a06c151400c0281c0103031440c4c4210710054039a210740700000e10f8420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 577824091 1250 577822841 577822849
    0x160c03181508010612050606032701180b1b041e080601060e010e0906130b120d020a0b0a1e020901110d080a0b0109030803160915082401020a02130902 66
    0x40301550000a0b01003801400190f52002e0740550300201204284864103100000680d60f0100500c1201c224813004c1001844035009203d8a02030180b40380200140e64031f60340307200c10010800009032030045904020407906480d4100d01c04c000503421898504140c02c00c4a40e01100c08041141c14021818007004694200d052010300d0080005844204403074003d9400506100141205544914048001c0041c80c1e01c903002c0f01d8161101c0e03090005440c5a101000907042c8032400010003c600c01c010416010580028060035418000c0c90b14010a80d58040300c181901e18001001c00000b18a90708012000283c1d0040c104110050500307004582c9405c0f072040c9880304000d14840010b0909051001001203407150380c202880c00e01c3c2c1034803c44d0a58031040310305d100141c80300b0460890884d5400341180724104040c090400080f80c203107820102a4001c264000c299400d9564081c0b80400744110000c40554440b03106040c0c01400300640b8a401b000302c6500c0000540500c25203c0b00310341e0040e80c07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 577825341 1250 577824091 577824119
    0xd0501020306011106221a01090c0e01020307030926032a07080c060729100b070c18090c0806090601050a08060f0403050418020d0509030f2205060f070b160c0318 71
    0x80d4003200043c00d022b12a000802c0c02c0500800d680c1550410010113011030340c02112642a034118114030b0811508883c401030107008074541031551030001150880181014060a46c1c00041c0544410402c44c40b108029486000a2040038030561195509000d6400c00401a104060281002080445644281e948195031b002040c215101282c020004141c01000007840900155070901d8104149030366001d048040e00d004011701c0e5181c0703144841d40080240c10011070140d000d10550f06250b5030b690f02e95901d07036050760804100d000760390001c00e250408644e1102203034480303002012240c45142c841c0e509400064019020814100800700744648400004400704840620046c1d42e241541e180b4070803542c001d400e242940d00100801100d803c1081c0a5641c005054940c14828140766500c01c2a04004c40e4007103900700901140702102c143c0c0c800043c102039402042c0d54211a6601d1150204543d012000c000105130034094010200e0f200301003c501100d14a11946255902c441224000716 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 577826591 1250 577825341 577825349
    0x603100501301e0201110304080d0509031608060a05090d080103020f0a0e07020d09140d080f041d0603060a1407050c0c18190612030f0c020d0501020306011106221a01 73
    0x45040c20000307046581c1b000089909604090245060908081c219a1242c52a4075000c00f0400c0105040b000c5540500000d00030103209400d00208a543c0c0700b410362291b800b01c03000851940380c0400200e5094000c94084035040c00c0d5941c40909a00316820491810821040242c001c81c0142c40850f04003100c662090081c038444d0010700e540f0344c40b25001010b040c01b540140d00d881901e40405091901c60050440e00298010009034540c5542d074000cc640e07014a6000c6e11a400f0000c4102022a41110b076881c001d00741502520595a2201410020740c1c10110381d1041c01c030280300000ba89240f1440103046010912010b89040340300b00e07400500b11294107005110702d01c03180c0013031010801c0c054107550f1000300218000d022803403070201902049184208003400f4032aa628204011510a41c45120712641c010b0500304180c0320303800c00c14001e40040354158041010045104008140024130922810391001c0c24001320503020f81c60302d035038007652804176200c000d00f1400140b402c03034011440f800380c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 577827841 1250 577826591 577826633
    0x507020a031e0f080d0b010203120c0306030f1c03060503030915031008100e0c0907020d03051b0c0c040c210207020607020607030e01080f0103030c0b06010e0315060310050130 77
    0x80c40700e549403170212211010700b141503600400c4104058101e1080c05035020100d48891501d039511080400d0424481b103442512a00601000304031541c1d503070b90100014070081c0d80400c0207a40f1a000e141d500d10a8100040d4046001e41000380c04210003001035910098000c1007942c0c95940301c1030540f4040783c015000700c280d0749030056000000010458007c0101045802e403202b410708202c040c1d1620820b0340100c0805444d400091010b168800c00c4c01d0001d10b40b03152180d541d4222413481034031000c1c2484014803550070300b40c0300c10605205104d940c40340800035840c0507100710180300e011b0007503016400480c0c00c450244500c0002d69107980c00341c41d01034000e40781c6044000d00240014100c002c01014005a10400001800469440940640140c3c0e00821112454039004d0040c4c1e0b0400c442d401542d814820404400000401c807218540612025800c90346207480b900e07104400d40d2424080c189001c4014800d079142c8103007aa440100e0300911281e50005040c8644410b0303040456140b1203068 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 577829091 1250 577827841 577827847
    0x1005011d0417040b0d1401240309020a0b0306130e0309010315090c050301080f0a080d09020315090703110904031b0303140f040b1312031d06041208070507020a031e0f08 74
    0x71400850050011031074401c41340501b1981014440711160f0316180c1d1503c411058011000001402507000017a244c0d0024540b915250350307560680d03c654800c841c4103024450380c0750780e00d4602806028181d641110703c3c018508180703515004400078002d0094140c030100d0004400150402d183c030404000070b5440d50340fa540c96040005c01840c11a9a03000c00115a100880010205100c0c02c1528009810780101160110030b03400042c0ca08007261005e000d000c0340480900180c41d40c002402000c8034441d40e110111041034400f0840325007001c41d006004101c101c1015150880058803e40149100741000035084010346001c103000c100460b090030614411006010a1007012031426900c202e095081d100204d490b41d440210001e6088900c205140c0c48036855502800300c205248050103035041110540d00e02406c00c0b4401d4040031082c500861195008207010b1840344ec21225000d8008e401e00c1006807841d03440500d1101f60261090a41140f45024000074600c4910361488901070b03a04245c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 577830341 1250 577829091 577829107
    0x90c030b0a060f020307060902120d0509011215030b09120304060b1513140307030f11010e09040f03050d0b060a03091b12170f0c07081005011d0417040b 67
    0x191403120380d00b200007403105880c80d8801d284e80c00802c44540c1580801d020842d486c0c00d1002c1400512955000f112034000c1580c0c2c20202c55102c0040e0154031002d98500c0c040080b0310074501308441c2400180381e02ca106036030050003c500300300704051300201c1f0b920444030301000145218816804c2610215044d40e00c0e40c1c0c0c40e281c3c910740300303545028a6101c0f007205031603c0b01c04001c002c8246d04501c11380c001c2c0c0104440300311140c1d0b000d00c40803005541200031010316040e245044140040d0702c810b11070108801206c020340e541028040d503481030303034822400c2040d044e487c3c405540b290050440110125100e0503008400d1315141c000e00000c444a8178041444221450010040b82100105d81d00c116118041042a00540413240b4075643d0480c0600f07144c036181e00b0100401c0d1144220740c80c1d01e600700081ca83e4104000042c88411107c90a05a40c500401801c0305c0c41074843c20311440c00080c080010000244840707441440e081807080d200100007181c2141340078090f80180d44018032150000c0b071469 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 577831591 1250 577830341 577830349
    0x50d050d02010f060e160219060b041b020a1104090804060f03110c1e0304090207150605030303060d02040b03071a04090e190803130f08030402182a04090c030b 70
    0x3403500311403c09000d0700341401c0e000103e14400a00c6480c00d0902510540c041d10700030301c040e20755402c00b400f1401440040c0d050000240c810000c0301402140f6040c903045038041030250701d02d5004107a50180003a4101038036031400d61b084032852154425a05c0043c0400201a000100000c1075261907409030707444014400782c01c5034203030000c03203640c14420030003421040c102240c40007008070403040310150010b554140c14990300803030b0003049407240f0002d07030f040c01d0107180000201602282501130011503152800e16850b80015560ba0360006003a03030411005180a41040d00c41040250440700520781d1420035040e4603603110380c42180d401c0c0001d010f00c9801a18001c00610340c8421000b0103000703016007448001c0c02580300e8080c0c03803080044041440ca01c00752400e050003030342290301c980a00340350f402c180301c00350700c180d030102e1040c18001844509031610000c49407184910100d80354648030282450461421221100c0440e48002c02c00420450035901c20300030208025a400503012408070180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 577832841 1250 577831591 577831601
    0x30c020d0201141f0b0409140a06030201120b0f10081501082a160809041a180603010b0a0e06011403101a0927100b03041209050d050d0201 61
    0x200d011641491080c854aa02c1d1802e0140c10580240c248201c0c07200c51060304111200507008401d0100001600142d0f01c0f0303058100c000f0341c1c5070403410781059881e0820100100c0e6014407009001c140f14509580b40b02607a40e00c50910110702404040b0b40301030325000905001031120041c8080741c1c2160034006500c990307482e0b078401c0090a0074400031a0804201e0254480198444401034080018800000e038105030306440410100220f11100307a0940c0c034205050703410000c4070a015a140c50b0310320414140040d0398a2041d1000350541e024045e10001d03644035400000e00c0c02d505036482d050781ca03015480e407003d12002803559600e030000505126000400c40c04030911900b0b402e05051080c400c1d0608860304c450200c40c1c144441e5401c02d00000c0d4030380320902401803016808204411528a8000460038090f000914004081c28941d50754903180d800c01c1e194015040c0d50001400020b002824038081840e4144940c00d080300303a00d96450004056481001003181c5580004d016004c000e5024094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 577834091 1250 577832841 577832863
    0x2091c031107090903080a0c02010b0d050a0b131104092618010c0c0e04022d0f04060b180409080a0c1a0103030e0f0d05101e02070b010e09150106030c02 67
    0x4188a00e0120f81c45c02408000080c2040000c20354030084c1e06c94040c000d500090f540701002c3c0c20b1000240d00c9040158446004160958981c1000d5000410005450416001c450340c0300e14002c6110402400303000080c00300100c04c466849040d0811508413408070794020580030341500c0d031940e440d80c400e00c0001d00a03085149d01c4c1031004009205000a16080070441581d039005100036646e80c541c00001d1800024101481100c413582101015508200e045180d2a20080c1c80c0412031592107414030044a066208404020406020f0303403510700031803000c0c02145400104045401e003100d03218410b05521038201c0b640400c11003080081000b003e8541d56010b0440c401c1c44010030f40c91030b14064204035070100110302c80e111032410030009540d0300c030300000c09c15000b8003201d101d0f900d8240d42000400c4c0d0380e14980c0c09000f403400343c04004110782c002c4800403a44080314180603440c081182408120183c5550b2090140107070f40d9001d0782107003140304e000381200d5030701103000000004007905246603404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 577835341 1250 577834091 577834109
    0x307150203060f240a08071704021f0e030111040e010b03061807110a0309060e040e070e2203030b090c031519051806010206160c0602091c031107 64
    0x4101c581da80b500c40f08004100107507400d56241e00111400b000c000c41c4003d4113503e4520105454148aa00c455202d20a42d901c3d00c65002c9004420000254810102e400952000c201070010104607041c011810300314003541401c2c22100680f000103425500803001d110110a00400e0130403030300c40c94030110341c010400c400a00d8910b04011000c201d06000b030004091030010f02001040d1564030a901c08180d5000c0300007500c44211441c9001000c1040500c24000040c2041d003107104103142501c80c0da9407810100004265003450001b0f18030341034a00600b0035041100d81610341d0402512001c40c0c2c20418866540001c00841c20700401905440185c0704071407030030003881004807442c980920340c80300440460345070810010380c829140b850039a0382c0190741c02a184950540c405c075003103280207000c0c0c1400d8081d510240d0758400240b1280800000c840002070002d4060b0700407a145a00400c02840041c11070185038981c866000003803041e048044001405d00000300450701c4083c00403d001e424102c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 577836591 1250 577835341 577835347
    0x7060c080103030c03030209060d1a030601091116020d141006060e01020c0f130c030912020307170a09091418030307120e070302091f05030c0a1203170903071502 71
    0x10b20003d210034119032004040c5a0300040010b080d9503589d00313580d10741c4c54480c018080a0b560341445000d00c00403c240600900ca10030001c14000aa80510b442d10045a0001400c1481c121003140ea2401011400d0341c005502c02c0c082c60100d1203501e08100342d0414103000b4800941c0090b02c0008030b4100703034000c000b002107050428007240e82c0451200b85101d400c60345ca011145107240001c4443c1100c07005182c40c649042401d136072050301600703c4c4510070f0180240807600c000c0340ca401c1c0d03224460004005c003032026100e0300c0b0b48000c2d12400178005050840c6800c1900c103440380440f008548400e101242050f12200400c420520782a001c9081e4150580180d4114200328034060091041503000786c10309611001c12610703810082200388011900244401d25909040191069009000340c003015005480e82010409050000c0d400e83d90000290078664041e103011303405c000c0c005440310304a003003080d5001900681c370320501d0340c58010201c00d0080d558604070340c0b42c5604050300307030200500702c14018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 577837841 1250 577836591 577836593
    0x91401060e01300e0d0e13020403020609100c050102040306090b0619141305010902040618050303090409050a0c060e040f0b06031807030f03080420101808060c07060c080103 76
    0x360710300d5110360502c0c40b0141251400040303602c1c0030313140c031043c908038074801c0001c90044076038071514400b40000c0940e0010201007185045602344d200c1c03400040c1d0171920030010245d40c0d003482004514000a249030420404d45a9500e6500f60780c0071f079000b5140300f91504081c40510400c005403e030410011184060003906100c0a201c0c050203500c80c21030440030a0036441036944928110542301460043d0030040d9607100c45c0101c0080d0042e006450000d55206d01c25444c15100d81914030035210020000c40c2886403600070040601000e101c2140e04e80188640c040004011155880180a0b151642c0314190300003010300c01203a03508a41c2000e00750034682c804401d81c40710801c40c3c1c1c00842d12002c0010f4042003223105840e0a85541c00285a484241c0c611700905a0110010f030050b81b1506103c1c9803000a4107a03e8000d26412540c954001080c1115800c414000c400c880c084602944005015a507a40782550038400c08450507980000001210000c0041c01e1061030340c82412814106015411 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 577839091 1250 577837841 577837877
    0x2a080708010311030330180c13020702030a0606090e0c0d080c030c030a050c070905400b101203080a020d0b0603011502010c0305070c0813091401060e01 67
    0x2040c400900643c50018445055840a000316051082d910a6a8201c200140c0820102c0003041172000b440b180c5020201d8403a88140001900d0070121170010141010715604002d008440c0502c0210300d0360b403c02600b00161002e0056140d264000c0c44000b40c007503d0280f040090329905c2009402e00d40085642c10b480b59511482502e00c20741201196440706414140c1624612030003000003001c2c803001c59520005940440101540f880c2c8801707440001c1d41ea9404942640c07401e80710443c00c0141946103a400789030181c00c0f5400140c038050300103175100c184900e20861000301036086e1051800a000c0120007600180c2d50700060180d1604660102c180ba140103014603000380007d8103407900041c25803c0000981c004054801004054965a507925a680300c0024076006440c409942000e031603d03081802031251600c100000d465101071710059660700301040d4044030b642106c1d042000300201d01c1001c1c900c02e50403418055401119294104000509405481440f09040114a2085e084078201c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 577840341 1250 577839091 577839107
    0x2103030709240c061401030f0c050415090f09020436030207120f021005121501120b041407031e110906031509091c080618090a062a0807 60
    0x2154a011500c0f16000d282100c007030600c20504d408500c920348008024405032914040301944104080c9090701c0e5100148420380d04a004810345569100c0401c1000500310f81011008495201000540a9a95001130100c90500d07120a041380302e000381590481c0d0b200789c000c6440055402d286540e00070b055070000e688a0440c040c3c1107d100f40080e003403040040001c05040c4682c5e00511038a141c1c100f50b6001410f54108004240103055540c02283c00c101c2503148a00c031350321040e52001d030203142403640807001e0316418100c5504540e4909560005100d840d801500a505954020031500011b100d05441500101c0702e110304540b80c440c0304d042c00d007041d80c2140d024910580303a0a0303ca41e07400096140d40000d41700e00c584c104030700d1070801141441c040752034010050110340324034445520480856400c0c50031039035150070200705500c0244444e42a88100c2c0d010f00c440c0100d03007a404c115683c09069036811000d01900c100e440c0802c45020f501000141854400d42c64100b504c0d16103000000d0180c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 577841591 1250 577840341 577840409
    0xe10180501050f0f180906010509010906050f0c030c0f240f0c090d03030b01030507110307020d0c1205070302040c050306240d020a050c210f092103030709 68
    0x100b00050018448010725003592200c8a1004580381c56426440d00e031035400303900030005032080c0e0911000840540c09142070741d00a00c0d06079904807015041003002d9900d58080c0d071440d0340c006010b0004a800c103004000900c851030703000f0b002d0038051280005003031800040d040070f4a40d401d481403507000c136000d124a00503844044045100e80c20380b550447d2101901c00c404030542c02904100d0500c09041e0507800100c0b00910030380e810411036441727a40841d10042ca00714551001d42081000901600c0c00c407a0102000d4051149801d01c1561103c848000b003030b005c00c0444554200c001e04106500e410322401c43e400040c1d0034040d20b1881c1c42c41c00201100d5641c80c4485003000840c060703548604444041e1216054029401c40d500d03c25032070080e00c1500142030608551060070129008074090448101c402560070150f14102400008604190f406c4010f0b0b180c0c009145044030412584c0441114a101050310b010b96582c0c1402c15000f482e407100e942001d016941034004048014a002c41801d01c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 577842841 1250 577841591 577841597
    0x172503050403090308030c0703181514090916030f0c050702010f090803130e0a0209060a050d0b0604030f14071a0d0908030f18011416020a020d030e10180501 69
    0x1564491a0640f00041140c101820300900801002008a0210300816486000c4d40310a0310440083c80c0c3c40c3c0c03031403c0e903020b0114001e80300c10540b491180281c1e03803020316030a1042d040341081080ca020680d280411500d9030b103070440030b2131200d0039680c0500c42d0442146001c80240580b02d0348100c050203a2245440080c100511545210f0307050348200004005808e202c0705481c0d0f950100c12007412120f41e540030701c080c10800c0401080402c40e00744201d601948014011508150202c0415201b40c0c03c6401265450f42d100d206a400c140e49480c0284080c1d44214540c1a42c6140b41c00c2640004030b007030b4001030b2264488030341808040d41c5083d080340c0da000c100485503070391100c0c1505600940040c04000b00f9102001c01070000002135081006d00c1503400080c600309110004110074281c0745603405480c985100c080105003000d125a11040d12810b42d801200d60344680d9501003a00304038502c405600040c10f2518081d5149404015480e4802d10703403500806101005d4600d2401880c10311800d818 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 577844091 1250 577842841 577842851
    0xf080603010207060e0706020f0c10140c060109090c0e040201140f0c0703080c010e030a05190306050d030c1101110303011e0f180c111c0201020d0606172503 69
    0x16555094046070603641d80b000090183c400c02d0118290790384003074000c01000d400b030544445550a00051000e41400b0001e0080301c1d0302134051002d079070020440090300c4401004211501c804402003120a00070900020001410202400c00d006003595139044009240111000e100141c3e82c0040c41c140c4224640000c156074502000b49900c00788145a0045281c0c00307420000424400100c1c0035110081c0c2c414024810040504212501d03840b4a440c0e207400b04405000d00070820704200c3c5030318405205801c00250580c0c0780d00005007564618076044001800c0144448108004071011440d201c5007030030680702ca460102c18040c1c03640014003521070f01e14a06410900140050899140140b00d059450718483d0784502008913010089020000f102c0e003080551000c0c103201e42481240300d45075001401400c80540701d40b6800120f00704104046640a1210604000f9103124110003441103803240c024041140111540100e002130014443c0c0070340d08100c503110300000d40b51381c0600f8441d02d03000031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 577845341 1250 577844091 577844101
    0x11401050703080c0d090317160504090e0c090c0d06050906030a1e14060a05150a09020717040807050111060421050706090b0702010e070b0414131a1e010f08 69
    0xf4140c080c1703000300e2441c1402d042c0311105154000f10070640a00c4400660a4107a0b40e076640ca01007070b003040311008000b0703401300803c00520300e59600010180c0050b20a4030014040400082c4000600744c462007001040095501c0c0700c11210300c1510014501a92101c01924052002a455941000000d46103140c80c041e07944880f000c00c49002c1481d030b40171075031306181c0300c2c00344480d41e0300c2004680004c503072407034100490381503c90204010080f00b4020310185016003041180006074101c03a0701107070252440706040392031841c62806000580100b82c024420030340740c01c000504a8810061006098020301d003400081100003104210240000c8200c91021302c50850490b4148204200580018a00058141003000d0100507a00580b0180d00900020117003010003603e54040c1c0c07040c601c07002c4003000200800700290648124110005046404820700c4490400a81e00c5000310814100350320340c0c3c11101403410b0098001e500700c441c246002c03120031301d10010b88040107850086e0b00380032480700007503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 577846591 1250 577845341 577845361
    0x80f0f040b03090a03170c090d051603080910140708300a05160206010303030515180103050d090b0306060702060d0c02150105060a090905040f0506011d01140105070308 74
    0x290042207098071060b80c918000000c1d0351180c2e000d0303c0032000940c1c6c01451980e140204880c05010720605204d00c2c0c5080c2c40c0004000032385644201c1100c10380110b9200300b0b401108001d003100114003c0744030668814031401082600420040d070702007440403e109002c142080c0d00291810140d005120650701c0c0003000300c213020140d51440d80c3c843d40d6160310542d00c0444240600c02d0040004190921442d110401016900482004c220b0300507030100e401003010074842c0d04015046400550300b07490300d86a000100d116020f141d11030741500291070004100300314003005821040e4905292000c003180c00d06400d40034621028000301d11480700882c0071400e66848204940d40310108030f0b01044015400c4801a4444402079065540d51040c00f00000e81c605011080380e1a680c200e07529502d0050078180e80314010800034100f65005012048000002001000868040c0031600c940f0070b1409208400e400304084141c10802802d49d150148034041c2e60403c003621065545400c1c0103403c0c0d41e03401da400d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 577847841 1250 577846591 577846597
    0x7030c0806240703050403170705060f1b120411040501080a0803040302071d09010f0507020a06050c1603020f060a0c1e031b111c0c021005040815061804080f0f 70
    0x302d1545030008840c0c04041c0c021000340201c920880da0892a024005c003882e0722402122000740054100000140c0c1740c41200046961000e81e401940c0384005a10010000c1c94011089040c02590300c4024042880031149080f54500401c1700e040c030596050001c05915101180c1c0b0060600101001103003c260080c02030402030070102d07076800b0030380c00806c8805e2142002074861600c21f503c1d00d102840000354a004440c41481e06400920040d0310b07550304d050060900a0040c400301c682445120a03480741d90103c2d425460085e402401d11030841c101960078894058184107490349042c100907846600314800c03c50b00f201c0ba4102c40300c0c0c4012803c0039005801c94076024a1080311201d07411411035005064206400c040c0403c0711400030404910606410079024090040307154000d0140052500940c02e412425841c9030842c10b2942e2840701c02e250450001000740c207814050304000341401d0030900d000030341030341c0344014882d07003441d460f0340348544283c4400c1c15245100061070f2080541640403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 577849091 1250 577847841 577847899
    0xa080304031419061e0b0603130f15020306092203030209040b03100e19051509120313110613060e030106050613090608030403200f0d0302060f07030c0806 68
    0xb01c40142c0058030300b0314001c01d00a1004480d60700c5140041d11021014800c2114006c00908100e2442d00c420b090140d140da074905040302c1c0b0f011208074100026040b00031501444c407400401607102c1c246942002050070004264242458042d003403419901011122900d1060300f50030b006030760740303d0100801c0240c9101440c0ea9007520880c0d2030103103244d03040e60110490912681c203a500c001c0c0b0342c106c090780d0b031043c0200241c056407121125540b1102c402c41c9482e001442c0741c0403128003c143c50a440c41d560411107030000503003071294100060200300d1a0b41c0c84603603011104185444068038540100300c4d1b1300e0255004000c00181c502500b40c400358081005401c004110644690b858a038a45220303810380107900e030060910760700140d0904000152020390303900000c0c2c01c8001c035210040a9500b00710f41c0d400c0e54003110070000020030383c031900302e03264007140294050300c001e10313019600e85041e803030103094081003521782040a0340701070340007504d280c01c150202c58642c00500c0c070801c90705001e100140c0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 577850341 1250 577849091 577849123
    0x110d140316050f0d0e1318050f070902030c1219060b0d0b01050c030301120f020a090c0806010513060809150702060103030f090f0b1b071d01050a0803040314 69
    0x140e01c85000400c00480110710344100100c565002040b40d40540b59005519004041007101c0081c404514010304c0078903040042c00c40c000f80b01d802e9041d2450011101000c1500e07683c04c00b0380083c05800003406103c01a000700b9400b50300d1801d116403201d203644502c01e60300041a2106001c01e140f40380790703204462030048000041c04115240e4407401801c0e070200c0000418a03150140400301c65001e070701555442c0307400801071411607191488080417480300c2601291046c00500c2c1c5680181e541c80341d040b014000c000400900125602c80203004010042e06190502000340300c801454050759614606517a40e03440c14520031b484110186103442c10035082103032404d156100f0081035503400120350b81264025035521a41001c076843c16a4100b80601545005039000038090207046240c0c1e004041c400c0030321011195500401c10490f09020954000c0c0404103414103144050b140050a080c0c058807080f500014003e1130017030469900d11480c40700a04820aa840b2000012024001000c1e041c031600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 577851591 1250 577850341 577850347
    0x9030206030925060315120b22062405060306010521041a130b010e040f050703032309090a0509030408161703090a0605090a05060f07050106050904110d1403 69
    0x804807912180d2070b130045a000034645030482c1d001202c0c1040c858200c4a04020481e11410280c03202081d4040040101400800341c403400305c2d60407000711400805500918000410000e00320034030b08032901143c01904410705201091144c0e5503007d003200d4200e0741c02d00f40281c0d42c1801441e000c500e0801550048890041c4404010504c081c0020174038500c007002c00f61958569035500c102c06501c00c45440540083e503500010302ca26100c81e050203800a018441d00f41c11002e540d0f0f00d407450f06000303400c100e00080c4809107414001c5030031a0080281c140180c98642400c90810204031207002c01000a1490740c1c82e080481c45091007801290050301c4048290351050302542403172090300303406109a04028009402040d4251008015141d050034018490f041315450003108850385e401c0450241d500c01d003400400030701603480000404000da4020340c0140c64520030304001d800c490442d0300040c02030700c80000304400a4a20541000881001c442d4028425228107101c0300c400d018924189082c8800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 577852841 1250 577851591 577851643
    0x15200304060b030f032712031b0601060c0510051f121e03021c030618050a150303020d050d0b1c06151d09010e03070311010c0f090302060309 62
    0x1c2c0c201c1e03030240310207404480004141c206659aa40700d0812408240100c4440004040d8000120007182d80700050000705a01d104060301c03070455125104203840940f1031117402c10b8140007406981c5c010511802c1010542050b0f44560741c86988100d1b02881f0b466803003000a040060302d403180361900007140420302c001c6440340b000941f0348100c01030035629142c000c0303ca02e50704005070814852080d41940035080003903000b03c1c1c1d0030790303500112201810f06840e094041002101942e0301d0072610b009420110759414000090300c101c99100d031065201409414042c80425000076030703080074280e6407a0032a51f07201c0035000c060050500407055540156001c002001440720096008003e0780505d0b01080003034243c3c5254070100549126103026990450600c0c0daa214110301090307032021103040045402c0480f41f41c8a419940000c60403004160310345d4100c00100002d00c10030a0350350030350801403d940c1c0d11242c0a80303941c031640300003482034500000143d80314509000307040b0742744d04038000c02400c4902 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 577854091 1250 577852841 577852853
    0x15061311030f010e3105100c0e1906210513020108131707020127030314040e0a0e031c06090b010519230c0303010f06020a15200304 58
    0x20507a0001101d511507400890315404260246010382c0310072a052481d40c00400d03180980d402e410b0200400c5000d100c41110108205000119100d0180d19000408d04446c01000e001c150381008101d00841c0c28285800009000101100c192101414204007108078000103504603184180701ca1191414039050100c0c0e07040f0905060701c2d061007600c980c0391a40da0039030714006030b09419101400443c07081146076002e02d03a40c001000ca560044c9000c40036440d18990041020354014456011103481000820038160300079440c10079226041c400c240740078608480c507405000c0180242c100b1a54548401d0b403013003420022070340c5c0c0c3d038071074010300c0c803800a13010fa068000d00051040a0120b410402180c00961040701201c29800b51418483e41c0400244011502c59520240c11468514000c0c140004056003030090003441541400843c0c0d20b60404021003000101544104190341c44110201c0020310002401da00d1070700203210009901d078449140c0c200d540c000c00312050785400e0000600042c460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 577855341 1250 577854091 577854097
    0x30709110405010305180c09180109080c0616021b0607062a0509180612070902070c1403100911060a020703020a0b12041104060b0c010b150a0215061311 67
    0x26090301c003001780e656224060210300d80154160742e07840d00419000b80052806d011001d400c0134410741d035404a0200c01c0102c0b800c54180390802d13202404042500c102864080200740e51145440400008000003c100070b50356603041c810740340c1d0030000c214100d0310301c0c0c039071070280c0d28096040f00d801d00c1a0b0b0b40c04141c400c8450345800c00050800c03810001c13024144d0150702180c540601c090448038070018103070741440e0000c10180205030f10080280e00b41c0c54101007001941c028202036680140c0e142c21500d40450b02d039016070301406004c4c0c01c8050784140d47c1d4010401a042409048020507101014074008030701c2690050703440d504c007101045451300c4980c0000e149042e03d100f6584903588640b103900c1c3d491240525a02854164600c3c400640003900c2c07500381c1c59075594054400300c0c000b610b0713041c2d108498200e04650300d5070f60b5440581c0c3d8284e2420758800c03503681a005441030300c0e007003101800944030130707103050724011402d0b803140410b40c04c0c1c441d00030195081e00342da0b00030001c0e580c00521401c400c1e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 577856591 1250 577855341 577855349
    0xa020916020c01021c050705070e010305150105090f0c0a03091e06050f060604180b0d0b16030614120c0a171e07060e03010b0405010305070513020f03150307091104 72
    0x845116044803030b950001808141500d03034281c5201240116400450386c0f6803003660102c805011b45a0001881c402c40012140030b58491005041101980b0400100e071060503030020344120211424004440c0d2200d08132500102d030645c42d90394034004c0c0300065014000381c0304018000309280804600351000c1c08134803071420303100340001d000f81e0701d40400700520a007003a100340f41d1040703003084200111180c00c440c4c00400168800081140012a80015081034001c0f50944200d00300400700103a501c1e141080c01516505418200442804c014003071800300300c107040c0c0501680039414115040d004c10441140e00d000020302e80b8864680740c401a4a510f1119600580a4801c0304104807142c141184550001580e800050926900d04207003180c0e40c90031420613a405558643c1591000c0c0c0311030240c0350185000700000c5c400c061524040c041407000c00000c1e0319019106100801d0a2061001100c3d0410469403001030001c3d0100c0000c1c2c1030012a5005101035490a82400000381c103940180040f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 577857841 1250 577856591 577856593
    0x70b0a021c020c0c010507020a0f0e0406060533070204020304110a06090303120f0b100e0306090102091e01110307050106030c17060a0c030608030a1701050f0a0306050402030a02091602 81
    0x8080e500c5a000180c1c0030f40099070b41c5907080508a40015440754020300141c90004100c0b40046544010600702408550001780d00001980100014803209000d107100420b002c0d182c80009203c400c086200540300301c1e02c241e04000003407104c90040c4901e4000e40b110541c00400841d9a07003003e14208034160701c2128064001c0e1523081c2e0001d400c2d400b03a1021012240c140d125505101c1c50040380c00c000f0044a400311045580d0b0703600e8012140c40300190121800d049840d1440c104100f10b04051030304038000c000942981c010032419400b5150a01d50900f02543c200034500400c440800588415000800b450310074803000c518841404815044807003181d004480c03032112030351140e82100341c416030f03a0000e6240340c0c01a07011401c600019803260021020b14500020ba07140c807050400d04540c4001d20300c41c006007540c40300622010007103507064014441101c026911070300c1c090109201c10050b210151a40e07907240c000a0a64400340720f08844168020820800da103080283c5107245c4050380260b42c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 577859091 1250 577857841 577857877
    0x1c0e010804140d0507020a05030d1d0102070f140108010e130f022803120302070b04140715090801112d130906030308060907090504090c0b0301060801050913020114070305070b0a02 79
    0xa804d000c254500964800d584507056206402d8030012f1720400c90341030b80d04521074100002036940c907000c02c040c081c0c0315000307046840c941c0b2000010300300d4406802c03400310001e250003408242e0650710402c0310000ea0200075441c8884042c000540007158035101d20200076001c0b5000314075820040f0f02002940d100d900001c0d004083d0a03002c804a00940740014586c4010601041c0455230781040b941c003d2880208680d001e0740c8480b04041e503690741c80011008121980018440300d41c0c2170164601413030303150b500b4a0030030105a001c80000c01480c08000301c80b40d1100c01c49986608004222080032140d5140c480b810307a65420700d40c00403c1a0b01c019400a401d40c40072441034030f0000c58190240705c83e07980b900142410101000010045501e0803900004007400003d200311500015500a1445449030155076150200340100f40c80004c01c0c41481d19842800080107030703049050291154149114035455042c1850207482c140b00e6000098a40c5001c4000c00444c549250010060001541c0c40094 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 577860341 1250 577859091 577859099
    0x13171b0f07060206011211031f0b030f030403060c1101060303120c02060f01030b070306080f060405010b060307090b1b03070b0403030606050414040b010323091c0e010804140d0507020a 81
    0x80c0301c1829000d041d0060b0020001044914a180410120b0754010f500b1442c030907119500181c548103400c00e61200154407405030f4442107a040c0b01d02c00381004103030064400c0740220b20180c3e8030391290f800003c10581d920742d0214030032403003186400c80f5000820000c200240d22030401610803504021a68589420074079a0004180302040c020b001d00f0b000c420395520360b42160360301104190010003000805a841600140c80c44081100240c3c000205014001c14249414102d0a50b81160f400b01c0c0550410030178400040e074000d020303c088400c2c000e0019124500142807081c01586001c00314103501c00450703058180301d4120990f034003551180d2001c00c100c5a80d41c02c103072481d000e18850f02405400c28031107a01f06040c41e03004140c035642d05240008604c240802541011180b0303000700442e1440800400144240030810454802600002d41d1040c55062070014020844048200c1c100200303040410f0801030f40f200058130801403c1d054480140311220000c01a400c6080c05038400c2400c044005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 577861591 1250 577860341 577860343
    0xc0706060f12170d060e090607020307031b1e06020a0206010801061404090f060e06070e0f0630090c04060512030f130e0a0204030308061813171b0f 65
    0x8030448941e02c04808001c0c105072070309101c51a000000c40d45282041185400b0540e062041101901c0f05074041c2c02a0b040c8690380c6450103400401100555004005d03280c00300790410240d140e00340928000064654480c6000355203c00c41c5015200003c4041810004001c00f903005428848125070856030160303a10041c035402da910324450b229015010303817101d08860800d50003940481d40914407442d000c040a544200440d00c1c8081201001e80000e03061002042c0d01020251620308110740c1c0c4080700132090001641c2d8402d405203260b9100540b02e8154141d502c881d100a00710400003c061640d291281001c2d0300c13404c1002441d44181e00d0035001160b649024000d034815542802d00071400d0500c0c28a101d80d00b903005070200159142d000c0710010b46558802c0c95140b003420b011201503103d42c55850040c10740c4d94040d02c0e02d44200c1703104150344252404030241d00e5018107034813200c000301100d0303040c00c802c0d41d5107080036180c11385400141008082c004040c1081e144a12104903103050701810825 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 577862841 1250 577861591 577861619
    0xa0305060405070804120c051c03090201110304050105040e090a050d020c010e03060c0f0f1b070302040c0c02090f13061b021204030308060907050c01021812070b0f03070905090c070606 81
    0x8000342c8031b0201620303d040c0318680e00c0d96507a1140301242d41e02d480f01c1002c2010501c0c030142043c0000d03154031005045580c0286c1c40148204600011400c1504180010308540224015401c034100010300240300e0102c100083c42e883e54000b41556151031071040020340300c1080444650200f01c00c070f001d626060800058041c881d00391408092304007280c0820000680e40702441e5810500802e10030701500c28003c0041c0e0403950030740e6008021481c07852040c8030549a40445041c10300588450200240e1101044107900801c0082e1130034031a6200300e28140030226a600140200d0310f001041e1501e20280700c0003483d0000e4a030202c0300000805c1c80014000e1040b40001000200c0d21404a03240f420541111600b00001d414175a0a01000100700303800ca8101c6503072507544c1c27002203e091704141890300741040e42030b0700a00a04503650400e5903000d602c0c0704401a41c162504004009489207114002c2031014240050299600e424000c114202c0d50300f00d0401a5402881d15100040c0071100841c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 577864091 1250 577862841 577862843
    0x50a110412060f0b030717060a060311090406110f1209160e0402030307080d0c0e03010204050d0f1e0f03030b060a0e09040c1a1305040603230102040b0a0305060405070804 75
    0x10408580890b5a402001e07056900c0d40c88491a1541882c400584e000d110b04009000e0481e00c4130f44110109142c11f16061b40a00640c0c00b052414105001250f20390294500e800802d60396101d96844500e0300e89c00070220000c04490940001c210490b5908005004110040e0b800d031401041d6214490f8080d01c48070030a610b1041035800c8102049494100d868040d4064002000c0d24100321440d01e03141c009600100b0404003103591012070f54400c0c0d410410700034400340c00390003c500b814141008601c00f4980744101410b80110406074000308812103030081604c03002070200c40090071492810b110b448800f0402180842d04100c0c00c2d100b681858400e683d1020310650711030305000c0300c84c802d000300c401d8050801e07039035031704d1061002c100410000d00d00d000f0032010490003030341c69140b40c40c0340c040c1c0c00c0e10390081442181403000408c041205101000816104a21016071542e4401811802441a54802c6000b032030045416401d46030154410ba100301c0c400eaa0a000b9a9100641121000d5045074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 577865341 1250 577864091 577864109
    0x20c030a1223040609050a06060509160801170109021002281703090c030a24020f0d02030c0418052205060f070207050d050309030d020601080c0607170706050a1104 72
    0x980b19500420080c41190080c1c010705001502e00072a480d0581043d59400c0c040e1015074845c10100071508001048942c001400804001d030440350100081038000c041c4600c8076402d200e030701c001850710029404600c0c400e0f801032000c0c0204d0b121000c06911482404040d5001d4020246e02d1040d529542c00c0c8400050390015086203202c3c400321078207045030005015034055104030a100300590700c04000811245024600210090003078002c0d14144040110340ea0810a005022801c0c01c0907a0805488210076101c10140c3c8917074032410f032010700d03000d181e10101e0400142101d031000c04026902030360007501e00741444101c80c0f841100b1051180b1040500400303c2d806140020000080501c0380c0d82c0056071032054900729555035000601c02401d02c0010703103d0b0f400004016072649000c100d00803001115002074030540d854158450380b101107040d0114001e03d40046d5840401c9540c403410304d681003814001589454103403c1040040030100c1d901d012043c908010241070ba4030a0050300c00b255030303d40c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 577866591 1250 577865341 577865381
    0xc0e04031403150415050301060503031c0903050f121015080a0b04020d0207050601090f0e0601120203030d050c0903011d190203010b0a080604050d140304030f1101020c030a12 77
    0x6a40c0740c80341d80c0024040d000419540741c95080301e58a40c01100300640c8004400c0341c8030340c200802c040c2110320903803115101c0d501c1049008895a00b440d01000140d080c410000307147e190303506066416200d01c2d541c40c0703201100000c11200044845109501440710a40d641c81c500d501c5480701e61250005804400109460340001200001c19801049103250301070005800d0a56107400ac030160b03000490100c5da80d401620040c08682450311070540f540071442030a02a14000001346515a4410b00420502030f000c1d403862000d540b07007041240d15141808208000c289402e05c144a19504a544424802e500b0942d03112902808500f002d000403182038003500300c100c1c034500d000302c401c00c080c40c00300c3c2c155489000c030f0561030751843d03120310080c503851001d04040d00c7c141c906075080c00300d021580011702c0300c611908c004900c00740090301d610542c5820f0400c1c8400b0360382000d9910080740e61445d07249600009020450340e07804009003100240036201c003030b2060032002186050361906000c030700c440c00c811 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 577867841 1250 577866591 577866617
    0x20c10140904110c0307061103040807080c0322080f060c0301090f060e07020703020a0902180f0d0f0321020c0a0f1704090506120c090408090a210c0e0403 68
    0x90001d1942040007440010f4400c2c001d400100941c2045221aa96400125996060103464000e080840000e00070080c41c604e400d1b900c0314094018004e014140642c0860901407000c401c104482100c1a003040d44901581c04081442c050580c0f0302448159015001d4600511000026101c0c016501130424a0a680c20070708850014210401080001500c1315400078640300a01450b40c005c058560180215038118010300000d95400c0e484103040e54030400c05441a2002496010802202111034070000c5003682c0000ea0240b0306403501501242c1c079a110041010703000010008002c240000d0a00c5141010408904030301544d0402a0702d03800c00320b070032400101d401c4650031840d44102411a540800d24000d611107402980162070352961f10000d10403246401c1c1032000c034070401039000307040e4060b224000c95840d0001800080c075103000458410016a1140300b1800076045013403a46022900ca0f803c800c2400a01e5402035441903103034134000c90350b409918980b5100c0c2c1e4058072110103103582 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 577869091 1250 577867841 577867877
    0x11b02010c0b130c080105010509100308040504020f09180a0b0a1202090901060b130501030609050402010f0806150a210e0303010e07031103130501110a200c0d03020d020c10 76
    0x2004142012403c2c2500c8010b000138a189050800b40200000000380380d030603c001c0c44150000a444034007d941071810420008545c4004c89050340c109a40140e00c0d0b134a080a1803ea6009481104d80d0104242c000c0b4108001290700e03032445003000c5442405064650b0341480b0440101d80662495050101c8140c009400c0c0140303415003000183c0000500300d95039100515060300305040403d40010b00e850708020030341c3c0c14000e0b075010b04184182040719082c50340c00030b41001025200541403203241c0c40064030541e070384072a54454072000302c3d00540d20500e013080201898040107010300c003108070b0400406c1d14180381c451804400b00c0000110300d5070f401c1030000f0f040154020614003c0649445000211038107101c00755001c1c0b0b0099454184540302458214290b480b07103100300c42100700c14403000c0640e41d80560318204d13030a10401c205c0e1750481c40410050400803044005908801201440700801d40d0000d2000401c030150360a80301d041e05440200203130140c03400034443c00590006142c17440491 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 577870341 1250 577869091 577869113
    0xc03040b1e160b06150412111207031b030b04081b1606110c01080a110c190215030103150216140d170405250308040801060302011b02010c 61
    0x400d80300000c680301540c08a04a10b0b900007000c8400142c10340b50300d8001c00c010701900e90f41140c03049a05119101c8030748042c9003203001e1403103514000000000c031541400f04101c80101e5000c80500340071680c40061460310340d904410310084a50603e08060100d050003030048002c2600d501c60f0000c81c4035126619180708a40222403842414109075159032010001007061803048822901c05200c100c0c40c010001d0f228010786142c0c2d1075240c01c0001c060320300c3ea07845070b503441c3d0002c00204001852044441c030050140100d61480c40980b00b1450404440300000c401c58202c0b9200720b40340d40c001c0c9908030740f0100d140030070710000b0000c0c00f9880d4a0240f1499640141c072000c02d4820400b14a540d00380c03540c15028101b91001d040c1d070741000180300f0481e68080701050020440b424020030609050b5507042e65441c804941d4860906075215800c00c0d00c03080c8034002d00458005040704d480ba42c44000482c000c0c01c45220032401f155511588034155119003a02c10003081d0141c427400c0040c1426122610304803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 577871591 1250 577870341 577870357
    0x40f0e07090b070308011401030513020108070c05010e03042c04031b0605250201090c0306050702010b12010204050103050f01030b060f03070b070f020307060503060a0b090109150305060103110c03040b 88
    0x1500400b140b0b112804014000403402680c80500d154501054082d007002c146d44410304060034407040028400804038111031441e82840c02205a58600d01e0450b0030501d0348200400079403d020100c8441d14000020300300355403140c0e03900a20318034084400740200c3d0491140c8400c3e45001c030001400b0902403c0c1e0b20012400e41591007201c00b0383d656442c070131584200c2d001c00400440111141000d1910000c004c140c64060000b00500764480d2a044841c01c52444010300d1a6220000211100c0c400e4000b000f0402014012245040c84003105c80d010303401500801c2e00191610780025045007520301642c0c102c94100355175078000e480d010b003400f840c192060b015030782503c40d41000052600844d00201115030007215005580d015901c101030030220309500c004100f043c01c1c4140440c0e50750314035682c000c407641d0800042c0e480c00e031800107a80c82e00f6160720500011001d1004403441e281c140c0c0110b4401e0340266000c1100038244a01484d2501a1062010301c0781d000348003c0c003400c840d44009003081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 577872841 1250 577871591 577871597
    0xa0f0605070c1805040b0109060f03080d06080d020a0318050906100c0b010b070b1b0a050d0905150f0901061a0c0a021e031c02100515040c0203040f0b040f0e07 70
    0x840e140c24500441c14180c0502c3d0004650f40e008000601400070440c6001d49050071003402558900042c3c0e85408103a40405400b01c0000a9144202100d603407110004014803c2034800440a500000e919841000019030219070130030500701c0800c44414980040e244000e0148405031100001c2c0009124070380000b006002e642140000811710460015000740600e44100d42e0301c0b0b40303600d00240e0346032000d410b0007070140084241c0d0101d0103900f020344560160300c0ca0199140c0e90600d20101c041c00444101414030700600d103a074100584074060240c458880c92543d040b080c2c42c0c00d061a0308031017035403040c20131410f8401425000c0d001108028441c04070783e10700f200c200800e00d0b000075100011400c41c40380b0f10064000051000c0c01c1c1404841505c00292010359015140d100c0d0184d1910801c1c1a0b01c0d04a0b40c2e01c0f400218804c000b5503c2260a0340c0140c800c00101004d0a4060741d02e074020700485d000701c03034100d400151030342d4100121010384860201880102740341448048210702c01414103024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 577874091 1250 577872841 577872863
    0xa12030207140d020d02010902030c04020903100f02090429150d05010b090f01050322020d080a0206060901050f180a091712180a0201210c17060a0f060507 68
    0x116812455a4420b040342030b000e40100c0a0484000e45404a001e00c00030075641010400b1000d60b07408031307078401c0c9507078151800769a07003494200003810410034020001041c1d144c000c141740c0b4038810340d000e8011b0000c207031000c103d407043e1040d04c4103141341d01040c3c6200d040f108100080190403c92100c180320381c0d5440c80d01c0e081a0f1a9503141c010348100340c000c1403086402003441e0b03a0724940620b1b00510381c1002e090152540c209141c0060701c1803800202d00c041010f0901811046441b40c501c02075413a900460000d07214040c80b00700a440d05000e8400c2440340c0c503040300104051801000c2050507000050102d10000072a01407200419001080c5844e0660b4a802800200d2000c02110070081c041da01542da40b0b0301d41e006682008803024001110081085090004419002030340c5031519809081c00d10741c4580600d040301e0a804200c520b0701085082c401c0e00542590404a1020750300390a8002c1c003010383d268000c1c08a00640c82c8036030b102409181d102041210302410080030031500410900e41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 577875341 1250 577874091 577874093
    0xc031f090e060a1406031908040e040818031b210a120906030203011202040b220903020601050d1a041a15030624060a18060e01080c03090a12030207 65
    0x821140750000d81a5190010410004503107560b01c10040510081d82c40d00650742855408a59035001017140c2080050118041e6014402143c00b560300030071200c0d0b0190740e180740c20300d01080e19030403260414801400000e408280c918022445800c21503995241c00c19408000c41007200301c4441a4464580c008220a0604010b901380f00040405004071030141403111a010000e002904540c441c41c200351048c8014810700ca1500748801201342c04075800304103913840c403000918242000304044051000c00c1c2d10800100d035503030400009079019400756131043c0c3e614001d07c00c9200750000014400c0740c2402070040500f0290803150740080c000d5801d4005407074091801c1c10308801c02d0313444d9840c4215090143c0345501d4100302d40c9a10010f480301824040a900d40c103141d400d81c402d15002d102c0c032008140e0622503446134042a40a00e0719480104441c0d566a01c050002c04960110354006890030002a00044016080703c6c044c1100360014200000c054480d003180301c0109141004046d02000004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 577876591 1250 577875341 577875359
    0xd021c0e1201060b0318010b03030a1d040510050f062802030715051017072105010f050a0b06040e0601030f020d05102103020312130512031e0c031f 65
    0x30280406a054580e2801d061002c003c450074031b5040b0409583c186186024152008000e82d41d8860540c10811280e0b4000d0220b1071801803081c1100390007c0c41c2600f01306500f409031401008491f001d680e25042d00c0030080c244102846078011a01ca590a0902829800c1215145060403000b4500c140c0c4d08001883e502c034191150304056a503421a00e84044c01480365015030500020901c0c00c6820080650451003161916400d03c9085c1090010400d984d09400e92801709034451540000208240c03031054a0080c01054140e460044640c50000304840c2804d12030100d030103498041202c030940c1e40e110001140603021542403005001d0302801076000314145400b07124090282d090382d00807400e00301001c05245217a480c0301800c0d241280b11a10300440d4022040758650396201003049040d64401c044035213043c2c0e60303403c0100103129004001210b550090007440c01049503044000d140305181d2185212013100351502580e41e00200b001c20000b07e041071315400500d001d404c11441603940d0321448 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 577877697 1106 577876591 577876601
    0x21031b08070905181005060a050d0c030f02030c030612030f07030e0a0806090313080c011d011818050a02070c2d060e030d021c0e1201 59
    0x124070000e01c02c104000190201800d9624141004452003000c01400c6442410266442c039022806250040844010b0640e568900d802c05480c44c00d1600185480340030074041c1030b030700d20711a40100d205001440c4a20400d041e825100c1c078082c0c05012900b4222104502c86400c100100a80b811600080e1402907806140c21700544030741d10045608860b1681040e0068032070340003040341410001008144035500304002e64a03880d690710f41642d40b610054a810302064880c2e1403004000014011034600f0f082c1450b10401150320541905040034003500103006610750940049039503140c1d40038054220150342000c40c980340c813031b49a601c40b24905020362411034402a8198a0b61701e50140810748114121000421172075807210003820f030140400f00140a800342040045025001203004004902603c4103000d8060040d80101c0d18011403291803035001000300c00d5000160001d10074 = true := by decide +kernel

theorem cover : BRFrame.Cov 577697841 577877697 := by
  have h0 := BRFrame.cov_init 577697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 577697841 ≤ n) (h2 : n < 577877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
