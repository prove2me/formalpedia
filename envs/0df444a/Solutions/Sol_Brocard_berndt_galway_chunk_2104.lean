-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:25.966803+00:00
-- url     : https://prove2.me/submissions/6e7583b4-285e-4f22-bdbf-a1a88c948a18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 378237410 ≤ n < 378417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 378238660 1250 378237410 378237443
    0x8072a181d010e0c010f021906230a09120c05030913150305010501080f0703120311090a090504020a0e2a0c030408150121030806040f18050606090601020703 69
    0x400501c20381c08020309501c2d060302058148008a40c03004465000e89550104000307000c41241c5e1070411600b1100072284c0d004845000034a640c01c8840148604032400d001241440c04001c80500140d524849007540c0d11144c50802460200c40130700012107003400040d13140e898131101d407a44a944505882008590110322407200c8552299101400d9907070064a0b2303540764501306001b003000f8040c00c03040303104104036039031a400002162170035a075202d03440004400414a050b0702408002e0802d0031482014400c5141035240c50400b4402400c1411010170700b410240144810602c02e908540ea50b83c0c600800c00c907103804d42900e600c401c01c0605901e110b094040c0855034503d8050484400510b000001f800a205076000035400b042c8168514000b020343da030b0b00d00308004c09034480c04000b5030344130b2441c0707000100c0e01030707800f0b9540041e0152000c6840e02c6c807084010116501983c405001d400b14118500610408006403588100f0a580082c01400c180700040d640d052207110007015900040305448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 378239910 1250 378238660 378238691
    0x4030b09010e010c0e1f05040e070e0303030a060603050a050c090609060d0504080703020706081b0309010b101806050310050f0118090603170304030807180308072a18 73
    0x5000d802c4000082000e41c5a80300010040710604900c64031440f00c0125400c10b07002d002002900b6030116480301442c251612003603040f401802040716041c08887c12075580941c0f41400154070500c480790000403c981031003400303001c50340301509519520b40b0b06001c000030f4900090881f0001001126a2502c40d01540001509441034a580712002c6040030140030400181c1c1303001e0000c0c140310707400742c031000c980380c110803911803404481b10f1000400350072204030001000340007142c021503814000f161580300c00340400d43c2d41c0c0c090348014001072451103200710300c00c000000300300280010345842480c41c2840f2a061800089070700600f4400c080c102141c24050b80102c5040701d90503032800d40803d15698506240b4014401440292034400c4001801c08030f90b822a8101c900c00c80d030540742c100d2107403501d0100300c03000410b030381c3e003142040401c52000c008030350410302415500e8441e0b100c081c14181000c0031148034010202c2c18604803201c00fa000d111024426001d0010540060720000701d41800490b0324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 378241160 1250 378239910 378239921
    0xc0d1209020d14070614030f072f07090605061b010b09040c050a0605160b07211508010608070b13090c030c08090f07060c020d050f070311010206040804030b0901 71
    0x29840032901c4400c0b010410701c10400181c03000140180c0e88500da66110664114541c2c016942e0b510008000051035090202011a0060030780e00d00350014040c0e6181c49000d003090700062500d6003414600c1ca07106200100700c604050000300304240810380c03800000c2440c9000c0c0703452401260341e850040c1900700f4025071000d20802e5004006801608150070900d03a4528240074450180d80486004244140902e0480e07020510784603102c03100e40c000d51204c81c4421000b030100c02c100001e115040103188000240c0024500000d10000303480490902d052381340581640c804800760341002000c0296000c00b0801c28115100001103a641c0c002121403c0400710700d503006a0980d03440c00c035040b010150f069001002614032b43d00c80001c1350310f030140101e90b00e4002c48060b40c11640113007401e01540d03124451403d200d510143c0750103074400050f51380d942807080c070744000c0505601c101c2e02042030001c643e0803012003000c01c0c0098070403170400e500c8070204e0b8456400b010780101021808185104401d5215 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 378242410 1250 378241160 378241163
    0x3180111073c03030615090e06010908010f060806160504061b1703071b0c090e1504110108011e0b0702060702030a2405240315090c04110c0d1209 64
    0x804200c280781181c5226402d050b20700b0b40000c2d140c80f90109504106e41c800b144e170f20045848220341a07141c48903000c18800c004010504010f2a08000681070409000c1d00842c0d1142160210b403030360504040b6032410f20300608240f0f481c111803e882038402d03045822036094520302c0c42e01540d14000d10384260140c00c15614000e080801d818001c400c080000006035000c2c6c4a81d81e602840c24103c055070f464a000c1504002d0206a0001000c000e82d003d50350115140c0a074030003c0d0f030406006100b980d010098112416694911754002c82d000c02c3d0707440015240500101c2400103400b08159a07240c5d003617000f502a92000c1200000d612081d0f6940b8010303a014998002c045a00c000c20303611741780462400340d92682d03100714070b0a940401d5040031400f44138840e0f2191040813910080741d081c0148044013000c803c58041c064403a404198245500129114071014001440100014000e0104507600706040340c03011301d0b0500080e110f549010490300002907940c509004030f4448031444100400340c4150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 378243660 1250 378242410 378242483
    0x609061203160b0c0306030c01030519111206100203030109150b070309090f200702010c02030304032402071a091015051807080a0e120a050318011107 66
    0xb542c040280c09000c006000c00d128000c01100ca48858410303656a000980d043e5500d504040c410201c1948240d02090f0720840841d07580e0000c0d0003110b00c24007110341060482c040039000190101000408200d40390300490300b82d808040706010100002e460b40818003502c0201074540c8585801c4034205149140603204000c1110b03514009480c0c0a082c0400e5840307005102402c0c04000d0183c86000c0c801d00f01509440e0301100e8450110b80600d100c90342c1310781c004a0500403590409400768408202420103544150440000148806042d400e01c040d10031554809500401082c400915130700350394005042c07101d4200c104e13030301d40846d4a810606260600c101c3e0519208441042c20110300303920381220000c2d030b5070350701c25140101c408440302c07412201c00d000700d907001003c100110300603800300d140c1c00100001e4034101c006045207115203034084c030103103c0040c1c0003005011900c80d40d628110707520b41c0050000c10221065440d0001d1303d0081080180c071080b10340c0700e1280c45c002258040c585003000000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 378244910 1250 378243660 378243667
    0x4080711150c0f07120b22080a030f0213140d0209070e0f0a03170f04150824030d0c0302010213030516080c0a050f0105070c060302030a0b030c090609061203 69
    0xa070042515008611020440e208082988143c20302c041250400e0350020300b0714006a41c40c41c1c42e80500c8400c040c0010803034041008030040039206801d8880700e0144039800283d92100558002002e5030041100c2c41e9900d0b204005094110420040303044c201d49900b60350f10307800145400010041801c080c0040d4000c00e003401008072056008000c404004c1045415880e4094806c05010420115000003001c81e0703241d42c04480002d0341d01c0c020700301040d0110308103460552110032802003002c0040103000818003640901c182c041284100c01581c2c1107504a45c0909c4c0c0c0354400180e80c81a81c410028140a100303c544418140b00b901110f0405051001455030360350349103401650b44842c4491100c100316034403000701d80d054000ca41101c002c40c0003401035103401c1c20601040031000142d240c05043c840c00304200c1c8000b0307501503112001040d00b1349005881c0e01d01404d0090541d14841002e40c4603400039000204d0f140c0c0c84106883e0084001d0700d003040c242e40c0780d00100c4c2441c0840c030080142d034400071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 378246160 1250 378244910 378244939
    0xe0f040e01151a0d0b120f1f1803030b01111b01170106020a03050904141501021c08041401090b0f060a06031103160315030606050a0e0402060304080711 67
    0x15004181d240680790032100c1d0b141c0d920400d0440f2948000f070710010048080143c0d49104107150800100c0f0400203050280c078440840c5060718050041c0b10a0955400146003100b0b50102200f5022000c030090b8030500c44206280c0c0004014442004018107141d40c0b0340710001036912400604074401283d0b41111043c107000d0703800310300e100c80c0035003c140025807440622101d500d41808140c1258a180c0040100c01081c1d41d06588a0304001003454220307503a42440d00506c410f4102050145031001644004d042059000909203ca10609074180026100e664820298040c09050b8019080008001c10115041d4140e0250519030000380001c04088180a22080c1441c0f03041c1c050581100c2000d04142e0f65881170701034801040400581c030105000040000307000650003003003d50646000206a04040745424101425410603500c0d69500e4405000a040c206040f2019110140c00100da92401c0c2c0e000842c01d00c40104018a0100b02054490030060310061a81d0382e044004c19945080740c1b80d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 378247410 1250 378246160 378246163
    0x10e0102041d0c040806040f02010509181b0c28020d0309060e0306070503010e1305070810050c031b0d0608060c030604180201020d0e0120010c020706050a0c030e0f040e 74
    0x60100001e1102c070440850015520389044500303c48030318010341183e5840362202909a240144140d042c403e04200807010303517803104443d40c01985540e074448a40d08107000c040240340030a00070a80040d81c10002071230101400107119020240c2040544d80080e1480001784c0030051501c0c00941144441c0b10714000c0542004142c81611040e07510340e050210b0030420190b40f84416150b010102d6400c2005020130801c22500660040c002400341c106000c0c0c035944d691030f207100f503405030905411000c2c0c10301c2c100078a40540e079041035250740352600f0750a042c10401c20400300c900001d02c80140028207141700401c1900071034020050381d001e40b4110714003018912226801200c0c50391046280601c0c51405a4100c8110340303007207406900803e0307000f6180302d09480c10f0030303400d0020741840070b155080941c0c4014220860040ca103024004a0f01400740003000e442c041042e01f10707030103000c401e003d030684055000c04190718079070301890500340d421012804074044842c040b850541007410300058000d05c410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 378248660 1250 378247410 378247439
    0x201090308071a1f0b09190602071703030103050d080717010801091713050402180904050f010605031b091b0307090f06050f070f1419030905010c081b010e010204 71
    0xb2034410400720b5603100d07820003a1030a0303c0a0a40c1d40071980708401d110444211000d403030050800f0340901f1000c0aa403501d81d6032000c01e580803c0040c1c0c007000e4244135201c030414401780c4065030303003000314195415951455210421541243c040050000001d0030b994814842c0702e101c4800351711030080f00c0d40c490a4039070280c01da04001780c5100c0760b9000724455a6103000f049691181d05101019138443c1010100300103035104442907102c0300c80c85821044030f90340701ba4902d07000c2c620800040442d03030045071440d03081da101ca03880240f0035085400321000700d1910b80d1020421102c222022800b5a8600b49421404503800004c00800027020040009080e004800d4005841503161010402a40c0d81c50441d01445074001000e0011820b1007080b00207540e102d594040e40d4070428040c3c448085141e071482c075102010308020109811240c00c8800d02d41c121000d20301401c800c0c6071044860302c084d1038040309481403410012100400000d02e05a0b40c10a40c04000c2c0040c90303800a56969995214011103101c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 378249910 1250 378248660 378248693
    0x52706181602070b041404091403160b0108010203011203030e03070c06050a1707350f0f09060f042603010f0314030c1c0c0b01120b0a0908030a09020109030807 70
    0x45060401304c0c030103d464090300d04645c0c607449015005a500c1c01800b028003201d0208890300303600301402c5100084244040c1c0307155040d104911700c142e0790030304100b030100d2810785c4200b01d56441000107010b001c030f5a952800c54503425090204841c40407001d450300e18400c0d018040d102c5d130200c810100e02180e000d030080c000101c00c0c8e40da900c42c100e042d07107485d000c900056410301c020643c144071040d05a001d4503041402511041340150403400802c259000200e4129410340042c01a1001c002d41f030046c410001d50043c104500422880c40c02d41003071200c03104090006041840245080503041703440400c003075801d035010b609860722541d5581c0001c22140c500c2c0000c03200442c281c601c00000c548000240c0d010310082100030310360464220245112104008081c04c00c103c5020782d103001041101e1070b110300801d80044000e42a103201c1c2401201602d002e1300740c070030650400203644003050f262001d90307030001007105d0000368001c0390b480181e80c207945039400101000d40102d895070900aa04904080e0340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 378251160 1250 378249910 378249913
    0xf0c0f03080d0e01141302040e0102030f190506060711130c05090a050d050601030210021501080d03050106052809120506010305010518070303050f04030807110a052706181602 77
    0x3c8407103c8035509031610846000358550f00300c00042d2002581c0300c80201d00d10300290000810825800c4a01d00b179030b00448051441ea0664000c0c404480d813440d401245034000d510302004031382862000924a4810004041c1800903000030500865036941482d141001c41d0010400414a80c2800a002c80e0810b050581c86041c000b40c0014440c2006810181440da000b0068035840c1c0c02c0d6801c214444682900f910214440e891185518444140e14140a888228003c001c055140e0100a00b40c034416081a01008020301002011000c10100b8501c5d9100c0d51038140401000f064048803500503076800295101d0985d80030100b8840e000c034441d8103890241000b80410360700c5034a41d5000d100807030001e4115600240b8100007180c82200609402c13107020403140d241c155280c4418005421221050b940041c038401c4540c0c061402c02d659400a00e02643d00d0480c0070000300c081c5000b0041e0444180891200200041890766000c1c1d441d003011501c1d00880c015810500c202d00c1010601d1460300015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 378252410 1250 378251160 378251171
    0xb0c06060a140609040f0603020306010e090607050f09010e03030f0706060905090a03020d0c0f0c0e0910060503150a090204090f060605040b0f010c030c0b090c09011d040f0c0f03080d 80
    0x200c0d000044071140c02201400c010f01d03000304d1509000c01000281d5140316502d584180100059505010b50741c000d0061100f180400d040c02d15001d404c0020207800c040520000f008407180f61580403081e01c1c10315100b4202000c42704030140c0424190310038524040d41c000000501c00003046440c0c2d01c818140c0b400c6100800065558134060f503070700c50036901d0290150780421130300780c0054418120550ba5601c15148900128026a920007180b50709400541180800504000d020310301042440d014002c03640c800d2010301c0c9448003003a00c0300400d1200b400c0421522001456a040c0d035001503c1d0035901a00421040c206d80c2044d07480c04401220072504103090040004091a00d80180301d1100c000900e2000c002d001c00006441d20b0081480480074041c007060448003042403410036910542c42c2c00301901e141305c0044201700400340140c0106030301007885c0e801000007049055005602c00c1e80128800d0a6598034100034407020300980c4800709617070306c04401008018214003e806104d020420a006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 378253660 1250 378252410 378252419
    0x20d0603170304021815040903030c0f08040b071103130b0a080903120f07030b13020301060908070315020a091701142d0c13031208010501110d0807090b0c06060a 71
    0x2a0741c482079030041e5011050380384650301000b04680c6a500100d880101e40340c1d03100000e01040036512004801da0103c0d5036400c4003007905800c401c440504070100c0c5014040c1d441c01c0e90751074036440f1001d0501e008100d1962070f00c8242800810817a00b00da111201c1109091b0303500d001031801c7d503021140100c0040d100001040740b203a800001c0d00c0d0390030981941d40030180c0e82c1c000d4500d105d40000f80082c04150301d03045418807580300e2078140007068040c002c01681e25030400b41d001e0070b004500d910800065001c1c150400110f40c030048a00455100c69102599130070385100b04036542240d0350000c80404007908202c80010005500c094551650514901c8403a5110100e045015460440c840c01d50700c8000900388210207260289036021003038071009414110f092802c40034540c000e401c03c40c1d01507994200036401c81d80100c1c00a005203800d00e01008800c10200c1d500ba2200c0c40c464030401440078590201d07005c80d000d83e0304900527080c0090190b440c0d204c20409950383d858240d5019005801501c0c002c10b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 378254910 1250 378253660 378253703
    0x1508010605031f0518010f0812090607020a0e09060108060c210408160503030a110c0715020c040e031b2103061906120c181701060801020d0603 63
    0x6048414070780700d5a0555440e04586120303a840e80341102c00c140350070200460035655844001d414940c4580c3c1e010b000d5030409041000c0c00701c0d19003049040b40d010000c8407a240051070301b202c801600a851107512102d1034400b00700310400940003040d00c8600d14003003112041e000030300503040728031000c211502c0e41c03a400860649407140c1c0303041145612080c272405d08002c2c0d004039174680051142c05d089240101009820180c10b403100800c680d2600000148848440d1a005185c03069075100202e5213822400c60015a81c0e50791442402d04201401c1052000c0500a1018184148016000344001c000150456440394407240c09400285a0710441d0750b008440003440c1c2c20304050400c0ca804040341c06c1c0740c1050294200804140d880f920010340759010740442d04034280200090740b00c0305005041c0107039150136560003884030ba04000e58484c00e02c074002c1480c0d0401d0122040c4c40a02103040c0f06051846016142580220640d0743c00091070070002038440d400b01003264040c01c01c00348407980120000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378256160 1250 378254910 378254927
    0x108031c0f14090c0d030507080a120e01020c06101212090e15031605010203040b090a0306020a0305060a12020604030b07110d110c04021206040507050d0e010f1802130f0b0d080415 79
    0x20f00020824060400042c0300c4a0040083c01d09504008007180340200be86030a66128079501031260350081801c02e4003003802c101b801d411695036407001c0302250414004546c10614208050209e10580d1805d0465038003c2003103c0140c17650810b25070f11403600440040030b000405807040d0291065424140c044400c5002d42001d541c0140d024600c0c0600c0c20303440031002d412405c2056032003c19540b002001452a00c02084c0600d80e6445c0803c00745400410003050704010782c0f000410300004a01e00005988610807542520350201500c0b0480c0c075002d0080310349456200041440d4031500303c400d42010b800000c0d40c640541c084046a00f120a80c40921081e80100c80381205090122008540c036841e1541005a0225a40c648242024000c006400c00d4402c19030164800365564110380007000083c0c02001440b80d40c00c025001e0000d03007540429912171810180203070907562581c01c24189001b58000c821302990050100c2d0b2803105500341020b06a025128081e100141d030101c841e1140e0103203014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 378257410 1250 378256160 378256163
    0x2190e0622050a061b150b130917040f030b07270f060e090a09030e03030d0509010f0b010f03110d021b010506030d17040804170a02040b0102060108031c0f14090c0d 72
    0xd12810705c0440c0d4510400403400c401c05080d00307460b402c2e280d9058460794840788424651110101c5d102007035007000d1080c3d032803805566909040c100014007005060360643d10880713030710080303a0302555102c0c0800c0f21010444040810001c01c082204842603920509180c1130300c040056501c5100d5840005450600400c8805d90308000d0318400034020031440e0740007031b036074a0181c20101081c90700c08000030b0940c0d1114070302c00c00950f959010301003c00f50901c94100001e50440041040d080c600b80003034012182010380c00105500d03070074402248905103042e583c1c4540484030964840780300c05540240b444041001020325860100010000e1600142c610380c0041c1e95220000340200704100030b001070700c00030020784454604210000e50005441c00302a18400d440e006482c0318a5607104000503a03451800c00ca0440d40b1100044c8420700000c07040394108613409005030181020000c034031024210710003188401501d00780301c010500c4d0faa1466188100301c1002500e240400040c00c002034406903100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 378258660 1250 378257410 378257447
    0x10c0905220e0f19062f03060109030606080106030209100b0f07140601090e060610020d0e12060c130b030f0112030210050c190302190e0622050a06 65
    0x41081c035601c5036440714010325081c0040d02c500700104101c4a00c0d00b05100c580c01011144480c1000500c0702500c2075103c2c100303c480b2038000b490000e0340482138030a24224404070004000020034030b40e0303000e030300c05078021544110280f0030a6680d605150003070145c2d200c203078080c2550314005075400009a4803542910244003207a81030040c226151201ca401481044480305000d00d4403001100080045130300814103000c0c041140500c464103642450406000f01d030250350040001215141c022400140d40c55091401b4003a181322100001c0d00542d0128001d0000d0003000d090007051b00120009103004421480c140c411944e40d24001e40480c401261704500540800780180121070f8000b10508a0320300a1048440c00045d03000c03618104c4200340d80c103a030004000074401500c01c80302c0b8980c80ca24101d0313050031424408800048841c201a00124404002d0703400b43c1c0403410f5441e1740c183d41288408103101842a122404100452100c6004d40c1d40314450f6101c000600702c0c498120302e04118007c0300b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 378259910 1250 378258660 378258709
    0x105161b062a0f08040b2a010e07050f0109030614061f0c0b0601140a0e19030308040f08130f180506010c0209093c0607081323010c0905 60
    0xf11007100d004000707441107800c8503040100244015400d0042d03c400c00f0400c0d0084541284001d14485007030702400b0f00c85543c1d0500c0d448050001001c60084110f580a842c24500211482e004848040c0d06800050810b0302d405006101102250521441050261450b0882c00c500840c45258980c0020750032002030034603d0782a0001700380d84007040c4c0110040c101007210010214020f02035400c401003403000903012181c5d1044600e05406641d4440400300507010900c3d0864070700401508000700003a01c0850700001a0040104443c2291094400c8440202c0d49a445082e58010501c1c81d00c200442e03090b001d03105c10040b0050388691030042e00140c6030406150650340c03d0115510000b800c00070b280c0101c002d404245d24040340d01d003045906d54442191071900400e055018044030300501c23800c950106081040807030f04502420382100d000d52099080c0c00d141c0c903160300c450032003412103220888442c0340c1c10202901500001880310030342c2c8804808644490a002c886200543c1d0303051041c007000f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 378261160 1250 378259910 378259913
    0xf010801080d030f06030c030302010e0c010e0a050d05151303090906060e24030a0f140121110a0f0e1f092414030f0604050c0105161b062a 61
    0xa038820302e4a000311071350210786141d03261911042c44109610941c00750751030300c3c3c0b43d03aa004814040001038031310908041c18000104000314006814900509028513410290002071203800c00c45444000c5201d40f60007902e1030f0243c01d0101a0180c1c4a0032008646540700c0481e031094a030282c1400d88000d5a9440d406040301c20402011a50306100e00481c40c3d00d065144207002095001144907145040c40813950044604d00c1c0702c115500d404810400c11080b0f00184081c140304000203825205141045034078030042d0030f1507541840460311040e40443c2c54100002c40c0700c0c542000b142181c103034035000c41d00c0d0b9a4028100d12648000012526506800c21042c045034666a0000c035071069003840c210780e940007507030014101d002107400010503a01740c0805282c0303d140c10011400381110f060040c00e000d09140d41c44981d107142214019040c81400319004182043c1c11030f51b01c81c103035080402044400c01031100108914180d010390030003d441a1034220041402c0c2c2440900700828402203164400103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 378262410 1250 378261160 378261167
    0x9050408120c0d0c02070f0f0e0c340b071d09070215090a02040c090b0301060c080c010c17060102010908030604050405010608120a0f0e0906090a0e03070f020f010801080d 75
    0x203059000b000c205010b0204039519902c598103000040e90000c00609040400d400128100c960111007038441481e014000c404001c00d0b80c542011512a28503101c16041080440048142c8158040d681500c1004103120041c4595070107840d026030781c118100c0d100c0803c11a00c039886030b0542400d000007410310311900e00b00214003035801401031040c0d8071001c5000030116080d0780295405c0c00960f11a415000c29880c05200e14012909981805134841d441c11010f500c8502051050700c003070006801d050b00c2400030f0761003151000f4540d04000c0001620f42030029010344a006103825007e00924000b403160350051040c1009103070807098190075079a5810030130001e00001801103030155240d44000038049002c012405400040303038032898540c400c42d54010308000e81d005c0300798204200780d18100102e84030018280d41104003030704c1061140e0348810882001c0c003442166100e0522000400a051004032001640c056108440003401d1127440f02c01107a012000b8004c141251700901da402824138007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 378263660 1250 378262410 378262447
    0xa05150a0f020c130b09060904050d08060a030c0e0a060503070518090123180d0f05090a0503030a09090f0b09071803050a03030501240915031404050a0302060109050408 74
    0x280c0d01c110743d40c0351826000315445100804040700056100e2090381040d1410001e010792018040e21480d400d86096101c0342d584245080c15841800000da012440c50b40302c80b5071160284d0780228440c0c291581d01c08048491800485e420000c035864a10f01040341c0c903010412030121440284180e00059140c1c110303c90726840a0020740c3e0543d41c2e8280800390261018a0008203000092149040d19201a6868a02425801400c2c1542014503140505904400038a2584809107803803612202c140c00860410070140e00602d915201c01300320b0041c0690320000300030581307112060922403401881c200328141d07080e14404179449519440018091442526071002c0c4009211059800c81d541e9100c81d8101400e103201600000d03107032001404413062038550071750004420000911200300c2c1e218010311048450003a1f642183d03c2703d40c08410107110350405180f01d075201c202c0e903005050901e00b2694922480c1003c03000b40c02180000528407481e4800c5501c260f40101c0d4403860442e508050308038041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 378264910 1250 378263660 378263687
    0x20105090c0915040605040c09082404030c020102240114090f0103031b060504030e0a06020f15070504051e0405060d030e0f130507111923010e1b0a05150a 68
    0x117580e003400042559507401101c5007120251507040b842800c1580903030616184940e410040080a5818408940d0030507030140e000703425142c83e00f010111803004130709203051503005140c400200c0d18000c8d503042081c91000c0c12504420010380c61426010180485044100c0c1d03107002c65004000108003203070180040c0503408145030005110304c4034035070365032040310410b0720140e00140b44041d038401a804d040c060b0f035015019a00042030301b04441105540e943d464031301c244c07180000f000c3c00321b041c1c24014416078010f480010700090700200000f01040d111403040340002d1140f410500400d055041864007281c5030341d0903031768290b000401001840200004c03441407940143c0ca07400181d101c0c200d68840d0500030503440d40c4200c4000040b401080c44d005071425000a00303044040c44200145004654030545c9916242044e104061540b419005061713649003240c0c18020030b410b014184000c00403152001c0c00484162544903201d00034803000103c0c2c5140c40707040c15400c000200c0d60600030f000011a40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 378266160 1250 378264910 378264919
    0xc020c060307030908030f0604060f05130908090d050303090106060918111e0903071403030706180803011e060203030423160b0703090905060a03030c050f1b01020105090c0915 77
    0x3c1ea1340d039841d080141d01c1143c04641c400c6200d014041e02c0e1605000e000010f10301c1d10215116541840e0004000385907015610042c0740d51000030000708404e42c0b0680d245034600820711260f2001c00d041441d00d03a0f20807134000d10b240d482d014010400724061003c0e5002e641000300e031241c010202d09068402814003c81c4403616100c2403164400c003030307100818112512010103031030b51590f074004107140c035158554205d12442e0841d841d43c1c40c1942c5002064604103500084041800304c0b00e10800303036101c0340c0810050040d100000c000b240600399100741c0790b02c41c04c030001c1c121402a5501e8013240c503800265801407681e80014107603040c604985100c5440c4542400950f50a04002140185030400d15031100b95161800300301c0c4414141c000c0d10820050903000400d002a160034000600f40d45801d000040610514400c1c400900c84200505d1414101201c11165006d9903c00e0b90211080f040664134010760914000811002d000700d4103070142c01014211009070340b41c143c5070711512465180c55a800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 378267410 1250 378266160 378266171
    0x16060c020d1401111b1f18020a08030307110a02220216030f030e1f020c1207081206220209061c0203011505120601140904020d1e0c020c06030703 64
    0x42d02d6003803207182c1d05068481030701ca80d030b100303e00321520b14011114601d004542007090f9000c804002205c043c49030201e0000005242102c035121010f4094070000040d400048148020134004c0c030000080d4080c5880c1d4440313101c501c0b6034090803541d0f0704602c180203410001121000541e154141020728095003030031001b5003040c80f0044942e00c82c00c120001900016940c2900e5000d594051190403c180e40c4c10000c1c111050501d010940030103110380c4090700c22940040d41880511003808040e402020400c03000740e42d402c490a00004517006040d00381800d0610380081200d52034407002c400d551007040c20031300700c44908a2585030000c6d08440b07580e58100d001000703034007211810750031420500c02d0003620050300d95041c10900d100800c801500141800b00800c8090b100401100341d00b42e001d41e0034038054030010703041d1104001a02501011641050011a18803088801a0020f02816204103489500880c0c13221443e402d65584004560140e0010780c0c5022180c14450001d542c86070803420003180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 378268660 1250 378267410 378267443
    0xe1009030614010f0609080a0f0606050306100f050f102a060e011b0203120406090602071a15010f11030f070b010f050a060e040203072c0316060c020d 66
    0x81c2d070b8040ca6074150050400005000d03042c0c0d041c5094010b000c4924080c61a42d0500b6800f60350f550043c0c01c06044415003e0100e01040800e4000340060300340a0f0603a2050706000303440ca80203200900440c0441c0e1141500495203041c0700c049030b001d206000f401460820081c801c103036194680c41126000102e4003113400152038448291843d100c41c461a070003d000c8401000f2982141c0b0f0344a0084003c03022074200380c000b01e41c000152441c003000600500d806844d907140400052000344c038000c08182c000308208060040d903920f0310300f0380740b01d128040c0c2c010360320015541284c40c1d001c0041c0e4045108405c0c00c0c20558441e034108600c182c0064100c0389010650343c02c044194100c154115005030700e040045c046881210a03031401400252054030075981401000b408080300c4035421f5000d1035020001a4034079100c4e4500c40201c0c8800d44040c9402c1800e015825500c0310034640c0c0c00e01911800f1401c00160300b01c03035042400c48229694221003981164200528240c24110a0b49c03180800c0c0c1d0480c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 378269910 1250 378268660 378268673
    0x10e010c02030d0f0c0503010626041a06030a03120f02040902160201180605040911130303090f0e090c01030908120f010501090b0c0c1212042607060e100903 69
    0x290100d289800642d151200101c1c071605135a80300c0f40c04207603582015005a003264100301902c5c1566080e082c0009440c0c1e5040c0c14088050001c54482240d00c07114040c0f00c18401d01040402d03071191a0b039003011050b624032080c1656a034612500500240207251244091a00c0f40e001c141c10900c50720000d49401d9817242e020044c0e030008180703190001c0340761810108660b0000c0c4060321409030019080403081c540100501140924070031100542d45410384054014101c40403108079032200c80e4064013160700e03402d00a009000a025042884071415000304009001090661080740c0748401050f1403c60301c4011000781203003e01c11191010284105035003001c010250610035080d00030402540d614180c001010701640da400291031400c10488903030000070202d4101d0858406480844e031141c10740b42400d10b0040070b4402d0b100a0b980114010583c503840e807010b903141d4800005000580714401c080c407910340b02d0500c104030104102c042220500e042c4440310100040c0c0c0c5080150309a56240c9070754 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 378271160 1250 378269910 378269921
    0xd08040308040914160e0a080a0308090d1b08090307050a0b09011724242a03030f0a02070602040602010203090d0207140607060e0304080a05011a01170405010e01 71
    0x44401c0c034004581400030140c0b62040b00d4400703460f0b20700341c101c1e810b1042c642411310b10301901c600100041b801e004011034803088003420080c1403041c11118100020704009043d0030b03040d17481038103502409414044944c03256400001c1c60081e28007880d02c03140d003581c0c1c110142d4815080340d9014040c0c2d95000920340d540781107600040ca000c0e00c4041d03460010000041015141c40703400302c402980801480301c0d0341c654100d030007540b0410b030340301d0000c803811380d00040d0360074403c11800407512801031640b4491100f080082c1c040140481020781c1e0909014031315035000e0744004200d00031a44140001081c003c16034a20700d40100c0b10400040c07400c0c60300c0c0c5954044c2d03441078000c00c2c0540c0d00041840b04184040002003c03040c490b2005c0c042540c10088007018000480040d80e1141c000810181c0038014135a10003144802540f00716607407035a07244503454886494031170070352f000d518000c10f4140406c03540301e00c0c9801150503234401000031321403101000322443c0a0300940e0159030381e17080d030112040c0c248241e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 378272410 1250 378271160 378271163
    0x901080a12210c020a081819030503030415090203100e0d0e06180301020f0703080426090402160609080904110c07090903051207080106090806060901140d080403 71
    0x180820030814141a2007107124100075104121080080003a420b50032a40ca00701d403001c0c0301c404501e143c2c0c038030b2003249050b10007039014107103c0340000e41f00b01400140301c00018151044c0e80304000d1800e808040701048201d80f001401d15002080020001060a10403003681c5070800c00c0040d031820075070007191400e102420381c21000e668545101200384020407400c00150b6261038103040c40f21544000c50583d00411690707030b410356030002000146d90b40a406441d4101c01c0c400740300352070f140369081c0140852801d60342962000f1484540351404001040d10040e0001040e5140d842d0010320401c1c0002903015001c0b0420310030031004800d0001d02e0314052000240d018000c5542c50308005420002210340100d0b8980154508024070411180041a8002110380151300020203040c5405c06881c01c1c811442001050800c90081000c2170b40c1041c1c1b03444c1607803601d40e9000c0c120b5840c0c500090759100203587ea568464001c02c0100010445450003540491001e0301d0910348180b6a503c07120300b038026420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 378273660 1250 378272410 378272413
    0x4021b0f0601030c140f01030f060512010f2a080711010219030501060e0a0b0f130303020109110130020408030c0c040f050c030703051308040801020a08060405071b11090108 76
    0x10404d20a03902c00241c003403c000c00021544108650003ea82c0254030017466040c543c40396104c3d082c0d9036039a030000d07004000c080d054002e800c5541100500800c0d100c41307082a51487e000c007410780d0040038145030780350b014807001b041c0103800c0303600c2c0540d11040002c290000300001e040000101c04800e0001d09998144e4244800c21000c180c0760150640308140c000e1010055481200700e0305d591000c20f80811a12a65006999800034441c0802d003171060f00d540c0354100104800000c109581580507507609030260448440f190018001128034028110b00d1050440c0b0301031020302d035517951010202880d582e2540051416030b036004032a0844c1c01202c003100082d04409012241e60405c0d00a042403e020704204002c039113440f1642448a00000e0200001c25959900050410080d0201c4100d6682c01104407511036599400050207035200d8469000024610004640e82e410a4000e40d0700849440d1296404051030b0708450030760a640510580e01c00c0c403480702d16815030303c0c2c6d80001c5019003880c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 378274910 1250 378273660 378273673
    0x1020f071406010e060d03051818041b0b0d020a02010b030d02010614040e25030f060b041505030d11010902090108030a02070602070509061c0b0c091002010b0f04021b0f 74
    0xc1c89182405816440403031104076620420101d50303509030110350b600c0c1d8941004d94681c910802029004804600ca15401c80e00007401c0c00e90710700c0c141c14414812071140740100e11204070345289462040040c840c0b400300030300034060500010403a402521541401d0700c0005607400d41c0f1000a0301c0d103c144082d5502503507490030188130380840742108050b284010f8405014a0181c1d41c42d031035403060b11a0203070745084400040c2940303a03000d181e1554001c0d034001000e01c1c1182130070708001004002e01c80c0981d02c51032500ca24210450100300d10b107c00c584c80140a07020015035442d007a680882c5e020240505550780e84808001603030b801d10503d0107410140010361721250a10000791401c0d40c00d404c4113041d940000c030200083ea9030303030f4a50b0343d015a059610b0400d22404881089141c00310100040100c0d68078810020441c0c0c1030405440e503540111840001d05400c0081a0708075916005800e41158221a4110940c00c00307030018041031860566020b15408111002400d20301d00d480b541c3c0b400d8000c2c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 378276160 1250 378274910 378274943
    0x216060f05190506031c11160f051009050f0a0e0a020a02010b0307080a0f14030316090f05010503150d12020d3e01020c1b1e13090501020f07 62
    0xb42c2080050810149081049081c0706000a654008240428412012200c00950001c1c49035181d01c1c0c0c520194002c9620007821482c8855540e100341c040c1d1070a0440040c0005010320f0907811032204007010703440341d01a85092030103201d65080a070503070342d4000e050444005880030780c00341e290b880b0b04040000180c980d40200b10080c203440168440c5442648049000d0040c01d601060b4141c0541c2e11154000c1b84000d03030b2900b076116100100f112909404040200300c00d85401c110909a901c41d256110a141516401a1060010a400f940340061018000034800e03200c01c04c0c0f0120070880c001d00f801111041c59560025180c1e406414500603040440610803039500300c2c2c0340d850498050030200388449004c0900000042c031300349100c201e690148018641041081d8115034611000009075000c0640070007080da042c11864403602d01856030b8902a40710480880620300120034001c140741481560041c450018000d0b07600183ca5139542001411401c0300780100601d81c00740310b0342c142d1041e1900d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 378277410 1250 378276160 378276181
    0xf1c300201090b1335220f0602100f1506020d0810050d020904020103060510020a03021501060e06071b060e0f010809061303090e0405060f0901110d0216060f05 70
    0x24094500c1301010742001300000c1c8804a56400101500101c9000b140d0800c20340c1005c0106441e0450451900003600c0c603004c5400c0d58800a140c125402e4841510341d103200941c6990710502c0394900580001070403841500c8241c0045006880c51540802c1d0440c42005c400c82003400b592000b03000da0b029482c3c0010040d0051aa10342c441c0365001e20640a0b1f10300408144101024030000b40f080805400107011680280c0c0b228002d0000070301401034100c034010f4080d54881e4103a0099001d4800c6241e5508006d50500219060780c49039500c2801010b034140130b04c00c0e150000f920440b10108016889800e541d01140c3c203c004100742c0e5160500543e040c011700410901240d0b05038100f0000e0400c0000120000550030341040d241e41d580e1405e66800d007022500740342e103600800208814a030510060141c0040c0390f60260010b5100398540d0f80305c05450030308030381082d04541303614201405609400401c641c0134007040707007559401c1415a01150781c0d070070440710400302a207412030303447d070034010810350 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 378278660 1250 378277410 378277433
    0xb0607062c1207020d0312060b0a020f0f0d0507030507080a02070f0e07171803040b0c01050603160b0310050405130b0a020f030402060d090f0501050103020f1c30020109 74
    0x1407500191018600d110606070703440c45111800380c05083c0702d20451003014480d0000079401490b90f402040119140d54003031031141d010440380801441110341d10082681d01241c0541d1b107034810300040002c5a0100010303201c0340c1100400b82e0500006211201c0410201d9009100e22401580039014007410404010b002e0002d5410134190512100c0c104101260030184089005600c0740102e5140e54a00000318904404141e0125060102084c0083c5014840c00504400003410f8001e00c020b40d950010300d691103050b82d424a41c07a1030600410800f80740c0f210000e5800082c1d2807802044940c032007020400f610410399003c00c0405220080009102c0209034040d00441102010361601e01c807282c1040711400090406407181038000781c03000100020350301c070800280d0f014090148680890515500904003403109034044d4035135448400c030701e01d0a010602540303c0172011009140304103449a0849181031420a00032881e625490080903404440340240300a42d40c0c00480c00a010b803420246855 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 378279910 1250 378278660 378278741
    0x120405060c0f030a1509140a06080c010504180605120609120c0a020103110c240601080105090c0901020a02330301120305030c0421141606030b060706 66
    0x6078180210301d0144004411a9000080100d0206002044007501c491800d003580c0303d190114035118100c13543d800c283c40742e80e120750084402003040caa0b6403140c03540c8841040b409280007d0040100317001080300d009901d51110000d110004209442d5030224055040700d80300001d00303500c0001000000720042104101030300070000444c3c1044280400c55586201545009041c5515212504c0380e494640007610110744e642411140800102128082c01f0307079030740c00e84403075425441e40015119402021543c2c1283e030058001800c1d65100240c80314560060310900341103009600440015944000031411603201c1e20700c40c90606011a803084800103100903510041000c01d04c010010000c01c00c0c1e0107000710742c15007002030b5243c0d20041301130341c14403d46d00084c04075000c060310300141010000300e00032410722415200400300011910b49541e024084108965415040c2c0d041c040e2034400e401c040d030608405800c0500304141c603505c01081c0e55a0181003014022621444c0341c18105000d11885c420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 378281160 1250 378279910 378279931
    0x130f0207060f0b040c02120c030712180e0103080702060d020706050a1b091409100b03010801150605030f2202040518160b04090c050403050d02100c05040e01052412040506 75
    0x17071010a0040e46800fa4071010300c00c40103001c0b6200588070f90520440f00c20070f500c284058240e181c44031001e0f002a4101c2d1207408000783c1c541c004503603410024441810380b9000004503003001040d5080060550082d21000140b5400b403003c0c1d00015000e000d00c5010b13000440000c200c48070a030903036081c1041040f0a440c100701c6c8002c030410920f5001001c2054640b01554002c5d0301755900304441541d00385503804840c20f10070000000610a2066200010b648107a03d4480d41c010342e00c2008459a00065420007410214080410b00c445c0013501d03440311074041940c00b4003801c8202d4001130100c43c1c080341e80c00c01500c0000520f815002d4103220b00200c101d40106d0f92005541001c0400d207040c050b5014140440b50b0b40d0200c0c2510a000c1d0054400550b403100407144500030301800252601c28404c45201d00c141000d801c25500740c080c5007690141c3d001d83c0261341d0b0582c07070003080129010384660011402012810140d200c01604401030004002d08400c02c80142454500f0902d85500200400c411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 378282410 1250 378281160 378281171
    0xe09070e060301020a09030f06020403050d0804060510050f0d050c04150510020f0d0f030902090c0a03150b0d0f24170303040c03140c10021e07050f130f0207060f0b04 73
    0x5c0d01e40224248051303e0700004100c982040c103260400013449250009840e0b449840304020300160b00640941c4514800c0009101e161101003408000002c42d0249543c00b0101c94141d9a80b4180710300c0c0f100902e4010011190900d00741804a4111609058254034244070003c051065051890201c654a03040d03200400c030040c0854255900c80840788098010881d200140b0a11248a03409c2040390a030010500f59a50604460150031680b1429120000c03908000038242098804089001110701002949180c50085843c1100419443d1034600c04540d5644c00610503000d50486029403500c000000701d102c508143d111094441c1181036030141f60b20401c10000095800201e0104496010030340442003419103e4103814802d035442400e800400c849004084d2507070024400005512f5002d00c41d01649211052070345032101800703000d400003c030901044490070945c04078800c000c0d0342a000912628846120010b0740c0c418441540c40c01d4407114208032610759841000000c2104403010401d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 378283660 1250 378282410 378282427
    0x6080f030405010809010f050708160f05090d1a0903120a02070c0909030e120318121c020f030708030709050d05060103060509150108011d070806010b07020a0e09070e06030102 77
    0x2503a1049000740380c1001000e5000c500308880c2500068a4080400c40c00c1c003d500d41030f500240b0002003100d1035070081940010700c0e42058081d481e0f2100802c09655024500700c2d1a07010300c00b0401d10f40004031150300c805400150800c01c003a51a50040e00f0410207103944000910201c00c1c181d40c0074000c0aa03132740c030410507480040d000178009812282c00c81c00c00f28110045040035502c0110032901e05800142076086942c0e03001002c4028440007403809000c0710603101403000d01104a00b504c0c80f20800b40c0c040f00c01c00c803045c1c0f4420040a80078480384101e84050740c003a40c400e802c0d0f8001c000101d07520340300402407000803070704050044007900d400c0e00c10385050003250320307210f03601c44c01848003904559441d0041410b043c02480060702070b0b45070048078a9503503581d00c201c5008044644140461203002062014a42c80100c0d940c0c08070344c1042c0050100b0b034205002ca14855000041c120f0780212114000580310b203c0c0c2c0fa81500c140c02401c0034240c51071808114200c008001080184264810040c501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 378284910 1250 378283660 378283663
    0x7080309210c011803150933020c0111070501060f151b02010e061b072c060d0f060c030c020304050d0305130801050f07020d050414100909060b09030106080f 69
    0x42c000c0009103841040d40ca110f82007900b021849400140c81c18070100b684981c070300d50a40003516158491301c4144800001000c012410602c5900d01065400c4030490702d1091184a03000b420141c1208400052034500d40050b201d07865100010842e402e94580e24200701e80c3e03481080303000003007042a0001c0ca0f1a602c00c880100001e0441086e48880583c030b0300e01070156442003000d28505030703004d400144c0e104408482d95410409440c1406070030311400102040c0b00e0040c1c104100d43c0a40320140c80e1046405980301204030f0402408036800800000d2150041803020b81001595401034a000030f24503008134008083c2c0741d100d101c0c0700030355208110400813a160003241c1d00c0b8268052070105e41324007015540d44001886540601c10f103600702001c3c04190b8552114040c00b0700c120b5000c84580d000c25800c01c1c0d440c2d0281d03114049000c113542c01c24130f807603040901c2c1d0019002424a0324601042e101c010074401c9845907085059040404281044141400d200d00b03406021508000c0c4000d94520790b005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 378286160 1250 378284910 378284923
    0x2060f0c03040f05070509011211040b0109181e050402040507230d1506030516080105100507020612010603060609091103070e0625060501051207050111030c0708030921 74
    0x108030600e061900c00034130900384141000340400509100b242d51b95034601440b240c00d0080142c0f0310340048940f01c1110701d0701c1d104404001c041a115014031134a0400300ca2540f030101d1205030400c90b1a81182380964110aa0f5050501080394002840d81000c2c014081210b000030990014001210481e80b0400300c12107081400c13102c15000155120140065000a00014406511071810341c000114510303401d03030000c500c0b9040c10a00c1c00d42140d881e04046500351401e00c0741d1508100c0306010903a0781d92203403000b410000d001400e05031900c40d00030814401010240e0000c80001d5803100107100c0d85a000c88418010020003034180111102c044214401c2c0c8005040982805142c1c0d103d801e0329110741040c2e4400300400d0b01c1c1c0107011488402140c2c3c074a03541e0842150302c28503200000c1964608810790007101001100103202d240e08040042d2588145016440c20901c0b003841003075018101000b44ca4041d104100255440c0e070011400d0094107122400045e0840031120007448402e000004d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 378287410 1250 378286160 378286163
    0xc070f0605100b0708031806070509040f18110f01020c0f09060d0b0a0606030b1203031b0c0102040b0c0115230612070302130b130b0904020f0403030c0302060f0c0304 73
    0x14154503180c40d8000301c405550300c8000140e0f00881c446044c03241c1ca4028601c00c0c96941700e0492010346800100b9290201101d903000030039418044903401d03003059445442444803070100022110020124000c80c66000c080895800c113050500c0700071400d0410f00350701c21407002e0008100c2c0c56132083c001102480c0000b01e8500413030010b40021603d1703890500340941c054101c1c16180311410043c2c8800e01a108500030000400e0801c4032920981c01d14a40c4040822a240c01841c29500e448a080041d00c0c1a0315080c00c0d084002c0c004075a0a503003c0c40100010056444441e540b080021101d40c00c2d260000c0940b4030040c8040c0040001c8600c5014030100181c1c90350030b490301c00104200190081c0a290407170394510314840c04008456400d81d00034102110440c142210741075695800c01d00b580b00e40034018079001901c1c1c81c1045031015403005080b180d00018409030030300180008030707409500f00e80c1c8141c000480c0180b0751000d154042c45480c1d040180400c0d00b003500d203440700b003c90803480080d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 378288660 1250 378287410 378287423
    0xc070602070f06051e07021204060e030109171213170307050c010c030902010e090c04060e040b0315040c0b0906030402060307030213030503040501110303130f03090308210c070f 78
    0x759041000210b15462804a034070401c1004181448084400400303a5906944980e1220201062100b80001b130610150381a0140c100e03d03050800100304c0340110910b030429015901c0b260300e80300003010f002c3d561a1880f0a107910b15120940514070328041c100140c6a02111081c100e0204003003180340c814141c07940203001d100c030b6582d280e1420071211441034102c20550355103090220031030300e545074000d050414000d80c0d80070b81048481040000100065408102245040004100c441d0144040b1200080d0003040025001e1a01313020a04141c0440c12007003084007241c0c100010442200b0240c1d028180c0702c56224200188007010070000c1c0300c054070280c4901804000541c60500c250115540010003041804d00c0960b280f81969503070304107014042c04034040421100c40044000160f0740310340b081503a81d8607010030f40e4448203003000110000750104004004044007040d031040081064108140c0c1c21019040c00b6003480a0b143c10107015101c205d102001680081841d203109003a015800c500c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 378289910 1250 378288660 378288667
    0x14090108040305040306110703080a14040611040f090c2601030803130510090201020f0a1a041a0f01090c11060609180a030e040f150603050411120a020a0501080c070602 74
    0x181554113000f26400242207a0405c403c0800014951010301950b44c4683c0303802e01a5144c41140031b00351140d1006000800d00e0340e0000402144007a00450501c0401891080c83e0644404045211011a400100b0a1a00c072845034408603070080071002c0c40000a8a10341004440c2c2c007040c101040180b001424081d0040042081c0009220744000701a612a00302d03607241800300356003000f40803c1c44050340540a421821501e90801144401ca03030781e484406050b0301c90b00c4484145010a02900c15941034444400000003120706190704d50061004d80500c64441d0301d800c0c1d014055480f98011402000000c013140b42072018001500340c2c012004490484007540c4142010b082402c41643c264410710520700d06105050b0004845031100324103540c140512814015440c041c1c86091086a00d1100030381002c00c4100e209034055600701d40b05031002880c3c00c0d070310300025024600d1042c003400740e500000c4110086281c6000744400a02007030800304001d10304854555414003075004060111034000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 378291160 1250 378289910 378289913
    0x307080f09160e06010806040b0f0616082a1f020a0e0a06091a040303020a0201050d02160803160f0801090b0414130515011211031504050105070f1409010804 69
    0x902c101c44604814402440c1101c2d501c00041d40350400c04e4500501050329000810210f0400e070040c01f401c0304018241c02800e182000610201d9404460128040c10858201070002000240140f00c2c0c00604111480c3e0700a80341c06203461207260400d40d00700e5500c20740799103400780d00002605210188a0702d0042c1c0b00c40c0410000d03a981c9415130202030780203c8407280451441d4002c5100307000d6944103c805143d19108281d0080244502d01000d400740e4071441600b401503105400030441ea4010810150900ca011480e4001c0c0b0440407004913440c900110401084c804c0240482c0c0c800d00c5586460700c8420110100074001041c117000f801080d80d00c540e2480b80740e45aa0b00950400c0c00e0000184865140642c1c0105a2602004044680340034040b54984009a840715480c180d4000c0703519480c0181d51651990b0030850035440c86c513058010000142c050001010029104500660000c500d0349040c0d10b005180c101d0440c3e081060000c84407451313102c002044203a41c1c5494003800c00b0031003a00c0e103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 378292410 1250 378291160 378291163
    0x1b1303020907110706030e0c03070f14220606030f0504200a0e0906070f090e07030b27090c04180602031513020403050115060c020d0323130b0307080f09 67
    0x1000f40da40042d2040400010386540d00da032003022021106400c0d140c120021004254450f4051710074211401780700c041c184030281080c43c04001d5141700414000b0000c41740302070710300d007240e107040c03c203002c0741c1e07124030803c43c0d107815000710104c0c2c40722000108030501c0c1a5032042520403984540700028040c4507805e4900d07898541125024194000004225143c5243c0c0c1940d204c0c403c0320f0080001d0441c0303540e40901400f03920320400b62007195400c00c1059403804000c40041c80d90701c0d912640a044580c0264000021904581c43e207011245803810524004102d50718100d100c01400380524a859034402c0801d84000504800e60744c4110007590329100d80302d01c64030321070218540642c4012280520807002c24503600070011a4400d400900c4104004c4440a1201880f480340070041000e642c0340100500c0c01140c20344071a4401d04007015008096516420440d02f12070407907180a80024524803003090021866000b00513254082d4076614060400a03c0c401d0b019190061513103103000443c015440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 378293660 1250 378292410 378292427
    0x302130905010e2a030708150402030a120c021f0c150b03071d150f0d030212030106090e0603030f1c0b031204090c0207060f11150c031b1303020907 65
    0xb085030466203010405a0140001d01c180a6002d081101d13a0060381018200410b80c60104c90303800014000600000072005940c210040c0200e9050103845038100020b4403140200c1c40851260b07403081c1c4090350070301c14840e11400184075486d900c0e803407141d01c2c00e00c40c1e8481100c41300030383d11101d0191003e02107851070b40940b003030702c66040c0c1c50b010315080481d035007814980f011118500ca00c801503036074440c00710a818191500c07040b04e421840d07900364623019041c1201070350101c2c1d01ca07204a070040c4611400200c1c0c2a0001e82001e40083d03032034201081948803403100301c0e0b00441c046019500e0080d2020032501c04d41301d00051004018200e0b83c5884043c240d99200046144000d800c0c0c0f282c001e421000344034145d0045c000c03101100d1070810391000c0e80e0b10000b02e400941e09180c82c0c075072603044041c1c01a1281c800807100781403e4428412030415507458060b01c1d60103420854241d640b40c1c10b108a034255408401940c0365440e5100f8031407131f0100e8000c0c5c00880304607901a2141031554440b407078120394108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 378294910 1250 378293660 378293681
    0xd02090c1c0609021e0301051c1b06021b0a0e06151207020606010f0e0901180b15040503010c0c11090c120405070f060c05120f0c070b03041506030213090501 69
    0xb480c1c0700780042c20807042c1d001054190828503003007000c1070501941d0880c0d40820301446420007041ca40000f0005c18101c001d1880c0f41c082c1c0c0704802120560b40400b180c60030340d60403030b17001a0007461200c4c0c1d448655a038010f001e92030417159954510b081c0601044d0500d0010656441160035443c1c0d104140c802e50100c498100010720007921515084001a565200c01d03034502d80000c0415821001c01481036085075900d01c0028141e01c0a0792800002e80700103410319645030102c5588288c1580e856664602ca0768072150400301068886180400f05130840c1d4840c00c0b80c4050104200c2c01c64002040c200c1103d0560b141140c80c1c2001d07855403060b1345094001e0702000055001d0020030321050210005030389044456032200740e2261511104100c82c003040c030307080040013903024200b004801c103250000380c4154082481c419041950800541e440c0034030691000b280203900200340010701c40d520480482d03640c4800d07002d00085207980d0100710341c4061048103162042d07481c480f1004115083d00201c0500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 378296160 1250 378294910 378294967
    0xc0c040f0b03160302090c07020105030f0901020412050715080106021905070e0f04022e08060f18010315020a1e0306090203153a030212070303050a0b0d02090c 70
    0x403420f8070010101ca074102c1c08145e1007400310200207030008030004200e4980c2039040e0b4a09003035882d41081100140380240c80021203540030300010540c41d400f1130b0301064541c000d1004040302c1d4a015400815550100c801804004039040180000303500064000c4511061846040c5d0f0701880f814202c0c1002401e42010f07030044500070620402051100c070b0507005a0088458000c6480132100440d00704c8105d4000b200403e25156500c01c0c81030040c20b10551051018115071900045800000c0070019a02d642d1020005644018018406403003542002d08862038002c52401c1d004000142c450f00401c02c44801c0700720f40080d04005581b080d00480001c00300c0503825900c134202401c030700360221001d05115018800c001c003442e081440c41c01c60a00071001c8008184032149080141c88200640b09000380c0130b61188804803e500c190300c000400809020f541c001603942000c0c15441c0540e0302c4215801e104503200300c1160090b90310704181710340054111512a81d00d50004e96005808446e010180000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 378297410 1250 378296160 378296173
    0x50c03040b0d020a1206140d0f02120d12091104020705010b090a0b100e060f0912030a0305071b050d110a0c0f030b0105010503100320030a050f070b0c0c040f0b03 71
    0x70542d041d0040c0042c642507071121030244008070042c40480300144501c001014444128205070305051200c1076030907004104504002034550045803580401c00755000c840c0e03110040040305240d21035003101c110813180c403040c80301e140e5544400010540122200d40700d01d50020310041004400d40c8800d0030f400300036082c85c405142502c005002040780302d10700ca000d80e0080b0259000b071441102c0103409180c0040c032540c01d0440100b0809007a0b0010340409030400056180826903030340400281c4034280c116503000c01c00e460004402052500c1038403902c81045c071000ea0301da00140021406078003c418616000c0941c01c41041c2d032034546007845c0d4000e00008030b8180041100120303154141c01baa401600086804d13640c1e134004448900c400ca902c82411400703428280000760091540b131094030b80d608000d18580851100080c200710a021b0708486a91225a140d010400144414001031070000c2d166800c1c400b40303901d01e5488059908440c0d1165a40d489801c000e0b0b01a6071180c00440405000c0310750 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 378298660 1250 378297410 378297427
    0x60105090907020a17130b07020118031b0e070512060109271401030c0905071701090b030d05340506010b120901020a170711031303020f0907020c01050c03040b 70
    0x1100c00d813448064400e21100c2e410411800c2c0c0220455040c0030640b01200e80461a040f000c02054104074001c134101b0030140c0c2c1c250808090701c0510b5019601818180078114903086034401d525010b0b900102c2c2c032101c0d1800704915990400140c2d0700640c410f02600c10300342d40300300049480122980080e0382c0c0920000c800600401c0c504402040c180070b41c0d804000903040c4801e0511910700900c070080c0004030a4100b8030079500290860368118182c0d080424140c800f104105c20046802d07000303442d58079507905940c1c90340d242c1005901060501350800038034044000900788041c010700152540c182d0745400c01d20b424503132090401c440c840e0300035098030995610382000300390a50110090031484030b11880842c106a6041c030032564080d2490304c0d00c82c07005002030380100740005d004102e003080c45a0b401001800010602c0280000c0882c1d0003a520103c0c110b1040000c0f0002c2c0e62882805030754510704101d0300640006980314070070004d080c42c944511203034000920754410358000b0701c0c00e44004600c0d0071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 378299910 1250 378298660 378298663
    0xc05060d060b0a0f1d0a120510110c0c10050d0c09170109050706050c071a160b01050103140f010506090d0609051e011401060315090204031a13080301090506010509090702 75
    0x704c15035102e40c1c0d480480b40c0c01c2d60015010000450315107500c0584103070200040c0d82d5088242500310b12a4094a003c012040303160422075160040c2644d45460015005880c030034203001400340d6030310031200007071141d034280c1c4020f08500811803030715010b0360746151054000d0b0042c1c00a1004003001803440d260051140d80090281144800449403442244000326100d8007030030640d075420f1088002071101da494044401402810828009000c8004110700c1010b451003c1c011210715008940400c4607514250005040310300c4001d0b40782c0804e40c0d11007402040d042603041c15044074004c070303003540d00c40503150009084100302d03120013800c813460901003004112010440c0b100c40e180000c101c0c1c650a0340c040045c2d080c0c4000004c007600220206006000b480c1c003ea02070050f14050020000b170035922881640c080f03034016003007074845030070b0004202400b030001d1407055400705050102015100b440c0d41e501003240011302602c08071544680001c1c02a91141c400c0d5501c2800041405520741000c0d10301a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 378301160 1250 378299910 378299927
    0x3070c0306050106090b03060d0f021c030207050a050d0b060301022703010c03110304020904150c030b09060301110a0c1e060905061f0302060c01021908090c0307030c05060d060b0a 79
    0x460301c040c00c02000080e5140148032800450320001181c80c0755a848904004075044050350494402c2034400401001d0b88444500020b03059010400400150250801030710340107160b88003510500110341700b44600e44072458422005640b29606012a40300c07400000e029000303540341da4a160000c0c15185102081c103542c50f100c2c4000980c0200300280314808124140c1d402c00d10a02c1d01048200049001410403050b2242d03c640035408048a0015a0041c00103590300c0c02d00440009465040c0c54105291010116401c03e104170001c2080d070981c2c400e041080d0080c01424820b010005149405001c0b43c820180341ea908408401130b400a81d61504d40e00900607890b082d41e0f90b200f0140000e01c1d0040c0025a1800070314944402d04c0941d11f180c3c20000103500c42444800155000d01000c5c080c0c3c0b1001900da100442d1a0312a00643d16010725800e103084070542005119074400314080020404a0000505940042d00d1590740c41c0340400141000e408940e003d00240b0000049a6140d10b9212004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 378302410 1250 378301160 378301163
    0xc030c0f03040e0a050708010b0d0908030705131401020a0b0c040306020f03010602010c0c0b060f010201090f140f01050c090d11150307090f05090a0e100606090306050703021c0b010302070503070c03 87
    0x743c0e03206449421820046400c1201c2c060301043c1000c0040c01702c23003004000307400e00314110000030454888035603802072660802c7c0c4a40303000c41c1011440c19030840351003406402600040d07955203940160500000d46d0395000701c102a00d03032154400802c28000c041012103028680220b030a65484002c01c951182d00e0b402481a28015481c1c8031102004c14854180f00c0c006170342210480c00310303803210410801241c0344c00040905566880b154080029020f003000f40d04940101a845503065100358000d090606501c0d8507807041e450402048130b0154200c040e200003000c00d592140c0d401c01c251902e5071490b05554003456100300b200902c0081210024001e5210340d913203650b1a802c4c03a80c2c603049803504001600910b0b9104000e040050580c184a80c030a42c2d45400000882e5a401c1c0308070714450441d1000d13001100082c0d1007040500a0140a008030f542004191804501d4000801d41d60b01c0720002e80900c40c103405e51240202c07940f503072107501640c20054001c001e503581c4a081e0b00d000c9560441c1d5100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 378303660 1250 378302410 378302429
    0x804030309060e1f02070e090307020103060506120109110c030c1018030819060b070503090916020a02010f11011d010b03011b050702060403060606020a0b01090c050f0c030c0f0304 79
    0x40442c24510882c0003901c180d20140003104090f8104201d01c0c1e840b0a502c1518086200c1d6450000d50203007000900341c096400400550b5803407516000040a8442c10b80010380260030030002030540413559081c084c1101c00d004000140c0c174099440e61412072003100c503000118800404c07110101e81002c00d03684041e44161200708000e4100c0035001c0f6020a03003140c00707404a601c3d80c00080300600350300e0b8181c450402d1031200003502e90b15007441000542104d4410384d0356a0021400742214149445450381259a6025104c406140075070020f40d01ca01e40180241080800c40074a450680154680401d080c1c0c50002440400b0100b036520b0340e00340d075903100c8191543c01c0c10703d0724245017410300c5040500600c40b09044c6040107100001d89296010348003c0760041400c000000104040c0c1c0310b184003604956014000010386030400c00a0440103030800a50070b840d0005909242c0d4005085811001e02000d000752140201060241903006d1000104101d000d8980642c0c0101070200003000ae8070800070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 378304910 1250 378303660 378303677
    0x302030310140d081b0118060501060c0b06061c1b1205090c010c15020703030203010e0603120d0b0112090c03170301050307090e0109020d260c0d0e0a0e0408040303 72
    0x10502d81640300d500c00110741001e2900000004501c040d03004200000400310403041074009101881d084a0804170903a0690321050180341c1000030600035580140140d15090f500704500d911402d07407080000e85800c0c49540009408218141c2815503941050511a002c100e4141a90b490891226054140d0300000e408e07800c6510788c0c414180709141c001c90003000184802240f0100658540398a040140c3350220503602400007030f0700c00e00040416030311965025843e545080d00d0a151908054031061180d080510500300c03444a003400e035199040603c001142504044006940e5140002d0340c103400c0a082002004c28004a000c4c64000c07284a46448140640758180494080c0028060b1640c1a0001c2004000040551b0004074101848200001d1980c405600003106408107a40c1124540c10058120841c0c190100c80000c00c1c1219402c00b030300e04408151100d03152000c004044051062003102e0810030b458010b0000068000c2c070320b440c82e46090131b044c444465085444210001054071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 378306160 1250 378304910 378304919
    0xa051c0c03051e0312010e07050409050903040612141f030203011406090609070c0803040201090801240906030c050913020d030c0c0501030621172d09090c070807020d0302030310 78
    0x111707042d256681c51840304590906056070030309078001c2c09440400c0030600c03011900710392512510b0f00400e5900000e40e9558a001400b42180c0403945007207590300e14011084910a201c40d0340194401c1280047d91004510821002d014640740c1d00041d4240d0702c2e140740c2c560002848020f0f03074013503801215020815500d05040000782c160495814001031005008003000800c030101458015105040c41c05109895003a00d500b1250761a11819044000b181038581d01d1180a00000140c207192100f40700040c110b89420702c48212600c215401b403c2680006084107030403c40031350106a0040c001c1070042e0302c606004000304046803081e562160000c01c0010558002e1088000300d030700201c1814843ea54600030201e01c0d079840e404c03c2d0b54808521001c0b0b03201d480c0740c0d8001d00d400a003204000401c6400d6451000e04214041c2c203100d5000410002d05000f95503c200140e4403d07502d40d4802d564505038582000c007400307408002074000880100300010541c003c000396200b04e5400c2c0034081d10b240d0b603 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 378307410 1250 378306160 378306163
    0xf0604320f040206071401020f070b04030f03061a070c090603030807030608070312030f0b04061721040b0c0a151e050403080604020a020c120703200a051c0c03051e 72
    0x750340081d44600e04202c294002200e42e6150309010446c10001414500001a22419079110020454030081a54108410150407620300400c021462404104050500c41404c518201d91141400d801074041046410001400700400140c00b40b884180040b0340d032880c0c050241c083c02c0d01c143c0d0110b4100600840c0510001400600301c03904003482c0c038404441e100d403c0d0f00520f00129444000c6484140d0f409540c0c41d40c0c0150402024100e981e00014404c0240c0c541c2040745d488200903491828052050980c1c0415081d03070165240d00305400e0f51604003d0302145008441c003401080801d0110051a100c9000d50060f140188202c0800c0203442c0760400c0c030400c8440842c0c0007004030700b05801160680c1042da010340284100d80c01282c40ca05008400038070841c0c0203402c000700c19803140074144100407554204500215140785622941001f89001621101c618000e42d4000c804d0301e070710004000400e40040c3d01468000c1c2c48020b0180d02c17804e0003520f03803a81c4240f24402604046104004500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 378308660 1250 378307410 378307441
    0x609050a1205120d020d0507050316091203081905011806090203090d030b03010e0303091c020a0c090c090b0304030201090c080c0603060f0103091502070c0b0307080f060432 76
    0x24040003410401000444005050f00281d8138400d22540c240140502840c4900c5064040d2a5035101c1076141d1138030120129042810291007820000c0c05001044010100a6140305240d410f00701100d9603a507040001100380c0d503134503a5480fa00d080400005901e4140010200546c001c64014401903881e286040d050b40301c00c1c3e81d1300c44190300882c3c03518039080c442e9004807a03080004002144040303e0405951542e0029110a48907421145211444241c81d03540b5079030340700030350000c7c00c3e0310720701901ea88008009620402c01c40d961108295240b0f00e1081e4401400f401010b9021500e85c20582002070007014a108120f403503010071000401c1442001030b28094140000b0151031456403000103112071540400b0b8000d041c191241e12600000c0c2d2032011109011419000040c1c03204a2424500b1800100d0703070007250045001c10600060b02d46c8421020b0b4080e20801c0a1085500d071707500854010405c991000a042d01100c82605680181c1c4030684440790b1414560700c40c03a291612840002c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 378309910 1250 378308660 378308663
    0x3070b1006140a020d0c02030118080319140f09072102010f111906020706091419080901110a050303090d03060b0a091502010b13020d0c0804200a0f0609050a12 70
    0x348006007001a01d485a400811b04620280000c0b0320000c401c2a4650080c40d03a40c2d0407100c1e60400710400120305400a111347c0e20700100d241c20b200c6550004d0352411640c60113001d529940c2500400290420420007003440100341c1501d800c54805041e00000011024a21089000076407803455800d5951040c044000780c600c01c00081c100e2003213540c1c55001e9100b50001c080307030120f4083c007501002c26001e119402255014482d000c8801041140c05420051020142145500c080b008140404d84075011b80c0c00c502420b081544a4034600300e4030f2480d09460b030701d001b8001c0c0703c00400c00428400106030129242d0550b18240a05601c0d4498a0041d019848424000a45d12642045881c5920082e034038400440d000015655000340b004c6105105e8a851072600c1075000103c40800e02600c1c0702d42802e400c22440c01500f181442da0b940b4240c80900c40d58922455203035020b812071076580c03986200084c0035038003405ea4010303503a10014203801d9403071065611130300e4603040c001142a20b03401d0b00c42419 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 378311160 1250 378309910 378309913
    0xf03060e0c070c0b0a0f0f0305070f05070204020d1b0e041b08100e040303060f05180103060b0102030f030406060501020c090714030a1e090204050109020f07110303070b1006140a02 79
    0x281d0320012000d14941000704140c94808807440000384d10700d500f1300280511026550784c400350741000c8501034413040c00280c100c01051b04d86010044a507074030294404581d10b9a1629503900c1d050341c000240a40640820000e0561500306100c4aa6021503000800a184c940300d1307008460000041108860700340d0500040480a404001c105601c5508441e62210203803c5c00c911850710b9282c002801e00c03003142c088012940d03440047c842d111201c580c00c00240002c68110001c01814008920300d0581803000920b241d89817160203007140e000340f00f82e95803068110106034072407400742440300141c26207218190140c0101c00814000b070034000000e510920003500c405584003010040d04206030710041c140341c3c0840da00c0c0301c044d40301c103002c00744404005180e0a0100b22528280100401c985060740801e07455881006180b160a8510003641c131980d170060505603040c02e00c08007281c1148151400201030844d85010001201c201c003161074162000c5a0381c040c0c0042c1c00d41c049141a01c505103203000503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 378312410 1250 378311160 378311189
    0x61115270a1506030f0803180d11120316031a2d060703050304030807030b1f0e010e10050904090602030f01060915050301170a24050604060f0e0408190f0f0306 70
    0x4c9106c0d00000c42c0c01c5888204001c000d40c510070000b50a00c0c40c1d080c5c1c8a400145141803401e2418010420038105441034000d42d441c4d8140410010745060401602806054a0700c4c90408200001d801c6000011001380c41c9248030a140000b890000f060b04c001e4225178402403d19000f10304140c0185c44185030b15460315455a1201d85068036000d400501c000c003099214000b454481e00d5103040c8400c05e002543c070a920012440e0b20180000d000d030320540d81000102061060141e0702d02250040c1840c09041030360ba140c42c0e51000c10007820400502a0109000000344000340705c02d25900350483d00960b41c1c0d009801d46440f0944209c030341d414003e000051007803006001601741600004004040c0c0002c8454107a1107640c1e141e2074920406444410308160700c0030401840a50141d282d0061040b2010000d55080c0300a600800740d09004048030f60030403600180820102c0710844888986903510035211403181d80b40140803401031580d240c0014040124074004c2406400b4207400c0c0c50081469100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 378313660 1250 378312410 378312413
    0x1022103010320130e0609060c04180626070801021c0506010215040503031806060904060c0504030c03050601141816020a0204020c07050901061115270a1506030f 71
    0x200d0760fa40e00100c1111203c42c03500346203558030381112072400040b440010440001102000e0b0504000400c402000e0b08000100321404040070700715003c2d00c0340302218400003401c9074189401020310b41c000704d0185003152030950a14076988041144007048000b260f03030303440c1c0b42c90b82c4600380e0080d40c8829688505944030f40010100c260001a400f04044c07040301c00d0a800e401e801a4070440a640a48050b00000306104809070303a0420001040361000042c02c00b07041030000b1910342c0500400c09050182d5500789001490b11410885005542020701c80210a48074107149484540a1160b07000750000c050b0451464108201c0550b14080000c208080540e5181489090141d140303964804501131582007000603900e03032003c2c0010600010080141f142000144a82040180c200000740144e40000c510103070400510aa0840d8651404244980b60180c414400301f0103000c7c4014481c4a02e80500040000020341c9400d060168503500f00d000b07581c4860f42c003110310500014290300d440d0711a100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 378314910 1250 378313660 378313673
    0x18090f1505100f1a0f160203010b150f03150307060809010b090c070213060b130312020109080720040e010c0f050c07060c0f02061303050c0301060f05010806131109010221030103 78
    0xc201d141c02c0c60549005d00442024040e64010342c07504008a540c1c400b01415407c09105e6403c2e0807000b541e46920240380501141c249008070f054286819000200060303646842c400c0b01c142d01b8402404031003040d51140703406401503038129403c0c0c40700d41c40c1841441c83c500e401c001440c040c41219030250710f440c2084e001d0156000300003103520512178a8180000d419640360001b003040c84400f90f007a90341c0034114030b040d000011041001c0302c21a814500648041000c0d14200c9410b50790000a4000d000c1d01c440c514401d00c501c0300002540140b03450003a41d41488190410301410090360389000d1650301040c81a54503000b84824450690302150f414004d550184c2c803803003074050007114050b01c0c52609600103000c40d4400d07011045044420b070400c000300306081290110035501100203018036400c0200120895400d4072900d4100319035a4085a810b4840c07442c0103400d1680715900f0b0010650071040104c0640c8080c0650740144a0b14400c010f12102070720300c51801e080c0028200c0d2650b442c640303480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 378316160 1250 378314910 378314939
    0xd091a0c0705060307020f060604022503090305030f03011401020a121215030503090a14030a020603060d140106050f09010807090c02030d0e0a0605060909060118090f1505100f 77
    0x209500c210301c800710341560303a10040d6105441030350040c584050b100007036508002001e00640d01a900501581040d0003803c1015a10041ca540700592081c0d902d09040324041450351016205000c002114488004248000c41c142c81c0b190500c005800d2014004995400031074801802c20042a0361300c2006d80d200e143c0390503a0842c400c8002c80c50200c0c030f00c10f4510011013036004807510750001443d00404d0412003d000c0052507404450814440c184000c07075203504025030000e20940c800400550942d40c0c0c2080a5039541d0080107400003008403030b00480c002c00d02801418417561404000649a16101c1c28040c1a00c141901405401d490604854068589202d0003000d50000f0b100302c41d0b10000c44e00ca0740826413800030003083d4201207801c000301200c8000c2e0919010318003001c01c1014802c000200203044551200d0700d81115079415007610300601800c44000c2000f507010b03000809000c0102d140040c80d01c42c1c000c0030403290b1078144106141440a03c903420074150100000c01036419050202e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 378317410 1250 378316160 378316177
    0x1504021201060314010c030c02070b0d0908070b0a06060806030a030c020d0c0e0405060f0112020f09060a080d020c0f012d0504090f050a060b0f090d060f0e030c0d091a 73
    0x12900c951242e07150240d03488600c4c80c4004980d961021228035952501039505002d8071400a8070b40c2c18141703c0b510165100c2c04186155458540311003001b0446848101c80700f1a410000b203100d82d003003440c0f106010307041902c0340c24001401c20300030034214680030410b088119410b4841c0e1214000070fa080c4181780e100640d050b918809580e0300000d030040b0480e0660320961052015194914140c004682d090006030000d002d94170844010f440181c8800e2041c3c40880411942e1b55900d42c0c40100046410800741c014680318090440c0d05500e030364000411407412a000c941e581000c640603001180c00d00080328150300c100980170240700e488035007000705158902c401d01c4e15503d09030316803080801742d4401c22020350b039042d910400c0103000c031203a1045601402e8103c3c2030501c0e00710410880980d500030f42c0e01d928402c000144d094410410340d07501200242348014414030248606860302e40d100d411000c0d080e03400f4054500408281803043c1c80481c161950b032081c0d000b611405408a480d02c0c0c0000d0070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 378318660 1250 378317410 378317413
    0x6030606160f0f120201180210031e0e030702030606090603030a120e061e090111180303120a140901150e0402030c120f16300605010303030b1215040212 67
    0x501c000c5002a40019161130240b0000b4040c103004203402070031200300030704002001a91443c6400184d44000c0107a020030709502d401b04400344440052003458040e030018462607031a290203195102408409080d00324001c500780c0d11695250000c0c810b030346000b10761150b4150402c010078041d8a0041001851408803c0d000040a00c0080c030f01d2454584203840440f500c01070b020641c14800c00d40910583d01c102c3d032a0003444207035241c280144c05409445201007544a091500204c0e0ba00c0801c00c0c1d856280108603500e1030703414154140b800400d01d6240488003100020300140c0c03a240140078104125800d6888400c2e00c5140621000364034001810881c0e146c041c0c09098102540c0f407070000b015201c40303640900310811240041520b401c42c0042e40707180841301c0e401c080082111201c1a00000a0300709004503004040c1030303440d84075000d2007000070501c904e0178001000341903140d4046002c0c11010780b01000d04e00c03000c0759156035a061107001051868503c400250050504904d603e0b101c0c1003510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 378319910 1250 378318660 378318683
    0x306020703020a080f1b16030201300c0f180905071b150b010c1e141203070207060e2103040b04180f0603051009150221060603060616 59
    0x103540c42e04c0f5500825011120329000b141560340143e0b83c810000040079203000030720240040300d8850907100800e02c0080d05001d0b1241e038511040600580050100c80500c44990b800034038803204034000d08210404000086580c8030a100316030140c0394176840e0314560400d40e000e6a1400b07850401520380145081c08010b00245292686000d00c0c400c010b805106070001145034805218010441c1c1c2034084d900d04100b0a41d103d0700205e00c020610a61800264103925503019240c00d0000e1800c5459072800070910400203c0d4407a8116203000d9801020540d094520b41d9544000071944961000034a42c0d101802646600041d01140075071050080001c055070b050581e80d06240e00280c20a602c0202c0005440c1d03540c5200003da441010421001210204000e81c10f503205e1540c0c401d03580c0301c0754941d5503569180f0020701898404002c9400b200d1380c01550344a28200d80a0a9040e00390340040d170780f1501300c010504a15180c2c0c2a01e00c1001d0161940342003030041c000255051119900694510302c940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 378321160 1250 378319910 378319913
    0x101401030b18070e0a12020103020f0906040e07090923180706020102041e060804021201090b04030c020301051006080613020705030d0203060306090705010507060c030b0907080114010503060a0306020703020a 91
    0x3035800740e91000c0010340458985030801800060070f07400058030451682c942804a001010000d02c01640c0a04c4c006844400078484130f00bca104502000798007078400b29002038074003520504544101c2540e40c0d41c5608950340c2c0030600c10341d8200c01c0b800ca0a00f180c00d030400a034115917011941d22607240c0c0e101c50014610003141078101040c41c4c00c948018bd40001c0c0c1404200c1180600103a90b10600d84502e000500d4000300500c5184054802845885c07041ea04445000c000d40200301c0b29500008441c004c0d082c0391901808031600840124084d50800e4001000c160000000c01c0072505c0035102d40040c5e0fa640f1080110720405040d014810740c0c0d0a10000000c40c8042000e809465841f03000180d403400c041041503d0041c000746180b1580d48007060a1100d660300c0006e4540380b46d401140455020300c51031094014200f250100c5800101c20020064641c1c2e000788030b0350491f216408112034498810004480a10007100c28a40100d80400200700041c031560080c400907002e481610f84510071b5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 378322410 1250 378321160 378321169
    0x10801032a0608011a090303030a090206040b0a030603140a02030c060c030f270a21020d0f0b04140a020105090d0809062701080105180411100210050708101401030b 72
    0x11a0400b00000301d1200050248a5095550300c40544103840c102c1e0400041c03000080c0d40c1d1000400c41d461454858210b0405c41d00c900c025903014084800387c043d29003c8446c001001000b041c4800e58900000c003843c3d08031550082820040c140e0007801410b40c81920800f44071065000488442c4644810461030041c50589009060030669041d642449000d10043c0c110f00b0001d40d6080d40d11501d41c0038802c20401041841d6140c4043c00519040b49622590001a0902c24040700143c0701d40b43c04844041041401e03440e20703100320311900306808501c00050b0020780c1c881413014002e0102d071080007050850f20304241340c54a0203125440c141d141084410128250b0b410004145400408011644214505004e101c00b041002071070032100c19031400300065841c10754152280c4205601502003020f01004055501c034044d0050a00104d50048488c000c1d81e400e41b059440100302c2c502000304448911540c0290700500307000802108041c140031410700311003002c0300c6190605903134111101050300ea = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 378323660 1250 378322410 378322493
    0x509030706080114040203010e01060e0f060a052a0312130c080d020d0e0604050609120d200a020f01110c09010b0d201b0313030804030c1401080103 65
    0x1840c0c2c1d403680c06516101511303a0f9a4010148144502e005100500c24140c40c0389801e41119000c0c502621070202030300104002c0410028029000a00001e6405002e60400000c3c00403000c0d01040e00c42d2000c882200c40d00f0f101c134041030242d10790000c1014480c1c1c0741d055820650008040c46100011003095503414009120781e174414491a041030036590342032601170107c1c45400c0c5450605038200700d40100091814840c0b400780a20403180483c00c40f503140c441444029416080c0c0d0210b8024841d15003010b441086201c441d04000490a040440c402c0d40100b0190480d81c0d0160507104004000030040d600100c02c160090118490784000c0c0c3c01a41d07500704030600030f28094244e15910385029a40d181a43ca050340a01d0b07a44000450301c0804c1170562040300d0800320182e071030040000348240c41605620992811a106c049940301c04014040004014800c8030700c00c07040002d00b180d032529030185d00d100f2121101e000c2580100100040b4010340c60465551003460310145200014600d080c44904 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 378324910 1250 378323660 378323669
    0x114040b12041a040c030b0403050c0f011508120d0207050a060c08060f0103140417090d0c0e0f0408070803250e330c030403170c0d1d010c0305090307 66
    0x503410081c04280481882260310304a0000740f03040711460305480c3c00304000864400144100100c3c1c00223404d043c812016200d41001900c20350b8100300104c10011301070306c02d64480b10003608444900091021b40091030005000c04a0301700c03414107031006a050000d4224000c2030b18180075042180c0c0c00501c03030348034581c11003d031600d509056040075030501100c0503102c0c4030320b030505185c03000090880c00e075000704076809030384800002103c0d030b80360142a105000d000a0650066043c3c6404400c01c0680c5c6200c0042d076050f104c10400325929100700321141c41058a019209003010400d50000c40c410800855000c580c03400803007174030041d0040411103181c1c0310405000281e42d0b0710003c0c0c80c501d08045a42d5000038a8405980300c09140080c403140d03a02d1400384030308196800100c980003250b0900650b0000d50300080b00c0d6a15039a003149080340c3d80c0c000c5401d102280240b4000c29040c50003420002e0640805180d05c1d100e501c2002c00544200d4107640084d02444000e001c083d0041e601040610041d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 378326160 1250 378324910 378324937
    0x80601031a0a050f04020d080c07080601080d175704051305090106051002070f2705060a1e031703070e1509090705041509140114040b 59
    0x1800c0090034507048281c0901002242400e09003400000c150800e4903582098044803080d9030880d19103031038580da00c9101010b008900503484000f58002001c14401d04035144101559002692034000300c482131841c01e000310100e50600b01041e00c580c2c40703e802d8400700c1003072003490764480c51640501c0d4000d20081480701001d40080200303104402a410382c0c00d00340303880107076050405050000007580b07001d01464086085a883d40020070b015130941012009042c0074003101c1206071300140094a071043c0e4020300050300404c0f40c0010b202c04054000312441034611608620086043c1041c60181902600b042d074090007202c80400c5401c25241021001b5446000214900c4d1440c03400031844441d02a038802490400d000704946d00d80c200362080030701d1404440040801c40b0003242201c25000d68480c10341c101341e06101304010369030044010003d03240703000d8140304c080103102011660400103018904904c1c600240040040d4003800740399600b0104d0484150406840e40c0c0d010346290405c45001402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 378327410 1250 378326160 378326183
    0x30715120f1803021c1d1906020a02090f010315020a022505010201060b090a031e050102120f0c0306010c0605070c05030c071d0f07120b06190219200a08060103 70
    0x3095010000808180345e501c5940c0c001c18000c820140c007142502112100d4901c43d509132503041d541e0703400ba0003406010404450b102a48408000b541c0d000c020348124003a84200000c6101c441d81044580d0489034030040140c4d6040245050700086d4200f19400800c0d4414002c0c40c6401c80d208090f503823280f20a15440025003840e042c002400d40e802c81d80300c51070f000300402c0350850585868100c0029030360003110302a201c1d141803240e08901900c00602901302c1d4030110300398000111401d00300e409200b00701038240440e1036004d2010a0f40c0b0068600a005c6218942103100080941d0002a030000e0319040800000034039460741e40c116402024150503542148901740503924445059507080756510010344110702d4801d9800f03141031005000c60f82402452250303400c0d0200150860480d1401c040c1c0800c0d16000300e54040141f8075121103410000d405001c43c5400050311007a020151260800c58100403000c4d8180280d01c402c200082d12900207101c00f0000c103041030b040000600031841280380703021 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 378328660 1250 378327410 378327413
    0xa0321030c0e030a060c090b03010e04020a0e150d060e2d03040609140609060c0d030506011404060305090a170a180b070303051f0f0501030b030715120f18 68
    0x854424520000c24480003880b107200030b440c000380003494075621080009107640d200d01d003a1160340c810390194001000020001c52070001d00105180103078400c2c0c5100310f902d503e81c1c440800005041703400164240580580040034038002a540c1581e601900300007448116030702c05a81006c490f0008000c0d40305d88110352200020341c0080e1030ba0b008101001641c10300f800c10300014644026489080c030403c0040c0850812543c81d641166920000140b01540d03c0031101441070311407216078081c1c400b03e403074500014499409003905010407110210842d280030308000040d00200030203800c1070014440c5840d0040041d140e041d601c2c0341721021080850300d6648a0000604090781c0c110400c0c200010180f0401054148200796128203516080100d250368a403490b894007400541108046a03d620a002a0084021803100d094401c285d0741400315810640a0607a104c401d480f51880e8010180f1440340460b2249412100540c00d0071070100e03d183c905403007501610841203c40d012400700070309150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 378329910 1250 378328660 378328667
    0xe061303171803070b090607052802041401031707030903020411070c0b04030c09110c0a060e0c0103020403050709050c070c03120806011817010209031b01080603030f16020a0321 78
    0x1031411003c40003014000d050a004480d24021100d41c0e6000d1703e0b020a08c80c041090510011002c042c03010001c85000408581c0401c40e00c0c94a1820b9000f1403a04008070a00b404400200d81601d0f0403104032041031221201c0b1580d107a100c00000d07000c10140440110059940703001d8001101c034000304d15511808182401701c080111544180301c0f4240420041000610004d080c408565031000005102d10058220860611514100b1800c0f0300a0f01450810442258401511801c00e613007210300007002100150124480c0d400040c029030301144c000c204000c0c0d640c02c410b0b4030640b0200351504000d5540e844180480640e00304131000d106c4060340d440d14648c0710180e40da00034001d2030401c0c540e41d4911050682e0248500805a101c1c0801400c000032800035011100000c0d400f4088a41c401400540e0511000c610b00a06001030030100204900d440c0005c161145180d91107882450700c0d200d85907075020313041d13101406c03a04046101c0001010980a855403190303c4081445107004810b00007005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 378331160 1250 378329910 378329947
    0x61a0304050c100c06200c01050907050a14040c0e0904080405100c080a0f05130905100f0509070c0c0b0d0c0206220b041703010b0a0215070e06130317 66
    0x103c1c010260350b586000d8840e0300c150700000c42c1d81c000c0c178001110b01a004c000d8414440c1b02202c3d0000303c0000407140d100c5001544880c0c440c0400809444009840d4010440905010300c1500480d07a4007040b1400d507854141d003c0c0c1c00740c1000e17060142c0c031113800c1343c0400d455032421901914040740c0440e0401080c01c081c410001754046900e41038108c0c9401d40d44080d101d00a8582a404120440c0c810f000b2041c054401c480000140d482d502c0f2800b80d45103029005024201e501861044100100040d462080070060050350002481900c44d565002001c9a030052201c41c10b80b074120000400281401038078000f0800d5041d55440030440d030003913140107494500058a944000690646c03a003400601c64003003c0301043c2d2142080c1c54545550502c400750008007102100c40050000c00010010803442c018032001c14103400340c45040c02d09444c210341490341100c030417010030000e25050401d450410f00034031401e403594040704d903590380720349448000194400040354005000a1a10707059160007594 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 378332410 1250 378331160 378331183
    0xb010c1b0e180f010c090e06010e1302090a08030f040b13050a121e05060c09010201110d0e060907030804061101021c020a1106150d21050304031d012001061a030405 72
    0x81c00582c40d9020024800c0d070b140c0c451000701204603408510f2a038850074ad0a119a0300060207540e9036082010325000175400700148900c18040401c001540c2d080110544146143c1c0032080c50070607280040700e001d9544109244000044840783c00302d0b00e5034803003000705c01506242c4e91303103200100c485ca0700341c074000c48108190b01d8a4601c001ca0000298001400c5a4004601d1000c00c0d04c0300000d070010b070301404c81c161021000d6440401d03260404203036540700380340150000c3d0844515850745a20a40c641040340000750040000304014031442e401030141c400c0c0c05205000051800207204c5e48800104103600701d804415030009800c07412641d000398420101d20110b4003415150078040c03400d0b00b0320b90200c0c00b86030140203a007410109108000003103240840300c51008080384e40d2041001801640704076030403404a0491a182d02141d5070100c421168264183c442c54603d6064500384980c46000b00c86080880d0b403504404524694526108200400d0b1a03070b120b9100d0070189080c6082c800403041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 378333660 1250 378332410 378332413
    0x2030406060519050118030204051608070f081308040302060c0705010f0203090901140402070210080a18050a170c0f010608010606030504020d1401091212050106030b010c1b0e180f 79
    0x7601070803d103481540e00403140f09083c00c8030950f051100c3c010808010b5032029602c03a05d0502000a00c800100002101080c1999250001d5403401c80c141c0d8900f500850810001c0c1240300000c15071000440444011030052003040d041c1a0349900003081a8070131214801d5039004214204455604408500e00d8090703107001442c00c0c1800700010504100301441400c04004040d0b45d4070500d92100e84c1210003882d00601702c0351a140000078013400448007910449049032522407001001c0030410000034003c1c0c0d1000c06404079031116102c82c50401501c01480701308610810507002e120400304110880341c0c9051001090092418020342d003102d000e42e000100341410002040700690780c1208007074105d5403000c1c504140c1411080101d00422180c00014080400d1480001e1026000425003565460707a641c18030280c0c1e05d07000b0403001d603041c100d80c1d43c0c0800c104841c0c80d00002c088800e008076100301510300c581201c0d41e03010514113028080d140f5841800780f4140d00f2407413800c1805400709605a500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 378334910 1250 378333660 378333679
    0x305040b03073e07060c24020417070902040b0712110105150102070f08030405100210020f0304060f0b060405060d020d1a030f0f0a02060a03150e060a0602010b130203041410020304060605 82
    0x4054034000c0d06c28070080c0361940308032007801d1443c20300499084c81000c0030b50441d1156207510300400c55401a80c040c141d64800c10300005a10700c040d000302c87c1980d0b007000c070080c1807020542d115020b9803421400401804210801c1c529021002d10074540303d40c80c18440c040a036400b05001900f4031f0340d1504881c141880d402005d0100c4000002240c0845078190b131030103548158a04100c0c20000744e007040340e01c0a03000140c3c05120225440265014030700410080042503105c80d01c1004640d480b030400c5800001c1427104001510302003014040340840000054940380c050159001102d03034510142400b4000144007049606082110011030300d03003c0001e0650301c042600f59550f855003504003d11808001400c0f402030f174480c0d042a115659212104410f0701e44a005441140c0401c5601600980003040002803151050003071600001000d02046111014080d401c0041d6000800c140e400350102601c1c084030260030408040340c90002400140c0741c0c10946000001e0301c012742c4c401c91250341e099 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 378336160 1250 378334910 378334919
    0x13020d0b030c0604140102030408060f0106120e0d0807090801050a0c0809060403020a11040609020a020f011112180a15050402011715040504050f0d0c110303070305040b03073e07 78
    0x300111003d644004004588000000e40100c1c518409c980000b00345024450a100c03050340044002e5060310344603101e10b07440d100010280d03401c540480c07442a00300c0d03000e00350404d1010b00544a5907003203c9185408180c05e40c48076211402d44000b61100744685541d2031400e6070040d402000c16402041540c003804060a05481c000c0d175500561801500350307802e1200502417a07403a540094005d00706040c040d5280d120030003029407201c620854a55030355090805055120401e401214580c964104010341143c881400c980840b204400c11503a00d8401c0d58290350200721584003030410620381410100d4140b03020701c00100380c2400b01c10040d01401f40282030082c004880004030304020401d4500080540d21030501c24603008030540340540c58000c0c0c0b88481131846e488a80c8107429800740465115210044041c50b82e01d1103050005000a20f0501c420b0007500134a0f4001c0d0b402080c94a0314007014a45175218004408a041c0803202e4949942d0300c910420b14180003900b80f02c01008050507005151 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 378337410 1250 378336160 378336169
    0x50c01090b0d02400503070b040e041a0108070f08010912050a021501080703020a140d0f06060f0b250b07030f09080a030606080a05130b060f13020d0b030c 68
    0xc2c8485400c0c0325801007200600014a041c2c078030700565011800e07140c03010b80e05103140714150021343c0d1080c15110480300860b03641400501201191130810342940752503d000c942d140070000c043c1003120704003441c2185c0e00307400d1001c810b00340c060b0014402801c05c2c3c501d492405d2036000a55400b15019034140030003540419080d07070b0006860001814410b5903046560b408a00f840f01880e081151b2400140c004a281800080d40c075007945d01c285c3c1c0401c42c3c82d8503a0520380350100e0b41700000d64007800c004031a80c00128501c4e108000c82d842488040348180c0c0754024010306502e6a0044956075801160201c12032008964001024034804e00b90040d208a0342c983c0420704000410324000d0548410040d03480402c26800b82c4d40c50758000c42516181c803105000140a0001c5118202c0012051002b14180710801c9c45030900600c0103441070b00c5038140540d581d0246401c000d2007603038008000e404034421a15000241d01100d444110010782c5e0740e0100382c8034000c60f00484c04440c0640d02c555480c0483c5d0703e6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 378338660 1250 378337410 378337417
    0x50f090106062309030105090d120504050705190f1e050d020a0306180605090303090618060118061205100c0507031409040b270c27030c0a060c050c01090b 68
    0x2c4282e03020840c1000000700d0964804c403183c1540640c60081049042540030401c00b003041501e5454144003a801d4907c00203031030050f500600180c000000400c454505403106581d1024658500f070881c0d640d44044002012180d4000341c0300c4880300705805858240320000c0000781804884050103441a60081840c02c107c80c00028092075030381c220002c0d0356985003990783d005540003a00f440300e80340c4511120340f030380c10944680050f032140a01050600050080320311015128000400342a8a803800805d01250007203003458010740d03150070103d9680a02070094855a009500601d260380c4042044402c07154050411002c100c2c040c0220303c0044d40c01a00c410300041820141905d074000c0000140003440515031080d4000e900a10b0b510f640c1230041e5007900c00d107544012200041d940c0c543d058603540f0460a000c80301a5100c481001c1c070161003862828250b8000c0c0403074075404841c2011445c42403098201c040403444800d402000c0160030042140b1641080c40d0143e485403908244800360300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 378339910 1250 378338660 378338687
    0x80703020309031b01020405030307030c26030f0c21060a06030c050d230f0a05010909120f09150507050c0a141201110706021213110114090d0303050f09010606 70
    0x301320100c180302c401003501a40c003d418001e00740e950381d50f07482c0750141002c2c40d5440100c1c0c1d100b1078030075070901e20b0b89102ca200d820910a884810319564950b01502d42c0050b00402105500d0300030b025064a0a5107510342d081092000038280440741401010400741c4052a8418401c02d03045c090b00110b0182d02c84140c13181d0003086140401e25514004c03403082d44240c551b03000c14103503c0800400c0b880c24540f0309814094607000004100c280d80b18080310090741d1610101400402225100b0814203101c1d0358881404c446a261031003842d07446182100c0d400a4030007a42000513000b1603803000b84601800700704420003080300c041002614141d1004404421106014030911441d03403046041c100030341000b5a41410000d407503a5851051074000001d410580740c1112a003404800035503001d52101d41014440e8200761080c601c200246c0045500e8007190b900e40c004010280450311403500c0d6000148429407090700d0104091600c2c84844951450081c91542d80303030304001c0100044c1e41c00c51a45403082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 378341160 1250 378339910 378339937
    0x317090a031d010c050303070f180602190813030311010606020f0717150108070f091a130f05040c060f020304121e12090e062205071403090c0108070302030903 70
    0x1540880b0040e1200c2c90440b90103425400000100005182d1242c1d10040b074115541b900d01425140c4881c4074142d000d10b001d0300025900002d4084801e0021034100c00c00a0f10a404061401c103540c0f080701007215003a4001c0300891600081d00141903801c0c010320028100d9840104110140058150f82d070344013070700c07403585002c50294074100368050a00130010414000740c031410312941c0d24a101542c5010520490b074240c0720b1a080400d4a034424001c03030070403000968207a40c041410030304202d0400301585241000f10350320142000c850031a40116481070340907080382e130882450807401401c0500c00350612000c40d00308001c140110741e4100206016550081c89210303021029000c3d1204886101c000540300c84003070f0f842c50a8550384800440242c4528804195040d1502e00034400c01d01000c5850003e010034030b85446440364182c4d4003c0d40d120f400d51401c0c0c000c0740000e1011041076401039850300082d41200b20400503a582002c100307604280c1c0d52408525502d44145500c0d100d000d00d50446009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 378342410 1250 378341160 378341207
    0x1c0308040f0201031d0706120c050d0b0f19081204231801080609250e090102120103080c060f040209010303032003010f0e06060a020a0206030c0c0601030317090a03 72
    0x15a40329901121a884102e080155180943c9449594030000740c415840010b814000b403c81c0c403513080c056004454400e0702e41a0412030be03203200d800980342e070a1510342c2014401040303a500e5912000f8480380301034500c1814007007038106a185410f08200324081418802c01300320030000842807100400300021035400300494a40c0c00c1700020078402010b00105885a1000008600c0100105105018680740812148047c68280401c012240000f80da054a0285910108500b00380f60030f0701948190f61000040c64103441141c4442103140a0b01706843c3ea10b404a6914031941042241c15040350a840e10a00b5a00c0c1541c0051242c2c00c2c140402402c240d100c0003415004810381e9040d400000060410984075070311146a41101c242c28401c18500300c500401080755400d01500702c44102007250701404a065a0350240282544050714400c9506400c0040c044071200c10f0100d113000e54807036075403854034003403805440c4460034020740004003a82105005c000040e400c4070803003081c2810b160b2140300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 378343660 1250 378342410 378342413
    0x402010809010902030d0806120c090c0a0e04020f040e0703140c07030215070f033e22050117060d021e04090f0203070803040f06030b0607020d05010b1c0308040f 71
    0x7405005000a405201b40206482c00a0300003d0051042c0300540303c010a07200c050b60946c0d620440b145190790021065008518070000000061078604403a0800c04000101c85012504a070301c00302084504220116040c000399806c100e0141e0004034601d0280440500c400e50f4880008001e030004800040020307106c42014000c1c00400900b034100c1c4901c680d6450914800750034807140000c00301c0002e15080c00c2c03d440d40004600e4442036a13890202512440d101c15400306050241c000c1d0942480c0240900540d1880c9841c0031502c0d00b104480b003114080c03408002403c1603180c191441c000482c1c98040000680b83e0102e083e9580381c0444054412010b401c0c0b0340b9800c003140c0d218494005043c5000c200a100040700c0d80c2e40d605109030229840c1c9640c550340320361280158000c1e04178100702c0c0141003154503c02d8021007910703400240000c2c0f40403040c0d800103060b00d0f020407044900e07175115816000303140703451500c44c4401140752496a080fa0728541e802001550300a10003010b08000031038010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 378344910 1250 378343660 378343663
    0xa0803040c1a1909080607080609010602070803090f0d0c060c050106090614040908040f0b030402030c030109081902030d020c10051501120518030301030c03060c1d1c0804060309031d0102060402010809 88
    0x4020070342c482c00d0306e80a09180302d00600c5d1902c1200c5080c068035800e000000c03403c0c400150b010442d507015000e03600b030801240c100929068610402c1e42d001c0c100707080890204914483c142c00130031141c1c5401d05000c13801d141440c256601a8440120189004401c100d040815140146e0024003242c1c0000c0100e070901e041c1c2e24a0050344c0007000c2e440400c00c0086904001d4000442c0290700071012a1284407c40b0100341c00e8500340c0b08001c0085406010a4000310340803280c4c40051081e500583c0e047c41010100502241c02c202101e031116800220039100301c117000c5c414039401c03440c90b00149911044c4040040c04030024401c4070801c2503658000900d151550702c8010700781d58035010035260b40f546c1d1ba0401c1800244240130955000d8a070800407079142c2e0241189650303150002c020011100380d10b50030040740c1c01001b4912250041100600c2d000075100d4002440544055180001c20449608000701190605000d040030010001e80c02e21160f80c0004250307520a6091814190660b00c042015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 378346160 1250 378344910 378344927
    0xc090402210304080d030f0501050609150c190b070c0b160903050f0f1b0a05010c0516030605220506010504110d0e030703120506010914010c050a0803040c1a19 70
    0x250303602d00010074003203034240c000304040102c400980d606020a812030b6050701c0c121a020306c19981e1224003000004220305201e4900c00e9802580d440c4241010700c4414411305003540b0206189003000c080505404101c101480c0640109192418510710a01ba50710110400b502034107100e40e8807500300861303130f8591103902c0c001c02551b030200c20703120207800f6008403070f984008100200c030382c901074034850702c007050008040004064030062544070194900001500d21800b01d074016078241c00b4000380109000310400e10781000f188142c400080c6440c0c070a030301900017141983c0d0f144002c030300c0005070008070341c001420070f054070b030201c0b40040d01105101400403548591071b900d0754082c2c1001d00001901001202900003036000e070f06d48511850361070b46e0010848804549040c046544140240420b200f103d0285002c0320060400e10065941525940e15003016001d08a412000000400040080d2589000000d0003620001020100c280c001b581c1a405013403204280d8100003c90103807218800d8806 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 378347410 1250 378346160 378346219
    0xe040611191b080c160b18011b08070b060406080f03040302040c020a050715030f0212040b0402120723030105060901030b060303130603050405012a0509040b060c1b030c090402 77
    0x84e43e0340780900040d5250a81d00c0f001c01e0910301c0b05080001c0d2005940d0454204480701e41e07c005540210400640d403440750090800a220605481040040d4a44004100c12405580b07030340668503111003044141c4085400007800d0760026000399010702800010f075000d40f41c0c100c4000c909549490802c03480c00c0000a0050000e104024001074540050300000c1c218242da641d080c41407841050b0034005038851f460b80d494801820000240c040b4114032052500030f840100007100082054203103a182a880e074001c1c4c204a07540030510844607803001918a43c45205034001c0c003891601c0d01c009208080140300140600380700742c00080b0a5541407088902d85802001c41d0301401c0d450700e0000700103000446044581c0d43ca00a44401c009846909038202d0000c0e0001019240340d04040c201c45075000845080d81154541c09000041da440d880905190b20860300201041c10040c07041d280020741c8010003074040d030481d1401540c9a19a40c40b0b180d40140c0680c0d040d29030720a4035020501407a000d560 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 378348660 1250 378347410 378347423
    0x9150402030f01080601050f100f0207180c120e030a05180303031810050903040b0d09080307080712090503040506030c1e0408150114150c070e040611191b 68
    0x8014989500d600b9280c1a12410422220960388610600c140b540c450190703039078031100801d4404200c80c0b045280e0003141e880351040d207070030694945410060580880a03120351075128030710110744d10f46c4401c68058911003013409210805031503071200e8481c4039103407945007008000030b80c41e548041c01ca5010000002d01900b20303592803a0040b1030142c2219034250b501c503103001c1c8080d03140f0030410030b010b0706001c0c00004020398a41460030180048940c8244103103034026840e0004a00414001000740d44500f800f074484170050710b803048005058038810070984034000d00e4890f070b210103c0c20000540d019118140d411550360346604081c0c00c258042e00c01246446058401b02140301d003617000141049402030300c1142c005d1450740c0d0b0403c01c1c21400340120300064121010440e6140340065461007100700c444d1415151000340d100325400c14140307402006587c020503043c801040001d1041107485804900101d0424020070070b001008412204c103141044030141c0f1500d004c051000050300362584c040c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 378349910 1250 378348660 378348667
    0xe0a08180319050307020907050a0f030b180103060e010b060708090d0303090210030b0316030302060619030c06090315020f03070309230a060605010e0907050c1603030309052104030209150402 84
    0x2400f140d89078440c000c101d0141020901040969001e40169800103509460b9400d0075454440e0440040200401c001e900419074042628064a00501640a54015907002c540030784581d650b00e094604400800740a00d0041008a02062132042034494000085a800c008007800d400c08501400204a010354420342c1000d031a01156059480820303c20416015203009246040030314914100b1448090056003220000617414903140d40140ca0228001d44200485a100d03110641801441d802650200e06a1001481030002c05c0c5180707850044419801d61a05d4440c0040100500000c3c20b100207141c0c031003a00004020443c510400e8068008014500c81c03540746580c2580c4410844041d01c1d024a4400c1c082290b5100d1703a802ca210003801b1340914039503110710200f1590360b8442030440045014615903034070300c600c800b18114000c60080d0360100d00040141001420844124031141107000c450001c880006040702c00d0f5405c03283c046800788031a0f610304080b51111100320b294113902c2403000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 378351160 1250 378349910 378349913
    0xf06091314010f061203200714031006080f1204060e09090c040f140901060b04150504030c0b0405030615011b08090310060f14030a060902041b03020406030e0a08180319 74
    0xa1810f6072145e40640c1d5050510a1481f98208860707140c41c84c7c1201540100c2c500b4000c410b8614000c1c0c0720000c0140441d0300f84a901c0c10680b0484040303422252042c2c001c5003030911640020803514104e0f004804555103480e203011b5016004180c41c60045010701404000111104820f01c00c2c07116002c40900140003480700120820010642d0b4010800c80209041c00b2803910300051052005544201c03007034615290500084e102c038052010049010404100008030015030940403150003421480405030702e903400c207401c141c142038004201400d50040d0320010100c580e4001c00360110202006407521442d0400d080055280c0f00b00c80c50035405220b030f040c00c10050410ba9200384200c42d00500108001a21000742d48103100c6c1c50500d80e40d0641c0141d801c08086400c0d0780c04120030b10b10003040001d48070a001c502d0010704000764420300100c0c0d1302160801c501078250160703041003040d4a01416942d01e90766246800b501407200140c0c0300004801a500c91078804000b0740400b605030000c00c82c03030030506 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 378352410 1250 378351160 378351179
    0x9012604050f0d09151b05030406050414060a02070506030a0e0f06061203040608070e0a09090b07110a0519060621031205062805060703080f06091314010f06 69
    0x22190071580c40e120700090f48042c41d03c91a61351081d034640e0040c00400680b0703142c08440300280714181c070401c180c22810342400510200f0050000f400d564840580b42d03864100c1c1c1e4941400511902405041f00300300140a45a011903070303009503042161065102d868500c1c2600050078140c0304800540728215088500b4400011f020b0b1250004032203141304800e80040c030f5910784c00744d84564400300e0086004215894004c1115527076030103003d4400007030241d89441d80000e0b50320424058401041c284103109045034014190450b1207803050090410354030750760300e032681d42c0040c10f98071400111a505000c100419904003400501b410740f4001132400c0400c01000000f500c15800f2000f003510f400580a036101503001d1240704010040c10740c41942c100c41d840082a8070300d10740ea126a4144080d011039640d44010160865074000c3d984c10419140210040c3c00045026201c14410849042000a06c010410301104101d41c0b2003c500d501503c000000340c0900b11030300070083d11070b0a000c40070503072014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 378353660 1250 378352410 378352423
    0xc080904090303180f05070501030c09060806130f0b0a0b0a0909020d021209031b0c0a03260a0306030b101223070603050a150807090207020d02090f012301050901260405 74
    0x15400ba201f04d1652000154101d4018014600c08a0510301041103042e0107101030745e6000030301806031040a020510030004444000030391040d910b0f40d40c0002e03049410800030b0040501501c5100d5441c000c0b84c0b40019040380020700c03c0c19038643d000a40b400c1d03c1c00b143d406850706034a00f0310200007681486031101d91660407800308102c1032081c4900006e6105030004685600c2c00703028100148560031601d1b00b06001e4030a810303c0100c03030038070440e5078140e100d0b000060080c0c0400d564000388250841c540783c00101c2024100c04041e005040003030025100e40c4041c1e03920039500100000401400c66245c441c441058408070f070003030244410000d8003540580040d40b0410042c00200115000d1011014401d1a64014101ca541c003808040c82895000d0740186400c90005001c3d9807401103580c0060601c0f0700442c3c078003d082c40f900004111030b02c4401541c0b0344656a5542c02d001222103000001c1c00c5002c5c0ca0360160400c844c410300b241c4212102c3d10300c4185002801d25414852074035080090f40e521 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 378354910 1250 378353660 378353663
    0xf051c020d020327011701090204060306050301021e1317030a030506090423030c0a060e0c010c080f070213020703020a0c06020c0d14071d060901060c080904090303180f 74
    0xa10150811071840481120b480545020054003a40c83c0a580d0074840151207088030306101040151a160a558500e458024a00700b00090780e620304084000b4103580a0b580864007903030043c020282e0640130300c2081485200c4201010b81c0707541e60641a08032101141d44207084801115482542a09000c8020602280325403010322042e00c1c1c810500524040403500900240d8940380a14280311442c0c950001c1c03210400c04403420302150b0f610450070304e02d1805044070510f5503841d800c0e0700e00200340030049a040c02401d28906820441c1c80d114064072400304000203c400c0010007004543d2040c130500c1000408200441d114022440d000e903480400000c1a5444400c00d000020158070000b02c030310000e200901020410103941c0d49450340c242c0c400984071180d000c0c41d0b41c0410310046c402e610300c0c042d130880446107805061500070b0042c10007042c0c0240c1c0800c0b45025501002c100c5020460310307000f009660018a2400da410103c00030854600d846c00500e4880107450700b400004420250100e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 378356160 1250 378354910 378354913
    0xb0403080405090c04050607120504090c020f0f0606060304060207150203190516020c13060806071e0302130608060112050a020c0111030f2706070906030b0d0201080606070f051c02 79
    0x240c0b11813445803003500580c031581e540b06500300711400c00a488051400340c100e507075081c05420551a0103a920548034414144130050f03200c4010034500803001c000d100c00880061025004600700a00810000c0c40000c0010b0b08003900020340c1c00030081c6031035800c03480300e903031a40c00c540364207040c480003100c080381c00038100c0d420b400d0001103426000040719801000c00190001c009071000d9106101a021440032020501d50383c2e6400052926001d20006100701c0700d03503840994500c0c001c10112681e42590074004101841031005070b0a5804403e00c41c02030342d0f21805c100d6482d54612004072030b14542d05920140850030300c0c0502c25200340c50740281c000110079000910236041d034138000218600085410040b61002000130548444101da01400121000300c4410840e4031441540707480c14000380ea1000002c0c09144007002459814441c04c1c2003a11b04640c5150410358075000204000c7c009480c403481203400084960402001002c070102e02c1da0b02c8415034010600995201003c04c11a52501015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 378357410 1250 378356160 378356179
    0x81005181e0f04051519150e0a090c08060402010f080a0e0106060e040605010e0d02062d04170a0b040311010204031a0403022b08060121050103050f15010b030408040b0403080405 78
    0x3900c00e400c00588507440325142103410503114014070000e820b0184a84c0c441f051b090a02283c552110009030b4825204402d006c5407080d12490001c0c00903426a00084441d0071040c1400010707031b84034800c6450b1a442d071400900a03203914a0300002001ca81039030a0b00c540c80c10f00e0000f0074540001d501221494111410040103580e840151046003d07410802d0380112507030100300c01840d00902915a5801813284c0700d20521100724920b00c2d8210118a400101c1c0e40460b04011040c017081d11880d05085003009040c1030000307035880104404000d40010184206a618151002d10940c19100290781008280200d0480d00021006d064070035107041c0c0050292032115180c0040d0301c02d000c4646001c180a180080c4030b5500c00b20350511001d424181000390049000000303080ca244441d5288401040019540d4511b10b0018502184030f103103981c860b0001c01401042c0c0742042d5400741100c4120b020300fa40c0e6a03491802c001103100b15000388030200380101c0d000c014401e00c60b028105890048d60007060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 378358660 1250 378357410 378357433
    0xc09100905120304290903190b060d02010e040b01211a04051006051e030f09010e01051509040f170d050105030a11010309021201060b070201081005181e0f0405 70
    0x1280d01c194001d04401c0000380490b04041e81c40d80485c02410f21203810554100404400081d04005090300c4816500c402101c1c0d61044c0101c2a00c00c6420407012034460742109066400600883c0c2400e002c14441d55032340c110500603034040c0c200030341e8280944c258550b0700394950801c400200b0f030803103030620004490107028119060612455002c0c110344e110040c40719251038001c0322680d005941050b080c1d0110a02c3c102070203100801785008d0307581c0d130f414030603645481142542112101802268660305040602107050b44e2000740805c0080103558640099549017002605220403100040a859007080382d44c81c040c0b8500040c019104161302e003444641d99480070180ea80c01c00e480003a01c4003080f414184c1003036010303502c00d0b018a0310103009503a12485c21100c1d14210b80076a400080c15140025946e021984d10481503980107040b039900001ea5824480410301002c01402040d28840320074000c26018107401046071060509440249810702d080b0210b24584e440c01d0703500b121907100c2d805040c41c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 378359910 1250 378358660 378358663
    0x190e1f0f1808150a02120406091101020c01140906040803030a0b3c0418060209040f110a1b05010501140a060c052d10050612031806030c0910090512 65
    0x4450081d07009040f580621a01e800c00c04001412281c5900d500704800400e00140018640c85103014500005610075107040c000b194000c480f813443d0440d000440d900541d80e07007002e0420080f00c00001815182c100110118041c0d1140d5004100540310100c1007141a2419420001c0e0241054441d01c4068041c1d040d00c80e4020380202d820101c2607a400d11050001c0c0740c4420010081d40010001710b070b4010300d80c3e40158212240072040d01e60540000d00c0000c0c5003800d00032110343c5c0389501010021070070b424490f01d41034040e020031034040241d040c0c00c092180701d105030301001c0150040020011940d5505044c44420100d000c02401801100b100041c0c0e0340c010981c60003055080070240c01511480414803403181d1034080c890400480c01051040588010440007041c61001e00303000030207052241c00c0000d00ca444001040c000d500400c407440040d03030b001c2c804503085101510001d4a03615900c0d20808280208007172590008030f0b02d04240840759010720b4a1003150001e4554003c40141b40c10100d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 378361160 1250 378359910 378359957
    0x204020f18030d1205150d1214070305040902070c1802040317190c0c080714040e0f0d0e180708061203030115050c010905030a180803190e1f0f 63
    0x1002113510000e0799044188240c020551003586401140102d03d81d00e80017071403030030040c28213403044982d10070311101c00754000c2180468440084035890404080340c5d0000c24178880c0780908a809a00420b40d88104280c00d0328420143c51b2003d841648c94203c2c0d020f1000a40103403101303451a5400c2c0d0a6182031921078000c8488103602840000342d50800726000399442204854102c07500090b291001580103000d105000151084004c81300462007040104805c3d1200d448201c1000e070002c200d01140d00c040003030400e1050031581816502c542e00440001e1146c88030b074040310382c2d0428070020840015030001c0000e10a0340e04031107240e00c0c041502c1429503207000034058480201a007a60194859000341c0262200281483c000709805d4030942d2040e046400a0450741d020038644403958041c0744600c0c02080251400320015410840d40110a0040b0f40a00c4003400506c880c82ca0307881400e4440201c15850000341804071102650b049100a000d002000c201d00d000580c06440d0245c041030800c401d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 378362410 1250 378361160 378361183
    0x312090c0311150d0209030f0c1f0905100915031e0b030c03150402090c07080904020f0c011113121218030b0708010e07050c0d12090204020f1803 64
    0xd84150550351002e00845800da1503540c042060354030519455000c0c0c3c02400452401680540c44615080a0510700f800c030704001000b0750030030b0501c0d59050b03c03552222400182d2051107005c46501290003030b030744180e56030000e0342c001030784103900c1c06d07401c1c1c00c030004074121a008103600c0040031988000f107088400f4480c5016918859800d99803402c203481d0401e181c030100040540391440d80840c0040d18254200c00701551444054041209528000b4190380d88a03000180e41441d009841e43d6000103481840754251085e40e01081b186239020a403003e607491150880d008101800310050b0419283c2c009610b00b070f03040d0b0580c490215021400c65440f1502c140e11040d400d004008924080c0c0c3c62000d950300c081c50701240d00b0300010200b00c031020f54502503003242c2c0f500c2c0c85550410805924100f4010b01940c1881703020003040003803450000d111810703405245008110704910042000140610017806503225001041c18902c00580b00d009203c2668402c00c034407095240c140078107440d80e81803201e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 378363660 1250 378362410 378362423
    0x705071a15220c080f060d0c090c110c040e030306060a030e1c020d2a020112020a0201240503060f04020d02040f0509071a0a1110090f031209 62
    0x42000c60304000048440e00407060803110440c0341e521001281d070b9080c18915a0202c158000a0701001d01114800c15a400e00c0f0792a22203032614200d01203600c4160050896030140303100e003003408107002c00340398200003800c520f2a01740100001c02c04d0007070494040c4601d032041c6009418100080d450705200b0304105000c9640610304540c9c80704100805a0003241502c0203054880303d02c41403590045c00390078441003540c1e4218032003000b018002403400750700030011400d010917600b14205916415440d0702018911900300d580c2c400b0140b0048464180d00c1c03002624450020503180c601c00c2c1c0642240030b00600c0c110744190341c0460640580313078000c4903104140e003540012001c2a005d41c04c00c00c003142c3c4140068407030f1101000c15030105048030421502c1071409035484c0b051203003644041c0304c03135001000d12400100044505510340e101c1e921412180707409004a2101d4040c0240b001d10100960707000b40d41e0300f04240101c80c1840c04140ca01c502c0210000707a0102c07915014481c0d20b216552903190840ca = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 378364910 1250 378363660 378363683
    0x3030f010f0f0b0f0705030f04090b0603270115081f1103060114071b03060b0d050c0f0a0509100510230c0a060603200d0f0303150305030d060e070507 66
    0x7001c43e1029407100c00c500b400303204100b0211703020420800042641390344000509607142d00d4041494100c0d80d11040c242e02c41c2c2410020310000b46602c444251813002114440100041c182c0c00382801001e08294408a00c500c2e0280024084004aa096641304a0003c0640900000601c0e041100c11701c07550811085024804651994407801110107168400788946180090684401400e000b0f103d40301c07a054650341c5424401c1024600484491400550746800202e00565401c0c1c0c803540e1507803072540505480d02c5a80035a40d40c6110a50080402400310f0000f41480442d07400d0f1003210f4028a80614604004442002c1c4900100c0d12030031003820341d1010742350b8140d044000503409015850b006100d07071580c3d4800310300e251150a0065204045d070284a040d4044031805548219207405d00c64502c0c00c6594010840900c02c0641d425418680001e054140380315000a8803030582028026102c086800703810b0030901d500000641e07203004c2d410485655118021180e0340b082d0040100182180c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 378366160 1250 378364910 378364919
    0x140307030308060d0b010e18030909011823160f0f08040609140c011404030308060409050109081207081305030706110c120d110403020d0b090a08070503030f010f0f 72
    0x368240b03078000000401c50750003611184c551010810b000c1e04084080952101400070120040404000001f00c50020354140f400040025141290511415040c55403a10042c0e00341409548145003811710140340d1004583d0200c829040200221140c40c030000080e61000361682c040d40d0b29801055844c0c2d0b5412620a150f80100e500c8a0050422100070341c542c2132000c009001d1040e4240200311400c000c1458800d038000042801000e1050550203410412080c00400c4d801111640e12840541d004502c542032840c080d4010311591201508400c808100c3d46500c8040d00410350040143d60f0300c0c0d0303031940c64500142022901c4d01000900c250b1082060f07400003801c68010441140041e607450b42045a1143e0503420500c140320b07203001d03101d800902a260000d162052202080c0d074890420b00341811a400300d544035070302180c058002c40d50000001e508146c00c005040c503407036000040c59211040c80c46c00381c0c0d6a81050ba030340c4d00c1040485002040000b1b00e600c0c2e0381c0883e261065100c221a1a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 378367410 1250 378366160 378366167
    0x4060b07030c020d1218090606141c05010803030f0f01050f04050604090219061218140f0d03020c060601080405100c0c021206100b0301140f0f120c0a1403070303 71
    0x42e420803a0010040c0c00402c0200d100c2c0c40214118a005440342605010100e02000080c0c41e41d0f00324000d0f4615024040c4155540105080c642c010780007076a0b0750310700007566101107004040b048200d00c0390134900007149481020000e940610900c9100340c505843e103480801ea51042400f40340e030400500c1803c015903203061741000b0b03080000648002002c2401d0340100d00d440c40c04020300714a0612020040006a41c000b607003020b10700034120204007000d0100c2c2400340300c0300a090301504a151100824080d04000c0c03141c24400840c0a040340c110840d55200540650045403852007103009040008480e54003521410340b2881c2d100029010150380c14004030018400c0003111410404298050001a11944a0420941e5403a0b00806c00c0707141c86290f82d4081149500034040e050414401001601d01090100da11088100d070f000b04079034011004101d24001e00784007554402c140c4004000310080101b4040300c1d4000c2902c00844a903240d842014a01441c0c444c0707150940d10007030003000828403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 378368660 1250 378367410 378367427
    0x3080306040c030b04050a0506190305150601050f04060e0f03030a020d051b030c06040519080708030717040c05040e07180b01090803030403090e01050108040b0412050910020703020f04060b0703 85
    0x11030f090000746182c07890089801c403241101c08085680d6610140306591800000c5008440103852000d06404e0850740c030307a40c49090502029240700b0b0441e0104405a0080040e5440300c2004680399071125034424009146042c41484940241032054000b20705050210440d1186c0f851034008001c05483c0d02001c803107030380c00f41d0304080d0002c4076800c104003220006e000500380490000004c1109003400d003005c0307007400070000401c3d142c4842002c1240020fa44481035036582a0030103c41a2640c0c1c4141e416646050341407200c0e40e02c0c480c0302c1c04109c200324181e000700342510301c255401c0104988000c0001c0d56400307280075070704002110b4041121107440d613070820864020103140c4090031366a1051114a0351b0000e41d0300f203000ca07900d040c0610541a44600c1d1500412003440c0103001410030b601e80d40008100a0000390001c1c034110b511212840c000c104a40d801c01c0060140c0c0c06106191a00944801c09800300720b108a2200301075a19900d86402040b09480782c40d41440d142c440e103903500b9511080f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 378369910 1250 378368660 378368681
    0xf071b0b072121060512012007020f040507021c0509060d020702060d021b0c0102010c2007030506011e080c010f0813061112090f0d0c030c05030d1b02070308030604 72
    0x302c1094160b6450003c105002c0b07030320700e0325000c24040e08000400051070041c4045403283d03807504001e11140b0103040c02c1d21113802480c03d100c1ba601d1001d800840c0c4a401094107094015062a00b0f200c82c40d0f60005040c4003c107281480d00b00105402c44049540d4451b6240b9158804410300c038484011546a004207016440100701e10300d060034100701e000503030f00100e845036003400641800c540290000e21129043c3c2c902440204507a0400c030202a10444110090041c00340c0051413410a40404200c0d4402440c1c01c20201d5481d9030f51404488010341c400c5045104281805e6400900c5c101c000850202c050b00c1611030040d040c00400c000c94000100400305400c500c55508800041035440c4916080d100d5111161540d0740e460409a903100440542151a0ba501202031100c00b140085840398103414185090258010310b800c080341d0403c42c072003016003180000201d49000c5501e5500c144184881ca280304500b001c1c07005030a0781c0f5022644805401c881c0708000060a61805038000d40145 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 378371160 1250 378369910 378369917
    0x1801140f060c190c090b0d0803090109050a060c02160f0501050f1201060f08060d020a031704320a08030d110408150103030813021804080f071b0b0721 66
    0x621410b105032406203d22210200d680e14200074000348294088540c0140c04414014000b4440d4540442d0b503030001403102810b0804040b000c43c1402c2400c0d0400c000b10340e0007004442c201d0440e810410024400355000030094481d009001000b444c0050201007210004001e540314140b80c8401920b040c4d005601e5030110900400c61070852480d07540310390b07002e0b111a41d5500052540810301501441d800f03011648280c00e1082c03404010b03a40c500b4a4070984e035100141640023007186061000038016504a0b00b070f010100b442d00c40003510072030124005c1c040001d01070b520000118051000106442c001d80034a45c20410212414000e90741012401058002c011072400750f075140004d040c036034018185402900500700400a0550005825400c4a120304040d1504080c5500003030780740900000c004040d01c1694001014054810242c034809040e14801c280e56070860302d0581c0300401407510311a1f4a08000801050101a29041c1c4514951280c4218400d1004903102d1a113503c0048410040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 378372410 1250 378371160 378371167
    0xb120a020d02030319020d02060a05010e0402010c061b050909060a080a030809120403060c0e030c010210090501090c1d010b09090126030406030c031a0a050603041e080403021801140f06 81
    0xc17440d814180d07042030302680906680700c10310b00006c0c03d00034040d0011300024141801840b030041c1094980341c003c1e909003001482150340d80f8200000c1c00040c88905d00855016210708a5183c01100074204994100c8008445079100380402a104c681405400100d40c090308280c0d001070302458800303410000c803104450720003100351843e810550064004a030a2030b01d0740300550029811900660941800314007401070080c070314000039075529064040c00b52807515502d84409100c003c0d032000005c02d4002c00c110f02c0312070b210711149007078001495244089982c10400068004001c3d020f850103120024001e0b18543d280c0703400b246000702c400d0420400700d210074544500c000020001030005240b15180840c028030003030340280c125500c1140075200c104554120411554528941c041941c40850300c40d80c0700d845500b440581050b80540381c507110300140e41e255051040d0350024100b1640708680c40c00b012000c689041800c80d0082c45403181c2c4010161040c0d00514046009594090010700712505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 378373660 1250 378372410 378372427
    0x70b1606140c0702030d030627021c0c020f03030106091202030c0904141509100507140c01020327060a021b06012402030f0a050f070506090607030b120a020d020303 72
    0x1140842510030154042c000a4590118141805200740d85040390408014051900300045c0c15131000c10f205902920741c0c0700c0048030181c1c95905513060a48141c1c175500704601e020320031000500320500399001510415031000d0100c0302c0081124142c80e61a0361f41c40030189081c140651810740c12a04a13814003d0448070150398071403170300b150b2059002d540b4208103042d070b0240e0300d03040180303900c03088101c00d81071700800042c0503000031059941707042c10b007000610b66501402150101ca404001e030000c1c1c0300c00120401412015009140507070441c039248140e143d0340c800c18031610015485c2c0704066030410380c0000ca40d4800c5502400745414418102d0b40002c01b01e401d0741d400c004d4260007071100c2c6229400440b01c2c0400c05040f446803400320b400154582844024505824082c010812042007000101c446413490850b0903241a070758494119203640c14001311403521800111100d800007481e04403580140e16207a40c182240303c1c00000900310400541d02070000c10f55001000b83d0b00b602c0200103555 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 378374910 1250 378373660 378373691
    0x1207110622051005071a06040e0a0f05060a09020127210c0503010c02100e100606120b03030a1713020a0f150903020f0105030a0905101d070b1606 64
    0x807140e658158101e5405007800300f041002c4070700c103902c502044030034041c0000107141c5d10400c40000d5400c00480341180d4070007002401401d00030102200d1801411b403081c04002014207440c8040c0c1c4100f09941c2c0c29034606c06e4403001c4800d0800040d0006000030a00006502d8141104440501c550071308100710761280d081110f44d02030f107c3d440c1c510b20038520f4558240b040c020702c86005003030118001e2001c1c00e10280000e550310314050f090924540d54030300e61281000b0420851400c19011801800380740d40e00c400140c46a201e00b20807480160820000103100d103000b108440f443c081644808040e42400500f01d410284001e040c52007481070b05681c64096540d041c06a03000301a0181505170140c01c1901c060401541c1400d54414410400024401070380c9200281c0e00c0f02c182031130902d03141d0351240c0403000030748003240024101d80980006c07601e03000b0710394128101104081ea507210351440c11800480e0385401c64400d20304101d07000d02030250a101c1d0180e404c4202c43c080d42d80803075000350610040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 378376160 1250 378374910 378374947
    0xd140c010b0402130918030e1903021009140306010501080a0c0e0d0c030c0b030118020a03020d05071115010e0c0c0703050f0105010303031406010e100203070b16030e12071106 77
    0x5a04100d00301404010005c00c501640320000e0315000c990140f1400d03507801a0208a210000e207200e2600071085080c04541c0100c3c62004640040030401404120036000d070001d04a8010014140e40404140341c441c02c0004200e81240c906030f40e00101c0d0303035860640340024041e4055000030000004203010041e5501c50442101d5030154015404140ca18a003c14500e000e5500c500000c1e00140010400b00c1a180716050b00c0c02c100d04009a62401c107104120024420003800c102e45514180038003000030b521040061400d0f800c10200c130101d1280c0820008803c1e1300b4441c4281c8000e1b090002000e00c01c9040c00741a120954408403120a40c50b40d5034241440484042c00d101030707559000400905505024005100b03c42c0c141059040c204040000c1c64171849040c404e024000854490001d207100700200e800700f58000421034507a0a0540742c28802005113104500043d05105a03040c144002058094003005072139240791416855594829900303841700e05161740007005000100c02c45a131a0b000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 378377410 1250 378376160 378376177
    0x703020313170408070602120906090409060e0c090c0f072901090c0807110a1209052d0301050f0412090b0d02190206150103050903160503070b090d140c010b0402 71
    0x1543d40341d50411043e2031410046910150071503001c4542c95690001030000c130740c401802910140d1b516440710021034040c1050707100c02400585080140041c04801103204520a403003259401026203802c1d000c081c041c080c4000003162503e08108040015400d1007030340e41a002e07000107004046400780000d82c2c0400e0240e00004009441d41144580e031075020480c00c2d0700000c642003010506403210060b0342d9450b40003800034560408074208200040c020707080710009020080c0300c180502140103400e5020407106d420b03030811500e44192030740e0510741801402d102e040301030740c080095901d540703404002111300700c3c20b103042c440410004500c1c40901e400a01044040b00000b5035201d51481c040030752501401c107000115080392042c028112303580441080507080903e80440e40d901c511a5090442c407030f400401e400d8071650f1044100f0404040090119180102c618840c103a407036264064031509814900e07000180800b01001352510020054143c02003480000541e8866080109013280d00001c017 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 378378660 1250 378377410 378377453
    0x705010f050709060e0a0605040303030e0c1f09050f031906020f030406060e092b2001150b160201140c010603050c03010f0b0a0b0f13030602031506070b0703020313 72
    0x101849001c1e007043c030701100042c064520358030711440c0260003041405240001400c2540307485101c8040d02040054410340c43b0020000001031281214259200c5d0240c0d40d884042400c029001606242035282d004c02c0080180140105c5070307005181440d120f0f100c12003159020382c01c1c03080c8080c1d021024083c2d44a98420340000405900700440040c5944004090901d80c1d440a018210b215100c40441003200b080456400000a4140c030141c0b01c00e400002c14594005090800c240303040d0b03054102452020070f040c440301c1c07442c0e1584450401407180c285680301a50340407000c10b0055100b0090500300d510318254842c2013410848004c1d0030340b807181d4402d07541076000c080c280b0482e20f401c1c400d00c4034900b0354880820550a05c0404240c1000c0c16100c0c040301c402000c0b0b03800c40c5c615480c4d02103c0000c1c9071a50103010107501c81c50100025042070b0344c045661031490140da5440d0904e00c00b191802c6400400400440e41c0b94403046010703600c0185950004000c5c807818800080e081c80c80e21031a80c03140b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 378379910 1250 378378660 378378677
    0x30a1809180218070210050603031c0c030509120a0509040b0301050a09060c0e031504051c050307030606031e050406110403030c0204051605030c0a02010b060408100c03020a0e060705010f0507 84
    0x1000103500f400b102c204000c2d4241c0080c0180150001107484500400c45008110755803080c0c00241540940794102e403001945181407030541c0001e81c045050b071000313a01c04000d42c1c1c4076801015510000005040301e40d080410080b1200350141d0003500c41200020300100c0c40f016070300042170946d60305485070740c1e03422384801005c81040107034010f261403099a450305203d0540d844001079030341d0b560080c04445040a04003c10180802803200c0c101429000c02d0303d42661100b20b2008100b54003c6402c1d0780080c0c600000803818600c81c0c02440b039044100e164032001d15080302d030081d0007003001a10846826640d22003607080424040080c20040d0b02a8035001e01c4991640140000d482c40203050124140600c2c05000d815070f084400d498000030101c084503100d8032452416401014000501d980c4a480403034001680a0005019504c1254480c1c00340302d05900a54150281d020300c01f0124041490301c051004e01d820001c0180c00c07010300620021400d8444281c0707580031034500392040c500050895 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 378381160 1250 378379910 378379913
    0xe07210c0504020c0a150906051e0708070e0108131e0c0b03130b0408040905101806080c0f04150603051006020303040818120706020303010801110c030a180918 70
    0x6414000107020680c0c2c154540480100300c0340d107a16005000426805406072525155030140d400390703001d50703480f80b002c20076400e00b058845198214040c000d0a100c0d06200081d0347c0c0b030700c203040c0300c5c0c0680308503100d41c51071149500040d03071001c400400e40c00788100c1001003138010520b2903c2c009900b14810321108a10412414217200d80000740d0008079007c0d508106100d0b620060042d07008660340c016030882a0764035189002100744c443c0c2c0e03005400e041e0410051050f6000803030881812118070110120000d150b030300400096a200307101f610542e400202d03401090703040821100e000c01400507c00a0400c2c030180f982d00300d10042c0c1c0c20880019903250108603101040c10001000382189000850442c5484c0d1b46030a600d20032041039159140b40042118101d407100c0340404c0c02d000c840302c04d6500c0c0719294040255250424840c00225600b02800403080400c524101e51903d1121009076107007014400b420354a4059483d004d218402c0c5018002420ba09030b8826901c400104118584030139105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 378382410 1250 378381160 378381173
    0x106090611150105040c050f0a05030114030118030e13060b03010305190b010501030f0b061b0601090c20031903020705010605060a082701090305030603150f07030e0721 74
    0x456001d80640d502012a48800103014103407281102c90803034010505240700030045902d400f502400c002511004250220038903080809107068178a1410b82000d1541c000c403c0609035402c40815819009146137943c0c04a03101d80303622210b0b60382c081e11550b00307140c400d51400700700c50290384007121030000070006008004090140070441d0303048000090a030005503c800c002c803d01886018149a5208094030301b50b403841c2c1101200401c010045c0e40c0b04d006513500500d20701c11408500b140c40c0078101c00810201c4981c8102040140181e4408801c540b400c00d6072456160308900d0340c3d905100521a0041d00308018910000e60181a54090384812161420ba400c1d2815070700210f22076079040c08030345400d582c401c3c65103511a006060307230200c45201c0260384e0b216000c0000000900c2d402c0400f600241500980118000e04056044482848146c40d1440c0c1881d800e0b1042c0ca02c1090030b00110780711074400c1d004151050344600554420a0340e0f2503240e05800e068607540c92541070704106042c1407050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 378383660 1250 378382410 378382427
    0xf070602030a0906031a0603160e04050c09041509050c040e01090b01210e121c050103020105160525090b0301050108190618060b0a0603020a1209020d020901060906 72
    0x1180000d508182e4801405080741001340502e40c10141e6503082c1d80215000000260700c01c00c0040d21841e41c904005002c0201d22110a0b403260201d410741686103120b00700752007041d20a1003d0781500d414480c000f4100009010100c03c0355001c2c0092410208100000d449128001c542181d01d0581d19444c000c0010041034050b80034580603441c0c00881440c030b9030000500081024941c90444401418400e12001081d030300500011074030404010140145410300241113180d0300f05001c54004102c41241000e17036600f4040280041d50521565680308035000314090401d228000380c42c42050052148001281c12080540e681f9440003410090071500784214a00c0b540240c000340115810b211403955901189100c00c00d0020b15a4a0b50081c4410b55100d444092964095039401d4078540c20071101038405140041e109030300800300007c1c824002d1003190f440c61643e0702d41940c40e41d81c1070795013030081c400310200381c2e049405103444100603642c1c1e50403e4064081c40c2c50303800200b07080007030040c251034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 378384910 1250 378383660 378383669
    0x10c120501060807050304210207051e0307031b030605070201050601080105010309020f1e0a030503040503070f0e010e0c0f0d201303120c021807030506060702060304020d140a050f07 80
    0x24a45001030255a50240b03a040e40130805040c0a656a111442c160441710070100020007143c4000a4001100c3d42c0030914404603401140c0300c215900d10756854001da01f241e50303c4e07264140d211440c1000000c450100c500b104082d17044401d10071076520348030320094403400c40f00000107035500d20405c0071560b000100240234100070300e0200070b444103a42c0490144442c42d80e200e03215514a4142800104207049a240182406840300407085da403450712940d02e8010b80110f80c031a0296100c08038030325038420b00d6001240d0070321035862040c3e442c0c03001416014101a01e10b207407101040085020b01c2030540020b10f1408090340c00028510444406c1c09403a24000865520f807183c00c00025035a00488040c0a05894011024040d80d00968200303440c41c0a2140c0c00a400c81044502c024250407400e203541d00ca6503003510140142e80c1e94900b000840d110788000298400024004600503081003404421101d12510340e046442c441210b1043c541111840101c4507544551f100b0b02c1c1045061103228001c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 378386160 1250 378384910 378384947
    0xe06030406020d321522050f0c1605010b0405010b030a060503010e0c01030b0f030a1208010506030415020306032805101404170717040503010b101e0e0a08010c 70
    0x8600400030400403458101a004111928000c50905c0d000300e1039040e9522001462518052818403c1906965191a01802d01850800007800c07922401d130401c1d2003103600360314892030728089506a045940b240c4100740c0341d540d81c400e015007071074845214003030181945100036038480c641b51389a075080d01c0d241e4105901030b90500390800d030b01d124002102403c0c1002400c0204043c0c003c0c03804501d07480040c40b00194075109618405080c803090400c05030320507220360303241446a0b0304c036014802144010744000700035800c0501d00c00607582d026800343d900800c005040e80d4400350807400c440c03059800580c155946503540000c0718204002004903c503603450a40c010722201030007400034100c101000b040a0311800000b4400f42c40b14001c841100c603520f90014060300c060301c500200b1525030700180500da000390f182c010b5085143c80c1500c03540e5103080e000c4d91003109013041c0314400c4020001c0310910106100b50051020f1981e61900c001314081d250640001506204a80005215031510088102d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 378387410 1250 378386160 378386201
    0x10204230f031f090609060b030d080f01090c02030c120c07050d080f09060c0102070501060e07050712030c0306050402041e0f0f150e130504050c1e100e06030406020d 73
    0x1500c0104803100c400702202c02c62602600b010f0b00050180520000c024485450b2400132030412071981c4c050728500310140c0440300703451442c076011713170f4000300640c0c00343d1992916400401c03070154030381c0000105075264816242820f043e007441d2450314843c6001c04174013400110300001488000c08c0700b5001054115031510b110b903c0c6403a068058840d0546902d00044001918950307503ca900448092000300c0c07000710365a00441c10007038002d0a66008200500081202003a1520303c02e1081c6c601107908000b0b01c9090b4409040150018621005044141501d074040000e80b941c81d40f010f4801841002080801c034200f4030381d1407607030a406030040203003115400130611506060034001019a5200f03040e00070072000103241600c00072110100c9940c0070700c0030382125030322115076003100780610302c60801c80c0c034102d030381404205007101d100b019000b01d50214850304070310740341100b401200d098039810401c000312003080c0450070640c42242c01345d61803a0001a10300e80902a0310403050b07034041c13a03007007040c1d07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 378388660 1250 378387410 378387439
    0x1b0515040e01030f1b060503240102100509242a18010203041701090515152b0b0f070302041d06040b03010203090f01150f051003060801020423 63
    0x70152060001030081c60840f100741c02007007545031011103405221100d51a806951b500e00424591080700d0098440068645821700f003400d09040505900c4142c02402545201c40c41e410003c1200420350071031031080103102083c696103101d00b0204c41da03095551112a251104140c6114204810420714141c8803d00311040e46540005440c6011400c140c141078800c00100103d10718040c1e60440041008031002c00f55000b10305500a5000503c100f041c0d80c1884100440b10082c11300403220a003038020503540440c0d4900e06100e80c41c5d1111f206079a442c43d00c00381070f0400c00c50340d0a04202245c4580e641e500744049412803035405948140305240c1589044e042040e011102d1b000461b03201c2c0100b0803407011070059610781d0840409020058000c54803450300031062903840600140c00c0b4059403070081a1100254141c5007403040e1101d0380034101a85140c04140842c2160b4032144c5010582e0700c2c07601003004c480a000600003452245018100300d44512031555041c0b8a5210561042040c01184071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 378389910 1250 378388660 378388679
    0x20306060d03230406020c040b01050409021605060a0b1f1205090a060908031f0f0b0f1209010615020a150b03010e0105010b03040b01050312030a09030306031b051504 73
    0x268044401d851040d01c42030103180a44440725100440540c0c49140c0014820326100c0c1009802100d0031a82250741282c204400c2c401100e018070411800228100001c2c40b01c410240c006001011000007068481b50030758031a0790803d601690305542558544462049510780020b1080c444141d1850b550a2215a108050103803898441a200c1e035603110702c00100c08a80078008000c64a4001d4014052000e082c0307404840b03a84100c035100c02e41c1c0c03142206456001c50705440001078502d42c2100c3c42c0100d05016650245401c03c80d90300c500304a0400c101a44078011180c1d16001c0d007814000403800b40e0401070502d40229441174044110b508c092070079004201021500010103101132400130350b0501042c04640904010203100f0455800d0600004940b20107100841c4524016410000281d803103d0815890702902c1080303099030b2030300f0f20102d1112201a400140d01501c2401d00040c43d0b035903960b588030b44c4d44035080e0508080d1040542004030741080c1c050501c504c2419042d0038071b024208080ca4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 378391160 1250 378389910 378389923
    0xa230619050115020d1209082206030603020109120606170c040b0f0108130305090d03081b04030206070b06180a0b040515210709050c0406020f060c180f060d0b010801080a0203 77
    0x742d01b00290803a2980910405600451030340e90000409942d40d005130516100c80c1c1c071b14950f007406641e001710380025442e11074400c2009613071f4160356a848861414546181c5e1304214a0161009580c0343c80000d004070009901014459601e0081c0a80074414001c01048620035549180204009c50958240ba0b03803203981e907540102044542c0c02c0d50151f42c203049405000e824512900201c1410540003415040302c0c18138440c02c543c0810a01071460141c02601600a501c0000d400c400c0a200441c00501c04400c1c19a0200019009111242804641c0d5220220550704e10b10300c2541c038181440c040c03d00e8010258084c50480c0c2403121007040b04003144100b14100d0000f4800c0151260183d000d034030900000c0010416a0784c04d10250a1031000210503034480d00c01c040162040c105000c1000c0b10200f02c9a00c258141000305040a210f00010702d280344400210319448001c1c01e01041c0107565000140c200482190341c00214084000c001401402041c0c222a080c0d40c4602e036820300682d40000d08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 378392410 1250 378391160 378391183
    0x10c06090c03060c020313080307080307050a050d060303031e0905070902160206120613110d0b211b0307030809010507052e110c0a23061905011502 65
    0x19903040508188181d5503603a0001040b490514040f0498181d000003d00b11241252041c4d02805603140007255481c0300d90f1750011b000c84810700014011601520241101d0740480c10114a044000300a810032606560012000f00b9540e10041c80040360704120b1011116015104011b0101d2686070b10b070380d5080300d104440c1d0403500018810400c0c41c0c5a00d20711040d643c0a0540b54846040181c200c2c080801100e142e070150740000343c040340092450280300500701101d40351910301a03100d6100c4016008076107010b80c100300d414181c507a00c0d203440e900011109a418016003490500c00d0f803007442c15290b03202201c0c82503010907010300102e81407800303e800c400d03000d0a01555541c1103103020b60405038500d5041403a8044100403a000e58000204070072203101d0084200300030355001c0310001860003002d951100c40e0f0311001c60500021940782c00030305041c1c01e00d01180c0d0603070980303103025240400456075044002003042c45402480c10600030240505412440d010f40142c00b404020740d07540741481d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 378393660 1250 378392410 378392423
    0x105031f050c12090a02090903071505062d03070605040e0f060a1e08060a02070b040212010e16050a060915031113090b010806030606210c0a0602150a060302010c 71
    0x403400c80b02002e000c66141608029120701ca0740307000060785071036408600081c5c1c0540440f0002801c3c22001208131000c40741e01180c5a4410300180d8408401031000400305504200700e6800015030030140e01003003125950440c44820840d883c10305140c24030311a40d00c5001449001e10061140441b00c5844a50102d50078031208502c2c1d82d0103000580802c0c50b580428401740c8481d1450030400f120302003503020b4a545600710743e06030f101c2c644450100d1050306005000d50f1820380118005140c6420040c0ba891003070400070459541c0c4000701800c00c01c0c501c0c806003c0399001c00b0308201d01d04154040c1001407000703080202c00349181600200d0000b65412016041682c1da03104020300d1441d00c2c069461201c0c3c09941000c500c3d84801042004011407203006020440010001e00300d498002003e030301c103840142c07041c181101c0138642e081004c14441030042d110b009004644000e501d031081240002c5c10316030b0050410009104c400e484c0e00700058100d980440c00c00302c003400540d0300328a403404025070044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 378394910 1250 378393660 378393671
    0xf21040b03090c0607080301210b0601051b01020a030c0e0303030108150718030609030e030a080a1101020d0905061006050c0a15020c0a1b1d18070f08150105031f 71
    0x500d1030605126410813548050081829010f0180d00c00c046c40c10784222584006610034400d961200741035861100078102064440081c40e80d5229601800038400a0419081c1c401c0389030034503c0c01ea0700120100e0000a90b00d0400300040d5500c066424001702090700035601e0365040c2445142c45032411035400408094032000300b103180e0703c500110004131800000b1110019142c0c60300c00f01400c9460026400200002c000030103034034011441000840d03104548900c0c200d01d1000036180c0e645485c0074000155401e000f00314001c0e6160080c0c0c03145500c1840034003400e280041e20480440810b401107001c00c001030291120050f80082c04100964014120f0b41031541d062900d80042d2042c10501186401100e610104100b00c1654803c0100902803402c1151501d803002c0c110840100f03000030700c0503030a100208410190102d0a10aa40100030540d600107840304042c80522381190b104d0907203940042c885401c407003000404580545001c801034101c0300080000303030303040c0100c40c01094641c079513a1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 378396160 1250 378394910 378394921
    0x6043206130e100608160e061c05010c0f08010312140705010c03051506070201050d0209041401060c061b08060907120c0c021c02011d0402070b04050f21040b03 70
    0x6049a212107140c40c03805206510280c0c05079034a458150104984043c100325010507044004a20400d804c100c0d005e602e80d51602e403d0000d1024400505407a401c8501a500043c9141a602d408261903000e000045503150507450000d00c0b00005890381390401078004018000171b110344005c11a18504c0749043c01c100c00f041e4456258038882c2d444014911344c80c24400c138803981d415400c460310807a070300403641c0840c0d01c000007480801c1c890301c20000c0c00207008004401806085501234014400c0c003510000340440c14601c0c0320000c031000c1e00704c42c1c045005c01c2150410415507001d10403243c8a080002d001c10349a01d0405060b00101608151007001c070800080d4409100e260355040c440e0ba50407061040d00007116026000314110041030380501d003448a119811801c060102074000d5061751900000301031480701c1e086c40001d0421040c0e005408204400214100b00c80080c0500d00a00142602e80c817650400f074580501140c10100b0b43c41f0071012030103c001010706580490328103106603980c3c0e6991 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 378397410 1250 378396160 378396169
    0x312010f21060f060801200406020d120603050105040503130b0708160f020910050415080d12020c10060e180d27170d0219020105070809040e0606043206 67
    0x103c9a1221850040b00141900054000e0500c0c00d007245a1091000d05414450009125034054080581d0041d40e6000305184038545140e40c04405003000141c03142c496880302e0035204162029074103030740b0224810440d44141c0c08114000c0c00504d0f144c1d4034050156403884c0d031501030840500c1c1c9041c05844081c0910295400d400e442035802800c01c2c1e49480e101d009510102800d005440c00b07285882c0000b05480488250b08007640d0007500103003a00002044211a5241102000c03060342d902071040d86d07008241044025440038030b02d5804982d13541842070503120420010100303500c008d01c040c2603008121004c5501e05070170110746080c000380413144c0683d01100198542500c090440c003200002e144064540304144070b81c140007501c0b01309010f154100ea40b4240345800950b002d0f00b1249407030056004000a084207841404414200101e0100180454504104650540e0001000c0041d5807516200e120a01505170000c440e40b00b1040c007114441510700c2c40ca00314072075004001b040780d5642c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 378398660 1250 378397410 378397421
    0x150308030703180b160302070215031812040947060304050c030607080408090d060b040e0d020706021609050a1d030a081e070e010509030f0312010f2106 67
    0xc44400c100350000f11460542e800040c01c880d400a02c1a042041c0b10340742c1d00c2070013101c556a8004210700c007200707101c101710f01082d8030103040e0101120642d48541741d0b00c10180980c084202d201800c203a103451400000d6010340e808051130b0800407040c0030180780c51110030480c0002000754001600e55141407131040841030190304840c035900c604044108030812030005642c841e004002e4040c5c60b51f80c0c8072864241c5011409981c000e10521051020441d581041c481c0306100a016070004500306645201007011220340c8012840c554200000c1081b0540e010030541e0300600e094402440e04110031a4021030420040c003540c50b080340c61318007184020b0b900760410f8518400c400b114104100207095480d03030321f03400052072802040036000000c4940c10320030340b03054030400f220000e20000da0300c40d07a0448000310901c0c4c900e814008107218170701140d01c0820080c03a0001c40000115942c110a80304c20000070b80503441090030110740c41041c413120320f00c600707000b10303101400e0750349016440c051070208090031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 378399910 1250 378398660 378398681
    0xc0a030b1908280209010b0a0509090c0a031401050607021302070c0b0408160b070209040f0b0c120f040804051201060905040f0b0a0c050306121204060f0f0201150308030703 76
    0xd40c107008a91403a000c6440c18950100086950200705298501c0480250f403800283d4403002e441d004004000d4800b0081c00c40900624040d40f501c505071001400c0308109641080b00356101090400322207401d0700c54055074111281c82c0b107200350303d8440020720034424404002c0c055a1005025612511160142d59000d40c0c48a8141e18981d140c1c2d46002881d0420300c00e1081c148168003d20b04103142c071500a0041d1000d181e801840d0542580034400c584002030821200180321340309001c041205018624042c0ba1148125aa91510350502090812018264405010b440b1050000103407800c03007101c007240d40c26110541203001b004110303030050403560300c0030103000c2c1007108000802c41c0c0700d9241018907100d07131892003441e1200e1801e9400c840350304a403140400c1c1d0400c04904a8903282003070b4218008000106c030b0003030942581c1d2b5812500300e0362260000c0f5000c0383d480000182c00020446000240344002c21201d402c02148110342030071440041c105c3d95000002c11b140318440d03001701c040e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 378401160 1250 378399910 378399949
    0x1c060204080f0109021f020606120c1002031c050c031b040b0c010902011b170903031b0a0201030615020d1b020607110907110c13090f03090509060103050c0a030b 71
    0x4603000c400ca5406000c080e0401c9200d10003030f140041000301c6c804035041200700903074020145a80c0b4041440228050500310b114180b040c0b42d0f85401d10ba4640002414034021a03001d15124040c90b4844d1014541103410150340908203001c02042106140649911034480f03012120104241c4004513018881e50b0410300109000040440f418201500180301c480d100381c5c0d070100c103810200e044900c106030039139006040041802c5401200341e03000007d0080008000c056910303100c03008105126248401d102100150000308401e0107560701407140310014010192501e01a07851500029107510b100103441041c813603206100d00a40d85108032904000f58040e100036500d40c0703641414140d8001d00e04016102d2509c400000e40d586100c0c01d6800d6683c41410028144401d0490411206a4000740f1580140c2d94529030321002c10b030355a04202600c1c0c02074a41044041c1813505111f82614018a070505040c1042c06000b480410042200d005c80e05d40c0c80c001071200c04100018012020341d01b40300220 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 378402410 1250 378401160 378401173
    0xf1119081605070806010f0e160c020301150905090d0c02031203070309080304050f0106090b060403030e13021b0f010c0e09060d0c08010b19060f0807030905120421021c06020408 78
    0x113400000800030b058420b42c900340c80c03220f07944d00d00400f0045000c80b0b41c0d101011420010255850140d0080c0540510003000072803072982c5007540b80d258503002d82c4111061038450041c4814100d0520801c8600065450300c501e8030300e0301e500802d554450a084000c0c011800000280140e40b02c0d41c4642d4821303910904083d56400d142c00c3c001d80e070710070031304181c1469442c00c0b42c0001e020285201d032004c9a100902a40d0520f1310750703203068076003802e10981141c011020702e442809881083c40209001d44c00c901f006001443c03099029450100c1810b4400f9150b8075160540f001a9005078664100000c11101002c079503480a000c1403031868014801400303c900074201058205041d0032054540382c00b030380d4002d40b50010751402ca070303200380e01d1003404042450000b030540c00c5486503400c268030100a00303010521071010fa403803600c2d0021450741c8d44501c1c00b003c1010720403640c1500f011012400c40c80011f0315680c606800007420000d5416100c00c40c4071180c4000820800302d90140c070700601c05101541c3c2c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 378403660 1250 378402410 378402419
    0x702010813080d1d010506010c020a06140d0f020a140a090e0a090605070509040b0904020d08090604120308040309091e0209010e0a080f0c010503040b130c05060a0f111908160507 78
    0x81181821008456035401e000001e0b1f8594451343c0e030a43c205400805c8440001e1a284040d01c0190701c1500d041a601f104000074007245e41d4a000c2d803000d662039050016520000024001c0005000d030000300a0010304001c0b074104154008405015a004100701e81c0c41038840c000311000501d0307420001030489003024104100b880d0404082c0080f20802e036024805a030030301c82000401354085800a40c4444220440804030302200054050340c07101070700c06441e2689402c00895501c1680d80120000760320001004100766000c0d4012004202c044400d01100f444140000042d4000030302c00f01f046980491a995142e00c17800c4203045041000c1d084080003910349002c41e44a00d40c00c11703241414401c0d211001403c0d403150040b0380c401c980005100e0a5900e46502203c0c41443c0c00c070302500d004c51044004202c035501c220061241c02155222040d0503c00080042c141d04281c0c0c00000e46134210240c01088030062101c542c408030f50141c0340381d980e50501031100c48200800c06000e801803007956800715 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 378404910 1250 378403660 378403691
    0x20904090b0f061c08070f05030705011a0409050a0201230c031206010e010c261215040608070e0612031b0f010c0914040e030a030915020702010813080d 67
    0xc0c02850310030310580003a9070b45000e01241c110101346002d160a001188000031540c80c0c0e014042c0e0f2445030103c00b041c141d00b500d03074504c2c5401000c41aa40ba965450f92048072507002c1d038560050010540d4144002c13126500c42da0345410405002034144540140380340d10f90203e0031a6488841401c9641c00d4840f088510134550341c0d005a45017089503910300c00815079035030145030712000c0400140c1d982c00603100c079540e940384800710701814588041b4559031701c505240400340c00350402c4481018950024a80320b4028410345607030903001400703a40740000600c100c1c440410008213941607802c0001c50768480ca408200500000b00341d410040c00301007a10381e14000518441e18a01b059070f821120050b1039501028201c40700f100812001c265886002c0080445150010b200d03168000c2c0700060543d0100300c03441c1141e00551070840020781d20080d07401008800b606465040c94080011820724000c4d0b400a030062074043d042c02140041500381e03804006503c0b044908a80c400e00052040c0400c052000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 378406160 1250 378404910 378404933
    0xa2301080a020102071a03010515040806040b0915010b1b0c0402070602090915030c12010f060801050613060f1707170307290420041d070806010807060f0302090409 72
    0x483c0140242c0e0400511442c01880c0b1303101c0c80350301410061842c0d180c83d00300a29a842a404040200d009000000f9034103401d200d280d100382c1c000c0740c404e006403401c00350f1941096403a040c25501c5a084100610102c0400800d441c904c061481d500d40c038001e01c1000b01c80c641110076046540c01400007501e1020480990080d16409600f40d42c1144941c8609500ca107c400e281180203406620102c0c0d030f11598946900107103400440d0800000f140c903d5040800196412038200841680d181da040c40f1803400c1010031840d070700003000c1080250504200503a0210410307403241c1c1c40b074000d402014000c440301c05c3c01400028014408000c40d001031421009499810150307040e100618056403442d03840d40342d20303075450615003400b81d07090355a0348550310050440103145a858003500000c0d8000c1c07a0307488901c1462484d0001a035034040008a400401d803424200342c12003581074002c4001004840c0c000102e500030794606003001900079031510340c201d000b40104060303103030320500f4860014184960a20503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 378407410 1250 378406160 378406163
    0x1b07050a03020c09150405040f02040207060501180c02070e040309080307050d0801060906020a061a040f0609241701021c0c020d08070f030b0a03060509060f060d03080a2301080a 78
    0xa603950440882c08100c140c4e50121000f40c403244081d103100c00700e4030306540903e0b0321a1044035150182c600390b401013002c80c0c004650440310607903584010710900d40c014031960412123580c0c900b07200d070f104020f01c029100d001911580071030f04004400f103410540920380b1540071b481400c0403aa00c0341c506080080d5200070596480000c27074409800414920320500a01d01a81c41d05d030000d00549140790703518802000040f05244c2c05003540c0f080d100c2261354a005561380903400300e0700480c1c400d040c40c581c14101d9840381e500c4564000d21007403040004014511042c200e031740d2188640c01c030580c1c50000c01d000e44038800c05006040107909040c02003088031b603c001ca030ba90007a03084070074000e4800e2058510800c2690000081050f10416580903413207900042d8584034060400034416640740da51405840060b0341e00035a42d0010001c0200d07552a6086180d440042110011183c41c0b80f9200038200701e10180845c01080e0701c481c00302c07a520745d4101080744031860042000300e296030b50320701c05510b404040c0380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 378408660 1250 378407410 378407413
    0x6130603140c030c0c0708010e0706080604060e06060a050708070b07110d1b0606030c1214030901051927081005091902010210020703090311090712051b07050a0302 72
    0x1496000100005400344604121400b0b5403440d1940d8000d18001e401900c40e01c00140700d00e50340411100c1080c080c0b07000b10700007030005148840c20100040c01d00f4800070000b60003940b0708001040005420442c240e0803141c01d8510f0355580808107021180b620508201900800700040c1071303001c015140300e079648200d14a607500019989402441034494507400c2d1018005550010440c5038841c0c007249000d40107201c0e503c00101940c2d203680c0c008030781055600c000310141d44041610181715041300d040b0310314000900a5441c0c00d140e640064494010302c09503180321010201284100d501881c985102800000306c001c10139101c8000b103181d0ba548a008038001070041000d40352412200c1c2c02641e00620200d0301a010700402c50840c1d00381c40307130100740981c114460a0644240741025100a20480e40a581d0b060801c60440c20141d200e003c03200e42c42030003180c0102c01c001203603501c040141070310f20b0241004a06a10740750f0134132003d44180c0f8800c04198a002400303804202000134001d030506c0c800d80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 378409910 1250 378408660 378408671
    0x1201031101170405060612070504110a080c040e01090b0607061b180303090e04050304030c06020606100801060503070c060e1f0e010b090106080403211d0120160206130603 75
    0x140b50300c5a0b00400c2e20000d0565110b20302007142031a001c0343c00c9412016401c211801183c1d51400103040d9842040c1440c0c11510005004c5040da921000f8940e1041d450348410749000c0c030f07020780c26501240c1480b40f003030362030b82d10150710000740d46100440d418160050028048080c80013042d10540065111003c040380b12101a4140305560030441c0e81280c0d05516200c100503e030552044186034020300c2184d850000b0440440000d0014280307401410455006100d1481c100c0e087c003290408000c03c62040c00f071280d0041001550040c112a408546407408040003180c03803034054003a00ca8007202d022903001e058071005100a482c04d2800544406900901c0b03c122405901400c0303800c0c00c4807280e0001c400d0001813003900d024214068005100c0d180c040b0b00340004540b01028407032012360101d119034540c2c0006140a2500c81d40341400d1f10200300810040c0e0742041c80c0c00c5903040c00900e074950303a20045841c41e54042d04801c3c0c9040d081d0040e200d00c0da9600d070124a42c441031203501074480030a1521 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 378411160 1250 378409910 378409937
    0xf09060c1d060703050d151d010b03040b0105100c080a03020a0e0607030207060f020c030703080c010515090a0903110105040303140906010605031503010e0723120c010302030c1201031101 82
    0x1810051030507000504840d15280807074504803031560203160841c815503101c002021000c800064018020300c400c00e580017240802260040d180d81c010b81c0848a207840900510020804403a01c041c1155002c44110054440310340040c0d995100b03034072001d003a041001c2200c841c07554050b0001c04d48174503036641e00520401002c080144034050810017800503405414180200c44c01400c1c102c00007080e0740100c8034821078260002e46042495002101d9030400880d08032058002401540d4121588a09154842450601140c014400104411030b02911a40b1070310502d4040d00800310300407941c000a104a24160a024020b0300300341440050400607200018256000820303c0ea060f03840703e9a6807031568540d01084115809440364460340765603283c603c045004000c000c5400280010365a0b41180d0401143c4038802940b20382700d43d0302032041007802e80d040d0400811130401c1032409080c016201d48500812001c14012401d4011a01807100c00200500030768030b1030b04128900c01da90311070b1480b0f000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 378412410 1250 378411160 378411197
    0x3060f030f0f030507060218130507020d081e1f0602060702030d020318030d0f0506010c0203030f0d02040b0d1a0a06050702040905010f09350a11010f09060c 69
    0x2600c0040c1c0072600d22011880003070700c025140200c9901904e0214101140c0340c0f42d110403a03200c50400441d6031000800e0700440c2c24085030006140360300c03000c10001c030b00d004003010b5240c1001407501d20401030310000081060303410311803051154034400007600302e03440e14a0400b44801810b0240940c1784140602c001807852000890034441c21080d0702842c00c2a03025540d080280d00090002006002200082c1e0b107020030030400b4107032171801100046040074030b40e40305d00c0844601800550411808040c0b8801603240042251130500c040404540c0d120322088111b03000340600c0d0060740d200c200019450b030f8200041d801090100c601c040040c10606290010484091100d10610012403805e000c5c40e0050315113640450400b900900007c590303a00c0205925045560850f0129000003010040450f0216428030900303502001304c02e03240c6104007840c8030300483e000d10701c0c84c1010441340390070040c1103000a4000f006041e205036000c3c000142185820406404c2031a8400c1c001180e4440c0e40e4004002e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 378413660 1250 378412410 378412439
    0xc070e101e06080403090312020c01030b031204060503061807020a121803030e1f090f0509040809270403031e0b0631030c06020d030504020a170a0209090606010306 72
    0x80140180d5255140c0242595983c1000b8001d8007405894500003012404445a00001546d44e501512040c03c84400240490b070303949180c103010354403201a85c3e03208449a800c035030585180d82019510382c0c0c0ca80c80014803404191003d0641d043c07100c014000300640002d95840326a03c50a40860450303901e0004803041c2d461900410500044084100007003400340729002d65031507000d44100c2400c254031402d4a03d4000d11050b5400051000501b04034051b03990030044080c02d0101d8111006091a449951103030048603078591285080c03142c0004980f01d803c0003128030303044000d00c07245203103094140030340103108280070b403201c19001c510a0307020720100f441141c1c08600010a04e82c20031300310071450b0034200c1d90030351400c6940325400700441c55a481010043c008600c2881c2414080e4100a0003c1c148040075210300c1c181800d1000b0701c0016a10034046000342d6416080700d51004480004071032920f851004060740000d22541400102100803c2c0c2500c03440080c1c03020700c000c80d0f641a4030031030700b030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 378414910 1250 378413660 378413699
    0x515030f0105102003040801230c0c03130909020f010f020a080c1002040b0714120414010917010c0f0c0201021002030c0c0d211107020d080c070e10 65
    0x300100010b00840c68264215145a15a032814000180c5104589006019101c441c1e50090b0b00118082101e100300340500031003200c01241c0703600740aa080071448600704019040322201e00700841d280718404010000c2d40c1da85080001445c036010354804540009120b811f005a0103414030065031300555000f041c5150002a6a90044c0344400702500d071011580c001025090341406000036008030300c030841c0007a1002d80a0985041e03500c0a903032800c0c0158000c02000d00d01c090308100c20716502e0585520544040300c4401d10305400c080103010040300d861816420403400043d501201c4000c0d07a4056110110001c3c0c00e4945880c4401d102400b5a10400c80120090059001c101c4440742074441d5000b96030882c141420007400c04920076402401c000500800e480000d4112040c0c120301c90700985000c0d10303a442c4001c10000e45200e4000d450760313071040380d001a014000ca6203200040003075540c200c2d448840e10b02c0c10f554006032210847d442a8105540085e002c80740d0010226803452100050b03807585 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 378416160 1250 378414910 378414931
    0xf0e010b07020f040b0a1d0a0501121b21110a3002060406170c032403070308180a090b010e011803020943030f0906020c07051503 57
    0x1c400355003040100a420f6122075042915005860f02541b0b070350030000003a080c0503010005001501400001c0380c4c100503c1602c5c01070600004110026500350100700141d0032865651a15a33100701c0c03404032641d59484108002070b400039003564640900403400d4054424070310000c4040024040101144940c080e507801398441c1d10540c04c0258018000d000c0b46145112400d5200b0300079000070b0b01982142d4010008241c081000b102603554050300154864902c001c468114200070f800c0d40c2240e0f051241d803000c00c46907a016140e00e90760400c440c80c000c507030049005a40b1100c0b007071000c050f00c404990445c010780004901040d100da03140109403540e5010380d110030100441d4001100c000034815507507400c200046101001588401070554804c0c140b00d40720a1960b0500070014580101d0402e07900a4243e0407251a0300c2d840c40c3c40380c1c00101e200540380110702d540e224607030072004080007100146180d10029003000780e0f900c04501c0c4012500103e0303070b5601040b241c070110502884116203860a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 378417266 1106 378416160 378416167
    0x6030708010c0e012001050106031b0207120204051312030b01081501020601090f060f090c022503020d2405090d0c0818010e15040f0e010b 61
    0xe02004008021010500c0d0000b0030040400040c0d034104840380c062800c030580002010082c000140b0001c0003503596810300940145051403141c8646901512941941400410118111400d248142c0f480307071600e0b0308000c0240700082280d0107030b00402907400f001c82c2e903400c3c142e50400d9003610001500c4114071300151074908002e01d01e48001980c0d0b006590940d0b40030070100c5c11540341440101f01c2e0f08660400101420041c0c11668441082a00015400035250007041c0b501a2135020b417a0000103400b00c01c4000f03860144a07080000702020204018105004a9010350340621b403000d0000e031104c14019005503000d641c80c10265124020302c841c0d08024003149010b05000d09000a842141e651106400e00500301681c2c000c1c40264681c0c1210390188040b40c40148000705405185560450344034601d410074081c04803a621040d2020030700b9103800704010305a629040e1704030308 = true := by decide +kernel

theorem cover : BRFrame.Cov 378237410 378417266 := by
  have h0 := BRFrame.cov_init 378237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 378237410 ≤ n) (h2 : n < 378417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
