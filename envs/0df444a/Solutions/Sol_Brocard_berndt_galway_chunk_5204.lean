-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5204
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:06.443003+00:00
-- url     : https://prove2.me/submissions/38af6efb-5da7-4b55-b33f-ccc70e859bdf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 935791366 ≤ n < 935971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 935792616 1250 935791366 935791369
    0x60c0a020d0e1f0c141606050906090108180a050d0909020403050309011116091d0109051c030f110306010f0908030405040c0903240e03120a0e07030b0907210f120905 73
    0x1103614140c40c1d981798000030108850554549143c0010301080d040c80d6050031000c9011a500b0f00039400c1450400c5080404130300d0407800700904001c006010f01c25100c600c2c0301c03030401c540d0703400880400c41c00061038101c0000e00b600c040e1007501c0c2645d5001000c0e62030b00c46c0d9080111040d0913125070307409090085003040d00c08481c1c125000c100a161240c8081018038041c0c2001c0640a1400030f1402030b41d05201200d80010300200320b901548860800b092100c0d110b0000403401041002c420354200c501d00200c242041d110f10028621440c826030b6115a8400104011601d65281d480380d1031146e0308c180014400c43c5015000200000c4d850b04e08045866170380d0f00c401006a504018901005000c42c082030b851139103a0281e549208151030081d458846200400c0000d0540201240101d568503c42d26108480902028001f5600501c4500080c1002c2600700c2d102c0c6c1e600c1c4980d8284001c4282d22646d960008001c5208041d007280803030700a20510b4507020307001c0002e259400104000410f021805 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 935793866 1250 935792616 935792633
    0x70804171e0105190c0c03120204090c05180a060c030e06120f0405010b040203070507030e1306180f050601080606180303031515030f130f0203060c0a020d0e1f0c 71
    0x50981c850020849041c420f19058070100ca000010740381508140c01c020b0000d822440700d80704e1a6242c58000d40c01c002000469009000715081103c0c00b80c100704090b00050392105c064440400144e28070340c8611040c4080001e1208288203680100e80440d96060100740143d076070080c419001791000e0303d00424400c0c1c90520000441d201104003c2c1d0505100501c0801d102e10340052101703881c114910705000074041c1a030b0007601c00090400400b9140c1e03060944400b0724044019580303400c20702c410307904c6e404070140c1a140401c40e030322480e00c0c101000b504544c43c0d01442d8098070068461584580790b10042c0165580031121140451016542c0444240c5042006510031078503a901e14840f105607400700490f102403004a411015428024480c12608207040c5540081440c00d8500003600c45181c03401c030001d4a2007011350306004a5040120350420381000344810182d960903903d6004c65054250f900c2e014203140c00780c012102c694010500103130305940c007240b8030040c10240c220700110303070700c0040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 935795116 1250 935793866 935793913
    0x302160e010312110c100908030307030504020117071704060b190611030c101d0709060302040b0919020c0703020d0c0e060d030f0309151503050607030207080417 71
    0x95940500004000740403c003608201d0000ca03610302143c07503070800b02c449640c03254200c00c413520036160f11003c949628024019900245008001e5a071a880c05400240050034112016030128020041800c04660f41034940d03445035615807207180f4104052034141c5010f00700208120ae205503100f010740701303070fa5490400e00010408007140030724042c2040001000c000c540b00c0b6110b0964006d03c170a4500078004140c3c1004003004250004001d42a03841c0404211140080d5249500507a00003052280040e08a0b01c15a03000707590500c0381185a0341482162081102c02c00c2d8461541d82d204040a5000d800070401525050200ca51035074481c0c000540e0300c09048002c841c003090403213042200819111003c1e0748200111548a4150020703140a4000b214500c1d50008040d80d909102d0104240b59960749001c17018280100b00607403882031020310301c100720b01003990103105420002d220b5a10074001c940c0e800d81e100d0440bd003041c0c60188010300d03800314080124454042c07207511907513a0351041c003401d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 935796366 1250 935795116 935795129
    0x4060908030f01031103031e0c120a0f031505010203030601210608010203040b0108062208040f06020102130806010b0d1e1806061a07120201110c0f12120112030216 72
    0x2403543d403640c589030032200100c1c0d000a0294100303020070741d40407020300c110300587d54011404a59552103041350034200440d0b2075443d040400e020410000307482d848504400318200c0c5483c20000781d000f40706131251381c44c0b492203106e0050b8010400621103500c10b5521051020340c91000b160030802c0c1200140942c2d00c5500692260781d03002c41003209002200d003407075004040f804040c02c0b0714148001c1c0001c2c5040300d0710140d1400248003001034204180f0900b01d0b402008030301c042da030b601134841c02e009010754007ca4000b4100c9142c43d42c0400c07112030115445040310031105005291110302119800a0500040601800c1800c5007030700070145168020040021311380e400250f00a0464940f200031500e141d08003d6602582e01030001e0108101c070b0032202c0c196000300450140c20040030040313014003041301490081c101e0110300580b03088400203030090030049074000e403985c0c0f00c1813050001c1c081c0a050f00d4541100d2248004018003002e000741c2d000030710b000b8819a06c440030342110130078070341c102c0340d0100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 935797616 1250 935796366 935796391
    0x515073b0a062303161b0209070806091605190201141003140111070f06150f0f12020d02090c12010b031b071208070c02090405030c011b170406090803 66
    0x50f41c020050031140b40d4191001e01c40701d401c0d81440b0148045caa041021500140941d145443d50604003900c4d0f02c1d2a4140d00a021005030314000100404408064524501400714140841c0c410031080d44c0c040c45007006070703039014108a24040ea0305103880c026846102955a40c0300628190464074120303520604c642804c5003030692440c9403140d56120000703120034440c0d140890301407000b1b005800321601c41c0d030000030340320103180c3c00c3c1171001c000d0420441504180e0a80140043c287e5500901481140d54003030441075405e980b8400c01c081103a0012000b035000306643c40c01001440c01c14a03c0740c20050010200c1c1c107207000300c4000c0004a0b000e0b08101848d5401100b00000241060034007034801d080406e805043c80d140d565410313116040d001d2990144460840081c95a41c402c0420612403034000b0000d401d01e041c00c0c1021a16948294020441c55090034100000340e071804034002c0440c40c03503664240d0a14856404481d4116026004031030298440c0b0f944000310b00d00b800550b0107480403c011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 935798866 1250 935797616 935797637
    0x20d1502040905131b060819020c0f0a0b130f080705030c070b0904060f140f0f0414010e01121505130804180605041107060e0a050a0515073b0a06 64
    0x9428028042c40b4160f44208180c0003030005c035a01c14100b541104021503d174140400c05d58501019004410078111680705180707400c0341603100007d0907224140078119144d15603c0c1e10014481c041036040c40a000c4923f6040708070006080780005106182c0a0801e0301e0400901c94902030501040f6440300000403008030b1122890b240034410b020041081420200d4102c1c43c051680e1202c22903100828840d695103400310140762980c000c001c140e0400280100004c0c0d810f90412682a4000e020300d0b00d2841d070000012a0810b009101105901d4101c000f605102d6641c80c03e401c06041e00500380c40f95089000b0300c0c400002e100b040a0b0029042644000301a0312030340b00103400305c0d1039a0703110703c0c451810075105488a402180455100c681c200740082032b03c03c6030010b6189005040040208a8031802c04800700b4450041075a40d82403280c10305c02c417100c3d101c0721411150650812600c1c0d445500e40c042e410b4010b04000918580b011007050310504004000c0d00040c07200405a21441c041035803020b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 935800116 1250 935798866 935798873
    0x120f0606050c061e061c0b0709030606050904020f060a0c02030703080d151505070206121f060e0108060f011205090304060e030f0a0b0606040e0702071809020d150204090513 76
    0x505503112035540d00501d1140c0131034070300714a9100082c003d54060b41c40c2e601c0e814001303105910f039450b1990300210070844600740410300614450903848181c614502d01000030a09180403500b0304c1c02107400a0400b14001e50351010042c86a02c030300c68110030b00c0299905000143c50900c0400001c6000c1d002842c0c40f4000013a2900540c1c4000341036003d08000402c00f07108030740900e4011b1041054134a44144c80e42200c0c8007007005403062884000b9920400d0080008a05007900820070344451031030070050381035851600395081c1d0040120540071030301d00400074201d400e05440e00b03010110145084070246a802034031108403002543c00a10a4000180c1032010740d4008a1080d10709800790010303d0600040c2807a00c1c0c46201c2c410b801020380400c0004a42146d40380c60646000e84040d050100c020305142300c010356251140d2246410050800c508007030401c0e0310384204161181c02078130301c440c3c110391541c42c07420707070151520f0404240b9030922000c0341042082c072a0920070f410810324034030010040d04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 935801366 1250 935800116 935800123
    0x30304180c0e030a05060a020c0c0d060e0f1203010e04020604090c0e0102120c06010b0921060405100603050d0e01030e010c030b03160605040b07030e0904111306080a03120f0606050c 80
    0x182d2280694841540d101c009100000c2c25a408141d412006031642e020044450030001c1c000300c55039018141400800500c442607103e02d11300741c4100c00700c60607540d4846200d03840c1c5030300040401000d0001d00040002000c904030032548548000c2501d072801d9200c20840040340d001e1011030000a21b050108205540c041201c0056019882e078440d0400100c4507d040da2600c1c140030f014240400443d080d20a41c543c00c8801c0120303040c45c0070003147c1040c8140a90354801e011070302a10980318111602c0714040d903511078034047d00d0b0490040d00348015a544e058035141040540c0b141015601e0300d441400e403500f031181ca00d421541f0358010912000140c101880e080c02400e1008064840c5c400410826801200308d904072101581482d8981409040076207002e011082c01e5a0441134100821042121540f94031899030070807a080c41c40c0e88260b03054001114800c0c0140d05803540049a8580428043d0101a05000400c0e0012604258003407204060340c445502450104402040c0c018543d41d050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 935802616 1250 935801366 935801387
    0x60f0606110307060b041805030a02010c0306050105071103150a14010e0f0103020108090304030b0f0105030607020c03030d090809030706020105330d1a0708060102010b1914030304180c 81
    0x1c1c50203003415000311004a840b8412840003d08150341c0b186105e106450300d810220000c40300252094030159103082c481d899911101d03004005510f44a00c0c03a210501070312440302a5041a074400e07040c146250b4800310044481e00c030a03645807140c9480c1074038003200d1b4840d0a00c903e03844540410000310f140c91003142000c044e0041c80d0071081510410006440c030140c42c07030440381c0910307210310181ca03140550f40c1103200d56080500750008040401030b90180c00d1140a0480d0070550440d8503d030740700707036080342c8030001310031255415042000712055040198100c05905401030801516041200c0d00103840c140044c4c1c00200581d440f50b040054130008044860900c03040301d449180319518145505030108106c141c0d00e031040b210101c03100306003c40c031049a041a03103255a6695107041001c8041c20002084031910300660800c3d14403031003418042000e0426600b02c85403c026103042c03007088185a000350a841d905844107103c006600395681524075401f0720035406c0010100340001c802040e01450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 935803866 1250 935802616 935802629
    0x15030302010c0f02070b071b08032208150c030c28170108150a0b09090717030c03181c06051f05060901030b12330622020702040207060f06 61
    0x85d02c02c1003d480307072100f1510b0b040c3c2e01058000400410040d00b049501c01500300c1c01080c4408201d001000203400e20105050020000e58071205540301c1c1000d0341c405080f10584820700b01c45021070301405100b00070710f4220002501407400c00b161000e25080007154114003a030700050903c1182c2c030058110350100030005006112070700640c140305a140d0745250428038403400c4080d060002d841a6040d07441000c24803c001d0599040307040c1500783e9035031450540070700d940c1c441c00c200008801e000700000b103591207a800000b55007410012031810701c0e036260b070521454106244e581010020355400c0600140a441103070300003983e09240c5000311082c9011828405003a10000091185580c0c2c0c0702650425070b001d20300400c00d03100250114602509804003044203106280390300e0307403c050340018455103813000c400742d00551f500f070b0091061403502981e58941245170502540035032034001281c221204441d40c005468243d05a021804983c410b01083e10100e503144401c14090805009141c01002c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 935805116 1250 935803866 935803873
    0x1e01140c071a0402060d09050105090d020303070228020306041a07020c0a0b070f0b010801020a11071406031e0f160201060506040504270321050c030609090115030302010c0f02 77
    0x1603648881003451040ba0104440e2400e0000a0443d620101125490248060217000503000b9180541c06000291060b6109000d008101110540b000090340e04c552400c0d802441c0c54030b04681c40700c1007415130200303401c602c1c006140040050388080104c03c0c0600e10031141d00006105400940b60140d6010703000d0303000c541009007036030300f16650000e80341c054860b8421401d42c0d480c810720708040c2d100104e9400400014290700001071646065010340711481c05500d446520b846506d2001e911072005000c0d40443c0c0140c0325031107196092074400740d5031280398824500281340c05610280894041261500701c0199994100306240d5811001b002d600d40050000b880000e080c500080e6241c000e60007554042d96448500741910030054514110680e2202844040b210703a904000380481d46010505000d0b4503002e440c13039220041361140500c03c010111a0a0035600c403c410400740400107402255159210241e200c0052040340a2400451007a00000f41c501c0d144000039060032960b0861100750340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 935806366 1250 935805116 935805127
    0x121014030303010e0a0902030d020d0f1e03023402130e1f060f0f09051608040b070c05011509061e031b080303010f03111c0210021e01140c 61
    0x100d0000c10349054400465010129683e803a1303560b4000c102c0480d01a43c148202440e48404940105000d40960a543c0c0c0d0340d442002e0500080d2003110600c0030300b4284080030072592003010304c80c2c1d011b01503074198444410300300c4010003041c3c007a900602d107101401200c4a03180c2003c52a105c201005402c10481d400d0084440c1d40e2129601c0e50311460441894020344400e141c0309054551041024040040526542ca501e84081e184d2509260040d40c410a25003404907a84900003840b80d000c540b4503644050340d039669a41caa994000c005000542448201c10303080c070003d1400e0060017025001caa21801c0d1162402440205841165016404a24000307409101001c1101d10b05400da0307802c189140e0304c503007500d03c04508031801940840e505d400f0102c00442d92848901a01080f00d01601104021000d0036003000200c040c50200b48111000c142c03040310040c10b0502e0b0145225400b80140c403005500b03611002c030b80070160f41e00d142d400d9541d007201544040b10000302d1500440e0241c2400d0914 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 935807616 1250 935806366 935806369
    0x405093c0411120d08010503160302030a0f02010c0803040b06130c0228050105010b04031104020301141314180f190b0c0409020409091e08040b0c070b121014 69
    0xe1001070405409031860208248583d00d415503844407850045041310b14108049100030600e17802801010711234040d240600a121110203030035401d982d0028040c0c25030305040e56440040e6440701004a0610403a4080170b00803500000240d40f10302c0c003c501e92009440d04100b0403ca0981d00207280003428680b850074500710340d0005c1c00320945a00c00c0c070a89540c546180380014110180b1500420302d40c24075002003001001031010707104492241960007080c0c0507c108210503800700340030750003c58041030110002c03031504d4087d0b10058480c42100003241e403603401424140380d008482407a00d402c0034015055981c4400c02c06421004413500141c131081e080b0001290741c81ea11008080c0c0b51500c10801325044141e903008135002404402001c554130f55a400c8080c0191580d03007002c1e142c0398841001d00d20308040c1d01d0103d105440d8420075051501d402c00c0e8080c02e0139003045c0c2110100784079040003c60800131210060081d891a00711000c5903141910030385003d0f0307520b5080300c00c80c0c800d02c4040d40d409 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 935808866 1250 935807616 935807731
    0x2220e1f05250e0301020705031801090f03030503070c021201141e01030b01030303091b0e0f090313031e02040207060603060501080a050319031b0f0906030603051207030203040509 79
    0x84400a1901d0340341643c0700000240a4090488098503a02000804048100c0c030119401c0b440d120a88981c640b8541d1224075001c0c0402910000e0003103502000002c001d01d200d9104e01844030701c01000c09040c032440c00300007821100640c24084501036001c041c80380292552820020700210401c0e900d0f9a5030440c3d9038000c5d1660706100007418952145081e02c20020f0900c80072851101018605480507a41e800e50302422105640303080c5000409004201c240101001b05c4804510300310701d00d4500d41c030719950300c40c1c28600980707031310821066803082c0401a42c440c0000c1c40c00038002c07100032904a0440c14000200d48040e4008425948044114800254044103481c00450801c1d00710100b940720030300550103441c55140f0022801c00c9001036060b040c0c1c01100c1781c00445180c0c0c7e00c031600e01c0d0300e1b84015012100300340005071250b40410f1041b003e091400307005140c030300c0c4244160380c240f90341c0f000460440441a907010079000c49010382c0b03c00f444062412016241c401c0441520792031103902d413401c41e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 935810116 1250 935808866 935808931
    0x10e010b0a12080f0d060b0a0215100302010816051e0d060603090c0608060d0c0b073c080c240c091c0c08060c040302010207080a02220e1f05 62
    0x407504e0106810601a200364400341c010f111681e007141e40d9140c01400203484504298160311009500c0c0c020030310400540c00440b00340c03070703041c0c440720380903198803440329600c078442c40c3d82c401003103c00c20040301d03d0341c40302d104151158a071500068607000100c01d044166482900043d0416281070940310114107511083e00c02c8a00d00d082100365911128046404005444406403990414040000d01001030800402c0c44c0c1d03010381c2401076544a206990501498044030b1040f0f010306508000c0b01300104040c1c0c0c40c24072881400740a2a1206400f6032a0508103a0340c04a03508100080e2007410000011b90351070350140325944010700d000c3d11000004d5401c200822880c0c17500ba0391680301010002c1c00880301c005404094211015440c04a40c8004240e106000880c0180201c44000921004c0010a01c080582c000c000700380b17108801940c10074403d421040c804049444208008500b5018880000403404840040564000c1c9840d00001d903600649015603489045901e480c0e80c445d103225100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 935811366 1250 935810116 935810137
    0x121b090623090105031302060a0c15092103090209040302061e162114060f04050f162007150c1a0a140f07090803030f06040c0c05010e010b0a1208 64
    0x1510b9071a01b0041c041120124480203400240002e08808029040018100101d00c1038504030410750544100100355202c41000a04014118400701741c03c6400e105000155141c910f4000381c09000b40e000100c1115040e18240c0158103e942880750000c4520b003602e404a506444921483c1013030310130b8140000302d00c04e0180400c625060b286207020304103e1218280c00f100c6000b80911104030a50400c80e9601341d078401c0c85036188400500d10782c10315004075440f803008040203801b69583c54248a131070480c41c200d41c00c00c001c0608007041c03205542c02582d0312000c190200800b160350034540319542c1c8001c050a81414002b00c03001c2000021103041d807001d8020b80040224a60751100c0103000c002d000300d00401001400c104041101c1e104100060910034102942c4800702182d80b20007180c0c4910059404a030404c08980004642d81015048052040300901c0e02065803126030722802c0c215110b80242d100665103800c5603414902c1c00e010f0243c0a0101c406480c1b1040c0c0c1f01c2c0d80e80c00450301c01c481d03040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 935812616 1250 935811366 935811377
    0x10e0d05120d290a060c020f0904140d0c03090906150c060609092103020a0c1212110306010f0f090e10030212030703121a01121b0906230901 62
    0x36420100786401010403240c00207440c0f200c1080a9007404040c401000740f55000303c02030500003c107103104400100000d034000e00151782d421410f400707000c0420f80c020415140e40781100d01000c04e0000810410780001c0c01540c0e152014071291070002c2c1010b4007940104106070402c8030070701004621181403030403c613403401c1040c00c050780d515080c0c1c09000c644c1e00421245241500030024400c03540d00d0348000701880c142e00d03449440c02200c00e13022400790440042c0003900030540390001030802402c108000c4440c1c1080b00b004e49402e100d0f80c0030759502e0091a41004004814080070f960007550102c0d100c006c50070940881481c101c4020300c0032507a0310a500d1030310394607000300b445486809052805590054001042400652a129500e520150044000604480350b0341e9410200c0c1c41100081c2e0003190640800c0140c000c01192aa01c1c0c0a040005599071518207941e003850b81043e2003888012500c0b01040c8600d002d1010700505600e065500006d2a4003101c060002480c40882e04024001d0816 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 935813866 1250 935812616 935812627
    0x180b030106050406140112020a020a021201061a0c0d0305010305191103030703091a030907030f060f09050709060603020c250e090c04050a09030c080d09020409060605010e0d0512 78
    0x90141c449584002d0b0090314100d0049000c9205071a40700c0782036802c0e26001a102e013036104e010200c2c81408081c0380180c1002c44d020300140b804842c85c804880d100380001c900162182c60307000445450814881101d180010814100302e410b003c29400d0100b9070070200302a40c5140c80b010386a4450341410780e50800c0c8140d03880d04010f003010003102e410002608481e00c4890915020b89145241c2c021200c0016078405880000044001100c0c880e4100c0e10181210a143d80e03201021240c1200c401c8401c5e07034644c2c800412070038403031154160351070041000b803244518000e00c1c102229050f4100004041c010000c079290302400068640401080150030011449100070881088a40b078010b20502c00780c003800d0280f1940300007101d40d1454000c44041245848008401040310307444680280440c404801160200302c0480141c01e02c2e00c610780000c20691020740c0007408a07092034000311105036aa080910140d40d11440041c1c0240381174034480e0389a139540d10395070340d90718128161905400002070b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 935815116 1250 935813866 935813869
    0x61b030a2006060105130305030f09032e020a030b1002071e0b0702090907080a06050a150305061911120417090303121b07060b01121505060d02160b071404180b 70
    0x1b030b440115084000c0d2034683d0f102c4881c4041c079610142030342d0721138810081da5060520b000706081791048400204100b040020001d00006904021404402d1507902d0750080440d445080445c62089a9a800303014468100070100d403503102651109924181c03400c43c01c1c840c6180f03407822500c1160701200c150100c0c5d030701e0310115807500c0e2554010048602504145e04100a070030782150f40141082c0105105141d001a001d480400d040d10000d8403590103003021a0f40100c0f1f0402003421031001c4c0d4030200e40641280c0c0500794540c0106070345054010b51504010510802100c0c551490071242001031400d41124000b960300e01481c280a4841d10b51140820107001a11340c22340c01c000b140212598850078182400c5c4011320744d0310b00660120307607290100c172552100f87c816541d0317190f00900d079101040d05040611050341c000d0000d880c4d0701503082002a400c0d5031701c242c039075066900c182812060341c580200024141ea20041c0c0c0018070038400d1106000c0c94050a4100711603407100103000880c6c0d0540c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 935816366 1250 935815116 935815147
    0x303190f020f160c1202060708071419030201060e010303021c0210152d15050f18030f15010608040317010609081612030e061b030a2006060105 63
    0x2c200d00100b082c001111030028841009807010b06002d5148000d40503034500320104502d51521000350301071000c200450000b84c6010140280d82c0c00781d040f1351024a8250b0060346000c01d440c07940b01130310000307420450800d03609000720400b40c40030100a581551465030080d680e81d8906018405002d4107443c03901020744200301503400810548003c1c480c1d50014442c800d1014410301450201004003058010307030904001c01c0b1203002814015030400d0078a007807002c481c0c0d41d00315980306080110400c06007103981c3d080c4000c0c0100c2e510320318032014a0070902c0105482c150746203030300076180e80000b00103555400e0203903481811a050b41c10702603041d56132407070104c0d078406401055445c0540a44000300d0611342c007525050540c1c49078801c80e2051300d191103c01950301210b214401c080850031820500103413094070712800d1a0b001900d2281010452540c18581030341d0b08034044240d90012504c42041c540c418051422003d000b1454207071860001c0c03010307881da9401044103041c03040015004a01e800c00c0d0f03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 935817616 1250 935816366 935816377
    0x24090c25080d05010e04210c1b060e0306160e01200114071814060f0d1b0305040b0f0c0417070512010b0102030d0e0106260106080303190f02 62
    0x14a4154603002061a0085854105129a460592404001240c2090310503046402550030205407003100e020898018104d014001c051810000c0c0d410382c8000042d40782c24226005850031044031407543c14500001e008040c05070b0707190701c41d0b4071420900000c0c400a4a203440d06800914140100d100c10f80c1c01a8ac0c1c400280d51001444400b0803140940c444c01035110642d0f000d0503401c1440d031601d82620460b1a0119040e036800b455021640800036070003144c03100d07800600050019401c2c101e03030f1500110310b6004991700240301515042404500404400b242c0100496400c08201c10b0a254503402c0301c20000809071385203144040b001c03900c120017910076600103050750b8045034541c1114440f92a2110918407541d40204034100c4d9604038100103016446c5480c00690056040c0a60740c0c20705c9000c1d000c0136202c42d02030f569444000c41d002000911140c000c00b80200c542c40e088010300d941e9401c68829601007183ca030000e00a200b0000482c54000701741c001e4842011525040e00c840c800002d2060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 935818866 1250 935817616 935817667
    0x3090607111503090a0302010509010b0609060309120c0303041103060c070605041703100f0504060501080601081005030102030a0605011b02151e0a020607022e050a02070c0303050324090c 82
    0x40f003000045140002c42e80c1c00c0d107100c0d078000d00c1661510840c2600340c400c40c9629540c421780610941032542040c7c0702441d400712800c022103c0c0c640700c11410400c0381d4801c6070680e4664000000300310500c0b200240c2d4407040c032010f60051825142901600200b806541d000800302900c0d4408141401811403e000c40c2e450b51a804950300c5c200032507620302e40d01040c03103201c018040d039031400181454a44188002c407907060315440016038840d00112a20300f402414809584c0e03000d0782c08105a202440a10b108a00941000034101d0a01c0000f40006d51b0ba150a940007003102c000b0a00103803501981d440d201c8521098190f154060400c0c0005800200312030032062000206080000b181d000510602840081d000d0b13547d5505d03900720f102801d49100301c0284039944982400310200f01e050b031005920503c0303500300500b0721520340d0b00d030400751316107500940010750040300f4807800313090821541d4001c210280c0308804800001010491000005007150b03410b0001090780060b86d0f104d00c1040fa5a03190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 935820116 1250 935818866 935818909
    0x301090e0c0316060906021f0e10020a030f0513050c120f1902181e190f0507031a01232506050a0c08040f11040c0c1101020309060711 59
    0xa225450028100c030f910071980058441203000401c24004542881d1044610f460410b6849558501034050b1900102060b03c900c0382103203184d072405003880a01440ba0a540d40892010a0108044207a402c080d0402c60201c010910841c0003400c0095840c1c1d00361416210500302440d01803a050904845e20707461560750103210f20310b40015050306598010a8801c942c5900300107580880c07a6020001100c072002c00124054280440d8180080800e40c807081541c0c0005082c03000040100a0303914080d050384143c0c0e01d41c4107100450b41c0500071200307a10504481602030303208800000b000b207059160300f000400a00d10148d0100d044400c202e444405020650581d1032612610030303044c10a80d501c003a1005417a10300403a1500c1554003429922040c030b5a10001c0c640c9491b1209510b0040d0400100c4401d000c2283e407044a071070394003401b079036a0328507121941024030301c1c00d2020200d43c1501c0c485046410800040c0308664442003a92202070f00440c01d0140d81c0d0b07209002c511111a1200003021300d80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 935821366 1250 935820116 935820133
    0x110604050d05070302030f010504121d152802150406060905040b1602031810090e101403030a081b0d18030e0306040b0705070501060e09030c0f0705060301090e0c03 72
    0x400020543c04a81c400d4003100c01011100c0d08040c02c8500a07140240001903906403030070128883e4241c0021040807544101c01920803000050406440300600e901c061b0000c80c0501c200301407120f0380ba0310341e8041200340e014907400410094441c9403002c050b1010a550300702240c20b01c401c0b984480041c0245400c00c000d02c0c00d03d4208190384003c00c0320031822000b8610b40e110389191001c400e441d080b18640c0040c103207141c00c03242003042c607901c40c24106d0100b24100400061501704200452f000765468281e080306542010700c4450241c6402d20039034069441040501c10107603020b00c044d81d101c400c03025480041070107514998054400c0944039881d0505200c115054105085802d8221510036102c00c084000031000307043e10340c44211409408203e02e000000c0305607000340002c00c0800d110f000002603603a10f907a00c0c54001c0e00b00b80d800e503560382d00110703a00c004580304104d1905000f1003000149911442c160025007a072005024000d0800d403100c0305a00d055208000341c4480c81001403e4540e47e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 935822616 1250 935821366 935821373
    0x81803040807092702060406050706020d0626120a0305130611090108060f1509040f140402030d05040806010308090607050d120c030209030a020d02010c0203070611010b0f0d110604050d 81
    0x1000404e0048070095895500001c10800d044040b840309030340030b014541800d103090803e50b103941011905541c2d00d5001c2000040140300740c4141303009444800b007034000c41010202540ca81c2c031100e40703c5103103680c03000751841d00080c0b10800340d03900d54080e450b01003500d82d101c07186807201c0c803c20300f002001c03e401c0c144080103034410314002d40306901080c1e80d241025a07402040041c5e0452416a0340e82002081d4021824030103d440206800303403002e480404c540a82d0b400075800c072010a02446000c0c50020140011480c05114000b910a218540581042c2c06c045505481d0003062100519808001800088585908082e941d034503030460705a84840d0080ca40c094a854140140c3c00115841c1500c5091228060f02c00e40d0a8184050001c0c0741981050342441400407100005030b040c410341785103001c01a5002c0080001600140d95100c40140340001d6035800c0d40e01c0320010f6840341001180060391030300c03900c2c40c4145040e0081d80b605200654040810304a1080e238101c5504001811802c44c1030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 935823866 1250 935822616 935822621
    0x405130210170604020906031b130807031a040b0c1e0a030203070906020d0f05070503120103050d020114010e0601120b1512010b03070903080a02030c03120105041b08180304080709 79
    0x60300240da40100c840d9442c1c601304003c80c030030300315060b50041d4140082190055108104103000d1144d001c21031800000c2d1203614074480040e40062003c0d0b01c0440213008204e49036898003000d6006002204080c1041c0c1c0d19050070304d2000b4010141d10801080300c448042e15804400001404000b10341ea440228110040c041d6000711007150102d00103103070000d203062001910080c4081903a55403a0a400314131011113041d030010f0001e41d070501c030a0100f032841d400e030100c20038000e511400040102d042040e202a0a40f40c114116000f1a0034043c01040320640d0703c1880c0364848402d182520b414074060551000414103041e65640242069030010b40c00ca8105004024803003d85c40280390f580e85e20705107040981b00483c0c014001400700e1008000240318003028200c1c0081e10f00540e41001115601d4078a546c00101010780c00300c07c003600400c00ca0502e442801d100c46151006400e0008030540040c19540018000408241020004000f404414800e940c082c1c0018000c1c0c5101591301d2428601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 935825116 1250 935823866 935823887
    0x5100218090601140904020901050c03030f010512060103150c11072d0503120702120111030f0109021216030e1509120c0705040b2b03080c07020904020405130210 71
    0x1e1640403002c40d05a40c010000c110050540820721072501505d0700070300002c0d402540e079540c180441801224940701c1c003032000d180b0800c02c0d0402c0c821203600d01810002074400c540e120341400d4102c0c500500100e01111000000004002408240c42241d504211220205010783e560f1501408001240122031050204c0820308110318101440c940792100c10300d08112071041c103504d40e0120205468120120b000303044440c1c00201014000980c1041050039500601d21402040000004000240c200301031345070b000d49030030304003103041c020102021821040040e0029180003891ba214040c20362007600007220755044401a5021480044c11242070000283d80c807a14a01600074948098400c400658400042c12001000b01516000c1444020b103000382025070000c0c4a801125030700601d50f00d010421526001d1411040102c40c2030040c1629009411991a203004014450150340c40035442904160100c800080c80d44a5003030f4861200180749000303400003503d41d10084a01d410034950310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 935826366 1250 935825116 935825119
    0xd06020a03051503150112050f060703020901142104080f2b0c0c081309020a020f070906060914030c0301090c140f0a0308030601210c090f05030307030c05100218 71
    0x10203803c82c001010380b958200500800d01c05500001041002d82440c5840030581c058000d503008010040d54050400c20211807200c00b007a00000c11908a59000350820009541c030342e941c90402d000304940c00c20034041c11800e29614a80c000125041c449200c00b11559103e290702c48503610041c3c4608854050306404814106890802e050071981c2ca0f1800707000960602d1307a8843d2400c040030340c0d039480d003500942114030140303240c1000850856003610041203600903680091159820300e2580901e050119000700b4422400c1c0802000404c0d04a5000f4060390480c1044443c01c0c2000c001091400c2c1034a10001d41c19824034075150240040081c1d4074040d2942e0341540944401d03440300f403040140e442c0c0342c8184c01860843d0200086414000175580188052404010ba508003000e08400380d03c0640b002402c0d690703100d000d911a50380100701d040007490b021b1040380c80e0525181c002502e0b4040d03000040d043c09218100e00080040600070400b02c48410380007103403680c41c0c20401c030500c640a054043e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 935827616 1250 935826366 935826391
    0x603070f030525080a0b0a0f031430090a030320030a0804080315030a03030e010b0904020607020f01091e05010e010e032e020301081005010b0a0f0e0d06020a0305 71
    0x11203582920f2440050400c0c0508602c1002c1d583d260101d8050f20024100b8203072070f5654207070180644d1100d0804c8000c0450520b0504001e0079400e041c00d02400080c1c5628065020140c0304130280c1007980d0301403408806031480300c482c0300052818042071054031182c0342d00c0484810040101a0010030500241483c20307500d6841c56001d0200030703500d00c00d6550b031001003410700c80040d0001d0040c8004692120480c00a1120450343d10702091500c280502c0032800300b900e0340250034002e40244180c03003030340d0000c0b031b91a0090b003481d030003040603440742000c041c1c0951107101c0d40342e40907400b420403c0010300c464142d546099030740408000e0810680c0c020540002c0c40d2107040082903200361611480f10b8401030107003131051901900e612800d850005c616040d0078603107411078102c002501c0039500030b01159020b030420300028480102140e038160000000c0b24400d001c0b84509035488141c0202c40c0707000741002015402c205001806402e070340d0384014201400050307804669645078100e14011260613290 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 935828866 1250 935827616 935827621
    0x4080105090d0512010513180f210e06070819030f0c05032203021207030804020306010b040e07110102040314010b04060b04181a090906070e0406060503240603070f0305 74
    0x12601c3d4820449080610365940e001400341313240280748098504031202c000038041c001c540041000c1e40003528162803540f480010842444482903a40403012050302d9203542208940d10041c01c3d141c0c0d6040464001c00c0f002c25660b0810088a003103807000d440f10148910701120000d4000c0140c00319042c03d29249042100c84803c050150042c0c034015010750340005403d11442451418429110b1010760462080e91840c48000240d10700401c035117406a030710f91a080c5040e0050602d000300690051010b07181c104070800203d100508031070740140c01c9141c08014072a1201071a40a80101d41016200e00388130b900070303010740c0d01c1540440100c9905945c2031054503179640c00e10209000364441d403000840010303445400e43d9a40d900a0780002200744e5500400d001503404540c60150031114000c0c0d590194041c02903482d04108114000081100c0c1440310380d0608000400b140400f0301080031411002d00c0790981d501d2040148034210300041d103519140d190064008091650609407040400e1070b0402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 935830116 1250 935828866 935828893
    0x50a050604050111120a1e0606050421050c101107090e0f010501060207050f060f040e060a150c12050d0c0201060f050f060a0e13020703090312031a09060a03080408010509 75
    0x2643c00c017000c2c03000c5c8020944c2d2403080950250110711041422240d841920803141080303440b072031002d015036503181c07034540d428002a07503071243c415075041c030b00089000500300000d80c0010b0000a44070701034031455000740d121401a2010100c80c3c2581201d8002c0301d5002c42c120700251f0090a402030302e10b0441d5004150a211182214020301940c0c2c0140c002c004144030a0078030a9140c4002040a01420f00d40010108091f0982d00103801c1a40010103800c00d02071a450810580d0000cac018071354080780b5243d078443c0040e00c5920040d1009096403904815022190701030010380700d8001d081642800429031041e002802003881e400750003c00744a030000171505041070f4015001715480a44030303514190904d4401d640c0b400c1646019030348004c14520300180e0f0b080342c1c005801402c4c825183c03009840d08602e00440e04007e014010b41c01c2602e00450041ea01030341b2000040c0d42c0f1400c0e01c4500f0360b5120800030540c10501d940000e000d0740740014001034107400561045209551140c242c5001644050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 935831366 1250 935830116 935830151
    0x71805090f18070b1b0c2d0d0605090a050105220813030f05010603170c0a061d03040e01150503040512032203030c1409030d030f09050a0506040501 65
    0x21810540d003032803480041c14a01500c05002c212049003012a68807544da0032a90075294001c4200b40741c1602e12010402000c1010404242160b0341220300e200b44059000502c20045c008002c01c080003054104803443d96201c0d110b0071329100b500040c05010790302d85541010f95820b40b45100315110340c60840000c19411941500c0c000c03010308901e0040c001415070325002d401e81c114040c4100e048640340170001c0001e40c00c0b410310580b544908008100c1d42c0c03071410803410811000e1744980840304100815940c0620124541c0c003001d41c4001c0029103102001c2c2078280d0340c095842c24800c18840000e020407a1079103250458100d60041c3d54524401101c070204655601040e100101640e000f00caa0b2101c2600300c2c0b000d16400130101c2c448102c188441569201d6892820a041e400300e07555103070700290241e00031008510b10703581d17070f04844c5402c000501080e650a50014003100b0141d4424000d0384203d05c5400003150581c0040488024984c14145651640c0007520122050740c68484981034000606 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 935832616 1250 935831366 935831371
    0x313050606041b120b0909060703050a1803110703060203090c0a05030c030a240204091a1504050d06020c06012402010b01020a2a0905160306051507080c0607180509 72
    0x208201c2c428103030b10181a94504c030042c19000362140c80300451160382d00d03144120740c490b004800050001d4144504043d00719070000e003000003550300f00228400b4184490088054507581482c0c100b0224811540b5035007803182c180c00047c08940000280402098005001c01c0c0035041207031000c030b68a40d40c2080682c0d80481d500765076055003192440202241c07102c00d120030380314048010b40b203541c881c41c11000200d901503001490301950307503100c2c0d03020794840d004840718a54003a6010003401007070450300789103030285100d42481802c0c13000c040810000507030180c90710405e180d4221505961500c001040100e290b00000550441d00c0b0141d4101c90f1050003042203001068000d4601d3b8880e5461300d804520301c0d0704040910f038000005410356020f410001d0001006610000180c90802034031320344000b083e040f9100101420403c0c00e00907070383ca006010200000c40c41a85940d0b14140c42c0601c081e02444403210703802d0049504000d00c0d55001040c000850003040710701610192210100000030a00307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 935833866 1250 935832616 935832641
    0xe100c0206040f080307020f030c1b190306020306060705070b040617130314070209180f010603030818013317660904030c03050906031305060604 64
    0x441000a000c84e20240095800c42010710595000d5620a03120701d01c0c48c7d000d030b4088103565006850810502c80b4110f081440c451007210014a04184100c0c00a0340e00402e0001500c0300d44d000020810716641d2030211410b442d408010395943d03076501e400c0e499031a007051003400c0104009c940151560302026400070311035401c4400d20810034142d41c030201d816401003103480c6d4000710201b02040c05279039031141c200e1182d040800c3c4c50a101070007002c02d82c00c094400d035503030646a05100c418800650880704859000c51301100b83d10000c0305030580a03002d13010f02150703003080f202d80085190247c41e1400142c210860a00700c50304071540e540316006054040c04a040d0b107980c00c008200c0718a41c0300000c11985c85008c05030104560111100781d51003003964200c44400c55038003565502d401480a0498101039001002d40c60340040a5901040c0d039100c00078801030401800d4090f4508040c0204140c075420b08000d42060740364503119001c0035503550301c2c080680351442501c002410501e454050010710488 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 935835116 1250 935833866 935833883
    0x50a0b070b060d1e0305042615090a03180b0c0d0212160201030902010c020307080304140909060f070212030f070201140c0d0209030f01050c0319051611100e100c020604 74
    0x40e1050513802c00c01c00ba00b4200d00700f0408000000d010309080004001620314040200c040da440c0754005440d102550019a03407440054003001908100400d110041e103815080078140045010804c900880c01c0350000d60382d80b080891070300c00915000440701481c3d40181c08031160580b11825290103801520291141415001c0c44600154840d4000020030361040c1040c0a6446159000030308140c0d480e08401e0f00e45c0d202280404c00580d02c035411959403501601c01e07982c20b00300858002c3d2a000020b10400000c4c910720b02055089100300314a0003c905891074446e00c07400c05a40709401e5400a0307a524006600b0406044803030062012520300580c08500f02518008024600310045d4105090305d03540350060700010741040c0000e0248a1241001d070b45e410f581c0b480d0500b40d000c06581940d015401042c0303044100500003400c41c4203407400d12000e00703142c101c0028514051340351600e821100300c60141040c0d80307000a101c1c0003030014019a103844040c400441010400c0340d5a400885002d80b1001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 935836366 1250 935835116 935835143
    0x183102061b0102070c09051e010807030204020309030c0a0309060816022a04050405060a1b0903171b060a0f0e0c194718010306050a0b070b060d 63
    0x520407000c102103000500003504001d015202e8880c044625030050088a0b141c0017049040b241c0348040c000d401d045424000015411300c5c0b00280d40d0030307071808024080c44d400004541000c5041061355001c112407411900c0400203454010180a01c901c035020220714080040303032034103000006140c01022550300400303080c1c040c2034401c4017041000c520944044100b25201c6c885464a000c0c40384920301410052850341443c030200c400b1a48401c0b1048010345843d05110111540031060a04698002c9518022050038401c10f001c548a440d401c5030048082c1d00c0c030f03c001d480c4042103071440340300d008008000342080401600150303480b0010403a100c0d000b4200b00815880c00c054941c0744034141c840c0401440e42c64001c0c48454482c00c41800001e42c401407003484040400b01c185008203001602045100f40c0100d60a48280c02a031600c070046c584d121248403000c0e4403e0340003138000c0070f00034a60012650b640503031412951000c0c2040e00c81a0300c4c940000c920317050840300b042046500c14822014503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 935837616 1250 935836366 935836387
    0x1407150504021504060305010e060a0e0f25020109021912080d06080f0307290a18290a0603050712081e0903010b03072318310206 57
    0x30300300144102e900c0414590b40001031200c1c100940050f001036280050b00313504080c038070b1401c0c078001440340b40704402c801018000e6850801c045a044000303001d0743e0106440d0310941e400b4851280c00241d0340c00016802e102601a41500110401d500948200c0c420004010b19100c2108070f6000360081001044900f4002810344001481201c0100c000000c0c034030384a20342da40c2040d020740000740065001061084c140950b0252040d8901141c91101203d245003445820030720b84010311f07803090303150385401520b8121720078200040d22035030104201848a09840c003143c1200290005000c0000600001400756101882140c095a4100004141d52483c00340102802e0450341411590802e052102081507101010030595410381c0d6402c51361100d4404081c10708440c07011062900c13a5005450410205281c0c16044903515000840000c0c02849075011500000f0307990644041d40840e5020480646065a4000742010707a03a542e10344110010521050400d107030b2040a5402041045a40c4a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 935838866 1250 935837616 935837621
    0x2060901050c010f0612020909030301142e03060911030f06091305120301090c0813020609032d0c06190e011106040b07080a02070c090b01020304050d080901140715 72
    0x255465200100d40d030094908000180c0394170307900484a94031600a035408519240034259032104501000b50f0456140c6012005c4403812851954080c1500f50b021480b41181c007000309411403080302095004030003100300100100031512454014601e0041c04070001c0501c88110fa0061043e01c403103031066100c0c10200001908080c1009282445662110000440521020024651303000100d80c4941c50031801d402078890601030203080142c3f100c201b000508034040350b1455941c041d50030030f03250314014011910305440800c14010388100c001480c9000e201201c500c1131910f00701c9064542501030030041c0308c501d024103201c0300035031800185120b400c3ca108401d607070034260051504680881d841c1a2071810702c1025030341501c865507c00200071600e60041c005580241100108528141858850f20300c207180d90301443d0f00742d603200e0b242c45080368030070000c2e1005444000c01c4072f04040c1d90380c40c1085055014000f4280400c4503009a26181d0030010240c0e020140c000c0009400fa08840350907100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 935840116 1250 935838866 935838877
    0x70806070234031b031a160c022404050a06080c0d090f0f08220b09010c23030a020712021c03030615030204050f03070303020d082508041209030206090105 68
    0x20340341d601e1000000c03a1103140e80c0881e210000d0308413032801d400c0d8100643c45144514241050744051428030100003c60301c00b0511048061038003420303443c102e04c0051210860394141440d41002c1c00d14802c849044074000b042103a5085a0180e8903d40d9000142c828403021100708080f80c1040c0481045680d0540008264030b10038030701c1031011495075442425645a0840c01d44d141f00c404900c0015402540d500a0003d00c505284d80360014644145c011786485a015031381d0420080c2d91552042005291110301c42402d03031001d9011890104842c1d40da26000078541c20014450800c0002c1d000d49030a64145009801800c840c024101c02410030301c2141c081c000c1101059520500001c405182180c1d09038142015a000750707035176285c10100700310464500e0032244244c002c1441000040c0d00040e0a00380f40c001d60500101540d07414400c2141003241c40c2540c644603005081380c81500754454070103449644031703d2500c0c0d20030262110444115001d40002904617800300411280743d801a4040c08 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 935841366 1250 935840116 935840203
    0x2070e090c030105010603020918061e010201021b0604022701030305090112050103080d060e0c180d1560090f200a08040218090708060702 61
    0x40e020050740000c80c0c21604260b00000010b94042130514051901540311510941d011302240541d0816000080b0842c0c84020307284983c0403140c0701c50045900039015101d1207000d85505000e8204c0e2041d401d900c0c0e5008039800ca1003640d80714030001803c6007018481508080c091001d81190f030a6507419a101e80c01240c01d00c0c14400d28840f2808120340601440b40610305c00d0000f161125400d514010688030b45811140340d410203d410055400740c2c1c8426a6005035013010300800c000d41030008540700d1000d0701d9010346007444591009068180035000001e440c80c034080100002103040c0c00b0306140601c0c040c0101407111030380d00f1440c00440401d0f0311012404148040d401540d40300b038040c250341c00b00350b8418010f2a848000c01c0315020a14498180b04071000c1c031034920010080c4c4020306081c440e90844c4c0041c030030550007140544d00c5001010303a445455269111160901c1c1200c10f41c0d5841511480e02d081c07045000003070910384089001c020028480c1c4003512521801110f05001844111015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 935842616 1250 935841366 935841373
    0x14070309170d1b02010813061e050709050f0f12070b1c0b040203221a18010507020c061206060c070308040e01050603190e1507031d0d02070e09 63
    0x1048080c1040d9640da801c00c80c0308010701d1480a42c1c0005801c40c80e20b00c10403100c3d400b155028402507600100c00d82d41c4140b000003800b280ca8840c1c030344000108020030214041c45e031007542424480d4050ba0282f0301401d00c54442c40d160b0b690303c108000b034101d41064060b40000c92201d00c1c51030740c1001c6a8266030010b0355429102069220302d400b8030950004010322144c0310380c11510b00040761091080d00882142680c040d855031904900c0341020407100141071078602d4040c041c140600480c41c1d0241d001c02000240204d0740d05146401c4000d0801c41151103095520b40000b007032440e40000b8030724210907001341040e070506100c4000703549100402054190000d0302040040d07416541801402c000c0d500c1121030b10344485c101141d49a8202c030580003540555020024003545548240c000c44000e8041240070034640f00c0d203001141004d0040303220b0300c9800c480360248210a42c0582042c601d0100c806107007415145c503800060f507184518844140942c212240c02e000c1070552081c03035a400720100044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 935843866 1250 935842616 935842619
    0x5130807060e15150a08030405010c171c020418060515070c0b03070201060810050105030307060c0210060906082107120c080a0509120f28061a01030b030d14070309 72
    0x80c41c0400000f00c0e1440c89407003401406030040d2405c050000301030401c5400550419081000181125a040d10701801c1809000e803a482c00d200c0000455011850400c0081004140c0c0000b100c0a1341250084040205181d80ca0707000e03c482c01c0c4501c404a440080c0400180360300c003242c0200e1907204c030100340d9104003150000b080d44400240210701a40c026800040e10600c0c141d4694100000055078442003400e0100412923990004243c400494101d040010f20040384a81a45000ba21244c250a0f480c01c20a0009140513554081401c481d82d00e019564801c812440306c15210349030380c54143c07420304240031040124000d00b0034409540b246003041c20b008002c0d80c0f0752910742d0f000b51120304001400040c1c00e1600d403c28030540310790181c1907401400b0440c560300303400f62a040000c0e070000d160441c41030b0341c21040c800401600b0070560826410015040d0103a61203002c10202c0407604e003c41e04114580340c0364200062070790078107480d03542c03041c0b281c10b14012141c1c1e00741e00054082c1c0070400050300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 935845116 1250 935843866 935843893
    0x4080912190201170408040501032d1b0504050a0e0a02041a030105100c1a0a020904182d0303090510020406030912020708030a0e060c0703051005130807060e 69
    0x1500c038640c00003401c0c20007500000d100040204110380760020307510094009200c00076000a00399010340f43c0c24203003c00c991074a041100480030406003040d20100504102d09070202c07a44e80002c14800c400309010544101e5824152814030031441400e40210110358204100c1d07403094141074025000c0c0c0d402520b0a560f80104440841e00f0361800034508030000010412485d00c0000d8000168841c05d107601c60340081d413152030324650031086004108000b0400100c003c2400d07811282c1440d402071040100141d20603901151320500c0000310361722207000048492008502c1e40e264803185401c01c94400c0d200f4240d40c114054035a020b0100c0b03007481503400b41000e54055001030000340505603400a183c444606018a40d46046482c400664100c02000e00a1401c04411a011041d450410208404006c0c0c085826441076100c48151801400804002c009003c180e0387d01006ca0110144056194030303403201a5508290301c020924541089184002540713500410b92103c845030654014101459 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 935846366 1250 935845116 935845123
    0x2b05010608010f15050a051b1c1407020f0d0302210702010806010311091509030709060e10060e0d0f1b0501120e06071107171e1504080912 61
    0x81246012407894001400000002610100100f228501c1c8081244980c04003501d107101c0e03210031001300070300010181d05201088a030348400e582d0807400c460940309a1a110302c02c4000041e410340c00210740c0079050100d40c0c103032001d40c0c02403a0000c0c084003915101004101c20745441b01021001e501035040c0c10003018034110621080b02a0001c4600c0e030f60303001d510006240e52401802141450720701054054201801e1040ea45140029100d508007196034081c00d80c01405694506030303040c403a400c0c001c284204180c2181044454505410300b03982c4030381412112186050090b04c000030b901141e401050b241c8540100340c0c15011b80820744414280d034803010840000100c502c040b0020b43c0c80100315030b50780302e001001c0c1060301c2e9100700042451500c03a00c1c0c50f480044d00e118100040c3c80e80d282d4501e10300b4001d0000400515040c080001404881103441721403058200c4c541101c0d280c07000d441c64a02003110038400c42c0310b04980351266116a6510015000702900d55080280001611050070080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 935847616 1250 935846366 935846369
    0xd0320010204031104090b0f09031b0304080607090e160504032102102304020105190c230c1324091d060c07020d0b04080a03060f06052b0501 62
    0x100001d6075640c118186003440d0740915140900551404580345c02040100e08256003003113801c00b003040f0381d86644410500d103000b07c415200c07200c01d0801002e038461030b0000007041201d1410f400d54100ea034802c40240c482a5043c4101d50140b182a00003444c0542c0b00d224036103030303100e240c209207007010b880361212501d01c0300c81300f0166403d01594025030f03d4281c040240c0d111221000c0070600044004921000c000e1950010151043ca880c1e004a0216030181040c0c07011410480920f0700511b1410798010b0411120000075260b05009125100c11034005146078250070046400910441280341e0502c5143c022040c4020009992820208044104d080454444015114010b03d196081404820845640360700c0300500d184003c46503841c02c10041912980105504055a00d84c000ca00224003200c500360170003031500390540200801c21101c0c0700a890698040e075010440191102c0860040b0b82aa0240102050f0180242c3c2d00501c01c400c03400c0084840b4245112400c112541c401c020b9460a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 935848866 1250 935847616 935847677
    0x30302010c02010f0c05040905090106030206190e0103270c08010609020c12090f0d1104090f0308070e0f0d0501090605011514030f070809010e070308030a0b03070e060d03 75
    0x1900280c92119a090040c0844d00400c008108981c03800c0d0000074000e03101e80e11410000946540c00500001303403c0d80046d004507005800c0c95540c00f40358090501c010603941107980460060589030703000754031a1040d080d8001c03002c3c082034140e5075541215401008507480482d0745588c42c00020512107002c0c010900140655280562100c101c188140e060002054142034504414814070416559582006141d03070700c207490501c4894420308022011020801c10650000e007044000800c000000d0003004030580260f5546400b500c4401c41205d00210b0041d450350f1040c1a2266400c06161124181091510134000024410301e1540c0380419120242c0c4012164100d43d460b8511068011000c6070350056400c45843c075603e400c0800400c2200094916000c01c0203000010341080d200354080102c01135a00e0803910007030394a18116041da401103510764004c0d400e10744030b41c81d00d090008401c4240d4a0b0004000b0b1a903072039409105120f41812000e4042166241d00c1c15200c1d4038000340000400c10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 935850116 1250 935848866 935848871
    0x915080c0a261c090509040f08030606070501060320060309100f0e1b120f06070305040f02030303280921090e0906010305011401080606102304150503061302031f03030201 75
    0x104a180070b01450200d90080d8050981b900401000544842101c0320882d40601c4047d16030720780c0c401041480c010390300010a00d40c07030030b4400702c180100780140e61400c00250034200f10186151082c000e0300e001c1568035900c03e5100d02224550880250403054510001001c00244008814015481d00f10031040c08410035421143c40f2038242807440003c02e4042080000f40211090001c8440e43c42c80000d140c20100b581c0c0e18081002c228508000800c0b05030002c0407a6184e0400c03045110f00d40490022613404c03d1741c0f58000c0a644c2c01580104040d881e04007096650b40a0a03010041c0c0f41d01590b0b0344a000c1061145020400c503800c40700c4e0038040e203e0040100381c59811841c25600b12000d04030101810210400100201c2e840040c40c540d1094090b00d0320040e03d03d114500740e401105144030b0004001040d0f40d2184441c280101900465144031001c600c040d221800681d031911040e200c141c0c011122a11940004085d5002550010216920560384900030070200281042581003240142d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 935851366 1250 935850116 935850163
    0x21020d02040e0601030c0c0f0c030f0809040b12030403020105210118150f031e12031a040b0f0d11061b0c1504090f150915080c0a26 58
    0x2000340400f54005002c0c242040024103801001d00b030075250100082424210a45c0e20041000f5410850005c662000d50101609868a040e8500350003021040303009614203400c0c607400741760800014400b001124065450182581c00446841d441850082c07011860300c6000711030301514020325802000c81900004018400c41002d0055a00c007040161611720300e2071045c000c654601041c0002c490740541e030109440d065190507035180021407406425920201103401d40e4135050342000820401c0b0510303825107188040e0400c401c441d0081d141c0d40e001018070b001c90000c0d09040ca072810350107006944407003094042500146660303010700485000100c1c03a0101c42612038040102011315541180c2c030340304d101a1480100c500380600d01c03482d5503040c1c0312592640c170086517511004000652041409660762104089005001c00407140011800401d00005a0034008101c40c0c3d03881c0d1008200040d21b40c6000806504c1c0010380d030500000c50448040300780e030715108201615150060b03000d0420f201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 935852616 1250 935851366 935851379
    0x80a0b0f060c010225240b0409030e03121c0e030c030d0902150307020607050904020c070b0a0f1404050d03350702240a0e06070302041404020f0a21020d0204 69
    0x500701190000140f0301d4802031000084156440c811740048848196801109408a940c09047c0c0f0b20f9480380c1080c1f41411081c02d2582c8054165084c140c25011600101c043c500c6c0e8400d584960031928180b04500500c6810442d0f0070740104101007003000480341001c44004c8168110341c0310102242c6030303a41c3d07051040c045080030113500c600140409041800c520307040c003001c0c0d15660700410040c00c00100041040c020350315a41650619403944040792100b03030301d480d1414404d0b0710012507100407428408812003014401c1c11000c500b141c00300c5006080518007801e0042681d441e400481c14002010034030901e1480c85564800040802c80d0642c403805d458124030003010000ad0806070441d00501c00c15003032004004490040303c40082c5031012150350f103420b0800109020885000d281c01030400340180c060380b40c4c01910035103101d850b1110812403004100400ca10507110191030707698050001003440d500459240b85c501800307a400101e4a01020b0f44c0904a07800080820485513020805001f43d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 935853866 1250 935852616 935852647
    0xa0e030106060507110d0c08031b060f01031e020607080f070c06020c01050a050f0702030105161814061e0408011d030a051611150c0616080a0b0f060c0102 68
    0xc181600b001c51404075261901c0d05008501e000d414040e41b0b030151440f041141824400d001414564141c03500d540d207409001103280f8161554541c0c603c107030008240540341e0059901c0c101ca80c020400200a42c142844c1100020703a000305076404070040c00030601041621004140c04000780200c6945d400f0946809145020f80d41c0203a41194800d08481e8426600001101c40f40e0001c2d06041e526140740c506181803d1088000094165007020244588250b40c065842496159600c03802400380d598540000e002d84648503031815403081002d1030055003003c000402d2145150344900c1c41d04002e9000c2d81903598081e50021005a6492148100c0ca00e01d104c1c038824081d0700000035500d400000c240c010901d0080c8191405085a6030b010b41e0204240201e400301d00000c0503048050384828140900780940241c9080c1205c2c1c06850001444146c0e1040f20908603001620780c40000d03118540004010800700d0700ea150040628802c3c80c400b642c03440301402e88a003804001603a42d0381d01c0d1028080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 935855116 1250 935853866 935853869
    0x90812040311060106050301050f04062d0b130b0306121f0e2a03030d06120b0705070506070503180a12090609060e19030b0a0501091805030d0b0d05030a0e030106 71
    0xa0b2034200f0001442607940c8001120f04440c42261b40400040381e140010700104815480381103042c0c0c40d4181e1525408100450150000740c02c0c4006c11000c0c3d50324800c0d1a0361081c442000343d0700e149910240200b1210f0400b5680004010300b45036820340540204628142c003408080b00072080810701241d600c25540903040c02da00c400d5000d071010f156101010401c10700c40500000c990400c03030b002d081c1c03d500c040043c1da129042c61042030018507650410f10820240039007094a240d0140d40000d94460b0050080305e0009a200780241b100f0394034207104036190b170005009044041e001d56030002d8185000c0020031086400b80003010700080080340c02038025222684140c0521044200802c401a007051003030a0f15181510464a003003141400c404002c82250402880300059005003d0364803207551005050310004003040019007044404c1101c0072900c2d1800620fa45e10030070905c44104020f0704040061013025200c040844010765500e400c41e00302c0f030040000602d45503c2a6290b2a09001c1c80c1d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 935856366 1250 935855116 935855147
    0x50705011d01111201120f15021c140402040506030c0a03030302090a06030506130e16080d231b010e0604140c012f07080d020304030c3003030908120403 67
    0x62030aa5941e024022640052103901a04024046c0050601c09040c68000409620840070313450101e940c04102c0c000d401102d100a0402c61b0303c404001c0d0034686d40301e9020f1017450704000d01825520f5601704005800300501c100e4041c02082c80d03041e025210b00300080055031180d240035071103102000038080700201a0703005a081504010500080b600e4607414140b04100c94a4085100c55100c0703556440c20801d480c011b03032402c4040000181c00740003c41c01c030000c3c6885660716162504454030019030329215084176200030314104800e002300b0007400d01c402200c4c14100c0003c0f030300000c0d42107a181002400c0740e0503210080c61048a051000c010710804040e09024204000d1255034418030220703940e9142143c4030162015003154003102e50403c4100002c0070282c1c210ba02c209100d58000b0344941140c0300480b804108003034003044c00f402d11951900d00101040301040c1001041a000308070000d849019424556141111004104440000d1a00700d4a401c3c9605981c142072600a0140e8000764242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 935857616 1250 935856366 935856401
    0x1005061009030314070b0705030601030f0c05160312022b18020d1109090f0f0625051314010f08060f090702030f04030615060f05040b0a050705011d01 66
    0x10001a0700564824103481d01458154a480c0042d2645842c61003a810050b103405007460810243c2940013006602c100400c0c0d030203002071061084030000340c4441d500980c0c04280103001801150103090301c0d401c0c200780a0301c0d10000c00300c0d0098418080341d02c159110110043c6128154074540781e00e141e82044003e89050411601c40704810130707911148100d000900c1089007007481c400384521041c0400d5a50b1000381402803a003805590159601c08011143c4018000d1081c402046100070848510400302c0d4031001801e00c07069050b010611015100e80410700c1418403803007031009088000d00010300fa88624a080e24000b0900161109000254280030400060b04000142d164a4090301180c0400c1c0c422501c6078445074801d0b0f08501501031000f140c044045000010f0201c0ca4100901c8210740c2c0200310700715070311188101d6009014503441d401007441000100b1051180c40000d080c50507403468510b0805d2030503502c45081d951825200c01d40c441940c203409400640a1185038804040b0300d811 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 935858866 1250 935857616 935857639
    0x123131403030a0210051e0a050703150614030c0f0403080705070e010605070f03020c1002060402191203080603120d020c01051f09020c01020c0708070617010b03010b0304030909020a02100506 84
    0x80d41c0c0d41441c181c0500039622140854003500c0f40107c48007000c1c4c90080d0881e03c6140c01000b0400030300048600f000081c1c10700004101c10390300501e156003a40d0690392051003168518000c042190b01c041c00168200104001d6011a4030a803406040a58403603543c0780e507184181d003850703407400845403c801038900b008401002003c1d0083c0071180b00030f601101c0b058503903100d07040a030f0074201e060381010f030040b1801002541040e40456030764400c9101f19618101c8c0c0d007484490344c8a02406004000002d18602001c0e00840e019120265114a0060403294252040140c15101d030700643c09503000c035500031a01035840740081c040c003035005544a02c140548044010010703401d080a108141801d42c5c00540b450340300000390111010850700d0400c440a4030756440e02982e4072400744c4250000580389400c1c0d581d4a03041009074a048419407480b203420b40e402c001c80c24206a0001c0c00440038051059030004540d085030029210030716054020b0441c07514000301c1101030310303c01040710f407049c00d40104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 935860116 1250 935858866 935858887
    0xc1e062c07180b0a03060606030f060905010302090402090a0e101b180510020a020909160812040e0c0714061008010b060304060c1407060203041703040f02012313140303 74
    0x2d15140b4004071003404602030300440c000c1070340b00e40b00e0342003d072030103080c020045021a055000b41d00782540341d240402416035a1513641c42204c45c2804000d510144003000f080c058505284030390b40021555000040d041d6205411038a0201c071810385c00b0806440d0581a2000315504d48444828040c6040c48503428500c5134281c440c140003401094420340c81c1d0b804068540703100b000000e0710954058618100c13410f181c00b06613503031207801105d80780781400044085213046010848031004010104900e08041c206020711401c1c210041c040d010707498060010320b02290a520b034806207001d07514040d018900340344c14407818400b120380080d030307080c0e0400ba0801556103885c421203502a401000c0081c0750100b07008100c49880f00000a039a100d81c01051010601060781d0044d8081c52003214100405a191700c11155680400c03100a041c1c001ca0000680c00355006891340202d802c0c15000502e406d036254011040c1c2c64024001c1c803403d2980c0342e0b07000c2c00041000a03290718806001c800540c14103840c20b1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 935861366 1250 935860116 935860139
    0xb0a09020a09020309070f0915050d08030c070809030618010c170f1f030317010e04020603041515080601050a0902071e03091502032205010c1e062c07 66
    0xc00d42d88866070020018031161400d001200181c010b40e0901c0c64050769030740e0f03001d01404c1010007403038808164020005e12031900801c0c001d25075500048440c11a44c8400c04402c1e030fa04010300c281ca40c10010000110320390b0b02480031a2048406038003011507101510004c500f11348000c075404003030000d050741000c0100c45c50310700b45a10901c0c1d4a0070b04000c0d590b0001e03918414141c0d0144607101307501450080700709500154081c510142e15066803c0c5603985124a441080040d06d02175000b040420205012404800c0c80124401200ca00030800c0e6610083e50350782e107401e40d48884130607001440103200c0b61810201010040052840035401c0a01c00e03105c1c0207032078603041310f503916110f0070003164820103020704100001440d03445241c0005000412010351039501c8080c10042c81821a4004200e5844401601098600c10303515103652401365520740d0704149002080f040502a0042281c00080709030050600349081d61150550f141c40101040091182d07103801e00c0140e0700203150a0000e4034620 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 935862616 1250 935861366 935861369
    0x1b03171501170604060b0720010c02100804030c0b0112050f0615010c050c0d0c05010e0415050609011e02070e09030c1f021e180303210619060c0b0a09020a 68
    0x1408010b000d40c903807200290082030b0700d078000c120000000c03a0b80814818154100d0190000701d81e0040c100d2801c0c00d00449201e24842c00c025400b50b48601d544910314818007405a20074428109030505603d151650305084400f64000d04c000740e0400d8001c0100070042c8041146400250700a002c2c908000c0d441185c190003401d8480d0400a00b400c6020500c0004c1000701845100a4a26280e481e954201440b4900c158050180458042c802c0341109003407922400010890005c0811100703800d002c01c020895114101d00c0b410444c82215100040000300c402c1a140d001c0c0da0001c00c00140741c8424840224002001d40c100f940043c481d14428003400b28400180101d00c3c0380000401c00c07a900094024051500c55038120000980f0400c207031300c520310061a048100700c1906518407014410036a072481101103804001130518803070f00325945900b03040381c1c001400808208080e186440f1084880d00c0039070000f00050025144030007403103c00c00a55810031000c0c81c050010584a4010a000400c01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 935863866 1250 935862616 935862647
    0xc0f0e010320012a02011d010c03050c010b030304080d091a032a0a03090203101a0f0a0b1c110a0203070b0c040f0807170316030f1b03171501 62
    0xb64031031030b544e20031543c2d06035003040100c03919404050080102c4096400501c202d0205a121208840803010500c070402008816035820841e940e1554003142c068002d0b0750108403540d01c614401103a40d0302440548040c111400c0203200c42d6a54800080440d4015403010b112030302c0300c24110155146810403242d00c0700c0034054a415101d0100c032071000e807203c002d041e82e030740d508080b81c42e210183d4942c02400c65140200d0458000d03110b210303000811a0034410201c4a1203905800306061401c002000e600310030001000e00a015036106645082c03030340400403074443c1444540c054110903046103c2c0e564103843d1100460309143c4803035000f82d92441042c10260a1000c00000140c0c3e0b0311f001e80444010380060403408000550726940c00e40d540c0414010040d11310015026842240d50020a81c3c5c58452500c07800c80644000791001d071184000082c141c03080115074030300c02040c41112151000302e644039540ea040c2ca11000c400706030041c140640702c510700e0360480320400074507a07106200480d010a13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 935865116 1250 935863866 935863913
    0x80a0302091306120308010905060f011b06060f081204030201050f03060406050a17190302060106050c0f0106060e01020d02010603080f09040e0601060c1b08151f030c0f0e0103 77
    0x441d400194448402d4420248040c140f00000c100201c1d082500c0100c00d220b901d80e036130141d0305e03103504400f5100d048030b841d41c20540c0c0c000c1c001465132250711509843c0c0e00008000a004c010b60304c03210142d030500e801106180102007400c00107620b04014450b50b11410420641c1002c1c10350340003d245106003290b50107088800310215055a8a036071116004010007442c1d1660030741d4440507a410803c03084000c0606010328910401000c07010425000d6441c0d159014100503800c0c82d60130303101034220002503020740c420340c603014000e0203003407040c0750207012607480d031400107000070340020318220407441081c0031641000010030007e0a914183c40e80080054262501d641c0e426000c40c0092030146419441071284900000e0000d40007601c41e036807140603030f030000b4000310f02c502c0040d81c5004520403545150f01081c507956551000d1407440b030b00640711035030101d1031181403070703100c40041c40d181c00541345460040400c000b0888861403540c010542c140d90a2a190f14589070354629030a401040302c0600c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 935866366 1250 935865116 935865127
    0x10812070b160302160b090709150506032d06152106010225060809070b0706050a0f091209061b0807021c06050901200a030b220515040207080a0302 65
    0x3d02a4060b516690040000841108902e0a084006c00400c0da41282140a1504040f904075128000c80250b014400701c0484247e1810003400103550000300001d041185010010800c144a054507654503480714500b0203190170000e04001020f034803110481d003024410003a22a0301c003041e04400300d440708502081152030340c4140060381410690b4802440d8035180d10038000c10416200c0714031095685030341e5001220354804000a964010a01512620300c0c010b1000400081e0a0340142c1d900030307500c11000c00c0c40e020b111011000d440c07040703004480340d03202184e0310090a0b0380b01c81242c000b4003a41c60682d8501d505490540b52002d100035010380cc0c548006840802e64030b516580290340e50b1000030b901441c03142410700364002e0400303640f01100d95003011030708030358000305581d00d0340f50b51017a00c0002e2512100910990003402824030f9550031419900b4a005c0210b158030014541410015000c40d07540b500d51010203a2660300884103114034410700404003c54603400a8560307113083c17410f0050341c49 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 935867616 1250 935866366 935866411
    0x60c0d0f021908040e0601020a02030604060b0d08160201110d1d1809161e1e03050f0f062514040e0709050f040b01082706040308010812070b 62
    0x1601d03801c0a18a00c82c12000440108194100104100c03401c030320440225031208401261924009100030b94554480c00205003c039000ba4404a400003008080b02100c0d2074076603400c00a078106014941445141140403400d41d41c104440c50300400200025060300004040044c0040e9003076105800031700510140c2504648036a440d141202d2001c24081c055860f10300d20181c3da501029009070048180044001000451070200c0340c80600502041d449803400e010107240010510300c0c001d110005d010700c00002090051044a030451202405840c50180c1030340084e1038541d010b0010840f001e000751045590b6810f04c8046c6e04000b101e85030900010f40f02c85c0075140280038076005001118140414042050b0300141840d0450b103040c1c500c070030040444400c100883c0c01010040b40851031020014104e90305042d014039007d007a241d8000700b41801d0104c2180b42c0b1200b260100d001c507100c80b0040c0120302e010080602e1841d010100e1614100d4213654200c5045805801c0d884070031030b0b07000201c011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 935868866 1250 935867616 935867623
    0xb060a120914070f0f060206010b0d1404060b0a290309030c063d0302011b150e19031b0c0b0d090b060a0b07020d020103141014060c0d0f02 61
    0x201c2e0071841c1071460242802000340c075040c080c469201045403c040000d00d0b000300542c01c0e000c40d40b07941c0251045a113030542855055100c4060940e500c0d6031101000c443c2c0380c4400f01030340114042c940c001a69034a4200b1712161203559000208070344850b01d00c80c200d03510104a41884100e0a0700d0a5450b07440300c8609600e1400741c0e00da0f59580380201c03002c01480040c4540c8140079103101c00100c00700012801440b03003017000e402e8442280341c100f4070403c2c005540608041204244030000c030805e05803054492540c06650841c013380700302e0f00c94082103001d820811071104141003030b0808090351403190703801034131050001c1030300c0e05002d41c050112424000da501c1410010700481c0c0302995500500c0c0d420500901c243e502c2115091011008201d1900b440d03c041d000740c0d84142d1400c2c2c07400350f464080140048200d03c0072810161107804420314003200c15040350081248581d805000b07400c20008046150500444900441c02400018130866001581082d0000c003410040c4d503c16003200100d09 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 935870116 1250 935868866 935868881
    0xc0312090d12030c0e01030b01021c05190c051e0304090905100c02011b080702070504020705010f1d010b100503041412180306091903050a02070f0306020d050a0b060a12 74
    0x5002ea05807408440b640c164002c41c605681e25a1940c2c6207030101c80065045a000d02100e034010b80c0800c202002000148440382610252410401c1c20070440b064a43c0400f02070403d50400241c81e0100041000b404101d0280030941d42102d0380c41a44441c0400c3c0d17500e0107144034200100313440d00c04401c02c0c44001c0c04415814008090144116810148040e010781040c264280502404400f0441d560303208809a60242d0701550180c10035500c0c00c020400603400400d81520903560b928103034802c201e0303184100740c01d54007003c021010505001048070300311201c408400d0f009600903442c1810703082c0d200d002c482d402a40300140c04e001c1641d18084920380801c02010fa0713034203031000070485d8500d1b0910351480d0b1205800c03001c03603049582d00d41426071207029030152100d080c0c5181d04404002070040c0d0161060700c2041c411629070550b96550b4203c4c156403580160ba40a81c00544010001824014a0752203800003109000c00707400380010644038070030000d0712000c208107081c034215940599084040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 935871366 1250 935870116 935870123
    0x30c2a0601060302030601110c03030a050a1e0908060c0a0509130e12031503070b0723161403061302010305060604030b0c030708090610050405061c11030f0c0312090d 73
    0x4040390303102c80700070f80203620a0f01c4182c085003000d10312100046001944584810020f0003840c100044c600c1c0070345850700014a440b051000d41200300801e6100c0040221030403605a4680c0c1c02c440c80c20034094101000a844440302000400c20501501c0d0490110350607988290303548804100e81280110007040c466244120501520540000d0169400065802140383c1e401d9445a011240d003015a80c8039184581c10341064148241302c0420489040110780700307e24103405c6d03a01094007030784d17a081c5039481091703402e045810301c3c0502941d92000d541e1003220714150b0007040740d42019140004861605200241019110303400650305850b040c1c2038500071a0300400203a00d078180724900300425041102c02c0c1000411504c0080d900001c0054502e00a0001c800d00d240d5841c100014400134010042030039030044404482c240401f04440c051740b07000e0340030303c0d112000d41502c0010181886581c0c504c484455020099428441ea00480c1030520741c480e4500311a6075461246c00300d00544560000903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 935872616 1250 935871366 935871373
    0xe0402010c0206071a0109151d0a0b091f090903170a0f1a0915010c080c0705060d020909060609030714120a0308010f06031a0108090c0307080c15030c2a 67
    0x80302c0c03020305e915260603128541014400b44005820040d601d821501c05d655003031000202440685085541940d0001030010001c1031450810b8003060401030240c0700444206651840901c07003c400101e4440a80b440c810306000c40180794400030428103527040280d492032000300205201000d5039002c8105103403c4081030004540807070b80811080300f101c182c6401801c0c41c1b030000302d81e0001e0102c60042208140c690015502c104e44910f54650041007600c01c8500c01d5001c0401c0c540d5a44003c5c01d0007482010000d41e4440000040c0001c080c00030b441203000740c8040c00319400c169008144a0141e40344030a80007548594880041c01c1201d81e000c207030303003d4080c50488501f4107600001c2135050352218405910000c0e0b40390422012543e000d0b81c0d0380400017940751035110b958400c034083c54204510f20211403030300c0302d444006410301c50b5030b90002c6a254040c3c185011141000e05010f07610300b500303007003850540c500481800a14403c0e00454160544102071041892700f64060001408186c030044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 935873866 1250 935872616 935872643
    0x50f011806051210052404030503040f170d080a020d06031707170a201509010e0705030606330d0204090e0a0f0809010903060f020a0807020303010e0402010c020607 72
    0x60000c1d8032400f000ba160030b0016002401d0142c0c0c100441003124800b50240d80d22162059201c10900c03000c60206040703140800002011600400261020b40389900c0302050030b44c47e01e82e081d029003122008000d841e4024040807401aa000902e0640c440303640704000d0b030f03120b00141d2043c0c01440e483c0c100a1099600d48103400d860b1240d00d0241035040e2103080c820704c030a507200d000040c0c240a44d8800100080361381c003400307102000c228081008408000200c038500030124040c0c010b03d60080301e000038142e40d51400150069070800c1843c005120540240801d4107084002c01d5140e00b101700d2910a4410b840003000c500406900005400550075130000e03124031000601d100a03601c6445a10a26402c180300d001100c50045040840030307601500c01504009141d8607201141c0051900d94103201c0441e0b40003000c64514001d054100f820a14016a40c80030311340080d041c0c1c50013130700f00070440d4020b1006001062100312a00e401c0780d02402c1001c1401264030000f0303a6885980030050561184414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 935875116 1250 935873866 935873879
    0x3300207050601080a0506010b070303110307020a0213060f1a091c110f010203031f0b130f0f03020924040c03050709060f05090405040501060801090803150a0b04050f0118 75
    0x103401828480c5007640e107a40d983d444550382d924400340c0701400c01c0c4c0000004120364148003008040f001e120742408102589100000c101c2a00201d031a2780141c0c12451100c030841c5004503101001c00544c060400045080c5102208684107500420a00120102c0302c7c05202c03400d001601d06600d4028a5000c036032010f80454888284514002c4400c0750103030403d05458507000c020490b0b25501a80110300f983e403610310041415070f00e100c0c0c00000e044400c00100702d111841c001014210381b94440018101c0c5402048500f1040da0b90010309482032407a800c2c070040c1e89964090340c120380102d544455600310400044007002c9141c0342654090300e803260141042d60940c0000d13104260b5900c0707180d032069882005130f40402002407a5400241c0c20459071082d40741c540c0c0410707002806040001402d40d144c6890b1800c40380c0340c0c0402d5a0780c9802000b044402c551040000544076810303070300f609140d440d01c100c0c8052400340d07019a51141c400e11a82000992040c80507000c410f0740761807000c40290b079440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 935876366 1250 935875116 935875121
    0x909031c020f09041a041d07060201020301140f0a0e07030c08060a0303090b0d0f0501030f03022103011a07080705011b0f05040b030a0b2101270201080c0f0d0f060909020d0330 77
    0x11f015295000d40803002a01364018030030743c0d04a80300540c9850011200e0803c00403980d001c0010175611200e946804900b0b20550010070b40300e18441d460019048203c00350180803040020a25032040301204014400a070b4851403000c2103038100540c4a0310741401c4128140500030103824100301a1900300004140700700c050001e00b0642c087e1302664412001c1e0560b141cbc54620365142403000000402c0100550007941610920400200340c0d803d052400d15661400c55600c442000c1c1c50346d03074442c00e03002d0800105c000c1a6030a2030340c5003422000b10200000280403800b8034450a05100c00210000d004c6030b04a4200c100c037020020141d030448040009034024081110304040095803906050350b40401d4001c400b403404455035004045030540c0c6500468400800420900d81c880003407000342d415000603230107407802d468107180202d003880150613000100d4200fa071014241f5401d0100000240c3c0343c6c490f005c442641c151070700c0d00c0300404a859441800d403c801800c681540c424418030130b40360899 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 935877616 1250 935876366 935876411
    0x40c230103050f0402150a050f07080a090b0c07140a0315062303060114010311074d06090a080102040906080a050d030b030a020909031c020f09041a04 66
    0x9032070820a40c3c45011000e90800360031a0003c0d08000d0460b04410700f201c58a0240001c140640790003854005c085602084640203041c040f2007482c00400d0308034100f0b4003c01010090207032190501d060003100e8403016a1001c6a229100c620a0121012009911010501409150409414540c50120410301002001d60b0300c03a0020302e8000740929011200c40c8410b05e04940030040c0200b0040c0d0030084d19140c0306100300c0c0c0807418107a03500045c000e000074480c06816003078054195500e00c21500c1000340c000380310100000003046a1484008250045031042a02d0148200b82e010702c17401e0210302260240c400c244807964040c45a0030700080140054005206880114809119081e980c2603641c3c0c4e241c0b001000104107404c50614044082c4c0720303620850080c40e0040880d02e10342d103e6008110901c000f0b0790503c2544d0000110101c00c55508e9203048210000c0001c00c42c43d145a21045001c0c501400700450300c01d40c0c072004401e259900b10314030382003421002041045981e69918502c104060003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 935878866 1250 935877616 935877619
    0x12030313020d0230030c0d08060d02041b080601030b0d0f0c05060c0d0915080c18040603030e10110606010c02040603151b080601050702010e03030712110f160905040c23 74
    0x1480704c3d079002d115002c0280d458a122400c0100031001d20140141c4810100a02258100c0718100d600f20140e5520301503940624007061190040c10490392000782000313001004113040c1170130f245034001d0580b07550390302c50f18441e00100305444501191800d080c14050541c040e40c0c0c0400c0204200141d18030103d000c100042c516229010242d5542c0e9101c0800b5910000340c101003050f080000f0342c42e990690041c105103007018034501000e08083c0015003100c03e03a403c1940015464180001da90030403003203922518105007416011006480d01c0305682d4500240043d0400101e1140703c42151110b40101000d198000c450f1902102c9501c02d0fa8002e0040350840e840160018610791090750090001c5806100180d6803d458104243c0041d07415490341190190548020841000490a410195031007481d5a91320303031541c4000142d455140507008004038216420440728500b904440d420090b003203403c10100410300356180c1c103140c4100900b41c0d100c00894406108800c480c0c4404007210f4000420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 935880116 1250 935878866 935878939
    0x1b0c0b01261b0a080619151206023a0c02161d061f0503130209090601090b1507020f19172e0b03011e0207050105010512030313020d02 59
    0x135224065540d625040d50403542c02c0c0384606054558401c0754102c507880039000815000712590324442020401c80101c001d40d403941e4042005180300c0d82c0e0800c044600c1c0860490904046052004030b03c0b141201c0060b04100750340d4061001e6850b00034481020110b810343c081c0e0f030107030307966102d0400e2010544a111085e03100e0000003030030030719100000000d039440080701e040119442520030780301a80040c14a140e41c40c690328410005a072031500051084880f100a00059490b040c00b141c152009428814441e480307034013501d40b660540c5001c0e107401d030350101c51485d400343c0c2c0755010440394001c0105a904a1b0785119011403040d0602e1301b00340c88581400215041d201d201c4d640c2d040030300c2004212015940402350100100a5250041c000406006000280030400701d0f071035003075800840c407600d00281c0c2c02107880310a0090a214140c0100425101301e105400004403850b02c80c80024017249044c09034890450070f43d00c40322400a401030f4060641d03100d10140850364400c445092000103200503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 935881366 1250 935880116 935880119
    0x61c02011202040915081c0f05070b04080c0106050402040b1e0910020703030807030b0d03051b1009060e1203040312060509011202040e120f0c0c040c031b0c0b01261b0a 74
    0x44e0000301c03007601c7c5224060707403207000b55490000c0f1007600e1041084030410000b400807001140c4c5580b2420300546c450b00300b00da41d0740b400b5a049820f55015901080c800e5205110401005030325104503640c200c0d10a01045400391190720b0030300f560246410050b0014039076189420103503000600c031b4007941e0081e11002001d82d6403e1080302560300c034040325a00443c480814178002406400a08411711010001c0300d00301c1413140c0c41c070386865420443c00c40c4564642c0942c6003030052621031000e1701c0341414050070380000140d103d040350348030241004082007003522107070000b60040d602a10192900404203211540c0d1202e0011306158084e0f003e0748518a048121260a0800240e00701c4002c0044000c0341000b030150102c00c01f5030040342c0030443c14003e44090064035602d9225001403000151000039140b04001c5000080c125120414070601c240040c0b0300003c03941d40c2c680c490443c1d0f00032005228401d4400107031018011901c084580c180301d811104c42466a800c02030303255860b0b094440e0348445 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 935882616 1250 935881366 935881379
    0xf16050f063301030908092806050408070e04051009150e010b0d0206130503060c031e010e130c081501140102010b0108150307030f0c0617061c02011202040915 70
    0x200302082000d803030000e0740300303120b03255000e0b4103d42007250180208600341070384078021500916000310316060001c0c0c2c0c54680d1188140b19501d41c000b404091074102c2c01c1030f04000201c0e5484909028601924042030000f44c01c1203020040d0076607083d14040305100721515454640c280070301d103001112026007003500d1411007800501c00d81504180050099803819620707002c0c80890307407046804181e030782e60302d880c0800c02d600c0400600c0d00440d5600040b5940b880c2c507042105ca95410207082000481d03e00004002080100d0f080c01d8004c0326807a140014003c891404d424030240542c0404c64074080d445000c0c0c41d41031340750026030403600d102d29848588600b60004908039001c801c1d1b0719003c60001d00104825011038001814030140c007030210b030310030743e225142d4082c8440385045c110394440300402c1c1405410b40c030180e0242c01c80c28406c5054124249140050303408100c81c0c8044080246008902c401d40e84200c0800d0241036501074110f5542c1d813102c1e0700c20040d02c00071700484d01d400c0c406213000032103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 935883866 1250 935882616 935882671
    0x5030f010e1b011e030f020403050604021c0209010608250203030613060f0603050603160b0304050c0a140402030a0b0901080109020418080403174602030f16050f06 72
    0xc4034016075802d44c12904244c1c0300704100306124034507800c0503074888101c502c03004548000c1000e140124000c00041c5014410000703050103045030118501640070310f030030061b250b00c01118190b40d083d041c03200e11039441c181d001040c070028520380c08400c2c2f580d00f481034605801200641c000d07a410749200301401060506901914950720070304510b181d4108080100c14440d03442690840e00c02010746100c20a254078406090201d034012080c40c500000500c010824100040f149200058403490322040c40c0001d00d407906900310394100d009070b40010000b02c00c0c0c640e90740b0036215078000800307110240d42c4070003295008102c2d84604900683c640014040190014030550030710300d0303018603018649411590354500d281c0c2e00b10078141600c0014840491411501c000ca40d40075241180711600100d861559001c80120f0385051140d00c0901c50041840c80354044100c601680c031b00725460303607500580c2000441c1140264000340490240b003618041c20a80810218040d460f1164100600441100c82151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 935885116 1250 935883866 935883913
    0x51605090906071b0303020f0d140901050f06150c010509030418060e0402010507080705071211010f0f051614010c0801080d053a06051f020318030705030f010e 70
    0x100c3d11a041440388095000e1080c0d00c0b09111b4a005804d106a0440c02e80141c1c0001000c83d828903180c54400c01100b220a14056000c0301e090000d1004c2d05021040c00c1310b0074406400ea03402004521050060700c0880030171030306401d540c100200401e1400b024000d441e074101d406075116a600001d1451030381c1c1c041d401010180c80a81c65990b6060f00d890b4015212a4000e11040755440c000b44444000309606000c084000c20a103504d00d082044146041c40780559030140c41414000b514a60344000380d481002d050700b00703482e424007030368a0b11000000300d0000900307040184400c2d488101c04a4184064200c001e0025403903c4160143c0d0301c40103881c1e01c03248540c6103000010401d200d1065a504072089906003000c1540021003c1130440200c07400703600d410b151550350140c6401c03042060f8104541d1580f061418400000701404140300000d48070f1040340c02e0301141040701249240315941c01e2152000078080141221004420031f04d8480c060000303e5030305023580c040c00201d00b0341d0443c1c00c0f141d5032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 935886366 1250 935885116 935885131
    0xf010e06190e04050a050d050705010f05090615150703030209130b01020a080d18112b06110c0d08010f0e0433110414040921020a051605090906 63
    0x1001a420035080d040d041c82c0080043c2c41c03c1c0325403440a004208140700e403404e0b20744141c1d03901c0d546488600b41b080c00e5504040c803d01840c0d00d00303802c01016682c0400c07036640044160100b40c280c620804001100b030302980040c883c0700b1030001100e2003016003546c020001c0c80b45c142d61800a50342c1448907181184c0c944035480d03001d40c11642d42003000400f058014900c403982000001a4100340514408840942c7c0d03c044905440410803525107207066845040400c03055141100f4049165035511400444018020016522050702c10b030301130f030108169404404043c040b41c04041c0d0029008000c0c0320288600c4070032001840000c68910b50000805100d690800c0c61103400301c80e2045598480404010703004a80c0450708000c00b00e286c104e01031180c483c00d4400450741c032076040c403912075a0b4070700c0000b006200340e00e841d14080c00a10b801c00c41c510420f00c200c401d4200d03c42407103404e03400c0c0030f90b4000081c000d00554014414602c000750300c00e01580c034260707040310040c0d584001c2c0035034981d0180c0e00c56 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 935887616 1250 935886366 935886409
    0x501030201090b0a02011413061505101b1a2202210109140f07050402040f0b070c1a12090a03092c01090605010f02071820030f010e06 59
    0x2849640030f400010311000040b8400047c2070443c13420180c000c40000c2c0c1e440003880d1031003602034040c0305240c09a400340f020320344900c1c0d0b0b445103004005030211403e10610f4040c4140e200040030482c04103a400204241c201c11500a002d010800104c0030710003c441030b0b40e62200c406c03600c81e141c400c800101d031565503000c1c050304451080c28120416141501314041002c0d03481c0c41d000d400050204041c40e188584a01c000c024420804d0107650401c075050b000380780924818041044074140c244070300c3c000c8070f0440c40c0199690301203003441180081e06030000d03132410170032501200c0407082450060200d60056546000641c80d0a104152601d0080902030b0004071003000500c2111220103ca4881d00308a551803844034aa00007100b80c140c100340c2c8148005d0381c0d204000c00003940c000034200c0c580500b0b8405010401c0c1080c0c10041c2044d4198a44900b807607640580707803600c402d01c00d044003226001441c5a40c80c1e00e000080b5400c100b07801d00590000c2841600801c519041c000c0305542c900c003944020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 935888866 1250 935887616 935887619
    0x6080f0f281104060302040f1e14010302040c020309151c09022817011b0503061e04180602072a0306050402030c0a031202061b0d1806050a150801050103020109 70
    0xd05a40b12041001c0310350055841e0310000060b17a035846400129080006d000c618003510042c900303662041035030802102414030040800c0c0ca00c0d9150b0b50f0741036070b0341140c000400c14103e0070304038654040c00114036081260340c06040410092000600882034038440c125003004120b039940c07010f451307107644000d410000e00c0740d90010090040c9201e135042c441c020b003201030046c0e80c1c008680000559160881e4165595260f0030054648002c001d0300640d5941869407543c10484086081d410010080468060241900c50066034950b048000555003503006841c074840e09060840003507104a6040300c0000f018400c00d480e24848506000d4404040d850b12501c0616603202d02010b00801070049038140621180c03d14650764910080c0f0107103018003d0010310144c5d180300a40380400203041c08420300c407050201c0003030310f200380c0403100c40c3c80301c1c4031004c5456004805a0f04002e030b41100f000300540d090104100074540e107540320a02480048483da1000d40e81c400c0c802e0f00f01d4400b0301000c0d0000c0c090140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 935890116 1250 935888866 935888873
    0xb1008070603020f2b41040f0c030f0c08010c09081b1c110a09150330050a031802060708070f0f0303050601030b032b020106080f0f28 59
    0x68028010f5220b80e800500c540c10b0b80441704651062028411108440c20681c1082003048500c1d040a0240322401d440710a010f2104015100d0043c0000e200301e00190400c4100f0000052460003958414610780c1102d00f2450f103d013a140c501d01441c1e09961800b104008d43c40d11860480b4111020080604000c00d000c032228419121300d8064541c0210480e8000d48841c0b05000489441c035000e1003100300c0d90340c0c0081c1007180b828034070781c4404056030400215081c41c1c0e0b8041040c20440e42d104001e018102e82d20316200d0100ca900071400e003030468a0329103000465070800018003504030701b41d03020000941d503c24054240d00c43d812019400000a10800f8009540d800042c25614042c1d1401d81c00c4565940e00c403c0032000c4008128000381d01d030001e001c8256014000e000007120201e02500c070845956108050b24040a90004038014000e00b824a103a8000e502540160018006403102d070051170304c3c01035483c102c0c0c240c420b80c10302c41d004803032840300b04800940c115441c2050011f07003410f1140c1c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 935891366 1250 935890116 935890147
    0xa0501051522151e03030f08071413091b0e0111070b0309031b0705031011070b0a0209030d110d050705060c090102070504050403170f0c0a1103070b1008070603020f 72
    0x205569602d07440c0e11003c2a0001404c51403007815404106080d222429850000c15070441e00030b0310418040314034140451660030065100c10070405004c0309031100d120403007490201c9016440849254a0100054080511201c0340400305801d0381303a00070b100002c04011907000c0c01880b0041303400c2d0840f12090080c03007810801150454140000c50303003030144212f001c0c850340c84003594841c0b2a9009180402480c10709000e090410100d01404000f4460411a01032807441138030802083e8061810009949451070f43c1692030490004d01110040325404401600341c01805410a420748561500e44184a01c603c0803280300e994008064496500c41c005000c0741764000044681c19805480c03c0410309440f20710400b0700c10bd02942d107071205040d048841414a0341d015014401c44000741d002c0040502c02042202e04080701881c1008840c07541481c2d41e41107000d8010003d1806500d8401d0045d0171100c228014151049101903400b6155500c206a0880c805c500c01641c2550b418041e801e24100b009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 935892616 1250 935891366 935891381
    0x41212110d110703021507050c0402091e0109030c0810110a1e050705060c030f31110909010606021504050613020315100609050a05091305030c0a0501051522 69
    0x2d404a480aa4980c0d00050010545a010042c0b070900420072170103101c401c011441c1461419201140b40918140110704065202c0020b105040359040f4450116445401928011030b041002100f45c0c40d2110545920381280060161b8031500300311480800d203520104868001007030b40c4960aa401c3c041800c614805200820304042c80780500808012640502c1101d1082c0d43c2070020550b6450000c1d00b9009412014101744001e000c0c40300541034118030200d00e0303110001c50100400d102203103440c040100301503800c045900207042c0800d00c00c5001d41500824180e9417980c00f0f0b0f4900382c20092080c15848000c80f4090455070000f008101e103015012000d40c0c6240c000380c1611282d4426142c1d180420300c0c03d0310040048150300008108059005107003e01030401150382201103440c00b000111540e0000d840c40401445484a10007040f00030400c480120190700c0680742e08145074100703036000303140440b41821041c4505e40c104503645001c1c5034022140245d078540c510650041c1220a0040011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 935893866 1250 935892616 935892647
    0x20906060708120403200a06150801060806010510170417070b0708090d050f03010902210c09090a0c0804030e03010b030a1b14011d010c0206041212110d 67
    0x4011001c0441c8180c4002c2c141c240b40a0b0305480c00e424070b440c0003008055081c40041503580710103118849544089401c2c40596040341000c1640780c07400414500000d601d6000d004550b1800c1c0e070020340b148000c910103049a0048400140c0003500380020350703c051414030003528081c01a000100001c1c3e05112414007200d07411441070400050343e690014010042c0c4013640810a80030402c400100c0402107003143e200355203805410708003c0e805000780c0b0f0106020f00d503000c1342c01090b4581180405412010136504221070403030345042030039030850f140c0c0c8150841c03030041000300001b549042c0140039510a4041d0781d0703075070401c40c0c2d602e440446412084040c078641c55500c50b04c3d6204243e40400c1000103a90103440d01800c001c5528544039082c410030f9202c01480d17003401c4001d180980c0c00140030411800d22515060001040d03c00490780d807104001c000b50b01030b10214011402202d6a1080b040f050f10801c6009010100c00c1c4041e601e00801c9020300e0000d034840c11b00300808910620881204001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 935895116 1250 935893866 935893879
    0x230105070807111e090106020102160b040f05120301090f11040509150306011503050f0601081b071a0106030b1f03090602071e020118080d0302071416060e0105030112020906 76
    0x2544030005440300c0c40c40c1d0007241204c444580c2d83c215071400e10711003401003015000031841c0c01488000600c05004c80d05000c0c001c1c0003104002414440c0300303030380e9992407036000054401c0e222100818511a4100b8054100c07060310b4100d120f010500f061040020213a0858485800c2914100402c1884030004121180f49920380d42c508189880400810340606000203294070415030b188801000c0307440042c416400031404409000342e40c0d030040b12140e00708403c41502520000c1503800782c15180b00c1c0a900070300f01800d0000c3c04c0b10b104408485141030702c41c3e40e5414888040d403041080704218400c2c7c0a60751407450055010000360096100c803580510441c0054181071280c1c807041d403104101520360a0705000f0000c03d004541e40803200d600020245800e28103440e007410540b682d1441c012094a0034140d0014080c020f100050b450042d07943c15031400c599545050003046e00b14034009100340c2c0082840c11051003400d60141e020341e03050310b0240408900b041019020002131000282100340c0002c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 935896366 1250 935895116 935895143
    0x31c09060606050d0b0405041e0f0b010f03030e0105070b0a0e150c0d0608060f01091a12150a020a021c0504050d0303230405100f1e06230105070807 65
    0x4560340602070060a40b6110551524503004020707082c0c3d20404201d5214525180402001510340301c4072407103800a911050303a010000f0b00d00040b00154044024108404400001950300c0041c400ca00075a48a07607200101800c1085c010b680a0050450003060f00c0035210010b09651030550010340409010320071a0032102c5801c180080540b0f00340c400303c209030400a10a2402c0c12140101d81c000c100c2d08008014501d81000c02c081c2c0944180074580324203490303c20354100f10019094030312840100420100c107281c189a44603a40e0080c034080e1840600d5010002501610f4601c2907500100403500603060140d43d14000d21000d00e541000c132420b125080c0404101901c5000b0b0215000e403198078005000058030564a80e01c10911183c2d070300b00000201040700040f00400c030703e4400c5405420225202e00b420b4403540291007140800b030810403d090740080c0c0104150003070800c480c0003040f5008107885030508500b00c103880400142c003107042042160001402e500061088500828030383c1c0030ba4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 935897616 1250 935896366 935896373
    0xb032e09060305010b0415030b010618030b0106030506010e060a0c080906040f06020325020f040b03070902221203090620030318010e06010f05241209061008031c09 72
    0x96a00e9001554580e645e0705206401c0c1c03d1502c01e0a56074403070000500d410f0303407450751540060401400780c5c10820800641c40c089240d40c1c1c0740e07000059503200c030080402d507031a44c1700203008100448081b8001010049c001d1060304145c400c480305500603070307101200403403079072035281c8a50b0000d45a1034010008000005031001074070800005824542d003e55503510050b22141d28064031003407a1258110101d5040c030040e61b1310060f186940c94140c80c046a84144100064104030181d0300038264140002440c01d030302401e07030a94015003101c41d111040c00603142d1407099a800c40c0340c8030040200702401001d010341d9009a40f00000103000100c5010344140c1000424155001130f60001090b240c21682400840828081c808481c10f0100003044558500f102402d0281d002e07109007806424941e801c010702410903980c6e03861082c0780c2d070400c0e0359890051482c0d21498004a845070414052030000c14146440c890080d07044603050001141032100c2c4d000c081c031242e40c3c42d02c281b4540d5940d032030102000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 935898866 1250 935897616 935897621
    0x103060b0f0921011d062511070608060414060310090516120308090f2d0a0f02030f030a020a0809040b09040f03080109090c152c04060b032e09 63
    0x40007402c000121746080c1e91040300711702201c02c285500407508401c00704280440d85480000100c4050f0054090960940301d0680303d0307200c600003084160003440d50220708950801c806a004020542d001c1102c4a220364201001c0300d000e64006502d50481c44402d00401d402e60090807116001f1810381d0b003400850840285031040b6640080000b584d850f00310f405168004a0341c2d544550701d00e0141c075030240e0701188030740c076440001030491411078043c5411046105a44071407101140c070f00116402041e00d410800d94600d050349040340703e17209048149100e010003209680b25500c1701d800400e1480e00c26902c021540e0058058079400036a20031000006076512034450703000714050303525030f22600c000d0705000b003002005801645002c0e0600300c0d09030010b1f400342004000c845004214282e4000c0c00c40003143c400690f840e00401e1400c9203100c01c14948076420ba40000b01d0001c80e002c200c100d9031a4807020840c003007120642070085002e010850900042010544119902150300c2c5190b42c0b11502e9004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 935900116 1250 935898866 935898919
    0x11418090607020d0c1109042d120905011223011409100602030715021315080a05061513090c020708160b1e0d090609030e0103060b0f09 60
    0x441c1d441403007441441601131182e14010360040c03903c071038202c00c1910717000d240a14081c00640909400300004080c0407014500c0a07120511001c0075000c00d208090485079603511031000d452001c2c01d061001c802d98007900304203048903130603100d488410704402c526000903d08000300001880e20b00881c00b04008800d0020740c080c11006044007510300c0078105201c244c00000b413807004800700811003403207000c0e0000f058038440e0340e0000b811020704d10f4a07201000030b8001c00542c0705ea040078865000c5010a60026180040004d0b540e03030340165030f911203445040c1c4505031354080c3c006141c2103840c00d00f03102c104000c0240120b13450111603120740d211801402c54011040032401a0010f0105004003502400948119a01131024803c82414042a500d840c4104410313107801c0280501d041c541d903016042550704c4074000d420304010000f00c0d03041640190500e804120001803442c004c200f41c0358080c0c4a07120641d81610f001600f000031214926070944e0250103425442807192068142034072901d5005d04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 935901366 1250 935900116 935900131
    0x60e1e030316140f210408060702060603061f090209180f1b120c0313050a03021c020a1205030c040509040f05120c0c0f130c0e12070e011418 62
    0x2d060541d1810300c0c4404869606070007840d80c00a605421140d00002400b081d081804144030b088240f0210103154680303d2a8012142405800200b08205401140c807911031401503058980700d41e540d11000c1e0501c0140d113003560001c458600700344104000b650244ca1202405014141c030700c0201155108801801c4840c8640c181c28001003001c1b602054070044401015940c02c070f0304100781582030f040142d400030649100000040009030b00790b414a84100015500002940c09185aa040c001d4031703030042c1c06070940030035951500824158070014010340d99541003103400a590300020800c80742644041c1015489420521011510b540da80440303c0c020b510416101ca41749180c1d10745241000c8101a00821461082c0108000c0500114100d510308900715040448003c5950014003058200100b201c81c02e403074140c07840b08860f000104415039a400711a070340e01210490705480c1d070f924854021031485c00b0350400100002100780001c9441000d00811903d9109100308080740079000403142403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 935902616 1250 935901366 935901397
    0x120f0e010b100c020d0206031b07080706140c0d051b04240806010801030b07030f021c1d0703080c010e032d03060a230406090b010905030304060e1e0303 67
    0x41c8018a03020010141003102428408808071041d00014036050181c140030740158000030004e4180f14000c8030b0402500103c0541a481e0340d000c1c1030460b03490f004808112034162918072690000342080d101c881c070070003401208904c3c188420611078007030000507004c0c03114030056083c49030200020b680688054030b01449811007601040e0007d106603205940c10342c050107007400900200b66440f605850540741c0001003000c00d9114842c08500403d00c15501c00308503880864074800007170000307900c0040c40b1a80d1005001075840440b00a5602505241d011629400300301d040000400c8032002c0c180b1000750741f000140c0054074400103829540f1a180c2d800382049120480301d042e003002d0f980c900044002081c0281145003140128250b1502800303648a1140d66491041142d40d6404034540024070191080c0441ca645a90420142003510703507480c00b08254034000304050500109035011920309a4440884542480c148840e40442c41112070342c000c1100049080e0382c40800c0180030148000070f10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 935903866 1250 935902616 935902631
    0x60509010801170d1d040203010b09210c0d0309150503010305100207021507080d15140409050a060c09030605041101030612110f060d1e0b0d0f03120f0e01 68
    0x1465084140c210005079081c20b800689161000103003e001c1a5843c02e103041000d51708007580303d00d000704942c0294050300000010524104020161000000c1503900e5040a4648601180c41c0b20424071280e2642d48110510101c2c1d00d020188041743c10300a0401001c030945400c80003501c0349034104d15001041001004108000d420044c01c60b03100746088003107051a840d030703000808a144458200c0b9861002084013003d12466108a0b214000743c1401040395214030800ea16071107030580b02c3d078104500c40d07204102d03480c03c080c000c000100358404003600fa428415640d1034020241401d8003810032401d4a004400120a03100780c40c06940120201c0c16082051000182030310550b403c02c400101e0100001000585810242801c81004842c840d050018190104405000b0003d00c502c1036420300c051565079072007005009581c0c0b60f80c01c41c1800030117106030500450061004004014110004a0001007071007000e02150302c60140301c000c5000c17524512964143c07000d0409114069568484 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 935905116 1250 935903866 935903869
    0x1b0801021314013b09090c0a050a2403020d02070609020310020a0c020915100801030501051503211c05240907030209060d06030b061f0e061e0403050a0b060904110d1b060509 76
    0x1080c000340403c0b030b800e4401a0420300c600d244005640e0712916100000d882f10b47e40c0c6402501a10500c00110404549038040c50034414081c000200041c1d020340248002c014000c0040d000b2130711031801d00d40b6082d990703019640c24801c1814004008603a6000c400c03c0c0002d4903540c20020449070a540c0e0344840b90340d41581400e07402c45401404d0004005a42810100151030108084048440c004048440d09904401c0d5603640d1007155001d0426070142c054100c4d10326019403026000388840214194140c04401008420840c90340c07883d45d00c0f4094400192503244240c00810f4805009001c1c107060648006034030055401c0d982044406404803003c010217820003000350b9030141202d00f0120040f54692801800c1001102070700da001d5400045c02c100009010158054503200b1440c016541e01d6590401a48518084600300c5030000c60401280c3c0600d40300601c42c0c06140c0002c890505000d820f01002428100350100f00c80d5860540300000b544102e4155460080100c2c0d103071280c1e41c548100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 935906366 1250 935905116 935905129
    0x50d0b100512150108070c0302210a021501080312131704031115030a0e0a210f03110405060304110a090b03281b0801021314013b09090c 60
    0x41c850191416407843d41e10342c0b80c0c0c0c06042e840d00000c0c141801f42c0544403030b0604070700380200d0102d940d4010904804038024201d00600804000b00e103070782543c00a102c22008100001c0080c0f14200c603e5005028038200b10141003003454210015a18400d00c1382d90994406100c8540e5541100c0d81840100d010018040f0715110012507040c04c0307502200a01c03000c1c9480404d804040c00300f99051b41d8031610340106290402c00e12044c035401c50b151846070241004031450703601e10045240c001842c0304100c15191802030058072041c0034400074150519090006100c0d03182c00083c42038130a48080c0308004000c0c0c5039094407002800e0049000310b1038002c1d84050525100d80d003080f6082c81c1140410b80ca034102004030800100a5010881903148001d0214000350803000f0340103840603500c0007600310411100c84040b0000c694442440d02d13650b0102c04015500a100d41c41e450104502001410490301516891031040c1115048013046409001c800301d401e802e07080358450b01c0340e448500b01521514100c1d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 935907616 1250 935906366 935906371
    0x70204051302090f1302090a020915130e100914090d110303190213121b0e13080f040f09050105240f09040905063301050d0b100512 58
    0x440801d04100c05601045144200030404c1d0a00710491010403140d81000341d40d040300c0e0b60000c0180c3c1c13540c05c4c8044c0140c029406000340c00c0c46001e142030000503010560003038881d01c1e00e04540c03255040e85420000c04440500419443d114800b043e00401c604000e0f01c0344000c00c0c2a0240300e07440031301c0d01040c11484c004c002d07900c5c40107100500100fa00200f600208896200010b03e0522a108510000e514080d015035049801d1304841c448001c20740481c1680c9824409000e4071070b0b421080c00900d62030024841900810144541002c002490b03401180e980b110319a100b4050f00d454000c0c0e008520100340c010f0b0308040c200b0701031500c041185081a00881d0701400003264110041000010f0562540e80240301514007081d001c69000d90944045082e107001a01c05001030203141502e1415944030982258a0480c50596038040501e004081e4202070002100c40560b10169a030740c1c00654442d0040c03038501c0c0101741c40750381500040c0c6030120ba26014001d0781c0c5410352200d038494107003800030900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 935908866 1250 935907616 935907631
    0x8090607020f0c22090b04150203071d0a09020414090c0a020628091202060a050402011b020406240f020c0303030402130f0509030c0c030a02030a0311030c0d02010207020405 76
    0x2103020b0000181c1c0400c101c0c544500c212010342840c6240740c151245040c890807a83d842c240b42a464038207100a5540480c41284640010450300c41c100b8494001c900054802c840041c010395012841405a0f00744107040010040c440d42c0c03182d07603411369002030760700a411506401c90105045409030800480040e04a0034a4000034204120041c00a50300c0000410320301120010b00705503500300e5580c100a90200d4103001c414008050503003803100b070301d500707401c5613000600c50345000401d01074140c8911342c003c5505030750300700d2040700e03c03c0c20002840c070119007a07038400d03940c00d0000340315010001d10041e0288d0301b4403400b21201c0c01003000341c0310611110700c180035500142c0755680d2540e00441141e0b84154101c484800800007544210010310f1800c44802605184c038041c07040044000002c0c0541d016444211000d102c1814203054580a003494001d401d580080c5103000003901680940c03d040102ca030841c0c0c2400c502ea04241e2804036003541010260f54001010b5081d411301d4021071358880f6030f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 935910116 1250 935908866 935908873
    0x9020d02130b010e030f06041226101e030201140c0303091623060d0b0402070c0e090313033c060c0e010f0e030c2107050904080a27060809060702 64
    0x111b0441540c0f600c00042000f03189d1044d01c0b0364007001600850360481c540c02045110404d20410809031103900d81c00383c81c3c40428100c0b00c100002c64003010800e800c4000f49085111202500d15401502e11000070000b003e0120400c2c00382d580f03005802c00155109546200c010101403803594801000350394a0b03002038058084084084010000c1008005a40b40c0c0c20b0b56003c1d0380d02c409009101c010304038000c0b801c1c0c1c02400004c081c002d202c0c0780068202998040b0002e40c0681d158414002c0e0b90b80f151641020a51082d80070420216000c0d4500071181301c034110068030303030384011481e42200710418190340030b4521142d440d0400b84003040c800c0d01e11150301070030701d08000c210100020f040c0a4503070100c00e0400c032000c240f0750640d4030140030a0007008405080340240103620300320968000e00c0c00600c88014450704100103064542100c603140180e4010101030300c5c100c1400c20885540001d00102c0300c1c58240010400b00d00c403039100c0804010f1100b6601c0d50401d0070450781690402d20040c00b00c904660 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 935911366 1250 935910116 935910133
    0xa1401050408191e030506030d031b0c020a0306020a120f20030603100f0207021801061403130515070f090609050d050f0601031a240409020d02130b010e03 68
    0x603a08022200003103000c00f8828088103010404031290343d00e2204030201c2010128580f043c068142d000240104421825500040c60700c0b0403ca04842800c800d206407011241c0c1c02c1940640501c215001e183e0001e440c0c100d0302c0c0d4803912400b090b6030106a0000000390b100400b244908060303c02d148120503401c0c2e0600805010b080100c0c0800030f007804016a0030b2001021640c556410464000a44040001440403aa000d03000d61f000303401070002070b07004944d192921038500c000f2014060603034545403514820f0740c095544803c195000107001314004000c034104440814810030011015680d090405d48881c45c04076001005094024189814003030000c500384046e82c0c116404d402036600a44403095100310f036084c040d04d09010307240171000302d000c2d61001205000008072002c2250070701c6a01c4119640b245807490211329842e003110042c03070241044888070340ca000c5e00011503d0b0b0004000c0785212101c2d800041c0c101c20300c2501d40c2c0c13000e56a80000b580715604004603404442007100a0059075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 935912616 1250 935911366 935911373
    0x6121b1106280c0e030f0708161a160b0109020a0306050414010302011d0d050f071502060714090907030603050c010f02061306140103030f12090203030901080a0216050a14010504 78
    0x7410000e000c0b004807520790540c0d10140d4464403070403280013801000c0340d0602c0465210a6100e02c894001d010407030240c50102c1c40c1c50a00d2449000880c1c0f0140700340300007400c1c1c0441c254000d030440035464440b440022070034004a8140c1448502906040d00b0060741c0b030f000030b94042c040350010b03403003140200c1c00e140c84001c110581c60790190440b034080c202214004800075076101c002144500455002c2c03141c40e041c100b80030000400c4401101120115002d445e1564020068102016030354001603200e003000402041c890b070210001c079100c1c10b60841c00e12042d48001008a40c04503070700c00000b0307540c900800c00d02104000400d50034038282001b481c0b400392460002d44030b20f4010004180154581c18081c2003110035441501103042402a0180e207513140e240c0201607004a4603082c0c001110701744032a540848038800d04030704640c01001140b51044d410015a004000102240c5140b5420302044a0f814014500290325a2003000503180c1d003241450040440300d000840030003203078036110810000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 935913866 1250 935912616 935912671
    0x40b0109060206271f050609010e01120302070308040e07020d050306030a02090405101415011704030305150a0b0a030608030906030103080f090d141c080106121b1106 73
    0x88454030340140e100740841c1c00003281d846014000c05031305105078003a0340c00382800210f980d07204454049082c00315440d0b02c000c1001e00c240a00951005021450042241d08122a1020a80c902c28010b0344c0c1c1c0c0310b680b621540115000303507010740740402c03800c010800e00b80c0c3e050003444804140ca0501c141107040001c04242d0721451b40f50000c0c02004d4403004a000d200081040811340704038580240046a58410703400c65822040d21080031525000c007803c603182d809641e58904c100c441c107907a1403481d99039440480c0034002c080e000a02d60585901c014080343c64110001001e400c1c83c0740895940c910700c0f0001001c17990141d018005a40081c000d050541d69801c044904407504001e07a5600e806a2100860807803042c420240e40c0000f68641e41c4003007010001c10300200d4038600c4e06941d10030307400701c0301c054000b10006507180016007458010b0100712302507104190320039100e81c0700181c9904d4845013030a020101d03900c0704000c0f445a481031640c0b41401c02070198010510310f68070692559440b5669003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 935915116 1250 935913866 935913871
    0x2107110d0f02120c0d171b031504151806180b0a0e040303050a110c15130b010b07330c05160b0108010e030a080a05040c0b070809040b0109060206 64
    0x1008001010308200d01c0c820004503440643d4001200d984004940ca8140e8464214042c03002140394000d0690f034011100000e148100340c503081011481c0502e58a0b000700d90b00003040120110b000540b02601611244508480481c49880e00000e490618200c0e2641000c0e80e4424201c4504205d4140000c140d0360035010b2040340c410300d000c1100490a0300003032083c11160080d000b500c20a208000c1230580c503804c030368000e20525808016000d80c403910302d5118864160300c48502e81c0030006006400040030425580102c942840c41800d0200d036888103002c09d000e0344007911010f4042030900510810001020850000441c901c0800400e0318030005100f03d440c02180d2071550b500d005091250041084401500c01c5510080118101d850094540e8800b8020b0003029031900c0c1307240028080005c101d50702e0301101d8a81c1003036a40c903928120007600b4001c1048441031150080081d4481e5640060040075100d0615103840d09810004d205c200ca8816a10504004078a03c08005060700441c200f038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 935916366 1250 935915116 935915143
    0x8010b030c0f0d0501091203021908040809010806041104142707031a06030a02070b0a1a090c160c0303030b090f0109151517100e06060c12210711 64
    0x1c0e000d10f03030f0a0107030050107180e0717001d0100050840c2880c1c002c0c0c3d0503401002051641d152040c40c2000820040f140342c80f0449000f0f0154008001c019050b40c007a85410b644044000c10100340320310022696001034205610086125061003443c01303003480c11212542c194250080c0032006140c00702c0d1107103480d2402603c0d4606040c1d880a04442c40d01603112200c1c0b9000024000640c0d0341403002800000b075001c4141907400c0c0141c40c010545032503241c02095400d10307959041140000d00d107410010b0222003d031a01b89000c02c00c0010501c44e140244d842c401a9004400b241003951440c1405030544400c52a814402c9250800b0082c40c0c2d031441d5034050544903003071390010f110540040d42c1d408c00015608500510303504280386041d1580c2c040842800d54649144030700d0203403104284d0403540300346070103040c0403814000001016410a48003620786005080b0840b000f51964403446011640a80001c13100880c3c1ca940d4840555a03c2c18040d4000e01c4d07600d0f00c10702c14406100095201c1584c0380000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 935917616 1250 935916366 935916379
    0x705130212130c03290711120c03090301090b04020a0603180f260a090e0606090f01050f070804051002030310150c0615090606180902070309080f0708010b030c0f 71
    0x210244840f1180700700107180e0043e000c11142c88001d641c0684003086400310f8001c4075140c4000340069108580000202c000200101080ea054001080301c54000c0f0300d15444a1009224080155400b40210f40c40035006000707a810609060040c4880001c15400000a050812020740c200d203240310703008030348260426150b14030070ba2149400d0743e03025900e80ca0034464100d040750540981d040d16005001c0c2d88543d0702c4401e0402da8076500440603007400c50f1650f50004c02401803200c2070520092240314102c1c140350491825038881884013446d0080081a07071071040104050003103003012040c0a060344180d000440c11450b02d02c03100800101e645c05503540149000c81c210841e14003c064a15090fa07106030f003030060362910801000780a1062045400c45030500303400003005801141d082152280c0c4400034412541400e68041c003950026a045040202081c0005840b0300140102c80040e000c400203055682c2c03401001500391548554100e10903000251150125580c1841880c40d40105aa51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 935918866 1250 935917616 935917651
    0x12160c2105130f030302212710031b0c050c0405180607031e090f060b0111011d010506060405061b030706020c010509070e010b1b0c060a021c030543020705130212 71
    0x2230314618000985ca284c11504100f0b20294090f0180c218000802d80408810781042c80000d041758001e40d4414043e22540005050310450700702a00082d600660b1610741428140d25220090700c4e0000c204c80c80c000190f615280c081c0390070145200c150045240d41c42c00c0c070002b00180c42d510f650700c03d2440006c00d0300b640d464a041c01a4040c1001d1011103a000008200b01080190300090180000c0501c070315035440d1800080c428903204064a0a644015204500b00201e03401d511004007040101030308144801e1114000003103c60000f00038609045e1300100f00c90500307115051030010030380c0207241400c0070f44005001360055142074070b10000003c0700d100c0c0c500703860341d02e05814050040b1050307400001c00030b040c1c2c010035000604034010b034481c1c0c040301c01000c1c0074107021400c1768416102c0c1e80e801da40070071210401000d08110071000c560030950f1640c22406241654034400c1a610a071005600805002c020728901500c201041800c5c600d001c0d0316040c400d038942c04904100400750010803101d07041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 935920116 1250 935918866 935918917
    0x1e0b0f040b1b031b0708060f0601110712030906020d110d0c03030b120a020a0b0304020a090c020c0d200d0b0403051c0212160c2105130f03030221 64
    0x42c4809000164150303682c03589040f034a054400b13043d07041101c40b07100340d42c00060b1030000015540e10443c07054010500c4c5888039401100c8050140200780d0707241c03051110100e0f9040b10482e40810543c42500c43c58099481c00c40e02a04209036022807409015070100e007034500c40c60114080d4041c501c513140c500d034202d4461400b94018031401214503081039407a240000403003000119401c409000300c4418801c181d40301f03104c110741d203c1120025004200d01d4002c1120b1590b54001c030010341d01d10300542d03080d0180c0b0008541d41849542058843c0c0c516003c008070701881d5030020408141065465103101c00480d200c1d81d400c2c07940540020304110000860712000c560380482c4540b25512514195a2050070b00e6441c80219421b448400c0100f410702c4899030528014050240800c0d80a20501d00741d03040c00790000080700c82c640c060000d005041129015400010078008081d06620500364161421410000d10b0100e000c0e02c0002c944045000d10321038540300c802035910454030489602c903620031001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 935921366 1250 935920116 935920147
    0xd0905040509120d020d060b070615061b0c0302041e0b030a020105071202070b0d05010501030501060302190e0619090f0f06021522050606010e042009040b03071e0b0f040b 75
    0x6c2072a0246213062004607900101d28000c080141c00380ca028801605620380c41411142c080c4116004110103069619034030401c640aa08180d000e0b011a05c00c403990303a00801e0031354144115181004042c10158142124280b0038001800002c0d80100030840c5140d0000c2c2852056070301c05000055079914a00c0741e107108000681c05403144280058a9500f9140c000016050070b014160209040000124a0718428401d54054101c0038031174a40d07014009d01c2c242c41c1c0c0460040a1504a40d08228000c100600c0c0c95020300030910503a1a520140c1c607180c80c22413400e216800c12220b044219000304a013560004440b031142003013104119964594540b00205402e26000e01c010080341f5160080070300402041d039512411082c0c0350b1040402d003000800048405012159001005000510403200c503e50080c2407801d601400c006114030726040041c0c030b4200c1c40d078003402040c810707540314002250b86108060020041e451000b800d000f26030405171150f02076030241d100c1744000441c41c400e045c40d029 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 935922616 1250 935921366 935921377
    0x120f22030c06080a05090102090a051306210b2d0c120c04060e01030b0312090a0e28051e0603031b0303010f0b0304020901120c03140d0905040509120d02 67
    0x60840d400841d81c0d0307400038040f2030080740d203000b10510307000002e00914018001c450098030001e0130007402c00e041c403041100340100f01040c0d040941da2f03010b0110b0100e8059444c04040b020141d18600d201070a854402c8a800d0004c0942a001000c20342e580031000380f6005101c4188801d500000d05c80d80c51050003412406880008070b20382e2050018800044042c00c0108103881e026940c0174030b801c499100541c01e035400c88140a40540c4401c61a2a90605040c007509045000038140b4034200d80d110b044100360f410030b03103180c58a035481b19011a02c08910503000b20001d0b203404014001031500c0701500e003000d5816000740703240f0140d5070000740c0190780510072140a0020b644000c0030700b201c045459035036034000340595100c03910084800708002c1c03071a5054900c01c0303900400141c0c0396800c01d241c80c81c0d040303d40282122911410400840007075021104481c0440c8120300038200e40d0314120004240d80815849280250f1402c0c080c041149004500080b82c201340340049691065402d0400000b481407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 935923866 1250 935922616 935922623
    0x120a08040e04020619030605090105120706030f0e07090c260f0a0e0a0f0506010611030409020d0e0609010c0801140102190503090d0b060301051f1a13090e120f2203 72
    0x100fa131817480c02601941f00c00700341d40080d00c80ca58240e8855050014100265260f8202940112402c0005600c40d811000201d0341003500801c541e00300300055841c10009821240701a40c2b5031100a180c144e00c0800842e2036069000303002c8034005100342040c02e001c405000c1c051204807900000e8807040f01d540103031001503405c504840001701c490a004a21000481040340c030303801004000110248941ea040d00c01031410000366280500e0032200358001d5202404281c4055102c0d041d80103481004d2244a203e40d03100400800c1c801c0480e003005000410582081540701840c582181450f6400070348200c41302082d903040b6034201c12600b000380c44c5018070406242c1c00b00808424000b003106845005000c0c0100394000d01c49030b12981a00132011440440250202030302e807408100c2400700100d903025000002e03503a1780c0781c11120448003175030041c5600100c070001e4803007440c8840395804000948800c0c810100090a04000a601044600c200c6031802804603917a803680d9040040c101c09000115403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 935925116 1250 935923866 935923897
    0x7110f0a0b090f06030712090c081203150102011505101205011217041a030408040e1510020f03090609030f190318060c030f111605120a08040e040206 66
    0x54850241c103080d40100569801403c0189800c1c5403030038990240c0340501110348a19025448910540e0020101c089065034000e01d00980011011381c01e015600181d850a4481c41e034a1801a44000c07114111100060440e0300d0040d446404200d01c40980302a94000c64003a0700d490791700d24040b5016072441c400c0b610f07400c1c5443d00005000c000514411034081c0302d840d400031a01041d0016502900940c81100001202003481c102c003c15810001c42e841340c81424101d0500340c840700342d083c0c4458115a2841d11040c483c080c2400b510f007d01410100c92420300c01020104a80d0f1842512030207880f100c24094903011401c48810354040c0f09140f0401800800c880f01c0d070a0780303200c01482c0300c5201c006030007041c2c05e08085000003480710030350415950547c41d8000c1c400701c181d404840051200f070740a003c020304070165105042d018081030b03046107010402001c50303d0a0074100800c08003201c030546c4941e4801003071100040d0070b03042541c0465840c01d00501d80ca650703070700100f51148074403000001c250f40c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 935926366 1250 935925116 935925119
    0x20307020c040f150608160807170405070501110616030b220f0b0d0804030b060112050906070f0e01081603090203030403081c050f0f09070810050f091207110f0a 71
    0x30f071181d0084084070b85030141281502e594a805607100117040c2e504c80c200703140685442030083c1c0141080c0f0b4008400386031624609803580c0300965030344019501100c050304094001c026560f0f20400c809103004110001d070416060001e00e400300c10b0300440f202d10515032a83d000c0101940c07001c01480b00c0d00b00100b07101010b160100303403c000400c030860039054400c0c5082d0440c10030342000040760082c540d02404013841c2609580b5840311a0100600203810801c07080300c01c0340c0485941c041c0a0140b2808001803e00d802c000f0400342c80c0014000c200410050100b0600350f441c1ea0101e44503400910346021402c1118011030120b001d8481114065094400002d0000070841c0b40300007400703074542034a501d90500c0f8604200c0310a0704c205561480d410382c3c080c5c0100c1c061200103500c880d04800e0060898140681d10346196060184210500c1810b641c3c03681003000c4601c079070f0002980303c05114003500f0310b603e003151402224051300f03201604003184504d2041590312030f09802d030b4030b91200a042040d120b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 935927616 1250 935926366 935926391
    0xa0219140f0a03150602071805362803050f2101140d020d080313060c050702032107080319020304061b0806010905040f090b040302070e0f040b0703020307020c04 71
    0xc0c10310001e038142070412604e00103840c1d84003040942c20383e41d80c014105078110f0b070044400054200076140c603035a0040204507074448005400480c095031f503030290006c40860720159203820703d074545195003550720541c603002a059042c40100128136606040c02c1740c0b56041850398040b64008c14507600d010012503c1038211079404148882d0480300c84114140140d4200c2040c440c955540d15002508481d0306244200013806a002965005024000c1090300a070300f6103403c400e84000381d001c0b030085040003807100e00b9820280100d5906001501404507146050a14001d251003100005001c8000100c0800d2200c1d115090410102c510204150740704c4c2403a007403100040c00f04444032510002c0000a48105030301407000b0511807c4140c4540444a18107828080500070091107000e90a0390b030a050b0780040d20035040340340141c0c000c1d401001c501c0c0c20440c4440e440b50010b03201c00c4a81c1556020040092812444d05a00010030f00d0007684945402d1001e0b4034220752000280c1c1c2c00760401c00d00c040403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 935928866 1250 935927616 935927621
    0x142a030a230a0519020a091809050d0305071b021f0504030b0103111e0a09020d2904050609010b09041d100c081014190b0c0f060a0219140f0a03 63
    0x140e800e18a134402000c0c0313015245080b84640c03a56540415001032007001940460001c080c5541501480032807080b055564182c1441d8044034001d002c00e40da9030a124115a010110070803203100804541d08124941d000211a040c100d800400340418640001c01d441e4801c5007038900640e4030010b01c541558403071a0140d80b01020000c1c4601440340d103201040920b41c21154070310b0340c40313016040d9a4800c0c18665140c2c040e500c0080070204485d12013a201e00580400c44250203c140c100c04201d01c541050030820059400140c826403040c40780d50014404c8684510445075000d2003200c0002e1107680b03a120702c2c0112075400340d4001860080c40710050724002241c1081d1024146130385d403802d40b43d070341b4285180c00391014010788001c080c0c14404010345003070584030500c040803200b40140a817a5100c4144d4056440402c032040c860b006280c0e8038504503000c010143c1c100d2606c40c019818860104000a022020b00e000c2900b0040813030407481000281c001203a6040940b1503540d03070384246401001d0301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 935930116 1250 935928866 935928871
    0x20f19020c0406060806010c022407050c0103020c12070c12050d0f08070516050c0d080c100207150507030e0d03020c061605040303140d142a030a230a05 67
    0x540940c0701044454074140c4107001c1a10155101d00a440d102d9a0044030071421005080340c11110f000c22072000110074040b50f0002410003030002d5640d44440c5170880c00d00a910005505250041c07041941c0c512000c12030204a001c000d071801c0c0c45c0c1072a81410a6041e901da8800405a50381404400600402080b1400c6552158507018030148c00c084045800010072584000002c2042c46105101100e0355800c06145010301d003211040b040c8500042c220b0301c80d00b0380c11152850001068031815009000200d12a0001d0404609214140e1100c81c0314405040440402e01c2e9140b0010302e469029610901d00104c43c10101c0381b20141c100d030040c0095005200c000400d2203250009002c104022034090038020b85035603001d00301343c61590203a8207000c6182120202c800b0500103407020045c2c1d48513244c406865440c1c007040500f800054211101845003d5148495414144030120314100e02200d0308460040c80c0022481ca90004820403250010181c96000880409125102c40d80342c00aa0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 935931366 1250 935930116 935930167
    0xf0b040e06030c0f010e03010f0c09180b030307020d0204090b04081803031e07030c0803040515010504050907031e0803102112080402060c060f0912071502030a020f 72
    0x1031501c0d00c0040503a95249504401e5000109401c3c50141394810150101c5101c005000400c221540840d03107003d903265903405030000f42000b18108607a0089400310421400811420005a0f110782c0c00301c0e03283c3c400e0090181c002c0f412410803408540381d642c032120250750000801074940c201072410002c07560000f0700e40012003440c145104078900e80401202e100804c00140b00ea04658000c0810000da008088240d042c8559154981c3c042000034000314803440c0300b40301510705840b0f258001c68860304107812550141e40340c582002201e250006a0000340c0b40c00c81c0b1884422401c01501c12a2001d5408004020a4002c400e210200190402e500151a441c2d8080c40c0c4004100040c030050744c0803404040d0001e481528445482d40c000e0506540060018244903d01260112200d01d0b050042e00d100c900e00340b54404004020009000312041d4220b241265440d281c5a40c48100d4020b0612580068040c0d0010114000b003946a0440c3c549000f01c01d4081c0c1c4466854015214151200000380b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 935932616 1250 935931366 935931389
    0x20a0e15100504120f020406081e1e1509010e1002090f040b06120a0207020d03020604120f0f0503130c180c09051309061415120105040b061203040f0b04 67
    0x90900601402c15a41510010b540c41c6241c07540944900c1d0001c082e9140030b0740c1060742c4800114024905201805030a4100b42c4100f0f6441b018422207032400c034500c40241c20003200d040390030b5220030700411148031504d00b00031548040d4440e00700c501c0c0102a100e42c00e110038403030155074840001154018150805040b13031309105104108007400207031a0042140c95002c20300b0405045601940301d0b105400503942280141024010782c0450004520f80c502600540e220100b04000c0000511103c4011a4180b510245070600c0210190007030400052010074001c000c800100903461041a549650303401c68040030003117a4480310f000004103101076000c0c0c0d00d03040001320b5540c64090040e5000b11480540961510f504803c445801072682c40422039415403201d15500354403c0d200011805403000c0300b9500ca040190b06c0401090302d2000103110b883c0e034144000c12004c1141088880c0c0e005100359014420348141e0020181988100c1e00710444004201c8008200000e8490152007039940c0072016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 935933866 1250 935932616 935932639
    0x9050301152c0615070c03030504030203011b2a12051e040320010509090a0608010b03060603030406030e15090607030608031903020a030e01140f061e0904020a0e15 72
    0x5844a0209842000030304420b020105446041c00140052401400f901e4103003055415501c4141042855000360005140482c0c00c0c42589401e100e66100e41c0a1a22880c0c98810094009090a00f9407007941150000c4030700d9200c00008051000400d469005850703506102c1211805032050f0060b0910050050042c070400e80c0b014000700450301500c4d00300c0000468820b0941012039481c43c1044c10034100300c01400104100d0b182d04141e103000b8450810b02041190600060900712803801d0041c601c07a60210b03090017000d80340031040300d0503070784940390110b07203554180d110602d03041c00750000b01c424901c0c040070800c2c2d80c0c1001c14164040c5545076800c1c000f8640d00c0f90955034a004002d0120880584504101c41c10787c02135000745103145250501050b5412f0604c40d581c00c4dd02002100b051070b081031020080c88142c03c98010f5808031003118181d035625811013554881310142d40c003450151410b14086020355540d42040300082c401d080050000c1e2600302c00062905691600c1507004041c0d00a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 935935116 1250 935933866 935933909
    0x6051303031803020a02060f040905101502010c170a09051005010302043b10020d06090c030608060103032a05150f160509040f05012c0c0a030c0905030115 68
    0x100b00030642c2d00755000f414481c0d880e03002c01c03165610074005400305034020400014919014000c1e94030a90010014901081c90310103c040c00c1ca01c068030361001c6915005540340d205811081c2c64510302c24411103481c0650310850450028040c2e1a00039105208010303a50550300381580019060f0f074401e44050100c040b05201082e001da4583c41300b01200c2d0704040d4010755602e00e406000c1c07022070040701120084400415140c1c00ca034040c3c4040b20300181c44407824001e02c1f0050042081c400c0c0c1504e4200320311490201001d4407100180001010001d1b4442c42e140f640c0012940100080300c140c401c0700311b800d080d2030040d035100c0210f80c4d03074440101b000c40010b14803108950805e05c0740034002a0095120701917a400c8030b140c1c0c0515600c55102e80e903100c01501460a61040c5e40c00b800081074070b1101851a05260007525262000340c40406c8081c80810029418000590b1100c1545090110b030114448106680d03a9080d07400498066107000306040c00f85c800500440308541071050008e121010544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 935936366 1250 935935116 935935151
    0x22080a08190f08060103020d0b13140609060f010c1a010b09210303070c0c0906090e0f03040501170601120903050306100309020a0e090703050d08010311031f02160605130303 76
    0x2d41c40404941503200040326540030360000c3c07038000748441c4006042940d51000624099404c1588907000e41e440600b1590b002c110504c2c0d40c0c104004584450030361500000040302c550022200504012140f038012003040301750740d455035004940e03003550240e075078413400990200e030004000e840c427030301880840d158503103810044a200c110034031003e907186d40d4900d902911400d0200004481509031000c000a2008983c4200800341c41c01c454007181c4600074400d41840c0c907000c85114895a0400c0004110503a000a42303402c05407841c420340701c100d586000060f1501c3d442480c3d441c05c2581042180401c01d0750040003907116220403580d488400d04032407000c500322440c040000f900240707900c00034000d075005505600d0384858980201c401da561a84c2e00c250610b0388904001010410100050082180e850015008207100703500410010b04080c0e61500b204036408400d200244c0d0000c1c0d07541c245864110341e4480d072a003109080c842805d10540300d44c18400d24800a1340024a07220240c1108940720 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 935937616 1250 935936366 935936387
    0x190509090a1802040b13020f090a06020601080d120b030a03030c031a06070807020607051b0f220915060b0d0b090c030c0f07060c0e090a060b22080a0819 67
    0xa942d000c0300211164280030040c04071401081d40042c16984003d01c025950004240100181e500715884080040a200e00c0b10703216040705082d90454801408822400641d058441c829813800e805140c1c10341c5800700c01000390b4050b00340c150064042d003005068058016024800c40c2d99000c02c4549081c1c039180307c0d24841001036903484141080307a1b00c0854032080c00303070a909000a103441d142c5007196444038a00301c0d0038109038011002440b80c1d00d100e4601107003030004a00d41511021405c0e10548002101c6080c803181240c0c031542d03030b04011018000c201d54143c101e00b42055040104545a0b0412080d0f90050b01320200d0f00c60030250511414200001c13060f004400c6812050300396103440d662601150440c10001045902c24412040800d06601a504107800305071248200301118800344034919000070001a501410403c00700031406174001110440c4000040c0c08a915500706203000c82d182c2c036a800308120344201501c0405208900e001841c0d03000c2c2e100015030a6505100b019281d00c20071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 935938866 1250 935937616 935937641
    0x40f030e0103050c1b010b1207030b06090601050d1e05270c0a23060d0e15090d0f05040305030a02010606180803030c0313020d061505091515190509090a 67
    0x1841100c80602c004440d0400c944945c00000c60034980000106003c0c43c0c04090170806588001c0042040c8000c40c501160800c800703071042c98003031030079000107400c51244207180e02d0300f155900701060031880d00c8541050403101c2c2da0401d001906002070030402d15440e0700011400c0c90044512603e1444000500c1c07002c0c288083d2850100a02e00b150a400c034000e801c0003d008032010102511007030380ca13100181540c40d11424009480000b804e40b03d4542011000ca83d00e5640c40101805000380303001510022100d6540380c01d00c0461340c2a0002c48043c0140d6000501e03c2c40040b4041c03030f00c00c0d010f41020042d110030f540d54003100744001205004146c00c5114040c1c55070000c001203440412404000c0d83d0046108000710008080c44c0e02042114801041c1a12050340d2000c600c4441d841002407440200011a0010324508241c15a00c8051412a07a103031300c26205244042c407001070000656561a50503020449440b40390840a061a4007954000e40304121141c00102c00400c50311400c00c00e4280c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 935940116 1250 935938866 935938891
    0x40c05090a090b0a030503040b030f131104020f090a0801091209030b0609070c08070c26061609030506040b09070e131101030b0a060306080d08010302030303160c0803040f030e010305 80
    0x5850b94240007000380190064102011381c4000c404a20200000c00090108081040c4c0d0391420240f0390003120f401030092816526524031450100b01826031480480b00100c90042e6603140704a0062518450342d02d07890f0b000641c080300011002c406502c141c20050290000c45050b901252045610a40a000086c030300242c0c140880c00380c0c1013078042a030344008603003072000341c1e103040e500c2d24086600900c40885800000c0341080c030007003c00c003640384400140240d0892049070b4400025032034102c0107000d2589003540001a800003445020404015900b0005441850415081c0071030740c980200e9000b4170611034600000760b9440e0201074a80f16001081c641002c07428a666800005100c41d18014101900d8003861040b54ee502d9000700002c01040d140003c00c0303464194a40d081003a10350354042400300400c01003000d610f000c000c03250f000c1e482d01c03006143d0800040b019201c40701c04a01c06400903002100300700410804a8808003028001c2e200e900b03201842c03070011419600c1c11202107402c2c95 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 935941366 1250 935940116 935940119
    0x301180c14030c0402040905070e0103020c07030803041a01080d0e03030a09030f03020f07060509030c0402030411220c08071e0e30150c09060306060c0c13020306040c05090a 76
    0x41140c040c00e1107010050907102180a102c0014090340c01c81c0d0801d001042c0d44106002106401c04920100c4200a0a042d400c081601d101d40b42c0340e400ea8880503003d14170000001d4204811a581d1560445060b4010300a0356140e420f0156141c2c1c4003d800804607150019044603072074008281ca001000b6542c5081c0401e040d41e803480a09032016100718254851000510900b0348240880e2010b000380c0e40c0e036241c480c1e01d0503081600c0d1110710011180990b20420078030004c00c030324040e00d01e44d801040d14517058a080c01e040f1942c3c03d80c0e000b120940d0f868540003018803020791201d403450103100f85d56a003007003103d81e660088205c5040a482c041c08a906200a507d0904105500b44219501140e021181c0c440001002180c46203140710000d05400c0428404d0f0942c16401540c0d4001c0d468203452400c10b0314040118a040c40060100f522504d4045501401c0380740030820a103002c080684100c03400c0003a48404006504240e4045100b64140a010300b41c1f80c0c4240290380b0110001009104052b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 935942616 1250 935941366 935941379
    0x406091a13020c1f020702120f0c04140c0a120501091d19170d1104060201061a04031b05132009030a0b040201021204060c20010c0b0916140301180c 65
    0x81302041421030201d801740305180c05070f550403001c0b4180a80c103402520100b40090031039410420018016481703245010403000d1401e9942074042e03880404852442d9803000b6545042e221451501c480d0401c01d424000040741030860764001c103603151a50581240101000300e28075440741015164006158044000c8001085802e101d03d20040091805245803001890403102550b0603509200182d82e00002c0c104180e560901c1000001c0401c040a040c000382d100c070729103d47d84a5844090303ea200c1500c1d1100d40d240d01d41c0c0f417540080c14001c181c80040d2600f8402540508a540b400081100740c42005c844811083c2040315030404005000d010461400d40d11410a007070046c0040e0704601c120304020084403041d4008001414154590b004c0306065498000c804480c3d0019100600041d000700d100da9981001c0303000e00e0300f0f03400120301410303030b03a004455894a115002140c1e00305800c8680042c1c40c0c0380c003014a0300c9041e02038000780080711603890000b891002141008104096100081121 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 935943866 1250 935942616 935942653
    0x1020d0c11040204090219020a0c1802190309020a080705010207050d060b0319060501050a0f03060207060b031e011506051c1e14101a090406091a13020c 67
    0x100351041a86503400016500481c1c100d030041c0c3c01003103080c0d500040c000110029000c1340081c0301c1d50f0f44000e049203485583c03003941c08441c2d88100300440d0111806180c1181c407c0c3c068851401c903151841042011481004000d0061307402c0980c0640130507030700483c0110021550304103442d01a002401901d184c81c040c0a103403601604103440ca40c0e1749030381e280380d00e80c1c0621010344520b41e240c03001618a007113814003000700ca006034041403042c840c45408010210724450818102d03a00301000586507441030070b180b070140c01444506030313041c01100022030300c103442100444081d030200b1008116166101000b074800c01514001e010128205001c65030610f40d8941641080800c8044086101868440702d01e00b0f400c006c09408a0351510f41e080c0c86040140040c0169210894802c84c1c42410704c0c2605550107155600c3c54000c00c05c0000420081a4649800500041910200801480410915108030038105940241c442c82c030345041c403650000a40280c0b0f141d01d040c10054003403124000840c016 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 935945116 1250 935943866 935943887
    0x3070f05040b0313020913020f041d010c080702070603051003170f0706020306100e01080f0702010b0909010c090f210201090302040e0619021612180b041406040501020d 74
    0x10490300308004500030034030101840c01030102100e242840c50403407040104002000300410904604d030300040d00540c2e00c2d042002190801510000b6071400714020012501006400b0b802581d82800c0300300001c140e00003802c501c100b40c5a82601e084a845240440030364000761184c8505400c00034050002c200000d0a0782c12109403140d040d40380c0711226104142c0e6404c1201d0940d07103030750b001c01042110705001da54100d00803202e10380504003025102c006003c0c0340000d8074000c050a64100094a401d00075170010035121001031000b4034900c2c00000c054060540d1400840c00911100343c000f4510070740703c18010035164401d09207076002400700207160030700140150580c10030210b16800000b40c0c94520401603124000d101070000303450300704c1c1e00601154100007118120b41c41080802000c061010510b41c0302603002d01550100c00c00c4400032240e40c40f84a02c007064141000c90001204181d500c0140200c81980200200c1d44076070804000325409640318260141e00b02c20800054244102030000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 935946366 1250 935945116 935945147
    0x6060206011419080d020d0507081204080409142a0f07051203040813050a050a05060d1b020d03270605091c0201020c121303080c0c041802010e010908030307 69
    0x61104619001c1030581d03e00d5540b114545030821124003010380d81c14888400c0008003414001c0c600b074559629441ca5100e280c0e03002010782d00c0700001c1403c112003241100c00506003020140450b201c40c407406255150240c40007440c4100b00c2d602c4600034000c10728440381d01407210034114200071717504038030013611344c40140121030502522150120440b240380c061400b40d0b00039240c1584a05002c6402d9420011a811651046607843c000304400c4d90340c54030300c800703a0b13200b9902c02e61168040126600584000842c03da54043c03415070307443d0841d80c00641d48110240301c1d07505000510700b40d000201d03100781501094220018400d100301c046400c64105a400001c110300300c8600c0b8020b90320342c088440d42241e50900503500001c0460b01a01c042111007004d6144030f94585c07402d2011035042c210090311b407100814480021458443d40f20b014410000a484044d2003400003443d50407404a10507840700e4101d010885400003c81c00307500c41c1920f0019540050010352942e1104001035507049403410221 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 935947616 1250 935946366 935946379
    0x6080c040f111b0c031906140c090111070506040e270c04051e0a150501082205030403060203250305090c0f150d050a0501120f0221030304030c06050901060602060114 73
    0x1502510300300625103106c10403440c090001040b0340707480019103c1041c2c1002107640c2c82418844000c4110b001c0722002007090070710801000448207918105007003035001d191700180100740000e40c001600c50803482212003058960b0702901504a503042056400b20b4201243d06c02d210080450401d94010780d044000d44140200e42c4600d04111902d6030021960040515210132605491401070210000684401d0802640a00d002949a90940d00f00c85230f10320515801e1034100f06205040c411a0055900140103540e01d2814203c3c1100c611107180001d01c001d05e030a40c00390343e15842449038038010901381002d08603000a02e01044000c201e0b501840c1e61103a10703d500c0300d00c0c07810120000d08401b0459480483d051070014210f80885005901c02010191031200a40c000751810f4159034100e0f9040f18010001c5088902c403060900daa60b14000c000c0c4000424442030607048809400c141d031042c1024065a07580c541040d0903501180310390005a800000140140c041001000d03c0000c00541302 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 935948866 1250 935947616 935947633
    0x1401030b042d051c14030a05151002070602070603020306090a052e0503060912120a0b040905030c06060a270207050304030c0e0c07030e210106080c040f111b 69
    0x40701c0349071628442c12211a0320103200e96424059440490003076181505201480e00c000d404e000c002032100410311074040d45d40e2000035628040c0a100d44400764400381c013688040d0f0a0190203941c0b0324007030044901500c80c1000000c0e010f40b081c000c80381b08100140c0f15402c40e448030302c1160b0180c24040c0c40950311608500c05070b45205124101c50102405c4061040942840c0c4001d0500b0281c018100b120b082d009404e0002c4810300180c2141d0042402503188031244e40c812252100404d16130301404d03445414100d0b08014040e000001d0011f8004c50b0083c5c4416440e02c408018845ca0320348651050540381d00c2240743e80304054100418410062032001d4034011503940e4040c1580d00c035070012142114046024002d5141491401e54080c00c10f50385280b8210542d1006010340000902c03e5101e03020310344140921619180c0044010883e035002403041c25201e1150359103c3c215440c0c000e0042b842c1c031301160310141c400e01440304829102c888035480e100c918a014505072038070b42000d44007442400f90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 935950116 1250 935948866 935948933
    0xf0b0714010507050912070806040b040623160305010303230706020c030301080706030b0d02090402030c0d0c050411070c060c080c160617102601020d06091401030b04 73
    0x2e26803040c1c4290fa0f440d640d44205004100302e43e84d0700102441d42d54021041030210003c001445504a80c1081341e1a8495079140342400240072101b5200b824090401007104074045010741c0b450056024402810f43c40910890840485809100c05800200007a14880d000002d40e018481c2d030f41c002c40071881c541005d580f04c03102641d000c6001070829034030001c010028030a0138408007000c2e15480c81c2c02c2c0281104880052140e2a06280103407189a140c404202156010816641c0c0044040c044051283d900c0c02d00604030b03422032103035074095410300c4040040c00c411041280e400581c13003590001941d06144045070103040094086800310420001401000d07007c00220b0030150018041c80c2c01d040c101500140820a2000c4042400941e5814003084a01c08000c0f0800d0b02e03445402d44000811421240c85581d9080b1b030101103a500c0014000016440c0d50059001e03134410a00c00d0066000030010001c216809200251208035684082800104810342103480301d50161421900d44140300d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 935951366 1250 935950116 935950121
    0x6100c02060f040503240105240f040305011a010f090b0d1503020a0905150402040b0a0f021024080610090c09091811040b0303090f031c020607030e0303010f0b071401 73
    0x6c07200100740620b03108109640b40c0459605025002c1944c01c8014092160070200d03502c2c64111040c50b410001160004115821100361001160008002d004082c840845120018030051000380080c05891600900c4c1d03014441d4a81240d080e240740a1420703049030010f20041102d035042c5156449414070010142e91903030032510140205001c001464244126508204032004001c90f003d540148000c0003c0e802000c00c1d00c450400303900b40550840f9280c00704904010703818040d417412502c1c2c01481030030705d040100b215528604a5030700c0c040141d01c400d8250794844084405040c80392680c8405d100381c01c102c0c0c02c41e035004040d0381001100700380c55002500c1aa4841c902007100e801c10401034405200034102412003205040d20104400c0218801098882c4903400c05140100b514011203000b0351800c01000361080c7d064901c0911801f00c206c0020b45804050390072500103402d0181e110b091880c0802140d040310300300028040211314182000d889500088001d81c0c100c0c145401041c1c01c0c2c0c00a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 935952616 1250 935951366 935951383
    0x603030d05060a15050d150f0302061c0204090204030c0b1201060f05091e01030c0c0b0106030c090b0d0e0607050307090e0a022206091706012117030f06100c02060f040503 75
    0xa41751542c031151030345003c0040f40c5103680035196105254004220907100f02c1c1e0000180c075019254560b55030f0400c0800300c28150780a030388003041d0344006800100700b209580a002681d1240d060740604544d10718400040740240804a24894415001000382e82d0050350b40601c64040b505059040c002c0100000c0e20b00300c030100c1511146110100720007555070b03042c1710303001c00d200a600b0f10300304143e01522610060710f014080c0100b03040c1c0d9180c3c01c002c103d00500080c002402c291403202d50300d916258040010708840c28a40380d040c8110350101c1c041d18043e000303a80c0b159040d40c1d00c83d2410303450540000c01108000d001c018526500b0404c03031142d00e60310b0940d0410302480307601d545265464104d0040481010340c0c041038084001c00707080b6581e01e07130100300c060441d210641100705141c4160300340b00140b4400e100062081e1116a961094500020042d503c100b1128100210301c3c0d9460f010702400c2c860042105002840d00c1c0020b00044c03a104028001e0280000c0d1110b003040e4441c00400e01d8402c54 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 935953866 1250 935952616 935952659
    0x90115110a030e011b03021f0603170d050c0c2821090902071a04140303010609030218091015080f100e030406021e0c101205010603050603030d05060a 66
    0x95015410f5960445a4140c0341c0b640040da00c0c000e2070306620002d4a485042034011556056603412422820a64100901454100500c518904844003000100e03070300c6024003540c441d00b4500010b000c030007000240da103c05050700140c100314000050070741800c0320040e80c0000d600c500c21a00700128940602960404481105400f10602100320150040c071550380b040c8405401000100700007001456040703120514418500c009803a0381c909101e420981e003000040703500c004400022100d500c44041e80c00c0341d000740c84d40a4281e20706c0e4405c0840d940201c070b0007281a031140005140c2810994028016020400c101005140e226051107081c02800304034a400c990000c8400d14540722a4410001c0d04090580250300d000d01e010400303502c400c1101e1400004030030082c81452400d4050085c03c40803036000700002c44c42442072a01801c145000e10101c001580b0701400800d156000b4442e007802581e0080042d401c1980e000481d5019110040c0240e0300030070032290015200c0c10b40314021048618 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 935955116 1250 935953866 935953877
    0xc02180c130b0304022e0c0206040b07080a090501050a0e011d1509130209030705190323010f06080718140a0c0809061501050703030b0d061a0f090115110a03 69
    0x4c242c010840755406600b07103603d50983d9060040c07615035200c0160642452030f4109100012900d0001541d14043e66000381d840410005040b4104003124009200030b10568031409900c61303c03440112850302423941081c1c041456442407460960050070b40c5003408a1240f1a04000c01c00b000c00306070810f01c810f140c030741c10715404604d440492412001405080105002c211704083c4120300003a501e56851141d00e0107a08450105a0070707a002c0034500740950380005141d24041d00d02c481d040c0c0190007402004050f54a0007007452440c0c1414001c98040f140010014a102070a04a5400d00b0a9081080343c003590b0751001404003000c0e080107000d100b804004000070f00c281c81041c0180c144100104015600e82046040000c45890072400e2100120203180003031b04c481183ca001e81c020000300d452154011240c01c204c004101071504034038004030b0000b43e403e441a01e203800f0f20244070980c005c440e600003841c5006104184101014903010b1540d442c01010300d54910003054144042e061003940040d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 935956366 1250 935955116 935955121
    0xd11130e0105010f050103020f030117100c0c030906080f0f070504030f050c0f060309070b03100503251d04140102120406090605060a030807020118080d080405010c0c02180c130b03 79
    0xf004c3c0e50b0b80c40082c0000e080542c9403a40c4200381800c01d00c41405501200e03841102c00c078011020401c4014180040385c00200001211218050a01068103000314002100500085211442a8052402820340c09281c07000d50b1104000700c162110018062000c00c0000d100010110b00d01c140031300981405280680100c120842c1404401002d01180f2030140a04006000052800042c098101c81041075142e49a80301d07848030340342c100c10580c4826407502c1b400040c80d01200540800715040000c480301120b00940d60005078a000c82c401b058440e1200043c0d000801041510003c2e0420665480006141660740c0b500b0700c44c503150a036020350f405540c0765214401c02c061071250720f40212341112001916032865075040f240b841a507000904001c0940003103607624103200414070240c200341c0c099942e940400348008124003c102c42c143d400c0d42c280700343d6401d424003c941c21200940c0140041130310981c0d400c00f040d494240a44403000d200700400030440c2441860004501800d41640c000b541e070f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 935957616 1250 935956366 935956379
    0x1e1f1a0d02060c0a080d0b100c0b0606040b0408060a05090f1e070308031314070b030a0b211f0b1c05070b0403110108070806090a09020a090e0115060804020d11130e010501 75
    0x71f588010351680641c10340c50003240d030940c20030084211135621940c200030b6592064081780450040743d00484d001500030030040380010021980078407414080b8000c1050341d8520300210768804401c0c4d2101480e0f00440c0d040d00d00ca0380e10880d805038520f418000c4440c003640c1d0b43e072104556841180c102507a000e607000b61204000c040318610881c0d000c000c004003121070501040341c4a510002d8542d0000d640d603280a844582c940841509880c400307004504c0b40100b04488032515401354030b00030300c40c001c28004502c201c403840740305c1c0000601c0007510300240054810300d2401d80c80210b04c0b0586441c82080400a00c6444950040000d18030904c0785828200d129000900780185c050210001d0148020803c2910f44803e629598085000b000221f185401d90001c500440c6060b00504121230900e03610024440c030540010310100800c038030000d100e0740c0c0d0707240486d07460304d050760700945c490f00e05041c081c08100f41404020062000400e0018940800100c0b0401c80301c01a042c5d244994482c801044103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 935958866 1250 935957616 935957621
    0xf07120f080405060f090c03070e01050a081212090709061214010c020c0621010e010312020f060408070c0e0a09051b0117091e1f1a0d02060c0a080d 65
    0x4000d0107041c68041030419940700b9880c1c48000700038000200b020b0340056000c1c00c08010950100074090199007407182c644030040b0984901740202e50180c86552000a85040002200b44990f003d0b0506181041200320b1503160002000c3c00d5600c80d8847d001d008200c0c0c0103d40300b4100240341501c1201025642e03458400d0f601040e4248000c22a450445583c40b0a500800c2802000c801252540d9036440201d00300078000040120200d018044000042040ca842441131070517203000d2034040070b0b641c00c010800c03a501c0c206200d411400d070300a100407500052010000d0f203441c80c13048800240031512a00103405158003122810351030358407006890240101440316621100c4003401348076643c00b100c80040c100310011003207a03441c19081303000180100010300c103c0b10f10b4401003402c0203100040b020810340e54040403c10040b20300010040c0c4080c000c2e180b1580161100d0003200804d02100d00040000e048941c80040c0c0c1c01c03a00c01c0100d0200d401e0f082c0007440800703201300015501e5607181c2500404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 935960116 1250 935958866 935958887
    0x60a0f0203040b271e0c0d02011b0f080a0e010305060f0d020915030303070f08070306050d290703061d1018020c01020d060305010b0a21080f0712 64
    0x150984100240700106404100140e440b200c41c04508071071040e9590301641098100e901c410550042c1a04803542d5400c080c1600c204401000840f8000141501004a161071004000f07010441e103da200c2541420303908800c0d030640c0680c0c405030341d003c0c1d15101d840c615032003108004000344441000010944c0c240c814a42c11110a552050340c2100c0c11012070701183d0800781c040d116002110020304504411850300e180241c02400740c03034032401e06840190050410402017404181c000f0001030070180b1a107d03050403900010140014081c9584440400c107075804020409034031a03200e01f511340040c0c030114034010740183e80e00080782c030300e041c000e0b06102d45203580d032400c0c0d075208005008135545c2c03a014010036950b14628400c0d0403892100e248001344202d11103406a540081002c2e0580c1800740e000c8801c5034000d01c02400f010050340100b01c046503840c040caa07130300211a035400503110032050303101e1140d901c030b40085440c100d42d030302e000d0545405c104812030350304a03181d0501f440150320440360780 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 935961366 1250 935960116 935960141
    0x60303210608191b060503010e0c030709210203070e09070b030f04110307170109031202070321090b04260c0d080709170705010e0a18020a050c0f060a 66
    0x307281440303841c070345442c0c801003240040d07160301da552010b000c1e03004415080400d82d10311558400ba501c19000d0603070740003489040b0720b03003920b500010038505151302220b206054a0b1b5030501820305040301044841031040c9180c104881c800010700050301d00300103200281c02d103000203ea981ca00b6040144c584080c80e04009000742d4180f080c0116103441120003500039900c4a0764119200c00400400c0c5081101c3d40001003d4050608a1080b81c0d03065002104d0640203a8440d00450b44035541c00043e03220f01740e001000100305038507402608149056050b03001074148008240c0c80344684400503a140103950595220360610a000c035009088103900c20f0010300d188805040c081883c010b15141c4155446031010300441000180c1c1c0c86100c3c0a00030003810b203d040070102208400940d5030344190781d02801d808a40a00328001783d5180407179924044807014030074a10007403012381300040a07400c011394030014054107004000c07c204040c880d040401003544001d10304c901e8400b0402c400e40e41c80c1c16091 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 935962616 1250 935961366 935961371
    0xa0807290417090d0803060f0604091a01210e0111040314070812030a020906190c1a010b1b0f0f0307120302070206032a1306080109020408071a0403050106030321 71
    0xc0c541502e500c1181c400d51900039405c59165600c0703c1c081040c00c4981155030350310400010703000c613400d8541e034021080c5840c4d464941034250300701c1c8015110b80c1440c0591a040c1a080a044404a80715400a132200d00c0f00c0c40010443d440c0b0a83c2c4007a043c0c025400c103ca990b0481c0d080440d901d5800c0061800500b803030300050500104e500c200704460310000c1c18411409800140400064442a089034541424400c40d88202411004028155000d48504490000f84145100f116065002c00c42e130690740e03034110441c6818032001a035000b003146a040200203000e103018004000d1320a001d05284804074001441e5038007a1481e2aa042c508480049000c1c0b5106011103c0582c644105880e8051038802d10752400802090b5031003240c0d20841b085d183d40720070000d104034505400c0e0066408444003502c44081c1740e40c841405105a008a02694450b5400700c2010001e4840f034814024600da40d480d900743c40d140c0c90703890301402d41320f49400c1139003c00c404021081080d5034910000798041c2d00754a04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 935963866 1250 935962616 935962627
    0x70302150c0f07060e070b0714010b06090f010e060d0516020105010b071236230d020a09050c090f180f061804151d0a0807290417 57
    0x6800d20701030380b070101c01d100b04007041d803c0030410154440ca41041c101e5048402a50342d9559440880e4083e0104440405c280700100380b0000b0140200d080c03503007000f0300280c00d2501402c00d0000e80300348041824104031214410921a13120302004111034844808041502e107000e44200c008078401004000842e80f611004112110095055908450384414500410741a0840072503500c0c00082d528560200548030050003541500c0b403017801e103001111184005031b44d4407910510310b04e00fa03503a41c1a0303c96110311710b1841d1404203442c1c0007961009207000c0d080c94982c2c900c1811038104482d110b120f050005050b0405290a507130542145d00110b4501c401040240c01101c1040d4014000b01105007600e0041101f507a507968000c001c2d103080c100070401500d0a41030100c2c1c0034904410b540080b40c40d0640c0041d0080e042e29030031320407107468002004040e1013943c3d03060f0180d201c240151141c1c8080940042d074003505811440c001800032002c21044e050a0608141810040310201200b9004100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 935965116 1250 935963866 935963881
    0x509010509070b0403061104082d01090c0504090302030c030c060f1605120c041205011b0c020a12030c061b020c030d02071a1318110315040c02010e1207030215 70
    0x101c1c4c090300c0e48400007007007810030b11115a250340100d40001c1d529005600f0350f0285501e1503d6100810140159480804d88640308228221100200c014103801000c10007031220b0b05060704207881030b9100b80b049034a070130b4094203102d08540042200c44182d800950510040400c482c560ba40c01500140c890020148400400340581c0f2444c04070083c04500c1c50700051040d2200c8042d074000b0b00c00003541c074441006ca80ba00300c0c02080b0240501d00c0c1c03a20030700701b25940140b1500c2c00030b0203664003520400340e0300d0520441800c4c0d0340070700704214100442103100350001a124000c000c0d000d14104200b40b80000040c0000e41064018171003c0c0c003c0d8000504890810380c000361501c05c8818402800c05624456284403650f0b211381a800c0410750001880000c0c80428400014180c840070802040301413102c01000c29103101c1540c800790f03200d2000e03042200e00d1401e0b51200c800c0300c02d24000010480f8016212505100d1050040041c3c00004038034034080c10340520a8032030741c81c40b8800c050400d242815 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 935966366 1250 935965116 935965139
    0xc010302090612150a0b1308030412080705010b060d0c031a01080a09050f01020304030801051323060d0f0b16020105220507031506140907020c060306040204050a09050901050907 78
    0x21800b08510744000040b4401c10f502c413600c401040c1c0301400141d542038407000d01c0d80441d4051503200801108030310340021400008000ea509541c50300b8207110f02990749468200458001c15002c5d01c1555070b13102d01102c00da4030b80340202943c0107040e0780448d00f201e40007800b504a45c1202d05d14104020f0310030f030301c80e5180ea01015296200343d09550000700e07d030441c00c00624040740f803042b4000d10341c400428001419000003100f81240d004843c02c0c20380c0405420b16400341c6480c0c080c1811052160080c2c107120102250600703030b1244000d000812182042d41781c40550084038441542ca10b2500400c0c8840d03a441800c9030482c00000e400207100e6414a88040d0502c041071444904820402840300c204111007809420010f64002403036121600014218000038001d5200b40351603440d00f5040d01d80f49052a060940c8142c40c60b0b0083e280580c803620911202da400181446d500036420400480c8603a10f00c5000c07800340180e2200015140fa01246d000e00f1201c000c1c000711913903030182c0002c001000d41032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 935967616 1250 935966366 935966377
    0x80c0621090c12010203100e090f0f030405120307080d200711190b16030309020621060a03030e1201020d0f050103060b04090b130501060333060602031e2a0c0103020906 74
    0x22002080c25554504600e4200054503d1356103c0303005110744600300d2f16000000d4000e031342c0129003c08683c4266440140e680c0f181d00c000902d054010311400340900019400300c204100106d040310040224500c10014681c81020102c07040c0301880c81c1e0340301c40d05045100c204d441c0b00c01440d169205013008402d4072903000f0500380000780c150400814040601c42d400c1a0190f60b4090009507d5842c00c0407106101801c80446800212201002034000c1c84c2030000d0b001142d0309074550203684034a200034840c4a0028139440b41c0159000c001003104005030b0f2041503600003030948001259411842d12206130381c0d164110303a22590410003114049041d80c8181f54105442e2a0921981c913013a01d4018050000740c0c0c0041c1407041c083e16a06803215480300a038050301101b5940c3d800e02412040305d081114403a014000c010382c018482c5100c0a0511400440720f00c6030503a04508040544081c0d070344685041071072048100443c800d0000ba0001000030003605034003420700354180042100406d2203400f45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 935968866 1250 935967616 935967629
    0x304030327022403100806090a020a06030c090b180102100b0604061b0b040b01050906010f08070e0d0506070e0a060503360709051f080c0621090c1201020310 69
    0x200e0107044a44540540c0c0003250030504040d44d144e140005821440c83c00ca44603c5c0310300c0c0102d20006010802c00704442c00d0150340103050300026410284114001c19a0340b26400a00124500102c1d041690b1406003861500c0c4803c24002e10b80c20900090501c0d03005180d560059041400c075030f040b0342c1c8078015642030311424644041e0340b89952840d02a0608003500250882081c1010b102c00e20407001d18482c140c0304141c0e07051690b07450316801100c10181c03038100000060502008501c0c01e9102e10541811003c00030003403900c507002170303c40c40d09104084c2e4071900802d061940d01c0703540381042c100450091495040050641c507240040072501170f151088181c01c000100000350005103824844042c171401e010071500c0031621514414000c02050301c07083c0e500180c801c5a400705502210360790013610209005040c41c2c8502209100c0300b40c00c0150413000c51141c262049078403403200a11f03140b28489403401070000511640c24030192002c03051420440364010801c11118032804010102143c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 935970116 1250 935968866 935968879
    0x103030e01020a0f0f0c0605130303030e0c0402031e13080409020d020f0c0a060516021c05091e0103051e04171603170a18030e0316080102030403032702 67
    0x12000100d0801214490040820000040850074030170500203048800b4401c00055107000d031180025200c0d03010310b45d401c1069021a00007800003910a07040310400fa10380c68219605690300d400000c0a0380c000b2078017000f9540c0d0701c80301c2000b0484682e0140380c000ca68103400040c0d508031500d500245100302d005540d505900003401c2080803c4641c101c070407080300703075545039102d110900446860752121001600c0c8a8144004504511811000801507400580007000050b0040040140c0000c03030300c60481c144003081c85860312988030303040c16610141da02d11000d44824584400034080300c2020300710515280c5444102c041150521a07840d410a400405111140004d80e94091880c4282244250307200a10007000b410550008403040c0c84a480c044080c8141c0c4d03440118408450300b024284103403282c1100c0c1c0c40b01090240540790000540602038400200e42d2048015113224158020303141a0760000070003040c554948242102c002d1081c0b40400081d5804098418000c2c0d004000707803140a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 935971223 1107 935970116 935970137
    0xf30090615040618050a020c0105090a120305060f0904020a0f0b0403020a0e0403050f0d0605181e010302061905121513150902090102030c0105090d03150e010303 71
    0x40c0000303850555041305604c03000043d03c07001e40f0759421142d0801586600d1802800754901c5680100000c01d5174256500d05041c580c1284440402054609810f01c40d0b47da40b40001840c00780f800700c4166000b9162400010141c42d0030346d01001080c1000c44001802c0f058040160084900841c0c04109080c0e4403d4038400308642110010001407007000b02c03040d91910711000e400d41c9000b480c00003424545580c04600000c091f520061481308054040146044041c41000c9183e00303803d0141c0755035403441d404989203000f6694001a9082c811740c105012511a02c1640c0d1248010158541d0a0500c2c402c10118064485403040c004c5050341f1060b4286c040c070380100801018000c1c2c00004071440c0600350002034001e0100c1c0d50443c007040081400744002401a940201c50050107029080360132907001e81201e2426803203241154040f04100f1542c003d1950017070440b030300744c103100c920032 = true := by decide +kernel

theorem cover : BRFrame.Cov 935791366 935971223 := by
  have h0 := BRFrame.cov_init 935791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 935791366 ≤ n) (h2 : n < 935971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
