-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2356
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:08.149759+00:00
-- url     : https://prove2.me/submissions/74cd6524-5efa-4d80-ac3f-28e071687e61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 423561151 ≤ n < 423741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 423562401 1250 423561151 423561199
    0x302070206032724090c0607030f030b040b09160e040e0309130501080c120f06010b04080115180b04061721031909030e09010b03010f05030c0d03080717040c05 70
    0x10072000307071615041000041c04045140d41c8a0040717401e40c0c4006445100140056001840440204a04000411400b07605101d45604400c1c10b0344c08001d680010700014030a07540051904400070800049203095610640032002d12601c080c01c14428907150a44480d100c0e042101c00ca070092000700070b901da444d43da43c01258104c5801102a144a01ca01002e000d00b458031030440f20368500c1a0303901d4611a040401280e030080001300031258171141001c907220300303407600e0b01030401c0c00041e0124240140030900f00680d04104646a00151071103421000c240a0500c6612405011511601c20129150040741c4202a8040c1160804400d40824540440e501060b0340d1004800c04108040106503802c1d8400351100b0300038200181190001d10001d14100401d03001241c43c6030000c0010014829003c480790050704003103000e00300710302c40032020034011000d0190260800c80003501185040f0300691488000c242c14601c072441e94135180c204480c00c01d0072441014050406c0c00c2c81494606001000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 423563651 1250 423562401 423562423
    0xe01230a05060f0c030c030319050f010605132402010c0f080c2104050109060507031a0f0109080307050303060f011407061505030709060302031b0d080a03020702060327 74
    0x492209241081d051110700c1d0400c1040c1c04466004000c00c107482c0e0003c00160940040000003140e0b07900d00440c044404400081041c4100c60a00e000c1c0720f044001c101c001815a070311071811a80360395540c000c4415002c0d155010060446411141e0341245c3c454072a2042040002d0300207000a862200e42141c2042c040c203807800003e00c0d002c021841000700b5100510360508014001e81114041c0345d902410070105541c00c480740c0e0340d00c4a04008100305800380680c44002d600703040140031211034070070005a40507603071a446441446400c40c09680140f0401d8064116207045030340350722492030041e91340d610541c3c540384a00135039147c4003525886030041d60209031100b00c86908001842d0340c0c58000c0c0c8170440440c3c0900c2000c080100782614200184e000405000c42e0100c0c1c034074518018035051040d13481216468200200250700a6283c00d01c0c00c0c484560700000c695500c880246c2d00314020f0107484070095001000209101e0b4034050203c034150182411941103894568800b035080e0b83e032140c244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 423564901 1250 423563651 423563659
    0x601030c05100f08100515070201020f0f0a0809060c030304152f03040f0b1e1506090603090102041a04150f27090203041208130b0103021e09010e0123 66
    0x4401c00c1c40ba101c0d14080d9048191003070000e003103d888400180d800c503c5000040b200c850b004c1009419507074100440401d003348200a412002540d18141d903c842d000c41c03010b004203100003044001030b1591800c96400f41042010b40c3d07200c0c28985800c00b000c01031000c1c40b409030750034031000d4050b000700203010304c0942c6511032020300c2140c480003120140341c1000f0810365100e190741021101003444541158490851000c00b0f801000000c100c012640070060300f10800f050314254600c0460b1207410490b0341590302100d0031501c81d41d07582181800b912503070b0841e81d040c0031001503407002c400c5180c1c00b03801030b1010060703411414409110200e505001c0f107110b81001400f25200c2c500c002c07800f004010707100c2004c0340491041946881043d410f80c1c1c0300399400c0f210201d0244041c000350f903000446070741251804450496200503619030409181c0d040c00085c1c4a41d40b19031801104200d003480e0502051002f4200c00b00c5580d4445025011110910031181b9100c05800160603007003002c5451303501024010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 423566151 1250 423564901 423564917
    0x9020307020a021f0504030308190507020c0a0603050f01050108040c09061202040605010f230702030a05030d0605010c1a07050405040c08040201090f0e0f150303030f07180303020606040c02070b0c0601030c0510 92
    0x40c2301121a5600503055070340c800002418041201c046011f50352091703101d500100f407409400403c0c46000c003000c0d03000c0810135190030140000b0402130490181100c03801d1034080d8250715242081c00802e40d40d031348451003103481e0100000f0121103045420540500881e000c0261b16a9140191007005c2e2400e2101c000a112440654001614a0910f01e00c440406005414043d00e82c2c0420f1410090080aa80541c000709082d42c1c0d1090600807400a0202841c0101001e08503a03221f2101018030044030914410b00380002c0c0704a84120151030051000a10910080c007100320054170750001510264000346101001280c1d42c4038103002c0904440c20004481d0302e0380e45841c5880ca40300009001514400b078408586145a58100b0103180225511120701c402030520070400f038010500b0154101d0f40207032180041000c0381d0007040b816404941920b01140603404000100c2c02e100700c50300294800d01c008144501c400c0070000748103059034030170f100320b4101e20745500c10022018944c02c011000903140c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 423567401 1250 423566151 423566153
    0xa0203150112141011040e060307120605040219030b10050103020406050403030c0804030b040c0806060306070c060b0f1f020118080301030210050c010f051f03020f010f0909020307020a021f050403 86
    0x30550000c0c007500c520b0f0594446000c012030715825200d80d10501000d5580125041c40380340500350710300e5080b03813040b001010380d189088d000c040a00c51442010303140568130700000e015511010030030b0b1417040c0ea64003002403841d1203240484080c9400d44001c614400410000700c2d095000384215801c0d14403944030a814980b4640d0200c41142d9207140498220784184400000030740c1c0041c840e8022842164403101071820020528504800103280e00e119501440920040d290446003a04a2a420090225050b0002c0001c180c0381c490703041d82070790014501c641c91440c0420603010307180252031a50080c085c4c1e03840c048214604a501d180040c0c03a890007000100014039089010f83c58464860402609008924400f2802c541502e00e59804080d1078104101e1217406240c0101007004059011049032415500469020101c4400d03040c140100d400501e848540261046002001088d40c19583c901e0035200082d101c582070f00f0100d001d510384c50050420380c05035119000c80001180c0d04c460919180d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 423568651 1250 423567401 423567413
    0x50412090b0412061e0e0f010c05160201020c0d0b10080303010e0f091609020a2709020903160f050a061103090904020d08120f13030903080f0c0f0a0203150112 70
    0x10b80d2108403181a5617030090001c000402201101100200745c0024040c0e820607000c80c24042d6170303c80f030011030745004107107030200740c200040e500400c841600e000041c40c803138801030740341c5115034058692080f803001ca07000c1003110f0740d455036100300170500b81e0383c142c0341d550b094007681e9000038012004200f1a00000403030740035a000b000c50b1300124a4044440c3c0c0b81034000515080f140d1504002d10741d80d00054500045074010003024040c040c9440f69038807140e1140c1a1170f40880341805031a50b5544c00056007403903903408100c152201c03001201c0c040d40744d03542c40b100b40007031861501c00c003805048071420004580d40620844d156001e44140076510b030080d041c04010b21044010310499000c22100e08100204d040c0102400480d454030803201400d0a0110f528200e01e08000d00031311252070040184400680c3c441c41c80e07021a940804c4a2391101c44c18244603100d4016074280140a1080000d0002042c1c00058503540c2c013402503040c0c4640800307480c81c00441c0142401035001c8119800080c0c00042d070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 423569901 1250 423568651 423568679
    0x150e03070f0f0c0303050d1503050a02090603031e030f0a0c092123070b09060d1d010e060a0b060a2709050112020a0b16020d0c08030d050412090b04 65
    0x2c401e03184040c5000c1155a07000c040a2550015400076001080343c0707961075060301c2014816115034041c40c1841c0e00d0341d0b8410340c0d5111542c030000d000302d1200020402d541c40030419928221103885001c48501d00080c08020640c100b12807030940b02a0b02d001152001000e4819003002020950301c903840d03c1d04101c40e41c0d044158802111311040c036109140e8021038480c0054005401071109050407082c07445007c64940509500031488150040001003c03d0391034a0440e21200300b140c4d130100d007109207855110040c0300d0040145015500345032990240c184041103144c40b50380001c00400c5800300c00001e0100f14061a88044041102620201e15000e000c5500d111440c0c0802c801c1049030740c6035056030307054801c00c0e8050081015126510b1b421454a0011036028140b0109681d0828201d05d09251000300c04100c083d00031001c001c601c00c00e200c00b010345040a4403102c001c60340d030341081c41e21070710081034105c1d03040d46c10f85401c0311860180741c440c1e91100b04072010b01d0326560915081060341c1700456 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 423571151 1250 423569901 423569903
    0x604090f0b1024022401170a05070906030b0a0504170f0c1b1314150604271b020a03030209040b180117032b0e0a0f150e03070f 56
    0x182d00c0000c0050707a07000c0241e01114503054605408500c40c18103001901e01603c030301c5259450f8400700075150319144501441d50450b021400310401c0c0010300b040c81810140d9040c000303084e0380244080801c0421140c2c03c0441142e110f03171142116941d0750f400c1e843c105c1d482514001c10000030000e51b0070111940d20050720406200c40c0c03207285800443c40340249400003205180c18181882002079609107003030906002008100042808030400061048150301d000400141500001c00520700080e1151420340f0003401064101d51207401d001800e14494028092146c480e09040c42240d50040840002c2d00384050200d400400070031350702c0e0b901136002e500714102040e00315540d0005512161340700c01e0b011a540c44404a010714550401030b804809042085503c42594000c00210320311307100e04040d80f404685162a0b20000d00c8150310200081c01c1c190340e2a900c50b208030b003040ca0510a0040c03103d56254844c40c400305e030300c481c0050001d00350350345040b101d071140d0402e00c8101c001c2220300440c44101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 423572401 1250 423571151 423571171
    0x2252012100504020f09040f020f191205031c14070302040b09041109060d020d1805060112081e0d15050616061506081e0402090403030c2f01050604090f0b 68
    0x31440841c003041b0b4441044400f5640c2c4601126002d0540c03c20120a0a08140c152841441407d101c0c040441200c020311540e048648211150700501006206603400d9008001060a00406003600c0380003502400d48203555802103080441c0145000740700b110119050794081c5407c16861204102c02049410022500d642e000c00540d10f8a5030b501006185802130442c0058468403c0201c20007164040307106003004803605100c81c40401c3c0000340c2c060440310a2032503800c40e1011441d21082034018003084101c0c0345070140b61442c044d001d080107045030341c82907071040010f060910009100c0525511540e50004010096031240c4500301c01c44c2419036008100c04a500c86c20081d0180040f0101c0d88480001005d031000d000121445c0740303011040410b004c01041303050415400103070541d10064001024140e507030314590302d130b103011304003116800da18500e000480d498000d41c4a0707200b45401c120800e49510b8040090341d5450244500151107130024058800b860310341d40c45a2841801400040b50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 423573651 1250 423572401 423572419
    0xa210e010f060e0a060503060c0a02011b030b190303050a030c0c050601080309130209031f0f0501180e030f0f09120d09051003050f06040225201210050402 68
    0x156a609001e40c01200804203000610070345054a610500c200240109640b981004001c010554000a00541040d01d01c005241e55040b00d0300140c3c010002000c540003610f065007015400c1b1a05036210040c520002c3d1400d0310742426101d41915405500e02004010a6050124245451207a40308041c42e51a40c00d01400a00d12510750344d140c031501741d1102442ea03000054010460030301d4480c04140d224003401c158100400b043c0000e8540d480ca160300c48100315940510421a055500316100c0c00f00306c285d0400455854183d020b802e0203100d803c40401c6030038181070304e010001c00400c645d9851504000182880304142154020b030780001241507008090300881500d0500c01d001020030a0b4240d1a8905614600303001e0041e4141c02841c11010b1510b080200b007018002d4a84541d4400c03030440b030040e40c0d48001b000750381141441d440820985601c1c4c10405080105e88106041320042620b00e20313a22001003070800203460390000c401082d640140d43d2030283d0f074055800090f0800c1c401404500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 423574901 1250 423573651 423573671
    0x30c2004110301083306010e1c0b0c04050102070e040302150708010311100806040b031903020318040509030403061a1512150105160203072c0601050a21 67
    0x90300e444401ea50425074000004001189040191aa04040000c8503034001c01544005c00a0500f103d201100c0074400d042c001078442c0c0c0714100080804c00004c0014000c0d07414130050200d0461070150407189481c0007000314410650900c1336034215007059008000487c01c108101042030f4019108805500c508050b540e003010804444034840c48060740e41a003190701d1401c098901e0304018906c14081c0a4020240544a034001c0d01558090000c3c0e90100f401c01001c400710f8076003181c000c000d22200300004107400030958044028100c55003d0940e0640c0d0104100c100300455a054941f08480e9000f008100001602d5401480c00b01d43c1107080110f84120240115424585050012144a5000801d00306009070b1150854105000e500c10130744010203107001801c9071050308004681101c500707206030115601000280c001e002500c2c400c0e10b4448080b45100d9285440c000c004846a00381000900d03035502c2001a00c0301c040e455070300c43e460050340480081b810745104280c1d1003100c0d16000110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 423576151 1250 423574901 423574909
    0xf0b071a040b0907150807051b060108030a08060a0609030f03020102070b010b0409150b03240d030c050601060503040f0809010c020a0b0a030609050603100c09180c0e010309030c20 79
    0xa03100318001c0c034007691245070120190303013840700c1500407142c01d4407000c0c61300c9007043c3c0c003250240d4010383d80c1c10a04c0c3d884080040141101ca245a1000b41d0341c82080c0c00407400807008805010b01c0a51900d42c070b04c040c0c030348004210842c241e50103500000360b5105d0040003c03440ca00341c1c40300c103680240001483c1401c252103041603050f090300172042c501c2000904000740c01640c85002c7c8042078001c01c0641c02030031b15403801c03072a11000c3c000220103090440702195800002c00803041d4604000c000c0c0c41d0310390141ca0082c0c00340b182108155254020000001440d50103881140d224030383c07011945440300403580d202c01684c0c101c101031504004442d0000f10058a030300500101902c0040511034407210b407000e00609840710340d00b240d0701c82c9080038107201d81502c0000ea45190f0401c00c00c00400c40c00824070017199800040c0d44003440d0340c2c00310103e611005209900124640d90540e03141510304000800640944e480b40c003008001801c068a1803012450b1040d104051f80300354041c9081144140d0001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 423577401 1250 423576151 423576203
    0x80a06050c0d052404020a080f0711060108010b03070503060f0703021810021b0f030705060d200d060e040201051215060708032d010902030a06180203041208010f0b07 73
    0x7a0750703900f004401d0510075018031009521394603821141980780101c41003005106090107032000a8207480c100124604a010750189411454035004890b81c039a0b41d841003502a11400c06201c0c0a4001c2d20000700301030802180c0c03984a5002024801d00589421070100d0080d8003031070084441450884103400c4581e90400590603200e401c1c0c0c01000c580d2809408800c00504603a07086110341e411450b0412036440200301e0308200c0b00700311041501c1708002c004ea00003500460140ba00842c40707410031000d00f080404007802001200032001c10201c5d850709a01e10a480c41918003a010402c28010940061008011164028200f0200094000c04903000c0b890940041071b013182c81c01004020002d01c8a1410b400a25040403804150007441c0d500030103041c60035040c02010000380d00040001c0a942c069000070000f41210980b83c0c01e0304154034000d000a400c161812079104050168140007548204650360603a4a8149a8412140f8000250402c0d60104408035030b5200c5004482200b49445a10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 423578651 1250 423577401 423577411
    0xc0922241401090e0d0509030c1e130507141b010618060e0c0f070302012009041112040b130b0a06030605060a03020a050f010903061b140a0206130302031b0706030f06080a06050c0d05 80
    0x3c6420041d011800c210344248039052f00a9041d2810003000002e0707a0008140001d810701c0000107649110720411840f2030ba03580041403020b9800c00b14000b03003103410340d102c0381d52140f120141004160b440750860080d4010075120070000d10014071003071000c0708070b01c001880054401c0c00005042481c40c401018000850680d20140d0980030070b0010703160a113401100790281c04012000d242c0701503c0310202c1c2e00200a03001501c900e11640c00282003030140c41c00030f516103401c0800b10003180f03810794001d0041c1906020440d65030f424078020400c10700705008031200b6250300a0101c0b00d070b18145414010889a0700c690b80741040001c00c0008041045403140000703103111711180c111501105c4101134031289441ca03014544034020007002c003900303a02141d0305800c00c103411000e441082060604910718015021560130300451034866412407a40080c3c428200d60701500d0a11403465081c02880c104d80140c454503003142c00c40b8070840c00181ca10b50101d82d001c9418640305080c21840810203048841c05c6403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 423579901 1250 423578651 423578689
    0x5010603020405030c01020604080a1b1e02010e040516050315060c071409040f021525050d21050a1116050c0922241401090e0d0509030c 60
    0xd00f8880e074142808850f64494081c0001c09180c20103503501c0440c3d1240100c1101000420201900f520543d840d40858460300550781c40e520502051850f12607070b112420803404250b01d86030582c8103003014010306101e1032620341c050758002680901035072540d00050002d000111491030f102c0e296501d8402405000c40d40c0c00c0102034035820201a07907101414904030900c203034000f004000000c2c004204e1000e29a5065500142001d202c0482441030302544540c40d0380c9689449c0079a1032a41988440d4080c1d500650440742a4860408240c8400030301042108a201c00207562032034031009908141e800107407201c0002003171009801c1001c8541c0007045a6810b81e8044c01d0868244101040000381d0a13a049408c00d41a041c602214400c0c50107050124527002c1c1e843c00f032002448030f2103c15100000d5510301d0f00e210007044200b0080100000142680b064503090008070ba07140d101d100d0812900c03e040010f107801803070780b0b000369070a4100404903a4180315642c042ca0190700c80c0c090030111510604 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 423581151 1250 423579901 423579907
    0x62708011505090a020f070312060506030114100518042f03010303112d150c1c0e0309220908190327020f03070b09190509010e190501060302 62
    0x10100b0045031801303000c0f03c0001c2d0040c4030007004880302c03404551010b6410704000c01c504040002c9400600000d81c011035020350084000109040c00034000c1c410701404407010403d900c4d0400069646014011001c0c00c820b0a84084455500305030344000c1412541c1110303e403105100ea0b2406030303040c43c07131140d4040c1c1010100040003019008981e41c0308192101000c2c3c5038a030761700411b038250103480310640040480d951040008045003880907031010301c06010218090315005000500c81da100000030031030b0340c04c4071000007810a210b103d07140c80ea40a402c06949012101c0b010440036201c069601d5098034011651400c46504520502664602c41d6100e6501c4152000d14080b9943c0c58400c145d0605052801c070348100c0346003010344040394140029150420790107002044101c066185041d406114841000c2a008160000340c0280ca8080724040540e96031040d81c102003003202c2c416603411104003401403090350074500e451640400c80443c01420304820010400c1503039801c1e80024042030b400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 423582401 1250 423581151 423581159
    0x409050f060f0c190e1306060e01030524030f160e06090709062f060a0c0921021513081c0e040213050d03090f0905010627080115 57
    0x81c0300c00c9a00280851482c5150325041003a81c200d84210f01c1e0049050408100851950380103030310743c400c042c1e005440d810b034043c3d990031481e0003400309008801c080781c0307408642c4402e0341c4031340036407840346108102c0006c02008440da401c06240070740c1821a803502401411951120080028ad42400c42904400040518100074111040d2018029a01a2030500c1c100103069400c91080c41c2258558a40307107181b1507524114240c01e0a070798128203401c0b103580c1440f0455260000d42d460244a448008001c14400f0503016280c1200c10312170420b0002c8168000d4440d1026401c001039035070300107000342200c0c03500203400a1003544980c0e8a8810303110141001d1202400401101c0200070100034041a0765a68040c0905082c00b14103045204940014114040900100b5040000e1230082d082002c2c2c0e00c4c42c0d180160803902240200c42d102884002c00003140707096401903d0499245072140742c0606141164150700b82900886103403010755140d0f0003e00d0b038400b4482d030000c1d1940080308091031818 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 423583651 1250 423582401 423582403
    0xe030c1c111504061104050325050604030308040c05010e1804080f4512070306020316081012080a0c0803011701050907080705010f091d070e04050103080306010c0206090409050f 78
    0x641c045030300c0005d0103000900460b140014104181d0310300c010724122705030300da0a840e54800c000e178000c02c1c0c228101050010030140c2044603d4055441001c0d0b405450b616140111543c241c95140175038000c03407410704080e4070302c00b0504042d00f146c003905071203150140d41411100ca541c0f01341e0720201c035400700c070050395000506600301d1803d030700100c6081070545030703800d803074002c031050b116117092140d00c000c60076612162041101000855010300c0079500c030b107400c80c00010004401c850f0035010a851000103030300c8030801d41210040c0c0e8a0f049901401d003087d603c520b043da4010908001c18008114444008100740c2009035008140c400070f0140c450001403450b6094620141142c1000d1703000400134804010041b448406482007817070321002550301c1d80c00403100c80000e45d00290f100900500c81010345015205040d201d0002520b6800d1003000c04c40c00d01084520900c4040d1603000244042855580f262204014a500040483e414108a040044d04a03a048030b0225255802a0000990080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 423584901 1250 423583651 423583661
    0x60a141e0c0607030c050d11070b040507030318061d04180b150114040e0c07120c0b071706011103070209010824010609050d0c080a110102010e030c1c11150406 70
    0xc41c07071130240b1129086000c041e006001d07083d040101c05803281d80002c05404e20400380d6019039001115110181043d0410a46410090205a001a1516182d15030b0404038000a004440b4680e40342c038000481c821603c103400c14104e249507442511031010320040e0403443d25000c0c2e03060040090107024200001009088401c00321075505000e0010080042c440c103090a4900310790007000b40c21107030ba5504000c585644940c40f40200111380c0b0f0b0604138607070b40c1c0c80401c800e049441659100d907640c48030581501c082c021a2140c00500d00c591000584035441031180e02010f150701c40442381407044035800140034102c00d07040004c103070b4001103d02c6210b1241d21a03004440e041c40b45041d5855041000c000c002000741d00840e40280141da841a040141025580c1c0041201206461004905140140c0c0400e00c40c0f291600560030162400e0b528038002c02240c091440c001c2c01000307081c802c040c2c1000116001080c54041c0862000e100c0d41050082c040000301400c80e070800d1425141601e461001c0310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 423586151 1250 423584901 423584911
    0x80d0f02010b15160203011d0102091003021614030f040e090613020904060513060c050a0201050a0b010f18151e1806030207020d08040b071e02060a141e0c06 69
    0x42160601503c900800e404488040c0400706418010315028004240900b0240f2030241d0251105000c1c0e5104078810b5010b4032080300115030384d01d0483c84065007117059004110b007107507114841402d030390006003100f52000010420b0400f500d00304004070364440c9060b049540f00c240c0c132031403020411100b03800c24041294041a00c01140054541031340101e004402d0042c001020b807030392030b804130301020b051803084800613500c40020300108098000007007054100d01360714170140d8201400b040181c1030710b000d40d25580764103942d4100720000354041100d0a00b564105400c2454004030046190242600400c14003440f40d05c4e00207600e1001024085041d400e003440c17108010280145507080030301031017010229900d615025031900340c0d500024040307901c2e104005000c2a00010b0024201c010384000e800c2c81030141c81c58250b0306802c1030019588071103940c4001c1d400501000803800081c00344035041116034040c44842d082180d01c0842c4081202074184109c80031102091000d040001084101e50003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 423587401 1250 423586151 423586159
    0xc290310051e0118080322051518041413020609040c020106050109060201050705030f040510061e1a070201080c12251106180307020303040f0305010510060e04090309080d0f02010b 79
    0x40340c40d00d50310386e46900954250640341c1d0501910041c8445820035000c0c040c20740100303003d108100c09102c0260540c02454482d1120030704c107070f00702010728291090107003400000d80d61000070f0342c40d028840302110101b00103e91082c014808a001034440744921185680f00d6000041e0680c100400542400c0503940f005003160304103800c1101c0e0b241c0c041c1c25681c000400b1030200c20151981e103400b9040500c08891100352514002000414901860245e02483c1040d5650101151609003101d107d581465281391031000c10851480194442c241d0554000c080c00300f4541031400300602e02910301d8080e00d00c3c0080000780040502c06102140840180340140d05015948820880d051034072040002d00466031044901e0620707130a00380500481e1299680141a60f80d22a01c4140101c88a0000d0200703441035803074030300040e030321064000d562401c1d9540e51b180c0c240c5015100013040041c01c0c504008500704201030000056007007007000241403078400d980310202c000002c003500a0071504680595032103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 423588651 1250 423587401 423587447
    0x6060117130b040f060212060406080d0905090402010516060902010f0e1e0301020d02041217040302030a060b0a170a03022503060905011103010f030c290310051e01 72
    0x203403540c1c072510051142e44015858040d40c0c46040c0f04680e46a080b2000e412140009030880c51100700402c4113201e444102c4003080348586510301d4503610000101c0c101e010440c9404180568505800816030140c030501d0071a2601e0b2f032140c0190f502c0c0c03100100c02c4901c0fa490304000300031076030030800786285401281340110102802c20002052a80040c3d07602031540d04800710312000b901e00707404946010025104c01d40d23a4964901e420006401d00080581d103000b040400d203250b80101e04101c1e801c80307400400074402ca40058985074000c001049200380e0101d00210000b80c00c08124801a04003d100400b801c0c5001c45800c1c0a0306102c081800c0c00c0c01001d01e244000c0783e80900c00e202c1c1040d03a420143c00074444241d8a40345d4010458002d18550411003c070001031041840c42919055034452009070175025611450707a03806000100d0780041801c0e42d5507217480e000100c04041c641c801d00c2c0051168500390f80e1404900e02c001c00090103c00b000c901d1750503020710b50b0007040700f1210b054800c1c04031230 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 423589901 1250 423588651 423588661
    0x7030207020d0f05010f1b09080105040812101e14030c090a0207050f06040b010f1a0a050703020a170c28080717030705030f0601021908030703140906060117 69
    0x6403400b040100100600e030040c0d115014080b00354402ca660205024041143c50444014001c2c0c500da2100d2000001d410702402049164040c011680261b030301c030706c000b82080200c400c075071041c0c90b00801ea41c0050070b6460000901e03550115140e00c02c900c140724515152820560161025071090000c0d03402a80035856136000c03501ca0300344c55603100060100041c1c41345c4203031502c0c3d41049040c495001386481000c0500080c85500c401d210704a8816102d260622a41c604a40140780f80c00764600d00103450900041c10f100b40103000400c5c1d460302c00c0c41541c68100392039030352007002c0d046042c030419100070105c0c540e00c40f1042040b040c049045100c6805030046035099801a50420313000d00144007413804911042080950124045d0b2a1503c60310302c1d0f01d916204000038250782044130a40200f040341000b10300c155002040e90f821400396180c0c04280c02e002c42d220aa02c0f6480074200c0c50070160380f01da11882c14014540b907540122188005002c07507040400005186209800c02c80603d2256501840b07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 423591151 1250 423589901 423589909
    0x301060914040e1c0c080304050706021c0f05070609080d050402040c050717180d1101030c08070219112106010b030c190c0f06020a1713080d0b060a0f03050703020702 73
    0x1101000d140c0880400131011244c00320b5501d182e500004061030700210521080080200781803007500c10035030031218007003440c84441854610028880c4081040300f145030361500e01c00d50040c282a0302503580440c40704040d688400c4160f1041c444c100c00030b9034500c180401c61038903000700000407445180180c10048940c0b20b00b01d005a40485a146510000821003c032220b0780d90a0142044000c0200346145d00d00c0c1001030285090440c200c0c00240750126440c44180280d400740d01500e003540c003c241c0340414000c01100200b8010f41650b0b61181318034040c1203583d40422040306582941501e090441010400c28034200c03068100c900c48030803d10030000945014002c5d50304000300d16443d0148001d5981090380d2940d6800701c0a41700045110100c014804150020b028002040e0381d40c0440402c20041c000451009039601584890890060000308000740f001e442c034500d801c080000c1150000c40040e2640c3d01041e40c0c600850f41300000b2040d9950980700f110390000782c1f81002e500d019940c1d0300103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 423592401 1250 423591151 423591163
    0x20907110d051b06040515010b18040b0d061503150204060e2814090702060919061104090c08090102070c05040f18050c030f0c030304140d080301060914040e 69
    0x42002030114040018001c8050f00007090840041074489508281c20816203a084040410300c1d0000080c00010380c2c100030108031044d001c0e5043e03074040c641c0e25440c20070015202810300580d001030302e40c1c2c245010800b00d1141e0540401003034081c07104c280c82e500d000402c50155010f0b1842c000d105100820109800081c2400c442c0700c200c0e50180001c0c0b2415000b040044920700d800703c8030b41c18080203c4c0c2607002490000c42c510341254100415903030110100e9a5400840301c07132017550800103880102040c05200c50392542e201d05001320f070021004a01108036002a40b1844076240c980840440e1650000302c0c994200703019030001d62030b1171003039129421040094401c403401190b46041000c203043d0158440110300d10302241503060f421450614035a03800801ca501417003406021004040c010000940d20004400540914201841c03c5000011900002851a009085800b1940004c3d040d43d0046004c1c000e2500d814040361708050010340c510b00050541d41c0039624120700c001c4450000a20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 423593651 1250 423592401 423592423
    0xe060f06060c031c06091404030e01140918070e19060804110310140a060f1208120a05040b15010518150a0903060c140f0f0f070f02090711 61
    0x7242d654003015129403962107803031001c401d01c120304100302d4a00030582e0041d0b81213541d1b030802401911148481401c0d201019900100400c10699100130341e5402010b512960b84070300c0d0207060902c1040e070b0100719080100d06d000301301080000c00708840c8130b4002000b5501c080f0142e402d0b01600c120801c07440c04426007070250b00184403410000408114482c00c481001c400080c094940c1d000e00c0c801140041c0661100c1c450350041c2640010300003040b20300c07039201100da0403054081100e1070302114a2181e00b0308a000d43d54000704001c0c4080e80000f9031405400358141130350015061400381441890030f04090007d0001d070703403000c030000d0b1f0607030741f00c01580c072656400f13100301505002e407900064000c2d401c1e0050041c00400400c030030201c6034205600e0030440b40030318000c2c0940c07140d14000303d5400ba1200340303244030660140b007059007803a021005803100d8552501082e14201c81c94012407842e821100040b80c100714072004c1201107003016142d2603040141380c10882010b048035480c043d205c14409403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 423594901 1250 423593651 423593659
    0x2010f020c0a2a0311030c120c0907230c030403020406060909140105060f09010c0203061f050609011b0303060f03380105040e07090905030a1e020307080304230601090e060f06 77
    0x400c0345d540d550140043d205408004001c001c3c008032080f5015120908000441d05c101490340c00981c24074010001d003003140034550051800003030b1070071140c202c03500304080d247c1c05071000b4000440143c5907131143d00302500711921442c4129140140907410380d030b50003c20781d050049080040001d078440c502910741401088104584440880004030f030b12141141d800395041c440e240900c181111840d14840b01180c0e010800c09100b903c2e00207000c2c5500c242410f050000705190088041032030302e00c000c504403903c2883c0c041002d99441011391a084026041601d401c40d813005420400b0f004040d2420005480703071403410882c0406801030148000510071540569181d66100b01d01c544240710610241104050401c0b58a9417802d000d41e41e50000a01c3e00e000c2004116883d840e0481440340b4180c03500c080e4020362506666945403047e81d00040c5c4110b0b044038210005002a00c1c00036411030102495500410f61903152414120a580d0110440d0b0b8403904960305001c90f417161003041da94000010b071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 423596151 1250 423594901 423594923
    0xd0309080f180310020a0906020a020d06021e0a030b09010806070e1c0203100209090903070b0a1d0a0b0910020c030d020f07150b1906020d030c02010f020c0a2a03 71
    0x140030382c0110300020307a45541030141403600c1000034040e81c05010480c082c0d50b281103901d80c4408059070b554401c0b0002a50002196202400281070b6400030490015801501c11b400140c46a02e91400e400007000200825141c100c0d20959041401500f401010048020403d90a145802400080c000d4155500541e803440d04682c42c540b440c141d2111890703014080f50b15032040b015511000b904240c4c01d062040f04800040f821180c00003050760241d0750022a111030648a280b1807000030074041030b00b00300103201c0b040450b43c5140203004d0032000d140581e50b91500c0c2d02c6d140d440703181800b24100ca5895480e01c1030154445000001040d50440c188e40080107036540050359111181d40203224005102c1e80c5003104c803508101c1c10750000903602c082541c404400207560b500c204424140e602aa40040c1d014000000003144250403501000d4000d000004240c0410400441603174005045406158448504901080796040b101e4103029450401c0f5003074580344001c2079002c0d4880d40b0000d01590042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 423597401 1250 423596151 423596167
    0x5030d27060c030e01030b0612010e101503090507050909060711030a0c0204110d050c0a02070902120609071103031006080a020c060714040b1b010b010e0a0506070503040317030402030d0309080f 85
    0x3980b103520070315401080c10380c440300300c200fa640c0c409d002401500302c01c44901e40420400301d2003852040540e14000c01301d0901103e01a01200101210b01007500c1a106618bc00203098403030b0b214041c0540041000790001d40352103e0081c000001c8503958049651003085503140712a40700503048003450303044130f000c55061852000080b175030241131072207148540307444188429401518001c00e84400d040e008d0b10000356491025504a001d548034140044500381c0c000350325441d000c80955400649402c02d031110000582005256801c216805103c900311003900340900d41c1c0000341c0d0355001c0c1c0b03000c10070b61901119940c0c441c1c8516018001d40144a07500000030300c01018001503e01400054002c00d0700c62950b031403001c521418140c01c42081c1e510b42018480c0039445104441715910000e82242801c07858101440101d074060300050798103000a01c00807001420340400c015510003840300713258480c01c260041606204454000c0400e041c60400b0120002d43c011003582c11210007910031342e4480b298 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 423598651 1250 423597401 423597407
    0x10b0a140103020d2a08090c010903020418051002040801060f08031206220b0a170c10020a0204020d090201080708010305070e0c070803070c060b0a1a1305030d27060c030e01 76
    0x41c4030090b04c2e40c0356280346140354108201790f1070086210507650341e0031a407103070713401c01d500c1d198021050360000d85100014405400c050708845a0803441c02c0000702c00c140c0c0e503102c1508014a00d0011001c1c107070009020040004e007402618090140440028a47c900c2e024540703a40348100202242106020000964559603d04082c030007100e01c1a0001520008003107560002c0c840b81400610a19510501049102c8100d1030a0901103c1e180102101141d40e02001001080c0e807007800c04521031455508010b0f200e034009040000c0c0a2440861000c010b84005880084028074000404c0b85003001040416400111801298400c20141d4810703220060040740d01c0c07048450203404800c0010a0000741540038a262000d24003910041200058400c01c011f0321440c54440c0c1600b40c0c80e000040d600313280c1c0c8280100070740800100d00320600d079516800301c0d08241d103011013900800d00c01d1221642d40c1c00c003205c0031402d40c81804654200c150500d03001402c80b5031407040281c10010301080030001030340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 423599901 1250 423598651 423598661
    0x90e01090b0310200f0d0612050c01080c090d050604020918210f03040506100b31080f070e0703090b070804020316141804080708130902030c0c010b0a140103020d 71
    0x11140741303160f948104000101c402a8000700c5e51070243c0d03203411400103030001002c1001d140e15500c1030140c03050304014001110212009014070900c2e040400ce00b101a560310685c8505161080004d007540c0e140c940108824500000c00007401248240c1c8481190600814441407804004404144640c980c1c00e401a0324040c1d170f4080413000d0800824001440b03030008007140700300ca5031411070341016101c0344455580d014070342941107050200100c415420f0b001458520101c04001c91070004241da61011925001d07400c0501c0c1460741088000380701c40030044c0c01107a0310882c1030a00303012041c1196034484400b10000c1944081121900200b41159000c1c040b4421401c0b101c21000700c0300c0d4852100c803d081d5490301c02d071442080400b0507552104109078140d80710b590440c00702c0c0e00308002900c5200066104c9804402c802001c41c0010440780d081d440a1350044a01d24146500d80319800c0f605821520204030041c40369008900410020212000e07254241d0028a00541c46072462820080500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 423601151 1250 423599901 423599951
    0x31a090c0d0b22051b060915040303121103070c020f04050108010509191a0402030a0618150e060c1605070305030c011512030e060403020303030403090e01090b0310 72
    0x2505503441c0c10a001c40c2d0050140224003c6804020040d50f1948500410030305800c01441500003141c0540c0c0324811440e0441000fa0182c03038a03180a2100700001c403156007541e9a04904c04c4041021300c141503025451b102807801198042080203814010040540001071000341040100d035201c0007192910002c201d01480c001d0400e000c1541c554040a0291000b2162124079114945200c60315450030940b40041c00e800100020603203000f109040c441e480e0080090360517115921000300022043d1048584115080c091801c1400c01c0d0700d050080c045061085020041c141410303200d0881c004158250028181d111716a03840403a10200720021039400d074003602030700030703024004203002d03010000300b40d0b659818000304a000c0c4840d40403058048076010310403641d0320300317004040028020144070558440c018800c0e81441d03566030019146603c1114104e0010b03405110070000c0a50840d03a40d40904030210080c8421710004000c030342c0c1c4a8503401060143ea0f01c4802c500200709880d0320180c42e40c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 423602401 1250 423601151 423601159
    0x50603040f06090b07030b01020a08120c1201030809010210060605031303030605180406050606120c0f0403060c050a110d1704060905011b020708010c080a051905010906030615031a090c 81
    0x1a0841d00f0300201c5240e041764103002090801150544940c40801d40101850748542d1490500c4603039000c80c0d1504000400038151070108100214507080c0131001305008504c07402d103c0360341d98800f000090400b81e43d0100444014140f179000d01485030440103896100040d440c03000ca2a481900b404c80290149a105a4000d0860f0b10852591141609100c0c4120301400040c82070303494a805100c1280b19200180140802c0c0c0e5011548200ca654003c0091280442a1a0030710352aa1070301c904407088410054023080c800942e0400542d0400e15043c520b0300c100780034080c40c4d40704101c00b070a00300c07030701c84417041031445400000d081044581c0080071a9800c00001c11160f40c0030b1111150300019050302c1c201602c21560000703801141401500004079a9644440180c0c58040a400c040c0402031f01a0030380c0c1190340c20300303984042144540c900801140c2c00200780c035403031070920008680c1d100b43c60340200089040280080340040c60306284265240100d004a60740b003007400d60801c00407030788190384 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 423603651 1250 423602401 423602411
    0x51003051f060201060603050f15100e030318010206060420090315010902030106080114010f0302091804080409270f0f0516140402180915120601090c020a0804050603040f06 76
    0x1043c0e0550214096a0007030300c040029441d84901124071031400c545c280b201c14017110910049040000124030409114102000e684908100107411a00030201e02000422501c001c0c10466038100000c0e90020f2060303070104200800d010150004003a80d801c480c00c41100011440d000f034600f0007984507400b004413201c1885584650420019620130300c980d10001d40d8038400400c0b8458a5000d18955260585500c1d8040000311800c0d400b940100c00000e501084800d803000e50101207218031441203110b0440c070396556040000e400202c03900e034080302019030300c0030b5228002c840c102000c0e003100c035400408c1441031013103d140000c2d0040103188000c00303601840c0c40e00d03401691004111425140a00180c20140300c03500240400c03805a1a010001c5490709040c20529080c0f407100310342c0004803281d0300072104c010100819104500c00d14956400da000b00010440341002d4443d08245032040c0c8050702109a00707894413800c0340124020302e44691400004942000710094442c111540e01c11002e000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 423604901 1250 423603651 423603659
    0x1101050406050628050d080d020a0806030d030c08180a080f04050a0611030315120111131a030a0e0705120109021305242125051003051f 60
    0x201802d801d4074102c1c02074109118a4040502c0e0142604030710000c00c1c40d2420042c43e0904100001a2224043e240417400708800c401290b041d00080c001c0c0b95482d250403c0d03d0030a2000d05190046608400d01010701e040d6007804102c0e4420880c0c0d402400f000b0f0030600001e5003010b01410900b603040028040b040015000c220b0240c0d0304040d0080b60700c1200c66031002544e400054480304031894258a840e0400c2001480d004c0b069100710000c2d1501a103404200c1809078001ea0842d2103079105000c2641c0c000ca6000f5484050740361202c003801d05520741e8150758048941400c02d900003e0078a443c45a11b0360088210158200300080c014080100b1200c0c0e1203900706d0761a4020014840305038020440a0407103021424980a00c0b401501e560b6040b0802800b0070051513a51410b040345154011100e690700d000701c0040c00054070034070445001610510b40006490011906003482d441900b1501000c108031a030383d2403500080e201c040c3d003004101caa4503180f0b504e80b006518490110b18200005c8049 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 423606151 1250 423604901 423604913
    0x503090409050f0c0103020a080105060304050a02040e250302031c03020c0d17090d02100c180b09031506011b02011e180905040f12091d06040612020904110111010504 73
    0x400c54540c0f041901c3c110201c1c900110168032480081c0c202080780c0300c00405c01e50902000030f40c0c0c410302420540d080180140e001405032428014070001c1640b1103e95121003c0c89400710444103030041c112120518a1540860340b00c0c284041c6040e113143c08621801c107454007980450f004c0c51815000d40303800091542c4040c0401c2105c591803031506c05d10308001a5030b07038000134050018204d150000c1800d820788985520280c410b07024100104046243c00321400c1c184104074a028040d660042902e4409407818145403501c41500d0640e114241824451240d07049542e602203a961442c0d01d40d101a891f00050302d004007120302c080c41541c08401051181d03036101c3e07000364043c03100700119440c256568082d0400c0d188141d40180800e070a40c3e888000194000c0003901e0501c0540c00c1c280c5100380c0e41c60400c40c44080706840c80340d8448100341042024078191003800c0c00f070a190151280070384556004601440e070010f100505880081400754920303801540b0b801c020801c050024030051030103280103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 423607401 1250 423606151 423606163
    0x1008060a09063206010201020f0c061e04030f030504020a0e04031d012610080607090e010501050304150b0102030c0a03021014040206030a020a03060b040b120c0c120304050309040905 80
    0x1901e005180c107400402c210f501040d4030260380d8604600d01110340010703103101002e0700d0162225055650030000c2c1c18103036880e40f0241c44800100da01400051410146200c00762003140d060251100c0306008110000380c0218144128420f54a00020144d80720300c04aa242e088681020382c004802e0000c000826034484010b03c1c030b4000c143d8040300c9848450707005407402d0b008c2c00940c40c0c00d8200740c0307206969030209114043d030000040c180c000003155240c502d241031620603180c0c1c034000f4205a07001d0060714440d4030000d004207800e280151441c503140d00c0b42040d4041001d42140c1440e121032440c001cae82e200b0000d0f94a002318141c140c6402200a1601039130741c042d4000400c01c91802d000342a440c08803041c11152140d41c0180c0313011310359076810070b00100940c0700e483ca040905a80b007001050000c84400544060401c1c1000d076540c40354910042900850003d011100340442005820f000240c08a4011a800c11105420b41c0f00d84403442d0441c107500815074000d070840d00e0602c154080c4000002e03c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 423608651 1250 423607401 423607403
    0x10c0212010b01032403150207171e09011e0e0301061e050a03121101060803040308030f06030607050f070503040e0a27020306011a190801091a10081008060a09 70
    0x400c0081052200c17101c515000b0740e08040245106212040000c551401c402040c0300c2403224005103001c403a55610040d07440298229203d441c8045014030705c6102940070341c620001c110883d1403c9c120b03004002040044042014072070b0f16508107046401031301803d08216a000018024800d075500d40000c00d00b0f03a00e80b0303000c01c00c2800c00c0720310028032030500065510689400144003505208030107010740703408180c00f1001185660318940090740540c248068005184036005540d501d0401c01d1000641c0d243c0903001038403d030042014001819040401c07903900382c040031104e40d11000141011801c40c0503584c40100c07e010302e041004000072050b417082020241041c900e0310001c5a0303421003060002e00240094050740301d04018010220184071a100b5100111103151600580145c410210700c25034000c50046905040144000c0210703004103007980d02000c1c040590800c2b1040010580b0035020191821700030a4004240900164500100901a5501260740500b0051741d080c00500708400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 423609901 1250 423608651 423608657
    0x40201051614010c02160b0d021b0f060a0f050717190609021228020f1908060306070f021002030606070f1b0b03040f030e0f0a060e090711070b0702010c0212010b01 72
    0x25070450746c1c03911558250942d41380c02c03405410054100241070080d40400003110401c10300f0000c149a1460810491281c0c0200380041c100a0412500400c19204001408001e907401c10b410446400d6212a8910361040031407031100b12515203000d060910103252811200c40b505204000c607a11565400629848200414502c00c595510a8883c5d070100102c0c040b0f124417070702e2525940c0010b0241c01400d0880c6014807280d103480c050000e0380c006090a0f5020502082810b01001218607052041a40c4510a414509000102910029101c0043c1059a400b5560100108001c3e031606019140204d83c8000d40300440d9069090400a880610507003550b8102820000716041107058280c03400b5561102d2285032255145e6401d84410010301091a00b10300700e00403a801c565611101c00000300102e44600145466990910401e050010302c4503080c06484149080c00280c002543c000301d60802228944403800340c80122800d10b044030002c2e60150080d03410038a40e15043d8401120138a09807 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 423611151 1250 423609901 423609913
    0x6040209010609051302091f0e10022d0a0206130f060e0a09051308191b120c1110080a05091605040c0c0203012c01050f040201051614010c02 62
    0x800c1143c04075040c0c054541c2010364184000c00d031a00b20b801400c42180300500c03040481404070742c0001c40008802802c00001c1c85004d081c902c2e03007040d241d003d0000b90f1920140ca02c0000da000250083d0400c400314108000605013640140b020621414182a0780100074655500924041940b60005405803080a5208903800a0b806020382e1000f03d0408010348203c9a1510f002c4000000301030040c914000103c0c0980d0072030008002900401d403060100c07030134000000307404c00006c10021034202444c0f40b82e0303104020407022800301642c0301808011443c014000d100d031031500c01000300b041c40724190000032725034000da1620341042701a8461110700808011507075a00c1d180a940d4034a0703210390b170f4140c900020140110b080580010b9080070315400c0c139000600155001c6400c40d200841d840c40f02c011040040348d504241c02101e104103000c100020b10480c20000901200a40050402410300c003001030701510701801d45003512481078100b0310001c01b400513000500c0c041c003094505100180030320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 423612401 1250 423611151 423611159
    0x5090f0609160501080702211e03040209060d03050c010c0c1a280e07030804151706010c020f040513030f0c03050301090c030608030406020a0b010e190506120f0604020901 75
    0x30b08119440501a202c0c440c0e514010055a403a42e0103400c60045000b0403001c000c0300c0c90780c81200d00404080104081d5556150410320129a551082c8107103500e0080040c0f10140c5d80e04504560815400c03610412030245524050b034203841080304040c01c80d42002d0078204069000315103070704030b6801645000104003900904900092040780c090000c126030f030000d440c134008c0050b052031515100800014503040103554407850440d443e030048800150010b801c4c0020340b8900150316000710a418400c20080348004031181021000f4103c0d410440d0380c2494006540d21603255945100001d04100403500b021090b031000000041e209030085000c80929601d800e01c05c034a011076084c1c040e6210303070641c0d00348080d00700a81602c40c03511003007580b03038080441c0040007880104000c0005400a1404c01514508100380100507480000801000e108012a0081125604034211258000080c1b50380d40d075030015000140101444031070b0301c10405000c0b00880e0010720140101c0c021519110039a983d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 423613651 1250 423612401 423612403
    0xc100501050105030a0902040b0604030c080c060307020a08070f0f0f11030f030a180302190609090b0a0303030213090e0307030e0d031413081f0c110d1101060905090f0609 75
    0x307208040c0052010030016402800c2a800300001d68401840450000355410004509170419001035801c0c40e0448010840319a00704510010030300281d038498250300d48220701944502d40810043c0004800050300b40c1040f840803100c0c1c2d421944280c003240c81210500f000003000500203800c88041301009040d10740d514002440014107001140114980f0f200c0200483d0360701d00d40e000e044201f1451300c1001c4016503515104070030501a00a042424600e46100204010b155a0200580341d20308001d407030700364036082c2c0010252609402d0142e40c808004c0781404000701d407980704458440c6020905207080c1000b1004000d43c60095950100c42c9100c1c0c410020203c0c0107620007004a418001c1c0f1042c40c2010708060b28000b5411400504499030310010700e403d2510184907a00102509842221038900d203203d020b8080469281c18845840340781d0703031690741c0d10b1005103940c00d01c503500002020702c03082504224060188c401042c800350405031051551407031a80320508441c062a000202c0100c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 423614901 1250 423613651 423613661
    0xa17010e0115051e0909011b0905060d0203091c110c0f0a0314031c320a020906070f06060603110a0210270f020108011403060a2304080c10 61
    0x104101d0698503d18040c10000100b20307505a600201110280b0a010f40d900d440001e44510440000415680e080d207100390107041c1c034200d085042c04a19401405645c0b90882510142c5140242c0146e8a840725a64a0314218645842400096603084030755100341e403044100007520b00c018101c0d40848000c0003003141f0701c82030611464102c00f003c40204081135040b051040c090401c201500c1c600ba4545d038500200a1a1450000c0a15242c0c02c0041c54003040c5159500e040306640a0042103080305600ca902c1940043c1556040e581c0200b200001c5655000484040603845900116082d0051510744003601840c480c2c2c0700803e00d007a40b41410b038050781084620050003076014000c0400f43d44021401420500d031061400c40c1858507100e0035209001d01c10300c80a0003000da00229000e244001000010144c000e01510004091280e40c6a01c001442c0351304955491804180d4090711250291080d11020b0b10340c4007510844140418030064000a04c43e10440c0381c150744441c5058030301101900c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 423616151 1250 423614901 423614921
    0x180e07121a0705090607080408190201051b0c10030e0705060705060127020301080a1b08070b1b1204060e0303090f04090501140c1b0703030e010f0e0a17010e01 70
    0x5000c4941d079000390061080d4860340554942402e034203100202c0c020401d65041b2040c102c0301d641c400a41032104900c100003070091904a1600250b10205039070000740b41d405180b101903500244c45000164421017440301ca001ea0030b0140141d000d0041c2c144000f005802030000c040594019004041020305180044415080e000780003800513900e043c41400e4804900c1068101410021064400c45500c2e40021802400c0900003010307018101e0400104406039032549051140c100324042054004c04141c0360b08556145420a440c4e401c11b0395042c1c4110311460030b82486025624184111160b0400500195552941c0c1c4554001e15201896503a11824000c59800802061750a0745450035410910a040c400c1001044591a030086c108040400741c508801644010030000b0035502d080e04440076250450004220311446c41c0c501130442c1c01107490480c108552084226a4035000d001c44c0d080c50080900704000381e40d034900c3c54a90520b10f0401d11245542040d90f5850034a005015100d064 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 423617401 1250 423616151 423616163
    0x103020109290d0b0414040b0c07020f030d0207060813031407141002030601030b06070215090d2012030a0212160503180a06020714040b0a180e0712 65
    0x890501c4520940030288201102c1c5207112503418402040142e006800c0c1001d48000210703a0054500420041d01d500b4000380d0b02e0030300780600300400310740c2603980705030016030250040b5520707510783c00864002c024501e10260144180121418003942c0003c40208548003542c910f0030a07158410070101031114a1405000178031031500005180c1c0e040e000a2503150306c13860307150110448013084075040c1a0392000c2c00c06074550110422a072541c060203a50840e140466480c1e142902540c0000c01c03007616521040d007100340c08101004682c45213001011400c1d00039807031600f01703400a40800c40d00c00c00c25030362601801c10440202c8001d8000001e84034109115006404240302c81503511900380c1000360700071040389501d25000c0114101b84000d0940219a800450b1051101810711000e003011340d0044086511004c01008407460210302986002e500725001f0404413099800941c0c104000e422003080c402e030068200c1e5424405601c00754011000105482c841641c0741e00000074501000e42c05045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 423618651 1250 423617401 423617417
    0x2030a0509011419020708060901020a09090b0604030b0c03041a060d020d15020a09090c0801120b0a0605180603010b040513020607080c0109030c0303060b07020a05041505040c031401080601030201 86
    0x1d50341c0030301400f90107141c40c0300308241003840041100c040094405041405600038490074860807600b0710219502a0045000390301c2d002007008010092a00e40c4510244a0381d02c0c0f001ea215603840100302d50041d13030420088005400d04880060180d4020380d42290752106454080008100401402d03109880c01800240107150940900c2600080c5c030004440c51540421032a1094001d4800b0b0402070109903a148140c6080c100940201c0b40000041c8040c400700e14010005e4081c0550030000142e80500040c80645031860380c00d001d031100303030012036002801403900c0a65500d401243c07441010202d00070320400700020244400c640c806e6402101d50401078203000090b00301310000b041c02c40e20032038040307241901c3c1e075100741d08440c082d01040b00003075038580781d10041c194140a10400740c0003031180c0d9480c0c01283d50000741c680b0070912400c3e0249172545034101c0c8101441000c5001450701138010301c41c503e03520380020003d110380c0590b52154401e00001003200c20300061040d040ea50b040c1c4031b08407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 423619901 1250 423618651 423618667
    0x3150f060d020306030a060f09111203160f0209070f031503020109051e09040503071a090705040b0402070c09230c03070c0f0c06020615010305150907032403021002030a05 75
    0x203903000a1085405d88961400000040c105101d0700e4a034800035400095035100920f820701d0301d80e40b0710a0701c0348102c0501211042c400400b0044541ca60b03080b04551305c012003245031000c469070640902940c414000800c025201e42c1040d05a841040c83e42e40c1045140382c442c07244c54040d4058007000c0e00045180c0c0d02400716041c4000c0c0d920721802c0344031364000859452000a290803508640c201c0f4240c00100d1041c0401980845564050702c01442c01003171031500100070f550b501001d1044512803500c4440301030550311194129024a038110200e4410241c4900c808006000c0c00100c035a40c0c60341244210800c0d0401c007060070701450303049003001c0c0b55440741002100c0092301d403c815900008108510310004445c42420030041c0319503001f500d02da1402c0740101076115854580b0506150810040211079120880301c10088142122517407141c0c2c950401c110011724200e010b841d0611010a005845510381404400450788205e403c03460f500894201280c0701d0050020b100c0102e0028001d5203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 423621151 1250 423619901 423619927
    0x1a01140705070603230109090b091b01230a0c02120c0a0302130e0304031202010f050c03160908100b13110f090402070b0a020304020103050105060f070303270803150f06 74
    0x58a0407a003030365100c050490100c501c0101303000aa000500141d500d523244010002409061948055584068207585842143d4034480e8490b00410604101c50310340c00e5103014620085ca442d107009465211a01c035101c0301c0003c0e00100080358164450a850082c5040315071000544e4140c062001c0e1484280f90710316070a0165102080844010700394a0f42030740d0a201c00c04102803c010750140e020a1814941c510b030190845000c01d41c0128410b05005c00c000d030405190f81201e410030194060341d44070071101801154008415000500c143c00b9a0020410300100d5070071202d500d8104607039182c8500b07014003036030b02202c42c268800c032070884052266030102d10410006e0300d0346220141c005441e00c01079070390340032008000701c2d1009030065000c802c0c032040d540d240c840c03c2e01621080c0d49162800504c28400703445409024001410140c42e49144404052a81c800407080e03600c0280c2e840d044c411a1400f40380541003202e4108088144440280981c41c010802400b5840085d180e146481850520300d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 423622401 1250 423621151 423621161
    0x9070b16021203030f1e010e1501030e01050c0705070918020d050708010504081824070c03051204062712061d011a01110c09040212011a01140705070603 67
    0x50740c1c0100c8002c00800c6410040c00114441c903102e15280700c0e40e04d011b010708442500d0a942c003010b55001c0c0401800010039405020382c01034110f07a001510a081d010040f00a440d0186450f1003039400c040900c100202e500b0080c001c030b40d00c40c40655241c0d9131618040401c41ea600d07401c1c8146091464204c3d405401d0641c443d0040300d02803005d80d1401074a07644680c1c04d40d101590101da003681c0c0050381507038102e0325042000100380d0880b44024005080100c41e820300110710303d0b8598800d00040c030b0ac01009542c07203082e80150b610009582d203d42101c0811030f00d9030014400c1c68085400c91b410210030362134070702900a1104554090409030341c02d02d00c110740d482d048410122186135841400368461502c9200781c1c0042d003144000443c9241091003800480d081c0c0d6281d0a0500600600d0382c231072103a020820101344181510021001c0e0b55034000551400b1010070821030a5107411b0390021100007000035402144800e884580f21000c1024004100f0301c29104041d0803500984014010742e0301c81e80003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 423623651 1250 423622401 423622403
    0x30b0a0509130b011413180b0907051210140103080409090c08060a150807030206090d050109140312060109080634030605100504030210030f140106021509070b16 71
    0xc508951810741e0389410f0903e080c0c011024450102c42c020803545806819030310709400c1c190b01031014054803581d42140500d070300745c001e003180e0840000881c160170400c04100102001401036482c62022489503844e100036810b260344040c28019540f07403001c04414075504995104190514151801c480040200f400050441d114515104001422030040101502403200340b0000595010105502100b44030103a000c0c44440d00b0a100400161390b40d10240c517041c01c0700380c449042038650380c07600e2401805e460780c00410140d43d5002a80d080d85000010340201030084070f42180c5505c4000c0191405a42440b6520340340e070126000408801c0807040d0361101802d54100c05145c1c1d0600e80341105845d400001c0c0600007903440c1e4040040e0711301220002e00404a81c10131501c2c007400d603000706881750411001d28050584a00c1d4501503100f4030b030b1000c9404518102c4441103035850340d9009440d880208444015840341d00085440000d002c52080100c40d00b0303424052400324031148203408107880d858 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423624901 1250 423623651 423623671
    0xd050411100f03020a051908090f0c030a081b01060b03100b030402091503010b031c0e040902241303060207060e1c1107030f030f140a020c06030a021315030b01030b0a0509 75
    0x244e6100d5072147e12616149551f2941c0300c00e407034483e85a44ca04601c1000300745541d17008050b21050b40c2c0740458401c1c2c0b12a04821626a00c411031510340302690040440c401c040c0d0700e03001e0b001034604003110186001e0080b154a907440b15076030340305030045400242c0c0c0183d84600d154000c50005908010455114080500080343c0c1d15007440020f820320120040e403034001d80c6020512861150301c402a960242400c450030400c000701500480c042018030b00e0408010301c440411071081506500998020110300e20500e1940b0383c407840d01c1400380d00b00b4a0100c842c2400c0c100108400c00001c640400211040c0d081d00003448451102200d11400b20b85072a021801100004030116454046814655010380c4039040700b1103001c40000c082032494051503902c1482031018030207c1d40e002ca481195000304076409070b100d8940020050007841074141e207003105040070b400041c243c520f05d41c0780040c000301d6480402c03406640700f0065040d2400300e14550361040f0025428040c2d0b10b090f4aa25070040c03a461 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 423626151 1250 423624901 423624907
    0xe07140711030a030e030f0f06180f010e030403020a0630060b0f040311060f0403110627090109092414040609020906010f02060f09120d050411100f03020a05 69
    0x200202c0d0400e0440a0140c000400d030003403c25180c2020883c0161900c3c0300402000c941030142e10300c580318100a0030405803900c00b04d003c0d40000004012000b001400b4000804c1080c0c59105004d03542e1b80144000c90245c400a440014020300405a0102070005170b43d881348030705e090501c880e61401d9007010b4034107100d075100000b01d00c0000c40f102900010002c00d29181c0c1ea10f085043c070710000d41820104503c01c039820803a9100c02400310046c3c0703003102e91016814039500c211000141d081e0085041c0e0310b100c450641c004c0240109042c112030030440054882180c1d5036291000310040d181030940142031144092203804107060004119001c0f6a640c4100241e50080380c0541080c0480c181d6065400b41e440c0c074100c1056140c00c01c1929048038003400c1c0b841a8050070f000280d00c420700100554825881d000000b21040810b00c00c2c01d81320049460000da031103070190710040017040d00b40c5065a5048465069845038200b422240520100301e03210b07404400d8251000300c0295000703109a608009040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 423627401 1250 423626151 423626183
    0xc081f11093304030516050d0b090106180c090608091f0f0509060901050601081618050310023c16021c030e040b011d040908030903070c0e071407 64
    0x314450b821009501050380e603224a142495032030700a03c42d04000c00d6550004e01089030780d4903031001c50040d6034481200711150303030754103291401020030744c0c01040d020f0720a10340000110802e070b03c121480b524039184c20000742c0c1c541104076044601125596810350000708101110180c5070401c050808600d240414a142c01469034401d58005440c5c0020703d40c044810301c00020020f0156560028080c6040d04651400c3c4038031319104030b1250780c410280b110010400c01d1000c0300320f0f00f04001d888080d0031030b007c544a541500000758050710f0030800016840902192107460b580305900c0e40d009280181c0d0700d504c02030314841e01c242d100c0c0e070b6403031400c0d20541d15100050f15072030242285c4a4002d0020300c00d402030f45c1400b07008100b49480c094440e519050070685240e0b00565a00a0314040740705d40310800e1446404500248104203003d0f10030300011007080840100003004001c401e205481d00d40d0034954621441c0b5900000b683c2c400b010a681c0308900f984401c04c0da014024076130042e070036071110a0300c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 423628651 1250 423627401 423627469
    0x61f05030d090f27050a02091807020c03120f0903031303060b01030507080610350403020f0703082205130b041107030804060b01020a0c081f1109 64
    0x6007221002140d101c40c410003400114907500001031201c0250300540c6200fa46004507964025250b09880b039545101051148010fa4151142c03220060800c00d00c0b012060f51003183d83c0002c9403100b006105031300301c0e916141030104000c030b01c0b002e40100032030400031070020222941c0c11102c04030740c1612040c002845c04180f2140c4400045014040024000c40c44000050075164010070700c0d0240071040301848a42e032200240c2d040005054a4406d5041e401c258112a124050724040d0b00c0040d1041e20b00303010050094002d5014921a070200c60041d044000e1003601c0c0c0c001480042c0400324203001064582c0c55001c181700c1c000120348500485030391a4000202d80d552800c00b41507130981d03243c000c0ca06600701813164869242c2c104131914144003841c0e4008200f04c4004100810140e204c0d0040c076410b90080000c4400203030b200c1c0c69505001d4481c2409a91112003030304102c9400c41c525205003040e901031190141c000900f488952600c4010740900c0302070100414086a8443e5255000d104404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 423629901 1250 423628651 423628663
    0xa080406330303020c040203060f1003020d230604090201080406050c070f050303060405070e03120d15060503070f08131e05010c09031713061d06040303050a081503061f0503 76
    0x48040d400308007070741103040c001c0c41e05218842550040d44104288000341d580d000a001540d0b004803001417451281d44000c4002e4007403100000f8525050078400c0c000c0c005c4090614080e030224405d14201c0d0b0381c84600b04001d0783c4286d03201038003040c40c900104002c2449600410351003840208101c1c40c007a100c8c2e4402c40003041c0600f080c1d8480d0400b0040c8085807600e8010309402c25098940300b0401c0b154000002c0c0c4078860740c00760030764800b00020b18861428098103e54100c4002441c290911541c0c0c83e4040c080c2e03402100d5060004450403940c0d90114016002c0c603024148421024107025099074409001c0d05001c0500d1003ea03101c40c404e0800100c003402103400c0c191040c1c0c2c03a916594a98070b03104498144c441c8086a01190a004005a688c50441c0040440e9008c4c9070034140000b203076a00b84203034040c2d00000b68114400040120515411000a00f030070040c65484280d40d5580401200e040205038249a62541010000c0340c0700c03000b81404d0f0108100d240c02010301c9103039100d00080c9803030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 423631151 1250 423629901 423629981
    0x2009040b15090d1a18010b01080108030a0e031006090606141e09180411120a1101031d0a030e1f120c111507180e0103081305060d0e010b03030a080406 66
    0x14072054804488031100b130081c7d0142410a00742245154148400c135a01d0b800b400d04001c00b04101e40001c0301300d07550100320316a0390302c900800801c061511803040c07101610031409040040784820821040c201c00c0d03217048420782c81c0040404401076038009005002c9502034007171540d21214149c010091070404000207400385d841342700018006443c203014010106020840055541c00900311640030034030350902903040450920b030004000d1051600d001200c00340410025481c841d9018200030550000f85c9a5800c0b002128110341500300c0c00b50280c210b03030b04d80c00c2010000d0341c0c025000c1001c4450b504508680e0ba810f0410103104031a80f40e6061911011303c2c01a9040d108550900540c035820a0040048402c0ea4503403403003150410302c0c000a442c00610004000440c0050021610038079501e515016140c02002181d41c0c06201000b0070151050f0701c003504640d403a000819481d445c0000840325442010b8481059a070307901d8845000034081c0749480656200070800c40001ca0495601c0c180d000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 423632401 1250 423631151 423631171
    0xd0f060501020106080d2a150b1f0c1104110703051c1b050702041b020d020c060306030d1d0405010b03070305011a1209012009040b15090d1a 62
    0x52500c0300090035510103a01505040e0458030501e04042d41c8003200d04c0d200111a42038242c0444210940d02000c1d0001c40003402c5100c0c2060b4000d40e0180a8100d040144400c03501e0002041b18410030030258030003441601c0201d141014000c0004000c0c640700c944a6000420014000094044411041d40181d900702c0016100103200242c5500d0a08400301d081140e5008022154400c0a08a040d401a1203820180540031034000215902e0350001101110720b01c6100440400c8071002956403128403010f40050300a42c6a802413504140c001c0d01e00c100d00c02030040020170300704030080d01d04409440c4000c2020f03021014a40c51a201d40c01881d000380000b0928aa60340f0304030000400305c0c0d2040c0c20480e440c9134900500c1c480d00c1505420b1369030214500d0848150341d2510980580184800340c06103200c40d041740c03603030450b407403191000d4000b4001c1a80c0c180941100c94041221084801404001d000070510140e030080c1003213441030303031050b104c1c51032141500c140e0702c00c01283e6001200c044c1c5403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 423633651 1250 423632401 423632411
    0x301061a0a18050f061b0a030e13051603020a03020d0218090907030209040b1e1f0905060325080303010e041104090203060a0c171f080304180f020d0f 66
    0x46503000303082c2c000300b40c80707590480e05842c20300001420904600100500c07480c00452040c0506000f82d240030b01c01c4505900f10380c20040ca602d00a400c40e02c1014600d44074003049110703c0c11a0f003040c041c60348298004801c8290410420784243c000350407500c020400c09d64244030320007580185200402c0d4241c48001c541c042004e1486c204803034000014000c190340e420822007040103842e00e8140c03641040e444012072519036202082891040d00003007254092002000500c0080d101800c920340603e10710f0b065602c0c1140d00e4032410001d542d01955444d4160b40454809400c404050f0049001607540ba0700004880744d4034040741d403440d0000c1c0c100c220301c21081ea007800104400804140c440b0710007981c1c00e00a041107500000c0d02c1e000b00500f02c03041c49072560348d410240b0344180c0e08149001c1c0601ca28222904001c080300718118101c160840e03c0b9417980c6000310f54141e00000383ca089a00705810f000407944403804040140c4a00c5455051464003440914201d86181c041c16110400316200055 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 423634901 1250 423633651 423633667
    0x1b080715060f08060601081e0f0105031608070308091801090b030d0c12030e030f0a051312050307080a120e010b130501061719020a0807031406011d0301061a 69
    0x8480e9141d0000c80c2d040c60701a020008800042107a560185013401e00761502c0e075640ca03070303114a803e40d41c24442d03450f07040c402005903400030323101414140c50003034003140c83e01c200c144d000c8070302c035a100e0092042c164400d9104100107000e42c0c000385500300b005011008280c03461180d40080c1c60081cac220fa01525250003041038103040401000014010500e80006d4000154076544038100301d0560244c1090344030111a100c0250800841c0c0700c098034800c84998403881c880000340250000301014403003080d0601300141c0b40c5401915040c0b40c3d900000603529010342a61030807a1a0701040c0200240f1940540301c02440780644500400c1c01d46000010840f1800c10080204c1f184261888036201454480140720880d404040c801e25107030480000c0340340f601c44030f90900b825a425502c07116000d000040011000303502c225203c0c003902d42514180526071200d42e1401441c00200c3c0c02c03a000890203840482d148007010541c4000100280001603d60786a100002d00d4a280c0204080004400a0108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 423636151 1250 423634901 423634943
    0x90f07020f0102030c03061e1309020a080d0203120405192405070806040c030b03011109090705090102330702010203010611031c240f06121404031b0807 67
    0x3048001c9140001c61851801007860390319400080e181600034280195003d42d01c80c1c00361400c1d4000c00d00100001c228080c1000320300080c000055003213003c1c9281c00c0c00004d032114001131640b146c8055401450402440002e488689607000300141c3d0240b150075407500c10459890340c0601c00b0781c02000a000f00003400c0640c010003041100410110918100030401e0b05036220821541080041302c0c0491302c000c809000300d000e0900807980550551030007461101c04104c0600512000409480400065590440c2a04c150046d40e050b80e0240c3c00215200c000c1e41170b0140da10780003070036004a0319065220880541c6d00050b045038040d001d80c0d8004018404d05402030300c00e10118451500643c40c149000400d41c50001000910203107103511703169900051107502c14200004400740003c0040c0d9641d0b010048135409003403043c0f0300400c0300c6081c071100c0061a4050020681d182040d03445441e2a181c0d030868850050b850b0181d0342d000d180400b9000521000014800c03280140400150480000e442c1c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 423637401 1250 423636151 423636163
    0xd080d0212090303040c0b0c1216020301060501020d02121e0c0d1b0c090f0b09070207060f05030f1501030209060c070e0c0a09090c090f090f111305090a0209090f0702 73
    0x8581030ba071044c0200000102c4004407141654800d24150351565040c03199940340001d940005000c1c0800443c0101e07001100a12072816103000314024030040350f4880041e43c640d009001ca00700142c000c4001480c000c0d500e900101030140300700100c1c42c2504040e0f110014640c0201295548036044020a8060301d50301c480c000c0e80840345021070007240c001c1a0b541d0922002d0520902044a44480b8120a802900c0c0c0c410001844064201e070000c0c5007890000b502e0713602c00d00600d004030b03c00a89100c01c0900c640e0a076403280c1001c079050140c94440c0052141000341e05480607041580801080020f504e516010f0300c40034614074000c01482d81000b0320706103d244010801441e9110511281ca0039039481107901c4c1c00c46804c0200011f020025203c200c680d0101504a020301440b80000010002200da204030403559002001300305449005055010511500c00c10800c0315107082c609010b540342210381c543d0480c049010052134203a5201c00f0800d10b00e01150b00c00d10a00806041010013a010300070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 423638651 1250 423637401 423637411
    0xa02070b0a020a1710090c090e0a0612081602030d0512090309010e0904211e020c010509040c020703140a0b070305162604080c010c110a110d080d0212 66
    0x20035418010f010744014124610b000c1e8440420450344040360f50b0111010420014104020051007109180302c0081d18040c42c80c401c030103d2061f9140020407a108501c103d41c281c40c21800b01e013020b01038035140d0b610250800001560300030044d604031030043c0c0c4c2c100010186940d50761505512017040707881030918090000e19010403904100100c16442ea4481c03200501890200e4100b00e040c0c4450a1500380c51810001444a02400c80d04004807250410706c04005080d403030074684c1c0380701712010040fa00c03510b8400b1030030b0101714103100749182480d1680000501c0e8039607104490180f07a4a8640480e8811403841040c516046a91000e05000f00301703982c0740d4040c0c0301d4203060026043c06808040314038031550102c0d040200c18880d8000c1507601142e4000c100e160058864a64182418480310175030002c1083c480748c0d86400c4d840c1c520745002d84541c0040c448890045d150940c501c0d118094400c4410391100d174000c0d403c000d9100081c1442018004a101c0aa00180c949a660180740980704002e01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 423639901 1250 423638651 423638671
    0x1051306080723031f0b030405280213110d022802060f0c0703030603020d0b0108071e17030913021305010e210c1e030705091e19050a02070b 62
    0x6400da0241980100710383e0401701c4218104c170b00c24500c40e0300034030010030b50b0044860b04030300200340003c0c440001041407000510350a440114010856601c017054444403000350014808030313024003401d4455000225041c1c5101949281602580c1c605080341c0c0314850050100d030929450b580150b00c0c1c204107014027505400108140d003410a401c100342e06006201c0d043c20700000400c1010503110350014402143d01078540e0000055525203099024030900a5184500c503010740011030481241058464800e01110034002604012902e410b034000309024400c180320030044c03003183d0f403105030002d8581420280010b0f2030744424404484003d1241d80200d04205103450f40d82540c0d910700034030083d4007108001004030340740380441441c2403240e8950390b40c3e80300ca41901010741d81d294030f22000061180440980b103803070b5114010000b81d008103949801503003038202050244400550f020a0304585106001e00016035004080d000b91182100c84211103a004038590302000b500305d804030f800c500d5100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 423641151 1250 423639901 423639947
    0x703050105010206150f0405070e19060e010e0414011701200d0906060b0301080703060608030a0e090910050c0405040c090501050313030912081e120601050702010513060807 76
    0x355104005458210341180200000405e65120111000b41810241042c000c038540f00700040c002c80c4540055038002c4100400544020f015401c400040c0d40150310741c454490241c2e40111480c0d500804001d4103da80d5452100e109411850140d0081c80302d440e802c0c1c0c010701001c0b22942500c0c204503400c405d1610309028840c045024500780c2e0b890990488002030120079508140b8050001171b400298070400002c004641d5000104445096034040d0200341704440c1c0d03d81500d43e482c80342908000001d486c2c000102c20614003c07102070342044c040400c4500c200280c1c0c402004039081034401a1194100103000c0049040034000e803080c00c80103040500c032007460000040c0483c80020320850081100d45041010103009200c804003400b040c64010509117901e2030195070300e62000c41785454401c902e1000000e01c0921108a40c0503084446603414280c030755100644e965006054100c0c140301c0305000018800200030080001032086036244965030034501da0180110705406800000c1032222 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 423642401 1250 423641151 423641159
    0x3071e0e131a0112060c051b01020408190f080a0c05030a03050a0c110703060c0207080a14161805040f06050f0f0c04031a06061903060f1202090402040906020d0c1707030501 76
    0x400c1303040340c0494010801244084042c5011221485042c0810841c41103103910301400f0f440546c060310079034400100f211038940040341030001081c402080208074070b00c0c1900700350008201001400380c13041030b4101070419081542c5c5e6541507400155004000a03920800c0000011b8607006052519260303042001d00c8070400c41c9081e4442000707000203020b19403a06800c0560074800c02c2444001c00745101906c0e210b07901443c0c150303850660b02e41c07805401e2080d1810a104400c81d03004040031515040ca01c0c0f40049085503807600034020043c0190350202103480c2c800003061843c01050301c154000703100f001391883d250300e00c8031000704050700034000804d0901091000420254a00c80e140402c60030000701940c0e0900000c0c080d00c21195208a074030380d8590007628094054011009480a10080c20030f95500c40001d10010305c40058065881001d01003c6009424030350311820350705015001c05440d040440c00c40d070064174411140e20000070b40c441d40418000031034040c2d158220000f46003e00c895494 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 423643651 1250 423642401 423642419
    0x60b0f030a020f0f06040810050a0c021005090102090d0807060e010e030a0c080c071e091103130201031514130507020a0201080c040f2304060503071e0e131a01 70
    0xc0588024000c9071141e020f001c1681c1c1d07440042200c0c210040185503250f4503207205030348602400444907402820400424a861100e008501a6800560081075218850041c000103080043c0901103a950300704041c09440c0c032105030494103103000d100700d107903135103454900174045401280740c0002692400ca640d0b01d92440c00300032521000180d241c41801d581c01420074000c14030130714400d5138136441070000001d981c102c540c280769000b101452106460540d100021400e85a80305072440440e0010000a0003100c1251001d049960061600190303400715510407200c1054030360043d2040820002d074825561504004610a00d88800d07800d200f00c0c200b00401a5450b181100000d051190320030010780c0000c07000041e2001812a4905404183d80d1010880c20a00d450341d008012196464102c80d1f050070a4003604040b2040540140203003450041182034160b680ca9250b0410290b2400004030806d540030450f006480c14034903213400ca00f072460b006c0c2080c00c44107502501d40b0b944000410030906 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 423644901 1250 423643651 423643663
    0x50913020108011401020f0d110d0509060304060f0207060c030501050a0b040f0b0a1b06050610030c020c090601030e0f031b1b0409080c0a0c03030f111e010b1309060b0f03 75
    0x701c8200b4951141300315100603030400001c503084041c68420650450b02c400d0f4002c0308060120807510940d512000764690403951881103041e01508280108003190000710b0950089081d00030060380142800d6050341c074802a101034240210000761202e0060100d85414882c40b0000c100215195140600e05031000400341918070440b41c1c108030120f240210507002d0120403036680f4a050a1030030302e02d1180307170000040c8015190980900c005e4603407044041d01034450450115003980003031481100040030802640c50003040d45040680b107580c01d90518804204689072000c120024503240c030040310459104c0885407104208650016500c0b411040c03452075690110301c0305803400b00e95a0f407241006170080c462822a07500c81c0c400c0c8002502071084802c13001007a070f84030303681e803290081940700b04480e241c2d14055164025040942d004528880200c402c801e403c04c900008940c0030220000614000f01d662001481951240c80000c10040984603000040e034007203800e805074007401c00c0403aa8500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 423646151 1250 423644901 423644909
    0x10080a0609021c060203042003060a0e0f0d080603160f06030b06190e011e020744010e0106060e0609190b131406070308180d050405091302010801 64
    0x55480202006544074040034282c1c08840403d0243c082c0d0f401e140120007540110350648104180d1a241c1c00554a5100000741045006005140f941c4484844030020800f00e540c03e07000340314140c0150742c0c1c50010720044101c6841910342c21081d252071000d15003010584200191034031040c40e01403000e03107100440d003026101c083c5400541c0441070030202e0f030584112100380f2090380b03000442c030f107009901c44a40280b00000380e88105180b81140ca000c820400070440e01c0c005a00300c0c00080c008020100100000b031400381516850051001400010600d2210224244175801000d42c00264130240038980d150311507040200714003490b0860050143d00c91010340b920031580050700382d0a55071281c04c454000e4593300203404586503181003030f2649502043c0c0b0100c6245d803c50001072202030f600030501c1e4142024182078235100140d81d08541d00c0100410080000361070110615041000b040300c0c20b045040e0307413199561079003424100a140e141c020950940111180300040040c0d0380711288038111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 423647401 1250 423646151 423646163
    0x30a020919020705150a0c091503020d09061524050d0b0f120304090b150307080702070915090f1808090103020c0303040c091d0c010c020f03160e10080a 67
    0x1071842058080040d1003000805001032248010170300e1303a882c80101040c000d1080c4002044040c8204c03000707035890701c058492850140104816103c5940c0240c00400052405210000303105030140c1d242c43c01ca1340c04510101e49003030b10344018400313800201c00b016900d0003048044422403c88000c014a94441d004071950300d5510340013200440e48800c402c40101150051503003400c5840b02c0c2c4140da49130802d01c070f41402682003150b070400d9810643c0c1c0c44130f10038010080721072450361402c909482881c00a031001c03085219580d0002010010303032042d00841c200c05800d910710140740112070030a45104c000c00f0003040340340c59010510107440c0c2e041d440020368400801070310b401e124001039009005e0181c145070240000810002008008100030003600e4500c507040040301d500c1c0c10710349076110074403180c528039502c007820f403010641c054480d0000139880109210361625001000c641004d06086040001d220340140511080b2080c00e15668024a440d44d0122510700e803190803035440b04140030141c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 423648651 1250 423647401 423647431
    0x105130501140d02033105121b06130203060c0a1e11010e01050a060602011b080405070f09020a0f0806060906071439010503010e09010b100c11030a0209 67
    0x1c2c5140741c09507284495852000c5440f0b00d4a103490004c882042d044000503582d0132608041b042c0c8141c0880809107400c100208021546000d00131015403088641c0e9900340c100d5507105c00249410002580300d0a0900421445070078240305051401c0c4003e800c16040c0b039000d12581058950007020781d0101036081a1403c3c0c121030109054520002d110040315040d402e000e1003614040054000714003454440e0010004150303105400c0b400c84940740203049003964402c013040401486443d8184d0094040c00c150340c0346503501c942018114286911803c20b494010500f40b5a01d508002502c0c02480981003043d1686050000100c1d50b21031100c01600c98040403c10b03005110032408501c10b032280490485000048000401110034468007400c8030007019500c00c5055240606805401028180c454506503400e061800d51240d030020006c080a6603a800e14000369a80c1a03032241d0300e130a1581700e48900c00c205040a000d4056505401d6020340e020301c200c0c90060300c0300400c00c1e03032001e104c0380b604071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 423649901 1250 423648651 423648677
    0x16080a0c1217060411040509181f05130201081902130605030906090127030c05070b04050a06080906071803053a020a02061e04031209050105130501 65
    0x15620445010240a11444495100c4025004225080c000c164040381c1d0355255100700820090b21032601c217040080401b40f10030801e41c01c3c24407190b60060308000c0260440084440514504420303c1c0782004181549078820711010f10510409800002164030118480c3c042d1300040d0021074090100887d0341c060003884803590391154190f956100d00c20500b003684558544004100e41c20a646e601031038050080030070000e020522400000580c0d0410180c0109005400405551840b20065081c808174004402c009101407000002520130100f00e15151070910041c456220785541000c33050210364414003c0d62140054010703800b0002741791041000130307588500d4074030401691000700681b02d03030f035801d01c11130011440d41c0060f4016404541a00054070b07034940c401045100c020340268004031111009402e105000b080060b442e01c4014040381c0300348800c8011648a5031043d298404c07a1009003654070ba01014807c0103040034a4024100b011110400081c0b05403413040d9410b000101917410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 423651151 1250 423649901 423649907
    0x150e09251203183f1e020f0d0506040206030403031d0a1101030603110d08070503042c0c07020103200a120b0405010515090d080c0a12051c021b1e1216080a 68
    0x190036584440110004610000c0c0305413074034445c0c18203c2c8107075a2440168210304246440d0010940c10100601e0b17141c03155024002c55903c0540180c04041d01c402c1a800807072011070b800a0340c004140001d02c2d8401c01e80c20b20b51400500501c442d0704250034a0020404141d0800c1251001142261600241001031800802da40302d0050024000c0c007020800040341001c0500d0810103009440140d503000300300e0b05000741610f50841c1c84114091045c0101c0300594481d0f8070610740c1440d1600b1044089041414100c4103403c462a028001900500c07006030f0701ca4140120580c00d1390a4809007c0c80d4100700c0080c040280e1500f02100c01b0002182d07251b003564443c10b501d0b04294010040e50b0352118008605519121b11030000e403120490010b6000751184108112001e400d2000c4100c150700118006600280d072280111202217000d03880c100c08580f0090041610300c00c94224064210808902000e0500c0c1002c1c0c01044000c030700b40040c4a05201c4610102c0f203c59005c180c0c40e40d030b01d0107405c040d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 423652401 1250 423651151 423651269
    0x9040b030c0a080d09090b150a17150112060e0103080703270e180c01030e12031006140310050d0303140a150e0925120318 54
    0x2182d80410010000100007401043d40030701070a981d034440700750640303c00251055079007880c00290440703494813030004034801d05409042080311030f2034040c124502045030311107260419504245544280400d030b00040d83c01085a4810b00c000d00741c280485490b00094a0441c1014030000d01080d50004030700c01018820025a01002d500e1070003400c40d40e0304080444d05141450150000e00104880814054032480162214041104005000e0410070311300440c081d09064060180364407a400d6081d8424804001842c031980c00003088041c1c1c1807800c040280150032440254540d05010020302c00c0c1802c0388a162429140f00750782c64022034400340303011402400309040c07a094101150050110100883c0c01000c060116003640c2c07810103483c2c01807640d001e1000d55141d042a1b0207a01c4400c0b480114225890340c1d850800d401e1040d03e07039506450001082d0302e980480020707008528402c1e495226908020160140da550006840d05121200c4007034040301d04003498007501450551508141c131110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 423653651 1250 423652401 423652423
    0xd08090f0304080c0103111812030c071805060d0c060c1103010c031a0307050d060c020a0503070f0204051b1b210309070512100209130e1c02010c0509040b03 69
    0x201da5449544104242e02c840c0c1200c0b0a40c002424541e0070501d00c4410425200440f00c80700c0ba0304d4030841c4680c00c101c000c20fa48800a019400f007070010502c1d0310070070310020004103501ea10700b034805200d42022408071031004003501d11402d911030360000400c6010003c00d050310b90702c0c10010211809030414501c820000c0000daa815800e0868070407030503a1580008400c9040d46003441100d10562041540b185251301400342c100c1151402e101c08514103801444070401c403801607501284080d140d00b0700b5035010320015101a84515803980c00c41c1098490280e1200b9200711022140c080300f400e036149482a0341c604820090b403214610500c40060040400200e09000c8641407040070101c610a40c2d0000c40d49444280108400041e0f5420702400c10344070032100d10040c000c001e800244440080d041a4400c0e6001040313064000b0006145200749031001140700c0c01044007000c20302c2e92141818100910f030381164100421420b45503004415903042c11800c442c045806002540464548141e0f110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 423654901 1250 423653651 423653653
    0x60e010915110d0615140c0316080403050601060503040b01080109020d03050918191401060509100302040f0b0d1d07050f0d020310020c0d0203040f060302090409150b03010c08090d08090f 82
    0x1c40016135500c807040406142c000d907107501541000d6003500070024000c4080050894000700810310002e481001416020380c2b0800300720f0306140e129119286420000d0f00441c0204200200344428401094040c034018140c0400034032080c403a650108040000303866000781444004500c2655564800c415040407114854000100e85025400f840322043e03c004031001d44d501d070400000410160070f5045042e2491601d84501d040c1e00702040c00007611210035800308041d800c0c040031031a420400c00140052034540289034868000040000c01c60350030921072221b04c0c0202c1c41420611901041101c11141c04507091002c180a19010a003964803a640c0250b060180e111480c0306407013290b0240102c2100142241e01d01c5400b03110590340d0348514000d10240300c0302c0940811855203c0c4d0001c0c02e0581010f040800d0801d040c0d6207030701d10781c4040b41c518280c0741d4540d800354505080c01d2060440110182c074083c100b604040140076280d0400364070300c40402c4451000181d02c0e2208204102c6030000840c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 423656151 1250 423654901 423654911
    0x6080414100506040c0e061615060803120601020a02090f0a060e040c0e01060c0f150e030d06030b07030b0603010b1605160806011d060f0307150804060e010915110d 72
    0xc0d5007500600c0c044a04602c20743c9801144203e03e4426035212494200151a083c5007070310b01801000d0281d040801110001003404145e100c0c4511405040001d1240e00019034454103599070055803860300800580c115400b050f03810b030141c1d0310b100741a9008040c04c1e450740015190301780e803a0301038101f43d007220100703003502800d00c42044204100d840c110b49044010b4143d69032100340464100368403902c06040d072101e201c01c0c0e9010602d4030801c0410000c90700800609103801d041041c1c21500451a42031010b45e40c1c0d40100180001c020030103604c0440c0f8901040358201c19400101940418020500c000c4400b02c4c0d07002d101e5121400301405550400111501d1610796419075440110600a90319240903039000085d080a0b4414040d050084803425800704ac2d4900d02848004c60511901650502c580f400009e00d08509041d08100403203190799220240ca400e040c04000e407050010b181c041e9a240c0755030840800c20000e0341d1489130041e80004116001c1341e0702c0b42d81207801a4600244040d20344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 423657401 1250 423656151 423656173
    0x190c09020403081803010506031c03090c030b180c060a1803060216030207120f03030902011205070e0102071401090501051b01062c0f0c0d1509090c090c0906080414 72
    0x3c08058103401d5111030441c10800c00c044145400d950054030611341550001081e0001c488411b004e1140100c0c00d440c000800710003980b2000040d03603840c1e1090318622800c03c1804190110301c1244000c00b0040001070843e00081d42c0071880904c2668504020810110f412046420001050100840c3c21010540d25801d403d050308013140720502c01100548220f08001031001d504540c542006900000c20341101c0741103032030a0f00035080f504022030401c03151744200821409184242400303042e880d0795242c0c403040420300280c0741c2802038000d00010f07091801100c0d001da074402c44c03641c141c6000386440c5440c0c030300c0c070a0b0b201e000c40c501004140e01942412004107102104803820031040031000003044103088034030708402400900741c40300c0150804500020354012420301c000e200413103620030006207071603c5d05140008101140c0007110500c3d00c401c8104284038415684901820140700100407080c0110409000d000a41c425101800b00000004090040c2c1003040c11020058005480d118440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 423658651 1250 423657401 423657413
    0x50f091c140307181e0b0306060c060a050115020609060c1c0603050a031b1205030c090a0906051009060206070c0f082b02070206070209130f0506040b010b0c190c09020403 75
    0xc00c4207518132401404000154248100e01c801c24407880b180c0f4165480fa08020070384000c0c0d4001000c0c0c9810620401011449540400c43c0c284034010010f80010254108580020010002da561004650294041c803595400201d00c0c00d80018118a010340d40b050031402d80c004503480e03206114052460b090000003071100204d0846d900b248a03035a46c00310402e4504041444c0c990102c4007800c001072030614224154000c00045130420031030402582071803403801c00510503501d290458a491601c0d150100664105608070701c1c0c950103142002c58205d803c0400096a5040040c454010441c14840800a10450325441d1a920b40c0045199640d420a800803002d11030404000a08100d00f60100300e000302e102c4d10079110003540c010081d42c81c02c54030340c00300305c000704015010202200204d51990001b841102000300c0c0d851082010b40ba0078030b8541042006901d059129012035501002100748099000c40d20607e0b00c13031682d0001e0b03228001c600302030b024455140c108022640c400a0f003c414000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 423659901 1250 423658651 423658667
    0xf06090506070f0c0b0c09130b151c09020d02040903020c01090609050102071e0e01060f08090601050d080313080406020714040903020604240c030f050f091c140307 72
    0x4000c10855100740c8810104031030080d00320a442d03002821403024000000d20950f405908920500b144506203400500001c9900d03102c0000d004000b503450f0103c00380c90900628011901444408040c2403030070300b1800504030780c001011020800c0da91501c4100719070303550030300001c80d6401401c1080107009074035001e0f542d5108030502c1400f2403206100080c0941c0b04440c2d030400d641043e8050130324640b40c00b044060340d52410843e01084040c40001040381181c5041250080c0b815a60710403001d08442d4000e8180800034002c12071541145005210300d8462074502921903600011003a5030b0b0303030b41d14884403255840c03050003820503e0010300081e01c6640001c910040e18031211144250050321400c001c21100465401005a0810400900484c5500c0e88a01c148800742000152106080000104980b48903c68a02080e1340d103c0b03d0030394040900c141030b440712050924010b075003411009651364800c025a030720442041c811809091a200c0c40e130f02c65002d0507038540907459041640c0c0290840b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 423661151 1250 423659901 423659903
    0x70306091503021e0d0503160201080c0c030403080703053105041505190803070803101211040b030c0405100510090e070e01030b091e010906050906100c0f0609 70
    0x541402030341d00700007100340601c0301200e500810040c240d6143c0c22811411058003030805600c107101d04060340125106000524030140c41c60394410000502c1c0c40050300909003d4211811044217001d00150a1000000c5406a90700500c02649882407441c0480745072203641c075080d022495a0080380e0841c142e40c2075030764032038124900341c0c07803001e407214248003c8509032000c65a09a4a082041116041110004c01065851012610141d032154041495a407041d00c048941850000410202050302102c8201402d02240d0312280d0428a4513035954007018522110704c03a0390b0340c40d10000a913a00300440380e00c03904090701c01e0001c1d24101c00d1002001859201d1240101469412098024411140c80081c1c400c1406c1c0d1200f591124241100d094800c90f14150505a480704407a10584d10214004d2040000014003600c20301d0070b5030b0007460404117900c000141c0d0700b810300a00c801d594030305040b90300c1042902d04030520303c0301c003000b110000080c41001d00401e40c8400170f0024840c0d203802c120300309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 423662401 1250 423661151 423661169
    0xf060501090e0f15060117041202010c050711040f0e010608060105270f0a061d040201030f0507020d0305090102040e0c0a030506010c0209160905060a050d0e06042105040806070306 79
    0x801000400d80352a2815a480e9150300f18415410300192099503d9400450614001441f031170710080440b00504280e800303075802200d502d00310303161650900400030191200d00c0c0c52030a0043c69034506a001030b82d5038100344074075201c1006420244c8250700c11554800c50780700900003280d50700070341903d8081c01e0060500900e4001440100350700d030094001510740c2000b6040c80a81d81d2060320500e40c00700030302620030395a12070310700150000e007080c400b03040045490840c0010341000e2001500302d42140b1400d00d601410801040140c54000c99001da040b000d5080104127070303407400380041c0248656000000450b10710018008610705c1c1c5c901a117030202d410b0702c0400040e11003000558103030300f000200a41c01200940050002c420941074021040210b0400c180b4179600ca0001440300e800140d410740019001003207084200d24240103520104003500302503d183c2c1456251407040541340f4160742070340d001c0c012034500c406100b1421600200302036030546500e0f0605500c000c000c1c000703c1c400d03903540d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 423663651 1250 423662401 423662411
    0xc16330501240201020f120f07080421051e04030209150a06031e050108030d1a060d0216080409090c06020613110d02030303190c0c080f03060d0f06050109 68
    0x40084140325450680302100c00326006070303018048031440200c40000d21411035400b4060741c9004d2489801030003003074603e8425844540b52020582c00701c544010103800030002d010081c032011560000e08503d41500040b1b0f018680d080501e42580c084c41600001140c505484604002c0e010718940540706a902c221022440d0f9141c2c8240d0b0050403403a00e13402907215070a441c0130013015020390300c00d60031041a13240c1c85400403403811101c002c640b826403240c1d030190000034440c1030000e0644078800e420115400303040615002d02000ca5428060800d40440c059800101810002d50202c110032405510140895446841d158102c01600c600c41d411070750511154004110a80003148581c4903810790461416601d001d0307100c18040700442400745410544608098000d070700e040c03000714070620405120708801c4402981900032610038100c1c080402c000101c24038002041c000485a0052a001200d0346075100d10000900c580c034116030040c00016030b41502400c020306600000d040310400203007004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 423664901 1250 423663651 423663743
    0x7120c0e0a0f06020f0a0308072f21070c030209060109030c120204150b0d050402040b2709010c05030a1505041a040f020301060e21030c1e0705090c16 66
    0xd40d846d144000140803904070710000708001d2040c60403202d420300e0001010208042803600850b5501e00081c5054140c20403603440042c0b50011384005d4104000d04001842c0051079160074041510301d0100a10071420840030808a070710804040c8090740d0088071012409075248130f090001c44a04404a0046041641c45140104060810f50840701c041d042d40d8580022040404d00418000f4412030307001b903032061520042d841d01380c1c0001400c1030140c4a100c0c116881c1070118610356000b0035540740c0782e0500c9412080d0550107026682c11404d4020b0104810840b5062030341c04c100c841d081240c02c180303424020070311a20420f0306d40240d0001035034100080111849100142e00c800d02490012900c465501174083c208180011000d42c030780b41000308203120145201d0b045502a032040181f552200c00c0c502c0c801208440340039507081c00600200107a6282601044458000070b2807005481404981100c2c100e5040c800021129403000700740c502c4850141c13a0500f058441740121190401c080b201d20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 423666151 1250 423664901 423664903
    0xd020c071e0b0313060603050714040f150320041109041a0603062209030801030203070803090108060907020c030703140705061c02070f0f06050a0e0607120c0e0a0f06020f 75
    0x100b540c00c1c03281c2c1c03589140e03220380c80c030910708880c4101241e100d66140c0e80040800c00601c05c1c0f0020303102e62001c0c00c1522100d18200000d4510502c65200e411f89080d840340f5491080a001074102d9500c04150140c0103655601c0070484020740d0541a001414901035040c540030042c01081c82d048121820004050604c101606c44564804c5143e0000740c2000825110b00e04a124040c80e03a402c82c00f1060f00d0030b032041401040d00d04100e001c5001c03480000045c0118a0144100c1014018000086090000d2500000c1882c0e0001d48000c1c010b400e020b001c1021f082c0700740840c0b8001d04003c0d007120091941c030b1074259100b00507424050074a0190900100d0f55103412011500b802201c1c44104011007030131402c83c40298000c0c00100da003148840300e004000f6510800c0c0540c20350140c40c0000d1f640c540181048191000000340c01250f411083c10445100e07000b584a61854451850018070040b007180107540490001c100305034040800307880010440101c6601c03c0903204036a0907588502010b029503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 423667401 1250 423666151 423666209
    0x40212030a0e1512043203130b27040b03030a0c020a06091208030c120a02040305060f0f1504020f0c06041223130306060945080d020c07 60
    0x3041c006481c850120303011a8041004000c048040040c1c4c08491b03140a08003d410404d10605641940000c5500c21741480c0001d0700d84001c1c01e0140c10350307203800d040c040d0700806000030788610500c0114005600f138641c0c441e98882414800d0140c1180d40d51228040064000060b056040740b01d2907454201049051003488214112608a84442200314969072500032580006256900c01d40003400340e103c0b1080c030f40d403420f4001c001070800166901c0c21400c1490820714002c0000d19010541000d001280a041440c01d50040004c83d03082c042c0340c2000f00160191080c001800c0d48e501c0c01007404241c0450104645005912840c0842d01031002400c1c2668949080b06045640040c0600030303424903030000c0020009510201d10100c003c645039600c0c1802c80d8441d400c9043d02c1a5620603045204060040c4c40700c1c17100014100f0f440c0d20700c040d4500c80a50005124a00400401d0660142005146c2c41500c2900c08001003d40d105d0480002195542c2d5491048000e40015596400124040705546c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 423668651 1250 423667401 423667417
    0x515060a0509061b150406060b090109031401110315040f0e1504050f0a030f02010b0307050a17030f0309010b0a1401020c010305041a01180b060c03040608040212030a0e15 75
    0x200c07410b02801208100c1e80b500030b07034400040c034540b50411041610082c041041c3e5060201e48600090800d410300b00e00b19003c4d82c0061200c0c1008021680e9282c0e04860390308110399204007e03594179070a46c4407650140c1610800c0780604030003c82400307034030919140c2e010b000301401e580c204009200d22079054243c50b40d010728400c40b5007003011034100e116201c50000c0da009014004681491400d001f0f40c5103048803003801680000c070425000070120382d0a00502c2c45103082100180b9030f16003131100240000034984030f091f562010542c84403204802c14004d44000901c90300b0f8641e00c0740b80142d40503003e86800d68103c0d209110180340440c0401101800c0a1400010703401070003003290044c0190000c250260080d1458603103040e001c40d58550100c0a00d000e4154014404440a402580708041c2d1b204404e015108070424400c29a03401c5002007542c04a0b9201e103060748c0c2540b624000b044501403840850400f501000400c5d109098100000e80d010f42c505503900b01d50346001305011040d50140d052 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 423669901 1250 423668651 423668657
    0x11206050d030806030f10050a3c062301020d08010b040506130504020a021606020a0218060f100c03090b040e070f11030c0c1302030415020a120f0515060a 68
    0x2a006000c03c0c030950f0101e911442c060100c5000c510b02c0c10150f45002e1028000d101d40d40d07207641c200509204580203d07454951074a440c00c10050000703030740ca03440302e140c06482817100c0b00028a0400440180c0c000d003009054108015903650f00049610f000b20070301d800301030f002d482880c0b100c060f135030301c1601e0240c100c40c10300030910f0a09c5d0400080003007a41c0641c009824801c0d80c1c020104140d1b450b880103110034080303034001b04040d4100415481034401d00d54059819500406401c4000d615840c0e09040101000900d10001e503031b036400000c0c4040866a5a181c00c0032000700358516680d0004038481c00e00f8025181c030b4410664a041200d0148280c3c0a2084010380781000f280406019001c8100105650b0901c0022440c040c500c943c036540100c0ca0b0f68083d0340c04400b040c0400d080c080324171408500522015460752038191140e0001e10305069038081c0c1641e0028030031000c00d100e84070281000e4440e2038144150504452000050301c419a101c00c0314180b0703c0309074299441d01c0c100312802040c0c13540b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 423671151 1250 423669901 423669919
    0x30c0406050f0405060a030509010c0e030c0d1b0602030403050c0301020f0403080c071701021206060f1e070615050f030d08070c0c0906030b1605070203060f06010c1208010501120605 80
    0x25400320740341d030400544452040b609010100d810b0303540d000a841d400076180d60018407890980c01c09829100141e10302e03410310074803003503114040e01c000c102c0c12101d06064615012801b010300d0020000c09020000c5008144d0480011504039030110080048900560803110b80c035040f8006c1500305c0c41071040e15180c01808000c02c000003078003500a000c40880d00c9c8103440b035541e920016501009600d00c1141c020780d41c0060710100380704000550603001a01511100d0400d08122004461441100390307022444c6d041e0014070300780820071807c641c10650f2021040c00110000403155a501c420341c051113210302c1c0340550f480c1081c140003030f54803640c20145c0e50300c00c03040d190803d0985084420800a5070741410a03940440c403165070780588401148907500c64681e500c1c00444400d085c0c018a0122010000204040405070364002034460f002000300340800c01d66141c820059030f8065010350024503a00d01842d10160864010084034100ca070284c079641061080200c510044540c00c0c080d40398408440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 423672401 1250 423671151 423671159
    0x6010807060e040504080c01090c1701020403150902060417150906100608150409050c090705070503072d06140105030102121302010201290f09090307150b0a1d0c030c04 74
    0x244e00030341d07000303405842040e00d00300c5030702481c5081d1101c000090b0342280200c0030400200c110502d500d10074600030f10085083c182580e03142e205142c041c04c94a6411912840c0b0881990f035280708680003003140c2403079400030200714942561940e640080450b0040c2034503001885020b00801c049d0300c26807105400e111400d0925100303558050b00507140b07007200552007400c0895504c852160705843c5001d02c0042c8090340140041103c1410300818080410509020400000c0c4c000070031b90726425808420706294110450074000d400101c0f144000088480b2400701e001c2c050b03254001c500c092008a14050a41e0300c2d00245400d0344104602100912680d00c0013a0700c0000d1414946038452051001007100c00b101c90700e0382c110b02d4038021411701100380d80304803031070920308002d1360521814180d803000b455141c10f02440d92039008a440140c482920a480c19013580d00903400403141f00c100410350240746403190100924820211403540c0020202c0d000709424081c0903003038900c10707011102007603d09414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 423673651 1250 423672401 423672409
    0x309080307030c02120a082707120201021002210c09100c02060c0307030f0f030603030f0c022e1d03071a0408010513031b0201121805010501140306010807060e 70
    0x203c03681c41d60441c001d082e40a007013004030100a09480c00259501203960802d01a002c102c00c580340d50a000320003152200c48030b440c1c0045100011500c1150149000002900060713040890b4808000343c0540b002070726903408030003c180200c40388030941e0344050a64604014080c1c80c421494440d50010310340866001e094800c15810f020303076201408080c1400c52101086113140c005035421404122508624031180c1c1c0d010245104118191500388a05443d548002e803c11340d0121511040000d41c0741190700b50b48030500c2e856119402080c0040d0ae03500003450000d4403281c8280960001014060403124061203041c403070840700002409031030403902d00494095030101005000030000001c1c0000500a0310070711405201c3e92208500d00701c880d80b45c0c6001003038041541041d180c8000c03100d820f000941d0f0300070a0340c0390300b40c407482c9c001401720107030403483c58405111803000303007558200380010079240c803200d103182c044400580848a1301d0342c82c1e140254417404203000d0003000610795440d0114900d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 423674901 1250 423673651 423673661
    0x3051b0108160e1003060303080f25031b0509030c0613051014030406050f090a1205090a031e11031b19120c060f18050f0301061e0e010501030908030703 67
    0x1c0b1401d04001410048020404900308070500030b01181d610703a4100b05050f0000d0780c05e030f44840b440f40c2000e450319020448420240f00c1404592145400008a540c054025884003c41c10940003480146c0f2504440082140e84950800d1340079006882000d101400e00c541541d901103420380c02042c1c014102818004c002c12402c0e1420104440c82e402121803426003030055001e1806201c1c0441d0500d03007113004040d1418040c0001100b42c2c00804400003240000307003010507a4074185407182d901d2141d00006052400180c00280c102040380384600507083c5400c40b0851518401c001510381300555004054036510844004e43d404810b841c0065040d103000c5039808000020032040c0005143c0311b94100c12903508a41080b42c00781e03603404052007800c2d005190400400360038a0903851620403010100c1e0340b580180319080c000c01b054484070000741d80a40000c8003070312644c042c028100e5051400d07050401c0703084c400c140b1a681c201c000403d25520900403580b00f6900402d40c1455500c511030110001c3c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 423676151 1250 423674901 423674941
    0x120c020603180714010203190e09040506311b0815011403030703020304060507061e0e0c03060114120a140304171212151002010b0102060a140103080a090506040f03051b0108 76
    0x3e44271402c0c10f42ea02c080240307002ea4081d0008010601d0700c4039201420300158004101c502a4050b0020310407039001c030004180c1503100103c0011400000c0041658200340e03008101d0a00501c80c90608008190781c1c01c6048452000307000c0304c5422040141a2a40326184016005800030403040c8038042c0114000d1403054400e280010b011003408080c0c045440344c10729013410b40741e1698a2030381651020040441c103140120041c180b9035140040c4103080d00f092040d0903015803002d10b2000d00c010b40c2804440e11841d000034604035600200e0b0501500c95109001340e45008554550507403000034000f9980001c9c1440c1d05040345007101d481b072023095540c0020300d41054001c1c01c249180c0307540c580d001c1c1c3c40c5079591260004100121204006810203000410400ca40c80c5403020402c0040601e00d82241126001200755983e00103550044456101c5034108580100d0005800510442d45124407002c403800f074800e84090340940d03c40040d160825011450002c1c0c60324000ca842104000800344c224 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 423677401 1250 423676151 423676157
    0x50d0803091f0204052121070b0a05060901320310060b0405150f070215040e040305040e180601031e0b0f100e07020307120c02060318071401020319 65
    0x149040321240c80c07078412500c0c0c0140c06540228017001a400d1124903032400350700301511b048400250302a4159901d00d0500c2201455080e19800300401d0f02c10001c0362041504410350324010700d004020342018003000d80c3d0260060050074000610099408010766000943d404100e581d42820040c811440c0340840040f07625008016603591448501d20070f1500078a600a2f909803168030381006c0040588a07103030340c6c80301c0c400c00b0084d0a44030050300d001c65020a41c12103580301541c103620721941040c080e40d0007000c0d94210102c1400305141e080710240c021254a800070001c5c0e0b5890300d0150320400301303103903070b4007800e600c801b00500000300f40100880303084007985102d21a02c4600d45441020710402d440035414920b003c014047c0c84082c810b242006812042d0b03000c27046040100c4000d59a105064016103402c2c0654610310510748100320b0000301c2900140120348a040a5400c200c4080c3c00052003034061083c88000964000c41226009407079405801030b50400d460000b52117504900042100c2c20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 423678651 1250 423677401 423677413
    0x1d0105090d03090810020c100507171305060a0218010c0501110f130b0a09060302031b0403030f02011b0f0810260d08130f02010207090e03090f0a050d080309 69
    0x580d00c900341190110740c001d40e80c12508601d13015546060600644030102194010010780c011440000384c036071242c0714008000901d17a0740d901d0084440005840e01c80484070348680510014840041e1607074005806801520500e4482e03030700000c101c1c4141403050054070032001c00d0604542c0100b0f030880388103003d80000708403c011600000d901e94003200b0a0706880002080320041000912003100240c2082c84546251080035100603000048038855007003010380000010303400c2c402d910a83c441040d24900714940b142d440f03103409009003031405a82c000640c684130005003403028100e04201d0001d203540b01c034251116200d0041b9039401004201c00051680200005506410000c100e85509520200c03010070340c0364600401c0c00c4c03c4903042c01c641005051414400c000f014030781c15a01d643c0d8020602c200b0f40501e407005070300b042c91641c003030a0000d1400040840c00c460200042251030000c41e420100710741000100700d0921414011a41c03c84850000e031400242d13200003c503004004181200c0f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 423679901 1250 423678651 423678667
    0x3010e0408071112010e0c0316170a021507060e28021908070e010e0f07030903020c0a0605030a0f09050607030c020f03031320030c010e010302070b011205060f071d0105 74
    0xf46804044c2c88204969980c1441c030200388001c0c807a460110104801130400c0f100989090010982a8080c0f4058440c03805421007040608012000085501420150f034940c000d856980d901e0700005408d0b1500d41c02c020840b0415580890290404460b00c0218402c8401c000703000140d401d40c0b124202c0c0c21205804400c02c0d01c40e02611a0340c01817204034020080c050805081403000c4406a101c0c1282d000c01f04148102c221611464a40c400f04c07518000034122898281285054003000603260000080368000c24040c1e48100110b00c075a44100040c4008481401e44504980719414068141d81013a030120304142e2207600040c014be040d81c0704480310161032107002400c561003524a603010005448229040007682c0c00a0741c044210388003412055509c4d500440e13101c1c07081104107410819051070b800d03150380c000c2d030603503502a400003142e41c00c039a1100104c10700740c10032480541d49407184400190400840c06501031145d841d40d500c409480210f80c040790100202c8010307c9050003010b10582c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 423681151 1250 423679901 423679909
    0xc0d031e05040b011403030a08040b0613051302010306081b040b060c0d1d1203070f03180b040801050c070c180f050906060109080c031e07030c030b16030203010e04080711 75
    0x1e8040c81c01480c8598241d49840c103803403000340c59a003025009030020f0040e2802e69070043c6500d54480c0c0c0210170801d65640c2c00700010380d11b669003c072503900030b8a088144403070030880a005d110054401e0b00c04004482d1203042c5071f99281c010390100020000e000801c203815041580003207400b003802514203420000d4200e420750628982028045c00180342c61410802d420f1100d8442401c80420b46400305940c0440855507140d00c2400ca01038000442d130321200081500c200c030540581602079440081041d1200ca58030b0069001d886096919801c00c0c01181000b4414806c5588055120b800f000071503240072a500115450807041c00303110384e6920141c9141509030b001c1c982c42440c00e9005081585041c0c4005020684680c000802c264402015100139450000f01400c020402e121140403251800110501d0001c3d540c10041c0074842c01d4100008120242c0769103405442c0c40d005416900c030007031100320101c0c0400d12403d040f021a02d0041400f14803944024440f95000d4071091680001040110f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 423682401 1250 423681151 423681161
    0x30a150b0310140f0301020403151a15070f0b091e1c0c030c0501060e01090e06280b1003020a021207050d0813060509060703140606040306050c19050a0e0102030c0d031e 74
    0xa2b41c02d4890744960300d00d0000e40e40f1404140c0003d1902ca021910310490205041d0451000265015640058034006114103454039045442d40588040c0007880d09008c900e03240c542040c1d030700d00c800d2621780411b04a10004034140d88603180e00382c446000c08032010002c44608144490540038800c200c0b40803c0460170038000c45e4041d002c0400e00c0185545403545003c01c648541c0440d03030803500605c05100c3c07003000b00041c0301c0302d4005101070178001c0031419207948000c11084064961181003182c42c0d00c0c255400d0b402030482d00c0c00316020303038814404824140d10248101c07400280103821894100d103515025a07040c0e03030044500d040a0820302c1c06035480c030702120700c140c6000784107501480030820140da060054281c02641d074400b850050400c1004a201405540401829613850354000b58401c42c114081c0c030400c3c0b560114421081011040103407965001040b03940004420b032a41421390b5000004440000749480c004200307070012100228005c0c001c4a80c201c41c500044a10b07144a200a8021 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 423683651 1250 423682401 423682403
    0x10090f0f14030f21040b0105220203240904150f0204151101050601020c0d060504030309170a1803030203271201060e07030603051b0411030a150b0310140f0301020403 73
    0x10fa512241505070848240d08000303d0030225003c0c4c000c0000080140c07a5041c11600c094442890b40755941002d9844031b001d000e624104d480c03010042188000c48146910100f8040c060742c42851010b00b020f00c16420070071500940312030011080500f00100350791040701d560300c024400604090310b407000c1200421000400c5d2001424407840907021482c28411990490402d0000302480c004041c0814422078003082c025044665503c00a8141402504985c1c0c1865200b2801607800c44e400410341880d0f0481039040000815091502c0242c2178520461000c0e00e806800a40c1468040099410302c01402e189042d08440d0703d04040e001c944a02d203005d808000071400210f140ba050900031014000700811010030541404810800f10f0300100b01064441280c000d0003d1801214002c0f501030030302c181c1c4e02c0740ca0001c0042080712030151640000b100d40030040070580303420380d141c0030350b016400284c9408a40d4840c0c43c80c00c0120481c035808100e500310025003003e1010301e00e440040d007284c000c0ea01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 423684901 1250 423683651 423683677
    0x4121d180a061710020903070806100305010c2a210c051011070b090111070803010e0a0c1d180103050616050a08040f060902040c0201060810090f0f1403 67
    0x10038401020807500420028110750941000780c16042e441a556035440c004a06081d5540010703030720401d84060080c14054814602280c0c220700f072944241c017400b020703440251099403030180c0602c802485510042070103802003d01c10300e0f203882440d01c00110a0400c204171549110746c6001a801000b105244003120380b2034541c0100e1b0b014034200141420000e420204c0312a2800083d94000031210003076884690f0024101c1c862030761807011140c0100884100a0002ca501049074800c1120080c011410ba0700c495400712002d4540440d07074001d44d2452031150001c079103403003050380f00d010000c10141f038000b40041590f5100442200b0103c011a002e81055855030404400c0054403281c1c0030788215601c01c3c601d082032600b1400c010050a03840040c2004042c0861110396406010701070f0040d14442e60020f0041140603e0710201030300034403d51060128901a03041c5910410b5890b10400f41d42c43d41045144061034990ba8915054243c1c941085400b000700f05090701e04001c080001d4101000c0c803c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 423686151 1250 423684901 423684949
    0x50604030627060c03150308040e1803030411010e0414011401020106170c010201060e04050d0e040912080105040c0e0d080f0c0f070e1014010e040f0906020315060304121d 75
    0xf10010b00380c80403144840c5104031106c0d410000249007030b007107404031080310410300440d49808040e008a5914559607030094030020003801309000c01c0c00059070031000241c0303031208070312030020901c41640c0c0856101008501c02c08010003540690195150034050140300005a843d140c5440d58800411031164401382d40c410600170050b543c0910502002c0c06078a040e200c0c01d0320f02a61080d54404002240310200048407a1502d05521103400640c4002c0d441150385d6000e0010381c074000c251900034404d4501c00c41c1850034040e11a8010f0040c1d400e00074010b88688541d13130940c1c6034040340e503110810803007008908222404c0d0080003030128015a0544d80081c100c1640b0b0216040c5030240042c0ca80382c178261039080b003080411400070040e000d1100a0804640e0000b0420001c0d00410540360901100c50801507000e00700a42c507802035205883e280400c851078845d1400340100c5000845000700400d252a00f0141d490703010b002560b0314081440302264001c1078202c08101d680880308860020510f1031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 423687401 1250 423686151 423686171
    0x50d02120f1026071503050702060a061a0f091c0302011b0816120e0f0106170604081303021c0b13030905060a020307141c0905060403062706 62
    0x41c0030040c0c0081a0340c0b0540080c40c1000c1d6030043c0e42c006610019241c481d44500c80681d91400c0c050303c001003c2e5600c0c1c00d0444020508080c02502c8102c5502006008400010300c8545c0c0600c02e800583e501d40c2d1018200c03102c840d880400b05e5000711803441b504501880840c0c40b580c2d95961004900d60301e102c0e00f10400c0f10302d141c06429034110003400e072075000c90655011182c9500041e0b881c0d002c80300944114814007410b00035107540c48880c0c82008900e0411720a40f116207800184541c210040c01c0c020003403540d0304c45500000401d403102c6125190002c0000c00c3c04110504040e010352070700000d10313010303403541daa001441d100c4000d5501141c030445900d1540a0040d0f2240d601d41c040d070540d2030114103601c59900100317580c0f024003549104820220390284028400c005843c06a54090882d480325081c0d482540d64034000c4884042c0428020114514514402c068500844034040c00043c10281541e0b9980b0103860240c401890700441d00e032141800f1541c40c400c610031540030b0403001501c0010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 423688651 1250 423687401 423687421
    0x905070501120506010c0b04080c010e010b01170c04090b120a060507030c0c050607030f020702090a0b090c07030f0806010323150a0302030c090a02070f3804020d03050d0212 76
    0x1525840b2a502840c0008000c002e980084001e0401b40e4480799002c030581e0341e407804900c02d00540e1452440356103841114050090305500078600380d04243c0b10a44c41c83c00b582c02440b49804211162030040354140001c0203091102d03005456500c070000c180000b8046a00c1600c0c1c500040d5038415500d1750745520600540702d8140c4201c0d142c081207850000405042a03c80c151b80d580054038007820140c0d240981105c0c815180d041c3c905807a401050b80841d418184070a41c082c107007602c2c500e44a00e03880030110f07541c84120310450b801158903440d000501c200554090721004030050140f418181c44942030f0841402c0060082c403110340380c034a420200e0525411b2024032105010300d490044821310002d10250307078001034003404d51200f110031340c2c0c8903540c0c00380340c0000c0d0140740303401080980400106410000b01b100e24107034009004480b48807100424010303c0c68189215200540e0109241c042070241c20314400740124903002c1c0c00c025107887c9410342110202e900c03003072416802107060700a009244013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 423689901 1250 423688651 423688667
    0x120b2809060e090316170705070f050603040b0f0702120318060109060b0d020d022a060601020615060d150603020c010f020c2509050c0a0e03070303121a040905070501 73
    0x21442c1020b42c914903004103400d50302e2054281c01418525084005006c100d0410903008800031080a007a495030014071b042c0350f440403540140d10380d5803c44200452641852410750340700b44e4021031f1010b616103d4080810056001418080840c0100c1d1404c445036421140118001c00508690007a80002d5510250503c94180c210162050401808018545103003095444003440c101005949100040e24480240304402811640704420410001a03000800d4020f415019107405d50760306540341401240c8980301222910000310305803000310381905121001d00140d080315400081c8880c299640c0c0904000341c3d40c001c0340020380016692412880030f0040700c414000c0307403505508180b600c0006545600c4812030401e00748200000c1e80c0080c040d04007400006040c0d41d0410040c6040c54001c100341c0303521049081011a1410000382940d0134006502030459415641d03840c100a036102000003d0700701c01451a0741d00c038152140c03880c03543c6d6520903060264403400c000c0c403942e443c082c0050031201c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 423691151 1250 423689901 423689909
    0x803030f01210b011a2a060f01080a1e020409050c0102120c03030f06060f0706020403020f1e0910030c0f030303050705120408070303141f0b0406120b280906 69
    0x2540c0d040d42c1e00006821040e201c0d040da0740780da2140829a140c0241c041590060850390302032001103d021010401d420400e90341d60050b0762040d1044ea9440e904981c0c2c2c1c028007841071400507801100c0c900040380e001c10000e90240750983c2d9211245000390006070684402d8034042d03450b40c0001c0d2002d1401c0d03070104807201d2804030785940c050804500c030810070b0300e03404001c0c03c0105d0070000d100050700701d507909012aa12906000e220585509042c14404020341081c0030032800748480050072210380c03a005002140d115145d485c1001540c69503018007020410207005540440114200400002e9070441d00300044e0080c29038491303c10380745050040540750040c00341c0061090400c043d1400800100501354000c2e003000303203c4d40d031310440c2c40c003240203001f81c000090f51608040c00303100f0003011143c001c081090785016085401c50321101c02c00c009108610171440404d101c02e039404e2945903550000c00b10140010701c00e614600b000114000342e075800c450440c92106400c03105110480c070902c1498094 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 423692401 1250 423691151 423691199
    0x1501050307200606030f1603060903050702090a1a0d02060315060c0a030c06150609060c0f0614041709030a0f061103070f090f03241104080c010e0910050d0303060803030f01 76
    0x4ca049686501f4a258080078001a4031544814241809030b0202e804290f40503060100360301d0450380c020020007510015040201c40c1075070a14152410001c8129200d4000f0050740c6951505001c1e4100e914004807211380008051140021031a010f216440740c0714000d40756015040d0451400400301d8078000e07a1007105803142d00003401030301d51281c5201c09941ca64200001c0d14030700ca04007007203118800d48004250b141005006001e5140030326419018a1203031061801d0078810400c3e4502c2d60180c0d200140e0075600c1285000046100c0300710007000c060080c84001a02160344c0254003042d8011220000820300b018000319002d540b040f1301000814030041420229410b542e41c0b00180002114406150564442c000c41400c5039a4003442c403524860118680c1c0d039036a00111915030003800007150100b81036091051040c1041680284900600d80131405103c1c105410828444007014050f400c01d40c1d207507004159908204000d40c06048408130112007585000401588000a04201500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 423693651 1250 423692401 423692413
    0xf0d0f06030804270204060f0810082a03010e0706090b1207080c12070e100201060e0a0905030408060a09140d1d040b0a0306051803031501050307200606030f 69
    0x11400c2c100c150350942d060240c240701a0b0b0500b00140a41e82d103950b240751580d41c0f0006000408a400c13480c40741c0502100c2d150510182e403141c07850141100c2501c104c2006402c40c0701045020050307240c1c2c41910070600c1c00e865040b400c0410220303003151001c03403c036030059000031428001030703400c5000c0b8001080c0c071820292a02c541d4118040e143c10000c1d1001c828850184e0100710174509180c2502c9a409089940f40c0300c0f4074040d1001003250062442160050700c4015201880c00e1043c00b91100f500da40d45001c49280d00c0e2011282c00030201024181e4042c0014480450788035024001c0c68052200b002c0c0110700c018246c140906c20350f001c0f074207050711a846040a0591030380c000183c01000580c0025100d111490b1070042005019030f514a039521005503c0040200212544080d000b00004901c0e40d0018007030700c00c165600d110540d1000b81107034202044689a40c801c0000b135500c80680c0c5081400071203102c215084078059600e80d00c409400c0030040203030310b0404000b4110241c109000402c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 423694901 1250 423693651 423693653
    0x608060a08190f0609030e040b04020403051906060b0409020903070e04021012110a031d0f070905040812250504140d0c0e07020706170c0d021c020f0d0f0603 69
    0x76456100c0102c0500034400414240288031840e00d11021030b9801070820b010f50021440d000740701b1403151804030f224a241001c407804e542070138401c4d102a41d41c48001020701c5003036440d084905103a295021610345072502001700d00800c240c0f010300000d03c0303180405030f140e41d0503100300742c1020941e402c4030680d0000c580410003d66a40b80303400d03120100c05d0074082d101c1c8014482c00d002401d51140c8504110b840020850b202ca5859402840c040380b00840d42d50b241122503a85a480705c450034101390b455030001c841400707920000c1e40895000382c4950081480c205186508450350b540846803507140c2018042c000d0941c0250415003500240c85240141c50141012500090130744c1c22401c030350060011201d4901046440081c0704050490321440c10054540720308002e641d620580180d0300040ca2414400c0a9151545510f900680c40040340900705920b24078204000c0d00924540c00c99070020100080020071180700070700100340c0007075490b5a21003e58440c0c40030b551020300d013048024503000e8200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 423696151 1250 423694901 423694903
    0xf030a0909090201022b03050108071d07110105151207060f0e03070504060b190f0806041a1002060a150305070e1b0409090c061b0b090a0c0f0608060a08 67
    0x940e0a20600000c10b5822400102c0c40c144460a1030280d1030381c1800d060007182c0d407030380c06900b42070625039050001c8d0f80c07110800c035200c820038480c200e4514110500340e415140987c1e02590300c0615441c1c1740749a0340000705d0146c01d481c1c040c0c0e13001c0303080000e1146061039410302d100c0d01d200c0d905040e0000c014541c54040000c040070080440402000100150000103a40a00841c0c0061900501c1404400d0b224810f5100380d511092441c00c7c1003130501c0c1100c803000d004000f4200c0860250325901c0080d03603284240805800d10040d0101c12201000550304d0a56907400b061800504c0c99008000303614001011004036012a072504400e07000c41c0c2020400154001080c4055910300c040350181511500e49008440d0308070f0012010f40301c1c021402244440d2660310090038180115181a6019a40e0b40281c9030050300000b031032800c0c0344d00f440240200d801d0018a542040504044441c071940a4a5403a4041c20a40104c040c0d40708101c0b042007059840301009411110031684510b2080c40d120000b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 423697401 1250 423696151 423696167
    0x72303041104050f280f050a1b0822050607170a110304061104080f0a05010501120f020d02030c03010207110901141e011b050105040515060a05130b0402040e090f030a 73
    0x101c8101030314003c010017130805040d81d1140840603e10300313010114040007040c018000865284c40c3c4249082c0e401d0744201c175072401d00c05828030b841e00c610741640c40c1c040910702011014551041c05295001551000920402c20107100c0c03421903070340360b4285204040d0702520303180152020301c0d410b04000c45c094101d00000c04498129901880001c0c1c0c00501034013419081c06a584038084600030002418058400403481e0f0070881d100b0002000b43da0f803558071200400c014804050301401407000440010705003080000c1a850004040b6074545500100207400d990094500319951105080c03414540d09080031040e000d0a2507011102c4000e0020000c01c103c00e060040081d14041c0d030002082c031070f0740142d009207068045030480c0001c3c1041801c007940a07010659080b20300f407041c4005074210511085e4203501401008094030b102618240400c007220213130704030a4103615a90806201c41d0ba9880c0700030402855902c00d165511b207807140d0307000d08101c44016003031255082008407151041c1d116900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 423698651 1250 423697401 423697411
    0x11040e0c010806030f070b2116030c11061504051302010507021c020a0f0806070801080d2102070b06151201031e05010e0303010f06030b0f09072303041104050f 70
    0x110303182d0380d15a000240740041d030444245680c010000007003070b8000161300a10484c08c0c15500911003014025012442c0c6900b156105614418020000c04c224807a03001811007103c9417620340711240780f001451341820400e1b0f498203903400410000d00d40d5411725005e01548544844500321010b001500064801c0c030821500034420403200c0307240400013a80f0803c1c0e40010b40c0240074848020707100c00303034020440c0040c01030a941d449050005012140f203a0840e40c1038940c040042c00055020610680304156080c0c40b07a0800824a07584003138214051010b0028940a190040090304100d401d00a103481900400032007034404220103001c0301a1060054112030b4065800b801401618040c0c0381219011071000700301e9424684075400414001010714180c8030244c0d4800081d03540c40704190104c4050040641e00b2030150140307640c03145400701c2443d1384040913040801c1401521800e180300f6107524100784c51100030100910050001414400c6884002503034200180d04012109040000740108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 423699901 1250 423698651 423698657
    0x1231e0603090f0604060207150504021021020f0a0306080304060c121103030a0b01080c09090c031f0b0c010b01050708030a09031e0c050d0f170a0b0d05010911040e0c01 74
    0x1012680305803041045151442c802810b4411320705140ca000d0020b944030702d1041d0381c030f01009101d070303161900c00d482404e0003190700500103000d0190403082038400444c09400002980307000b044881c001c503020b000510400000c0d440c003994486640c0c07000b1b01102e4250304030300c00a40c030a1100380284c07500940a0410f0340d40100c0003000d04866040c040343c0201c81040e2a02280c00040180304244086070864504420240c885203191f645403071000134980103841e003440c1c1c0300c4200404142001007070700c0110340111403000c0d403644288203601000051581030740300d11020b01d00001d61030310b2100d0a00c940c0341d4994003468030320300d450b555464500b11400301030102c084955441415004160190010440d507a0104030455101c4040703801c080e00c21080d0b9201a10240111120216440c0c800c04021022a4842c1c50303411b10410304d04542640003d004242000060ba00e040c041c66555444000010326482440080381d8a000c0d442c0011064000e52a40340c061400d1a5200340b9001c00401d8003c0180001e103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 423701151 1250 423699901 423699907
    0x12160504240614090411070b160f0309020a03080708031f050a09021c050108010606031b05070b070c0203060c0409150302091303030213090e060705041a0d1401231e06 73
    0xc10902040c0c400d1450f915403041c0781a186e81c2c403880c4943c000d0301c0314600401c0c1001c0d4565440c104d1800d40d0f080720b502800024120ba850914040c0242e1081b81001c0c00a0700c0c01441a850744c2c0ea01d2400d50000005071038a0a0100800500b40c5499020170450000445d81c045a2458540072484a000601130881c003940c01280445014608882d003c0200300c1d4148180301c00c3d6914034a440c000c1c081ca0103820006800d05500521011501e6100082c0165640c0c40600c1e2102a03102c07428140700242244003000721000c1d004016a40c100403107802040c8800c07500340d440d450130411070116490381c40c000803041d420610400150750b8151703249a00550680243c003d1032900d180840c003c0c03281480d0146180960a8041840e004623803185200050b10400c0f94000d441300c0d4000e460038055481501c5c17862140884580c3c81820403c042d00051100b034101040d00c131001640254001130076000030b620b0280501d881c66107035030404101c0c10f211106503010700910171209040b0314642c05543c604c9020306000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 423702401 1250 423701151 423701177
    0x6030206121e1602010c020304051513031703071b020a09180c0f092405010516051509120c030f0304030908150f0a0501140906121605042406 62
    0x1600c0100110000307441d14030b44614115402020340c0c028030b58100015031a10081c0301603580000203c0b002d80388000c02c00682c1d0215000c5141250b4030489000c20f00320030040300000012070002c11a00000358450620340c8070b2a2152004006084e1003079030051154101c543c6001686800c91200c040e60420351001c0340490104039150280541448012b020881c5103a001a2852040d041b100c00c0c0c1d82810340a00214544284800080d201c0400c0d240d140030811b003081110303601038002004900c10007040119a00b0407034640d1400c15260300c4034448044011020056803000910840558000f80242c180c03c000048804596034080d207080c0201001000011034181070050305c141004052030400c03144a40600c04503c0083c800a4a5105aa440c1000030503c0c036500c0c3d0060506907003402c54800e01040c28002003111885016080ca600910416210b0050324014420f00c00078a0969840d00c104a1410041c401210001c45141c01301d0043c014031481102222100b40c01142c0c5035103407507405c034610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 423703651 1250 423702401 423702421
    0xc110402090d110411040f03051b01051b010f0612060606110709110903030c0d140910120e100603050c04050f06100323070e030105150d050705030a0f0210030603020612 74
    0x340c01c0c001d05c4018030215000611044118040095074801c03016140a00140b42d0241e9034181540c9801e40802d1050100c070030902c0c2c0e00440f41d6114601500046644000d4030030b03441c122401c580110080c480004068020b00c202c50248100134001d518007100140d103c074500d1622030010b8001c1e81d00b481c0e03c803181c1e03401a161881c141d0b652100e0040c10340b6030718a20700b0011547c1e24101d00317010010540060721030b002201041c00351264041e000e4680300483c00c400e9400c54070300d648269092099a651100700322714120811450607025400500001c4103811030800318a01075100b8907103441359081100708050700c54030380701140c1c115009031081042100c003050154054a10700818000c8004142e108000300035075100902d01030130442c0c8400b840300c00e010051500380e071400c403160b0040c40c1e545541c001d0b0900b4490301019501d0b008106889040f0b498200182c1040344140e030a5131148100c43d000b600354600503007040c94070a03990404000d258510707404034000b405614070004580941000103107040c07103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 423704901 1250 423703651 423703661
    0x603291c1110020c011d0307061101021e0c07090e030f07022707080a0218061b011113050a03110d02010e090708070807141804020403020a03030c110402090d1104 71
    0x2400320001c00e00d5020000c0d968034200b24a280000d1b4000220f128413410b1030520a01e840010b00680b400302d0800d20161070040d8803030040700381d66608020380b0382c811844030700036460700e51900040c5503650440d001072880e000090300813080492401803c070300303441c03c00411210b03440d03883d4102d941c440f031113400003800e803810b07510b203c16003a0ba820b140c904841403a0790300d292140030581c0703031030320251a60507180b0102d02440e645420303015681001450585040c00240c4020000e5113103500740007622801050954092010340e03403c0d49001300d5100d9a00c41306586103c090070090390801d4030305281d61030f094000a00ca5808500503000101c86401b5039119012a841010015007504000e060117100180005400c844040000d02c084010815103803068480d00500110381200030f081c0100401c0307522592024030303016035100e6030800000005032038590b10300005600036203501d00d046200d401d00070100003892075000d210718030410681d810f40d80d0703280325541c1881c0c0044100e400c030b44020020400803c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 423706151 1250 423704901 423704933
    0x6091612111203030703140603210d020406030b03010b0102010b0a27050705070b1f0506090d05070e0406060905130807260d0e15040213150603291c 65
    0x201040e502444004000006500624050786c0400c07120140300003024441d030068030400d0b41600000c00b89603040c1010148038807000c41c0c0c4d00ca01881c180c1c640a03510226402940008086130700d07507035003c01d1840d007031084104541007800280f001030b51003000030740c0c10202400740c906482c100c42c50a041403003100701c0303e100d06034003590204054202500082c00b45c0d0044030080304c18030361080c00141140311030b100701c00500550300a0340581c40d003408200500d43c1c000c10030503134100a00d40b0000012410403c05800201014031001409041031b00b0000305842698114500c02c600f0401404016411858514107940d08400d189480c1d8100d803030554601d8540e4142404070070615070050141e40181c500401c0c1000c2940e00802440c90082d40142e02c9031185a00c0c1c81c50031240703000080c09420264219010401c1c0e6040000724280d01c0780d0007581484070358110030f00180d507503501c40e01000080e00b054451031440610600703400000310002100d045248180d03481c0104030000c2d2108006001d04215984 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 423707401 1250 423706151 423706159
    0xf0311031608180a052407050601060c0201080903120604050402010e0907050a030b03060603030f03040816031e110c10050d02030a09050118110f010c1b080609161211 73
    0x11076181484281d03508080d49101c1030048107902c40b811071401603444003ca40f00944182c6400da03c0d441800b00400780003c0c8130080020800070580081e40038007481d0301a04040c0c070fa030b00000c11103000061a00c64000d040382c07000c2d0b00070041101e0b104880c0c2c000f40e80c840070071035010590b540c6910040318032201316640c20b5003150303800c0103100e0031315001405010040c0c4603030380c2040103548650801d5aa190240c0395030b03800d0b0700304110000321000254000c680c030a004031529442c0c060804282132141c0b200001c15400904403814001e10b160610b4400b186601081c42e00741e4011703003001822500c8440d01455148944240c0c2d0080208a006406a030882d1070008000c540340d1604400c0c11015000030f03001210317203501e414041d49032810704c0300c0c0b88966690803c41200700540301c0400e00c0310020b0048111782c1400300c007220303500005140c01c4401106404561044d6500340c5080304080c5000c5014040d842039411591030030a01c0e41c00380003201c0481d20305610140500348581032004026009101050b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 423708651 1250 423707401 423707437
    0x41e090203040501050906070c2004022704150303020d0807030621050c0402190309020a18090b09210d14010602070f051c0b042f01031104030f031103 66
    0x203018045d401140300d4045c05081d600140d40b40c0108446c13101896a00405415060b0540141c0d94012030184c0c03039880001c4c10040c60202c404440d0f2408568040010030900c8540d4592141c90415000d605414141c01c1c0e251126603003035950288d11411860040002c1001000000d00c07503074031a80040000b0007070b85145a00d100e803808003240550311140000d0b500b9100e080c0c842c1c0d800b404d02d8421940f040c10b0180718528203415a0204030080c01c00c002e41603910416244020924903d980c1c1c0c510b4180d40300c440002543d00d9030b8988a07403101c0303000f03040110755044454a030540d00c000300c14991210701020511f03950740c070780a141000204001c4580362481403960001044454002070160265403101c0c5550050550780e4040050204c510600c1128a6402c800d01e00001101400e0380d940040c4541031000c8914106e40b1454603140303400c10028005600b41130040d01c1c40d6094400e0300110b148020280b8175003401c58a17400030b610b00e80c00c001800c01120300712504003000144151002c1030100003179510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 423709901 1250 423708651 423708653
    0x103020904271110090b0a17160806040b031902030304031a0f0a0209010203093714010206151002120a03060f060516030f050d020d020a090e0c041e09020304 69
    0x480151144000c8030f001c020a0400c030302525001d8841100301d00c25a860b03d071000e0926480c940150031920b182030500100a96801c000103043c03050303a02c12404040c2c82805116500002895400c01408960046151003a03240e660b4401245951100e03040464001c4090f540d480400e240d4843c9601c0548000b0b100b01200c21031911024159000d401c070f0300c01907800707a2100e2510500f01d108030071001e40075a04c1001001c1a5041c01e4030028405103025900f07041c900342500e00200b11060b551940b001402c0000c2c0c051203010210850740c40e20030020310080c652071411410000c0701c414400c443d103108480610030784144c640300f0007445249c03600720310a5a0b00c1710090440640904400d0181010f01520140041015845070f015203446031020310b100c0500d25403d0700c095a5014440982804000e0200300c1801c4441050008240541c84a2001a0f88554010300100310f40190740101100e0b020b140c003480b002d407100b0070542d4152040050075a0104440f9074810342e25001c0c07940807510b81800441004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 423711151 1250 423709901 423709961
    0x1812171501020d090e070c0f23010e0c1c02061c05060906090405060402130216030e190f0306020f0d180201020616020d05030c07020a0b180607080301050103020904 72
    0xe00d0040c003a02150b000c5400d0420075074008040e40500301c0030145c0d000000701024401c000503404d5601954442c5c00d03a03120703616042015828485200403d00341c1c02d40c02c0b40c1c650801d108103405118030102601490003400e0000390700700e405031082c1001080860841c01035603540e000710380003c4800a01d401d0740400e054002ca0107048105c1c1c40f20f100c1c01d00880007450508200755801d114607400380c040c4c10f641c5d4480d401c12202c075100400817891181d00703000a0b0000a250204511220b01035228010380c20709074420031030b00e8807810003080e00c190142e41007080701c03801e0241c0b00c0054a501c080c015803942c3c0515035007001401b984554209080c00c0000c00728510100c01d2054000c5030007a404d030b451564401107801ca150303024400880040e4401005120076070311650182d070b08900c5a165152800d03c0c29000525140d0040e0086d070302e40d8000144080d40c85152802c0300240940c01d81c1c181d41040610740316034001d80014440d41e4185500095200c020741d40315805405800b01c81c1590000c0945402a44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 423712401 1250 423711151 423711181
    0xe0912030a110c1e0105010f0b03070c060509030d0f2708070b04150e0619020a03090f030503100f030203030703110a020d060b0a0501051305120a05010c050a03050a181217 75
    0x928a440b04030213034000ba0581801098142c8088180b417170800b61800d0300d142203503031008111600700f0080825240008003503005441c01554001c004540302d040180c0754000310786650481403441441c14101e070010741d00c135100c182c82040034003807200c034240650700707040000f803046140c014502c01d100401c10040080d003d40d442c14010302030314108030040b503440165540c1c010a560700c80c416496490360075095056600101600d902a18001c02d9801c01d07a61030361012500d0541c1280402d5011007084210382d8002071032001403010020b5200e280c2d1541d00400d849118921018041101010850303c10300c0c001c00184800550141903030004e2502424880028000400040d00ca442243e0000a5940c03090f8107584162901c01000f001c200c0c80c1100304425100c256100340c08070b0280741810710100d8028810104c000b039540d2121542ca0250380c41c01411200001c0600030258a031070540c084100c501401404060b520400c8131003400300b070840940310480707200711100c2031086010400c03120f122900f0760 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 423713651 1250 423712401 423712423
    0x10e0c0306030a050f07061218110d0c3b060d110d032129150d020702030c060705150606130303020312180307060c1b03030e070e0912030a110c 63
    0x108d04400c010a400c0c0c1c5c0650b2000d140524045981590080c003280301c0b8419081c140310300034201c0c8900101a40c0d40e025501c0e180c5e0194021000c1b002800074680001c4403e98052585003009149564928908292850000d0105809048104c0d401010016600e03034595542a008000000080300303480e0090805103200e22150350b0001c1e221a0365030b016001e001c0c81d25441c0748801c0b00c8034983c49150403c080e040018580b030303074442944c02616010500d0a030080582c1a8803032005a40c0b1055030040c58a000710401d500741c001c0303008101d0344000c200c000c281001c101300b4000c0c003845661222030015560f405070b02030200810500c00d0f030010406070004000d0500c403140c00003514107a03071440124a08165480b00321360603034104204003800100b07680c0c02001c3c10403090810b020400c4400e144100b0140c00c0b18401c9001c00e5580c1c052200451003003080b00c0c010300728510390384428030300304400b1601d451210710000c11403040400494480c1d05660840c01c01000c200030b005031150101940ca0799240b8034415 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 423714901 1250 423713651 423713657
    0x3040f06090c12140606060a030e010603022e080c09010e01110f0307110303030108030a18180b04053607080312070801080703030507022707120c08010e0c0306030a050f0706 76
    0x4130780a08001c03036003500c610001003040707003091401801074000e040e00b868401c0c42e41d582c8180c00310040c0d5a05013101d61005c0d100f0b50b80102c507011050203071030b0901d0852003602444030034810884088500740448003451020310f0074101c80412240160395031244c1c4101c454060141c1c0080b03c100c000004041c10314540076201c0000078801c040141600d034802801040043d030020010007503024041e0040f4615481c001c5100d803409540e03001e02a60340c081640c0a281001d4942441042070710f0540030b0540c102a0300341c0a4211000408100740501c105104640e65182c5d521074903401b00d60092040400506013841521b0307444105450740c0e98803420490303429000c01c86988c004180b40d20001a400d0580394141c40d07991600016070200040a600207a261007001111980c2181c003007038032500c0e1801540035848000303888080c145054140c40c6900702110030084840f004002009401d600590060030700c1039401d540c1e464600101e41081107092002c2c020b0b00c1350709007011104100141d2041190083c1d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 423716151 1250 423714901 423714923
    0x1090b040b041b0302130e0103060b04060e060f0f040b0d05030c061e0a050c0c0a0c03030e040e0304052e0e1906020d140903100f0509010207050303040f06090c12 71
    0x401c02003114210307030743d080b40040241c440da00040e010f50300810601c80350810744020300c5e0769883d600d09551800d070412030744507464401000c1641028050030700904604441c200c0320f4a0100086451003010b004850302c5014540030f110700a4035594003103040304a010705608001c2c0b4003401c140344d43e40d205001c0b00e1054403031180087c58042100301d00c10b0441224159507645601c4148010001d884007808822411508004d4030101590400110169601c240540d12209282d41005044008080701541c000c0d401c100c480701d6604c001204440940703c0456030b1041c00c82040003a01041d101c07421022500d0b51034500d0034100542c01c0902c2c7e1f60300b01d1040743c0214012110100b1550040d50b10f00c100c5015901004d450350495004905103000c3c50b05001d03540341000070301c90000c1e14041031201904200303581d90001e112055a94080c041d4400d02c40e6009502c0c00c4450303034035a9a41e2000a0000c1e2100454410450070400d05420004265411107041d00d5065111000c8054030f044407401110120158 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 423717401 1250 423716151 423716171
    0x9050a0b040503120d110d0e0106080102031e1009061710020f160f02030601170c0406030b0402151204061407030905060106051315020705100c080901050d0207020901090b04 76
    0x44400c450a4034005006403e089a0a8603c0c4140b904158616094262a0406d0342c414040d04400b5204064080001241180c0018040390840e0140d41169500f40d00400400c025004443c200d04401662085404a5a41c408581e40c0c15440d0035040524128206076000950480030305904000304807400a540d403450110074010224421750400d54100d00b8180700002844140312410354540d8040c26401080d08030340e03400071307007005130982010a0340503220001c615603800400c00d076203c254090710200501740c15034603030f4001c1c218020f100a20500d02e2524504811030243e0985040221440340c105a40c1058a0258003400102c20314060b1302c681d410008024a101c0c1c041d0135207454200300600426420400c084803a540088514000140f04000000703030008505001c550f03001181d40900f540d10b0030f200c10003203c40701381131560003004241d103841c40c00724844804844c118030007401c009a03a401d21905000c0a07005001000e0b50010108000107161003098008015454003180c080107007281d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 423718651 1250 423717401 423717419
    0x180402030c0703090605031314030d0e0609010e06040812090304031a0402010e0d12050d09050601030606030c0503030c06070c030314040b07090812030a0213031209050a0b0a0f03090c0b040609050a 86
    0x44030f0230008100001942004502d5101c49451078524100550b4523210340d511454007610b403042201400c2d640030404000c0c60120a02c0748545440328540a01018101070f140c0c1e5145002d08009a000314422802142400c2c00c200219001540d0001060416400382d44010300305a04c211400d0b40441c01c0e0b004405030b24a0b104a0360190305d075000c6c01c5009011003800c0125000d4100f094000161a038400040c8041017040040900940c861280480d10900794504480220300e103900a5000b54028000f09035031750310210300564041010711342070501c00e2242c1000c030042c0150318034012607054030106101c288004a1102032255855803101000b07a55143d5007036a0f60210401042c0703a4120030702c0840c030100740075002800030f4009003501c0e4180d15101c0d19590404201d070031215000c1100e1900801035810500d908130001e0200c40381045c10320101a1014254001c00a400000c0540d80c541c04004c0210090484000e0301c003802a09883c1c9441d0702000d05010396038020544208290900000c404074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 423719901 1250 423718651 423718657
    0x40b06010801210201030b13090c05011b030e030c0a030312060b0906040608060d060e0a1e1a1803030108010f060b03041214070b0c090907090e0c180402030c0703090605 74
    0x80702d4245090b1070b039841e08403c0352181007404904042d1140c0d425041c03a668000300031921120b03290009600026031425200d40810383d4491811b00406001d2011203038040f0b040c0131011905801c00007aa00814000241480611102c0c603501501008000c414140e001c101c450070201801c0d030820002c0d480301c6424555018013450700f41e00c40403c0206208070741c824040c86070400e81c090651513000700d00350355180584204080c0654550321038918403052203040b004100420452950441c10b0f00d610b42c4426110740c00c011075142c040a8850003140d00e032000c00c95803044283e03caa0540b07840e941c45141442c041c102c41c85c4510302650611501158240e0a00704690003240e12081c0010251301050b02640c289542c2e0440c11b03d600c105200c910003094002d00303007610404c501d88510755500080d00400045000140c0f40000f00030121005100c10300d58800559000b01d03c03040003580714144012031084c07104050000c1034019001209000351004400c0162500600c1f0f62500090303262070701412101c82c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 423721151 1250 423719901 423719909
    0x906071e06050f0f091b0f0d03080403080721020901020309030a0b010815150d0311100504020a1710020310050a030b1806070801062a0f050c150d24060206040b06010801 74
    0x6c1c102c120001c40040809825900620700a0300302000098100c00150a002003000300750081181d4400b0081016071202400c3e0b8000200d09040b50801103180f101d60182d020903a50b64100c80c0c1c0092014010f0307000700300382d50040c40e000b0102d0707100ca90346282000b0042d40071f1207060f42c9842184003c2090f4161808000d104051211007102c40074034a5003081902003404805800b1321000c1e016550040c1c0d000e01414524040301c69010802d810b0510501010030440e80c4152100421403039034000d586004035422502d05114540075072641c544003c2c54558074856030005a0204c1d04000c0001000700104c00b961050501e00d09508032844200c0341c05407200d404030381240c0000e603100014445180103244d03c620102c0c41d44650000c8020008003d48140c01480341a5100060890141c00700202041204200d89083e503641c5c1c20b190409a41032040c0c001e6540c07040710243ca0b80020003440c064082e2030320340019218424540556a2000070351165001d90701540c0403c0100d00060380c0f54001c40180d0304032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 423722401 1250 423721151 423721153
    0x2070e130b150f1e041505030303010807150e060715150602060f07050c07030f030531170703020603192a0e0105030a0c02070f080717060c0906071e06050f0f09 70
    0x4844c000c01040010500c6c4018040e010b06c440101059030b8804002442c040c0500c20010b00c0343c20308000d60302510000c55402e6208110b94180028510740b00e540a030741e480ca40c8442190710080809003101c0281140c4403175010604040e1100003000d03179000615901403a8807a481d4041510b03221000c807014480d551101d00103a2294404000003101207104d240014080c1c540a0b00f42440601c10341c180d9600424800f0f24810500e58980c1e900f2880e00d44c41000f458814410300d5100030001c0450b407133002910019100c0c01c40800004d01152050040c04c0f003d402040c0d01b00b00c0300400c2d4200b10499a08a55845007407141c805200d2003403402441c01d4000c1801c16143e5904541d542d041d094003074080c0609980031402500400034008601212a90142c21034070080c082807801d2112180162140c2c4000d144150710040902505180c0501100d81c804015240c01e0b0f40c8203810305103001c01c510b0445131102c0c81c103802002c407024030070b40d5800b050040304101c6054604d6150a5204105503405803003942c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 423723651 1250 423722401 423722449
    0x105040e060403141c060503060a05190f11040e010317030105030c0d08070f0804060f09050a0b1b031c050711060604020a0309021203071208040302070e130b150f 71
    0x2003401803141044010000051034640b40d02d00d213000512505d41000c040c01103403541014090361400340481a030081c1c1c0250104610b1500c8183c215402e10b0742e684060807955a00710001040e605c0d0b4001980245000d11000c0e50745503204000c04c14844240b006840d002100d2100d00030300161801100e0480e0002401040321030402401c004044041000c00c13560312908004000003e40481851481180070383c0300d1303130345442c80d02801401042003950348c10204147c03800c0070302044d030b41c84032100151090300c02c1082e15104984650481c203d486407150040d8400800c09440100082014501c41110064180096240c03081e044c1c5005504d4194030040d50010000111a800c003640a05400c0c0264500404c039251142c0200344950502244203490340c00000c5d1510a000c0c80e018402c151f000e551610319824900b54a00035151081c81c007074024000c802c600440c0b11300710150080710074587c110145131140d0909809c12250000180825405001040c00c1d581080c40c0c41c28072160420501c40c81c0c0c1003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 423724901 1250 423723651 423723653
    0x30403030311120a0b040b0f1507020103060f0f0302042720060a020a020910052d040204080d0909060b040506071e0b15060f0406230f09090105040e0604 67
    0x1010b49020751080407603803424031003400c01c1961092080c1c01040026800510300d00d1483c00e00054a4038182100c1c006c05000080d404551600d1802e01109402c90002c1c40c2c42d14001d100480103003015500503030399138901007000700d050b000b00c0c8400f108580c42190104420012100100d030403403940c24240000d0340d5050340c194003240400711103e8100046080101c42443c00ba00061007580242e00751400590042c83c0c0042103040c03900981da0440f4000c07110017609490000001d11030450201b180c010070041c0c0c03400b4a080d032507540014000b404c00800543d21140c403098199070761143c0c810003200140c4a41c2e400100350b07401c0c0c42030106840d400d0807440d00d0a8189818422182c0c4043d804039000130f401c18040307001090010070a00990b2140f20030060a00303000c01c808000141344410341c3e04c42c0c5003c0155181e000e0f42070f401c45013100c2407402c01b00d400013210f017003e0103030121034680900490400228180300804040081803180005c558260140e622035051104079080c02d4601807c542c800c502080c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 423726151 1250 423724901 423724907
    0x9071514040e040312020a181706070c0809040501121a0106050901051c020f220602030a03050a0e060f160302130902090a030c15090b03250203090a0e01090501080d0203040303 77
    0x59120b070180c01c00c420954451603c0c00100d87c804000f090005d841c48030501d0f620450700840c180101070816010884018618209845500141080d0306210b43c10300440700304032080041d64001c4400500c104050f607540c070101e0f41c40a006020840354400140ba110740c1c400c02203d42c40f4161243c80c5d0380c16003881d15050054605a016005030200d101c002c40e02180240c2d4640020441683c0c880101d070b4035507400340213402c4003180c9080030148a102d90101400001e50001c00d403180020303940303800b0a8517120b900d84d440c002e0132080d407003d5a40c05000f04024119101c0314805000f0070400c00c8903d40d60000e613504404074000d40ca500408241440410040706225401408900710020100320b502e503a01d9907200c2c8401c0140d40031102c010b0607402d80811203500400100c3c010304c1e54408181c038519001481c09981040c2404003000c3c80e02c030740000900c080c0300300290784031030750041c00004280342c45003c0040c0c414801d125011500382400c00100d02d60388007144003416001c1c2500103505190440e5030907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 423727401 1250 423726151 423726179
    0x7030605060d2301020f03010f06030c050a211107050607090501020c06032a0c010e06100e0a0509250f08031908220b060301050c1321020402030907151404 68
    0x210b00f0542d0244001c007036145407100110300078003030202c2c040b45841c507100002e01619402da4441c0284034080c0300c080c07142504519081c074ac680300751a0755490442c00344d04800042122000c102404080481c9903c104040010307054000c1c0c00940703400d2443c43d52b60004903070b00d12881004176041101440071401d201030381c1c44695803120140c005a120300318140d01c80c010a0300100c088201981d15843d0f11000050107010f041d07000701c818444880c4d01c5040034007031070700000c002d410071821070f03074900024001142c184001030801d001d419a407611640c0360b211100300d1400501504002c0e240c40d200004030f143e03000086444044000c0a2a00080c1d807910f002c0c0c5a0480c02401c03091542d0341484085103007003003820581c03031681c840d80c48800d480c1002400d06007181d03001007000100d030b1740800103411807640c40342e2000c044500382044a4031404195000903011924060029001030010060003402c100c0418a041650300201c0a0103d081d02900122071403d2503903649000c1e000100302c2840400c1940002d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 423728651 1250 423727401 423727463
    0xb0a0c02040209031c03111e0a0c0b1807080604030f1101180b0f101802180909030901080a140412020309100f02070b0403080a08060d06090507030605060d 68
    0x401070900040e040400e0406404298000005d80030815a100041c5c052084019014004c104039040ca03007042e201e07003100044e004901d009504041155001244545911000390760700440c00156420250885202d4241d03a252452450098680100d13548000040a621603038040c1d4882105110600050311181558203e2425039500c0c2c00005040810308000005964828105d003070040c0703840980c0b0524042c0c013421320400c48500c80810080c0c40d070034481c1e1b0700c0c2c00e031604480144c0c0e8039100f154600004a00810a6800050400c02c00158a40203c06010091400e895232000745d40d0b04072182049408040702c1a1550950001280108544200d58550f0301c581e801182d25000300240010400355049001900080581c03000e00b24103641801f03003c1c003c0001c20503160400341190348002d040c0c003400e079001c4104842d020004d8910fa9941e130f411008030342c110074100031110b00780c1000b40d211805800700f40c580b036003400c4c041a502c0c2004c203403025406404c25005140030301200c0e1001c00c1406280c0b2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 423729901 1250 423728651 423728659
    0x30f070809060d020f03061003051512101b09050603011a030402010912050c041b120b010201060302060a03050a0b0109050f0f280305070801111905040e0408180405010b0a0c02 77
    0x83c40340c2d018074510081104002d034681850300ca10f080404c100c010032620502108160800050284929164008030b041d00411140500b0701c04c01007008a2814040d034000c401e00358241703014001d00c8083c98080c0c01807444690382c0c05038003644901c00c0c480213100a00c9010004c1d030042c6100e0032140c0a03240a55001403052600e46001503803440f51455201980340c0564094000b5a0450441e280c02d00c44c2c400503c072030401c15600c11580e41d001070000c1000c07565000c2c00e1502e0f01901a1140c0c0f00f9800341d809564000c0580b911441d00050040091408403a1088880d142c819112030940c020701d001c4d012940000c204661a00d1080288111411405141f540000b800c0d81e40c0300107000780490101002d104501c0d100d504900e1410a145088410740c0048016490012142c2110100c0b104903081c241e2041104240b44013141001c80f01031055600a0141c0010322003400704004040c1c0081c00c0820500c1088249501c2d00070401084031828400d2600c07a0000f08080b034001d5008010048401d40010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 423731151 1250 423729901 423729907
    0x31b0c0c080303160c051f0203090115050d1e08120106030f1e0b010314130201080f0708070c051c030209031608280615061202040303141b0d0201021902030f07080906 73
    0x3c180c04241c2c1e00d660100d80c80454020080140ae903509104561307540340b04a001d141003a00d4500030a81c001580007010342203050300c514000044500102c18510710f03038003006490383c6e011020403400b4010020300807080001e0400c1001110940c060003088008290000c1c48109190040500002840684001c6052648490341490188000c1c0c0300141310350400d000d1100d29852070702c00182410b030020800501c0d21080018013071030981c84142c4651140031070800001d1107406081007031a101141d018061a4000795084030311032603264020b0140e10406408841e5500040c41341d0301600040c0d402040c2c1c3c0c0d503006000b103403070300d028541c002140c40b450012a184a140c041e1241000d84025003c1002c000b0181d200070448964000c09560018170300920441c24182199401010614a031100c44c81000000c100c8800c0c00d41c440b80f0f1021708a040d9011a1448098031002034040d4108091040200c41280080d8001500120884807940d240b40901481c1c503083d81c6e282419504601420354005000b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 423732401 1250 423731151 423731173
    0x6090d080a1409010b03071d15010504030f06090204050606071703070e040f02090907090b0f0702040b03100606080610080c03040f0c080a02091311090403031b0c0c080303160c05 78
    0x102d0700c0c0034000c500c40f50000c2071011851091500d001c0442c0e00c91030400144000c42c0c1846418144444d0f00041e8094400840e140303020b004a0311405240c0010381080051102c41041080d5640700c1c3c2002031094400740700359540d030410800c042c001c01d18040c150380c503010116100c80c04240015640050a401e024004140e50030119040781d0000b212a807007161300041550b5185400421a036226000d8600710741010f08110011f00f09025121215825040202c1c007181107589507000115800d0002e021103082003002c40e0b04001810143c40b41801190b8160085030003414500c41384040700460343c6540310191290000d1040a620042059074400c118800200005413040a0040103061100041c41086103a004200101314080d000405030740e129000311001448007061080c2d04102122a00f031195118182517001e0490068218100104928480480c6801c90b454203442c5005070300d440c6185031917001d00d65030f80c802501c08554080700c515440200600c552242544a0b2140054a028003c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 423733651 1250 423732401 423732431
    0x203032710020c010b090105030a170f0f0a09050306071b14070e070e0f09150109030503040902071a0912130e13030315050604090906022503080906090d080a 69
    0x60452940c005400185074072100c03d09010f0540400d2040742c05440315450000025541c1850002c01080b0710400a11400c01e2150801911308001c2d5807003e0581d0f0364507a10020f0701c02d6110105030303400701d80d01034804911810006426807054046450782c43c1440c030118801a0319004a0741c0c01c480c403180342c1100c055280d000b030249800420401d8aa0000c606150704040c2400f0801c0801c24041c0845035a03003e01c2daa115200035030488d4250709100f982200030001210b4400c45908090003c0c8800500000d5954140c2d000f0213506008038481d40080c880031034540d00f00c180503a03029080b030307115501441540c0c1c10040100242010f03d081009420f80c0e80c0008203403454100c5026800301c507810000c805040c5c25000d4403041e05034140e044046175040100251050040d4058140e0299449001d0030812519034129110046031921000321f00d40d000d0385030040c810380800c3c11000544240d003c50048400011041d000f04413250282c0201d0126200c100c031305e504010005d446081d1100324003000c80013 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 423734901 1250 423733651 423733663
    0x61b1c110d2c0303040b0c07020a080304090f02132d0f0e130c0902130f032915060d020d1d011a01050412020406080303010b031b04050102030327 64
    0x424140d000c101030290140c0c81c185840c2d01500302101000c0200c200404100110440b580507504c50304805e050b40790300c02c000029001e00c203c025000520b602c804594150700001a00403149a00011b12200104901013000c0c0d0181c403003002010f0281a80522001e11224080b08110300d4071b0407840b80100100003420141c503042e5001c00d62107007c0d00c1060115800c008040c685c41348400d803a41842051035640c05032401130f140b00720102c141e0701103912110602d422001d14000c00201c00880301554807424810745026158401200795800348140000506010708400e1085088003001140b14403100180030081e488500c0009100d5400c011400d072880c82407154019209140300301d0341048003c401802c1c00c4032a40550301e5401100320b64503140603a07100b0b0890f0251762215140311050030442c4042009004141c101e0703007e0f404080008504080f400025501c6118000540321111010030000e9200c1e12550040b0382c0140c0003040000e518a43d0a4010f116103110001c080c2002c001c02030455007810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 423736151 1250 423734901 423734917
    0xe070c081b01060911090108060303040909110a06170106080c13060c02211213091d0c01030c09030308060f060a0c0614060d0f05030c06040f020102061b1c11 69
    0x2101c9407040e06105509104040180002541c10046580340d8004070b50140610412a81000040000681503442c00e2081d50000c0c9901c00c0c1c01e01c5540740c146070070000c010a6004c05400f880102c80d0010f100e6103d07180f10711607001c05108a442c140d081010407079036000c0040030310b0504841001825446502c0d61000c00040c03280c0d40e2003c004440510403c072604402e81520450720a510601110701d010118100c0481001da0440a594000107044814980e1995000540152410040d03102412011030507141401c802030690310040311500c019803c55121000050009515110074000240603510041d0042c0005045811603410300700018070641c046011400000c641c0500041045850f01604002052011040c0602d1608002140010000304006084512003140b8402800000c0c401c4414008a00064135143e1426040a5103c9851410f0490052051000288940440114026000001c086414508104400c0d10058458a0a40128182d0350bd003013403140ad29006009202407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 423737401 1250 423736151 423736177
    0x60603013c0e0109050f060a1202043c0915050402040905010f0606260a020a0c050d02061009200a09181409030c03090409061b2a05070e070c08 63
    0x10f40c104070000094500c0a0040d900e080030030814401ea0780d448146480544c2c0300140c0d0a40c0001072400014080d11407910841204103101e040c521406117010002401d20a646201d135080c1e80a62500c60708950305100c025001d01c001c00100d0b07069103455045150032500050004c42c104509844607800c40780f00020303094a46030380729400c001e11a00400c5440d051084032240a070b0f10201940e02c907a601100a02203400d90f603000800c003407100d028981d0003000640010031100e00c4114040003035039402054410840040402d900000c0360541b0307009410010401581c0f00805140c030701d16950301908900d0000d000e00c064608045440401003811010b50728603c1c4010512050326101a030a990015259400a40040159010448000040300c0000740c054500150036445401d10b0700041c00d40f521f00c10059a6000e40d2080c0180d4000c0210b0001c100b04041051000a5822104480340510000500c7c58101000401012120302241507000000b0b0600628240081d40c64083c42d9110f505100d4003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 423738651 1250 423737401 423737429
    0x10c021206090f010212010b071b0803040311120a120207090e01051603020301030b040b06032103070f0905010c150e030304140c1e0405060d0b07020c0405060603013c 73
    0xc0703580200840943c2400703000003185024003811055884400500410540100c00900c0d0f600300301c0c01c1c1700c40c84c61181c0b01c0c1d10300c1c14405894290280d2254020b02c801d80e080031381c1c243c3e451400c0c40c00941c0000b80f04030750002000310305040d80c2d07507004201224082200b0b5009202001951843ea4064810b0032102c003c00005d2070b1a0900c0c0b80f207003080407070154a04051050005000280c003414259400c0340d041100304209582d2130000929140141c0d10341c0144006d8881d01845285814003c0c41c09560242c031008a52140c00000710b4030740d01144110384c00584403000100200d4640c00c00307203e141c0180b40020803400d248600203032441c1e0003901c040b03448480d4030300681d540c4a8140301c8203401c803a00f100c002c1400c2800c0c1d80885017041c6020700c241c3c45203640d100071030025542c00444040d110b6018500034101d26000c13801131340341c10300c26005502450608000030312500e0042e089905907040b0300100be008411084002c0a10305121019045c65014210281222122a0201f030000d10100c0301c5961 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 423739901 1250 423738651 423738661
    0x6090c17060c030f061201020d0c0f08091b0d0c0509011715010e0114030a050a2103180602130b03510123030906070f170402010c021206 60
    0x4074080004040c425450014030034481c4400c040c0d0a00e9030419400c4076824450060103010358028420b03100401c60452030543c046ca43c0301e400c6101940c48111640300d4882581c0c58214842d21041107070303224250300c1d40c03800882c080380c41d00e400502651401142e02885580d00c40700410102d00080c5c00035030f010440005c5001c12000e08115070780d100140403400c481c440d450500b10007040a41805080458491400c0780400c944007001041c1102d6041411550101c00c5818080040c4c01491015298500f4400c0e5041e03000b0301170701455442007070644400580314004d49401c0029000201c2103c00f204510307500080c424032080c0614004c2c4003d00390258441c204410100c0b4521038a4031001c8180110114000fa9440c1600319144001c013a5142903070560b11070004807071a01a0700002d001010140c0c602e56034a05400c4051481900d080c81211615200d0480541e6480480c0d500302000072003203140840c0d400740300342081d500544181000c0801c1a0560b001903110b000241400343d4562206082003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 423741007 1106 423739901 423739903
    0x210302070b1b030307080117030708160c08072309040206160c05030f010603060b01052803020f120702120903210c01020705030301031101030b06041206090c17 70
    0x13a5030b440c01e00000b40502200780140302c03804d2582043c10384440000000c5490840d00625007908211215001074101440317032000315040784174032400042114082000c2805440c0828003a10240d0b881800c40700d41c4c1d0010340d122440ac503a1203062001503180d410407555000c01c0d801409150b20348604022040250603480541c141c03051850f09484000c041d0f000d21b007941d00c6080207200c4191410300454480c02601440f0000b180a002820883c0384c410a5585007810681001350600b9880047d6008581058982c0131807040403c00304080154181321710942441d00e5040035080141e4840801c0d40c1e4440c24010342c03007009034000c04a090f540d4101c01da07081d82004000a540c4c0f070742640b4029489400a03c000c490a081450131500a0740c002d0007480c8600d200035007d00e00f0b00e8507250b04a104100e14801c141c810590301c2c814400031510200f1000040c0c015890003031404806c8030649 = true := by decide +kernel

theorem cover : BRFrame.Cov 423561151 423741007 := by
  have h0 := BRFrame.cov_init 423561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 423561151 ≤ n) (h2 : n < 423741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
