-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3896
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:48.349473+00:00
-- url     : https://prove2.me/submissions/ba605b37-7c6b-40c4-be7a-f94112b4300a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 700539568 ≤ n < 700719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 700540818 1250 700539568 700539577
    0xc03020c150106023c030915091516142802090f0709080106080a1a010b0f030a020d09060c18180c02010618020307122c012901180803 59
    0x207907440b00ea069810041d0040c5060a0070b2001c0041010207512030801172004001044d80f004212071802c18134000c01103480d03040c000ca000054010b28940300d000010f038100c0006e0107442001c000403030b195200781d5948400b5440001000c1c03859520404001c01e59200840d0300845000040c1c0200118260580028101800181c45184c03440c1a0402080c0f50f64810007019018040e00700082c412543d6589040766140c40d54070b030030344005e0021f4141101e40d64440190134100d5664800f00c50405079001d41200b5035900c0900001d8415502b04107d94540186008100e0f07114060000010a42012540580b5812a10b82d60f0815092500020301c100a00041c1110200301d40d0000001c1152000034240d0040240360007044051865040e4500210755580055100310703055900c04102e044641d01000a40758803402c1028109232100c140300d0101e4881940340081c40342000041605420030400d100d01c00d810100ca402c0d9000441422107035542c02844056051048900c180c02c281c2c40c16040383c0e10380c0913 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 700542068 1250 700540818 700540843
    0x7140f01030b030a050a050d020d03050408121017010f050705132705042d05030f0310180b031920012a110f0f01030f06090c03020c15010602 62
    0x19503220307050660303d0421038424040d42c03050440f010b900f0907003499641d032480300c0d14080c014400c400040c4401d034401d0007564003455000002a0402a2081943e641d000c00180b0841c1d500c40c0f03800002070542c84050088040c05d11400c00042d014059004180c00c0e145c0c01000703c01802801c009007055160ae500020007101e081c06007002034580c0301000300102300080800c80c1c4556041c0343c01d1006201281661750900820540c0150044002285c02d01608241c00070191164006221056003000ca4000866100c49070501021080d600d6035110481400000c5107004400c5d6a102012860b007030410402217246451607101541420350764840880d140707d130f80d5143e801300e088000c002e826401000f007420700001500720483e80c0880c100004010176540542680c5198400c1002c40300c904180c00040204080646102e00c114491030056001c2d155241c00d07408015079400300020148518403984610b09000c1d600580d8604402d40e80700e02c3c0407a1031300100350000101004000f01500018142e19850 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 700543318 1250 700542068 700542071
    0x610080a0c120218040c020f03070602090d200a2403090204020c06161220070f080301120c0f0b070b220b180c03061302032d07140f0103 60
    0x145901d00440d41600d591015086090020400100390a04801407912414003134404200b18079250404980e140f1505a01c901a40c20030411040031903c01e4008105100004d00441968022070307450390340610841032600d8800440708100d018628050100c00010080003410300340d403081e0704805c03c00340d51007181c3c450103065840101c0411901d890301600c091001d4003064904078035000385040411069420b640c400900c115107040da50b542d2900c502030040685880400e109052102d8040c03055201500945028240480c42c50014540400641c040d02c1390300c0314204800c48910700786c00d4105d560742102d5034010001505102e0700d01414251072185402032411390540c6c0304c80001070381c80f122048844001c100b408c1c801105004c01c24803014040c8112803140c82c9060907503410242c86000c541034080d07240e002100424040c00c079480c600d03594280020145d4902e0407651011902c882028042459134025880c04107005010910220000b40b40d5044001000d548180002d4210040d00c04000d0606 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 700544568 1250 700543318 700543331
    0x9040507050118051906080901090b0f040f0624050609150a0504030c08030702122b030609021c0b01080103030210050c1b331314030d0c080610080a 65
    0x44061095000c000d08001e0311040c0503241207403014851406034091440420000700c04035401050500c03032b4600a6030070240caa016030310743c948010f034013110180060361600950303424400071501c24807030440814080088180d400c0d00c0c401140c0502001a8801441410b060007081c2c4a52200c80800c0800300d0b00c102072513511801d140c01610a23006541010300344052501303012070142800000ad208480c0200c0f40ea00140402611095868070944440305c525003940791580c444440130350240c1c0c1107880c0ca003801f02e5460b858032495012030700441852201201004030300d41030800716204080d86c0d15006e1811580940c11918082c8d901c00880242400d01d5039240c000500000c04101501e640155461040780707003c000d140207035a126850381c00b600e2100810407050640720301d1100d0b0b6803041c1103802046000c5584110f110007406100034810f0345c20a1007004c0f41d01a00320140001d1090038202c94000030581c1c5a0b0000818040c401403056003d00b41c100080300d05e072500040c000b0b901050b180c1020400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 700545818 1250 700544568 700544597
    0x91503030f0a030207060b1c020409020102120c061501030e06070c1b090507081005130e07050910030318051f030f0518101404020625080c010506090405070501 70
    0x4501c00c440100c1c440d07a402160340c0240c164160018a00a4010311041c42507000d18402c0283c0c4001c1e00180317649038003d0120b80c03801418190844000c16005005861034502c40035244015540104417411840d0080c90802400712451001b49a0044c401e107000c005458005001d07940d994805010b01081c0007001940d40c3c10401c0800d810000554413050300343c1a5903480d070f0721401a00c0d080d034000b00400c1c036440000b40d41d58648400310f0100e500080c008410508092078035001040081160100d078080c0300808611501d07042c0e4001d0003110310034a0000d1440c9181001003061003038180011000d0b890030800c0000d6602e4101d01605041d44d0482d5007141c10007050250f005210101c80056428105410081e0862020050800d0020881e05880840c0d581c01d00c0b5a080b1418420300d401001c032448049405420420054454400715119280a01070703001c0d07181c40000c1782500115102000002c0044200f4028001d003504814255405900340c1130603550705840d01c240d030203054104180c14400f10706 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 700547068 1250 700545818 700545823
    0x2130e070906140906040b0c011d07060c0201051b06040b070804110105030c120106020d09080705060a03110c0714040c0201090201021c0e0a090209042004090207021201050901060609050102030702091503 89
    0x249035130080c08503682d59920102441d280c1c00c81350080a05510f00a031031428103070928101d50301003001d0303c0075010540c01c00806640318040c410040c2c2c100002480070700e2003000740d000c80407000c07200f00c40281400e00e018035028200b0003000306008104404802408001444080300107012002401e00c0c9860344d558821a0b40d081c0a4103902c4200e00d038651000045403500460f03c004a600c2c680d130b030b1984c40c0c2d07102c41040366521203074410690080c408208540c00c02c3d109174002500c421001d01e0603403800780034110443c50307c0100d81140c0004071000c6261000c0c0e103090f1080310300e00c501c180000d0002d03880603000030b500c800ca000340c010355104000e0f41c0341401c18801c0d5610711080e60000d00000b46d480c1c87d241a50f0081d00001600d80c022403420b049001041422400d0303013007507507100c20b0380b610b064200035051005e90000030703049800c8500c8a050340e00400080c01441d200e20301000c00060310f2850310b42c001b0b0450b00e25501107410354004200c2540507071110310019a02841714002400c3c0c4841e0400804d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 700548318 1250 700547068 700547077
    0xa03050303070309020111151512030d0504021504080105011e0506070b0a2702030d03050c030112081207050c07090c140705190318080601050f010c020310020d02130e07090614 77
    0x3640223450020300303404003030400180034904088401d8800e48800060010380c00000030056150b5009000c0e40c01981300c1504159801440a000e64407100c9070b1545001c0799800c55000b010b07060351600c005100c100c041c0020844a4080c65000400b41e520300004568944502c0001034803910140000401401e03040c1c0180c014000612000c180906681074420b054a000d50800c138441e004442080a910740300b400382e103000d181454000da16592820703981841c8903021070707811201d0309014010001c00041b01401c46104802e6515141e5590107110b02640c20b05040d508044142440c03d0428441e0030b038401043c61b821b003101140159035600703a04190b4902650104076048820351024898201503001e000d403410700c0610318102d4842516010241c0e20340341c00740a0143c12040041a0700d056600c00d0f50b501989c1400a010744290000d03104c08402071740d001250040d00d4503000070b60010b43ca400c0f800312000501103611209680d05081c2002001c882c140d1007045c0800120001c4a45a12100c10459 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 700549568 1250 700548318 700548347
    0x30f030e010b0f0918061005011e140c15070801090b041e0209040b03010c03090c120b070525110102191e0203070902030703060f050f0d12050d09050a110a030503030703090201 77
    0x10741151801011f1448481c0075809030a0014081041501c42c2c6107d810102129a4a5484807641d20f2001c00e01c00446410003480384080b8407a400004d1010415451080d02812050b41c0306012507041c40c200c07200b698601e22482e4001ea2400403008100b02d4505e07082e075070318041048096982ca54030f03070025028207501c4040c2d070b906529000a5a0209415a00041c00513110300e95440002d81c0d600c03040f03a002d0005100c0940414040c2000540da180300b4002400b2502c480c4041226484001d501c0c01c9402c6e10b00c042c01c03a45180740400001ca1036804115044240e036090003048409821a580c0c20040ca0101051450f1601106c0c10070003107580500403d80074044000d02151249403142c0700030050040740c07042c81940c800480380480c0b070303040001b4a5800390302c01505490207400b9a0341c80003401356162400b40104481803003c03013500300041c005c00201c140648000e043c0645a414a000002c42c0c2c21511445250444820000540e0110580c0c1e448601402c00103002d0071300d0b0005807030749090004031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 700550818 1250 700549568 700549573
    0x105040b19110607080c160506101a0c033c031b041d040c051c1b050a091104030209010e04051c090905060d050307030f030e010b0f0918 60
    0x105a001070019a8203503003098140d45141d920224a241c0d42e840d40750590382c01000402c1d00001551403000e41004216020802d036240c512518540c95a50904109441210009800d06400c05c0101803400e140c851240091100c9131420700844103d982d01c0c41888500c0c1c101c0e07a100202194007031444208001c11614040107650965840030550045070b20071100c01300d03100b0030000d50f411a0402035081e10141c6103020000001d02140c184041ca404000500c200c820b003604440124044e2940c0b030401c41c0640c81001101c16118440c9000710710714044820108608842100401c0103540d141c0c044411190070a01c001038602c400c004402d0b80344034580000c1d422460784800092108070ba804d8245c8198011020748803000f04050381524004640301c2d5440014202c83c034107010503d8503600c510740160300100400041005e540e141c0e42940c016075810340100f0380101c1d02022054050040a0700c2d22403400082114240b44030004a10800d1f540c080d60040e58000d000400001e00c25480c5201140304004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 700552068 1250 700550818 700550827
    0xc140a020a031808060c04060f0f0806040207050f010f02070c15052224180e0c0903011d061b070b0109050c21070210110412030c0803010e040b091f0b0105040b 70
    0x1081001f41e2240c8030790320015000c48410030402d40700b44d0200301014640d039608400b80c0c42d0b0f40c2c2004042d4001110030781d103d005409007281c10002c244600b62080c0302c18600561541d00314142107165180561003100401014841c5940c0030354882c048555106401c8203120b0f0101c1d0407040c040e0404016000602c00c206494000021605682501e02807885582d0b9401c1a005648140403202a614443c1383c9460b0040800b240404100002410705600081c0000070060190b0700c02c1d82800f510110000381d580c01c058188a1428841400e400301031001600c00c034901001c1d42e0300c1d402e00388014881c0702d40301035544011071a00203a020071298848a511085c00da00210250040c4080c001920420094420240c000000705907500843c10550f03607415405042519105d0142e210b14400b1604808016440220200103001c00014602800c0c0583c0704503114030386450308003251800640000798640c85a1241c40799031494840341420010415004580ca90b200c0c001600c1038000e5030811003000341d0202c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 700553318 1250 700552068 700552081
    0xe0c120426040f0b0c1b01030209090a02070203010c090e0a0506180901050129090d050a020d0c030c0605070822050414060405060a0506040614070204020c010c140a020a03180806 78
    0x3400a0300c01028100108641e260821300c0284140c001c0da02c20340d0800b1440f819104a030400d5840030100c181005450444050001040483c1c2210f2001801781e0214800e0250305091264142007a0282841c1b814039003005628911380200904205078651218009000390f02c8002e181100b210714902d500d4824101070221768040c11003402114088a14004054034800e8041100602d44d0070398841e19103016000001d024810001c1d0388191058898070983d0401600e544402140c003600034500903030382504620302090365a109504c00c0080100910902c40855105001c41d000846180311001182c45c1e032030345070036005045502c01c80c0c2c41490400c641c00c00f5000202030320310542088904224503a82c80301041032401aa000b080c1e00843c0a20090060600941460010440e8400101d04040c125800981682c1c402c45040c14141d44840c900002243c0002c0c0078140b10545c1108075040c49010080203686a00003003003d010001e5040e030b2400b0750031581c46a040940781400644045240c5a03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 700554568 1250 700553318 700553393
    0x50d0c050622081b010f06061b06200703030e010605220b12011508060f01060f02190f02031005010308030c070812010f03020907031112060f0d0302070f0e0c1204 71
    0x20451044e13508228100d900072501c0e205020956941da150200c0131194984e05c0c0f018800312181c1203e803195580d0660041454940c10a00626058034585650303ca20740703001002e03109070604030403032a0704101d01400a60b95294215540c0444005e99260b4a02501c2c0d04002624000410f5034000420846040c04050107401501400c104505440c04148d52580c000e642c0e800b0803110052200807510040c0441881060b800808400c1c510465040c12401e10f01d04100500c013907012540840d01280100840c02c061280c40750685001e00c08001c1585182c07500c021900c00105511400300d40064508208051003058a48000c41300301d40ca0019a158500714030a04640d00003030344525001000184038a00c030303004101c4082c0707155200606200c425a601007040c880a4102517010b244032034407441c42c0e00c4511000d07111078001d600501d0101e2400364400c08881444d00058400417504042146020001c0101e03002802540510422a540c50174600d03a07135801100380304081e80d4011030702079a08410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 700555818 1250 700554568 700554607
    0x6210b1009090b0604050d02090907030507062a02030c0909030d090b0105210a060b010e100f110c0306040807110303030408030402010314070c15020d0f09050d0c05062208 75
    0x10402c00c1000100395001c100d180e024520a0b180e120802140308401414031100854100500c1c00844000507126604c00c1c1c10041c01d07030441030000f0441c07044d04140c2700551501c074a05a001001d55041d910003900840e441c0c0c401e44640034000d107000000b1843c0e0003010011942900101d882c10407640c0528603140c049074500384101072080203003803401c03100b400781c407149501c074550360000130300a40010307641e9803000d000b204003181c0c10310040550b03440385038480c219100d025044a035209034502c0500003010f4403d00402120401c56401445001d20648000404a81064000f1500d42e09c94440380390280b003604030600d01e10741600001c400e0104200c0e0314006035004600c01d8030107209a10148000440d10101159030030006080d43c91200040b4a90140002413002a00405850501c12500f00b5040d00c50030400c07480e441d603940c41c19805110741440032442d0220180b500d815110303555107a055030380802500366038142c1d0b5100f4681d290a0704811402e90a1b5500007442a100c1c44600d0f1000200c260 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 700557068 1250 700555818 700555829
    0xd050901080f0105241918150c110a03060c050d050903040f06050c101103010801050c2701031b09030201020c0301050c030601050a091e0617040309090b0f0a030b0403020d080106210b1009 82
    0x1124102045231000390302c01410341015690750406d0074203a92100092038018140e0583c0040c030030700020020803440e009034070541b840e030748400d0303941d272039030240d0303008440c4000e050b24100d4109000511000402c1c5000808030398141c41c100d619101b0100c5403a082c140c0000c401c00c00b29141540340b4001e004403601842c125021003000b00720a64601c6268844e034414601c8070b901c140301c10b120501014102c2c0a844050810600d00055905004030349016000741c8020b001001c5440070002b00b045603410000303444211002c1c0d000703200d542402c1d06c0c14a0305000c06810b0318140940803a81518051058441800414145004882905d918058200b40d14102d0280c43c00080d425110311808080c01d000c00c030b01851303040c0c1c1e58039001c92425040340000d2400c3d082640d4800fa609100511a503039081d00d201c060350045c0804016812b01c2d1070064a001c10354540382081c0182800100601d5400000340d08403041d0701c0007026090401603442c00300401948288a51208418842a000b06c2d842490002540d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 700558318 1250 700557068 700557107
    0x902060f13080319121b0302070519241a040e3c030c0604170d0f0614090106090524030a05010f0501050715020c0f0d050901080f01052419 61
    0x280b00e14082c105941114030241030f05180306e4101c0305218820b50003000c21601440664440c00103805070b9109581c4228015180341c5031908201c00490010100c03400e0320411705004008605228102d51620014004441e10071969224072034a1240180040c1c40401c4050030250600c200d00c1e02c90055100c5102c584060100403003420141582000080720740200d4a08000c2500d030350359a803440840c0549420080e4040014419051007114034050036000c0c14542e603002c184507003402900007510344500c01c100e100340016001000040d4001c80c240042d1070b0240c0e11040070003a411105859500b4441a1030b14458000081084c152061b511041c16a110190707a00c200d144d80301c004441e10b008000b00039100ea40b07100342c00d01807042d0a5000b071004101e5941503408200010381d003a0b003442a000066008603000040203405580d0040d0b034030b64421020800d102e031950500c004a1080241c2d608030074020310308100001c054001020540b001e0600c40030302130351500d541c0d40d0300401000c0f40d46015030310107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 700559568 1250 700558318 700558337
    0x804081203010617090c0d050304092f09030109290f070207120c030c060216050405010e0103142506080a0c0203030402061305150306090a0902060f13080319 69
    0x8600c810869049030381c2950f031507080c80c5943c6503161003120f01800d0001c0034840c64501d14a1078990134818600d060040014644aa00e09900c280550307040783e885050303803044035503000e5040c0b940b904090800d00001c08225124210b14000c0fa0040090400183c000c3d100341e03070090000003c090b84500c81e0010029046503d840b4014030400b0342c44d0540d142d0f0056001414107100f034489405d0466034840c0100500880c44e55640c841c030f16201000d070401c8006800100402d0b400481d01c900d0303403005102c00c0e50100915854090162001e0302d040c0401031910140a2405240c20030030001820500003000d0045880389161070307080d10507442c600c5404040f82d103003070000e440c140303039441140e6203102c40750003440c40c50740d4a6082001507405100001741ca0311000601081c203840c2e083c40e100da455801d000e42962070500c0300411400b9400100701c0c034006e50610b4800b40050b1a0170702074501070003042808580b81c900c28600c0e070000250f190442c12181c400894022014024480344614011071030300c1c0e400c801c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 700560818 1250 700559568 700559593
    0x40e0a1b030e031902070b0304052802130203180d0306090c05040302030c0121050a23060d08181509121501030312180302010b0301050a18020f030a0f080408 69
    0x1642c0c5003048501854100f4070420000d0000c0c0c00711038510851901c15135481c6170310341030301e1034140d0800c0d135050301d4a5008415080e00801451888803044095405510f064011a40051140c900042010400b1030f00480490b4000601543c02240c0040c088240c40c00400d884500800400080c807485011b6802c040914004038007540440b01a02e8000c0c0c0501080640c5000540e810206401d0050001c0010000c07421081c0140c03003414000d01c611480400c1c00d008903a140380b0288950444010342c442d4180030b110b8642d513060b0082246036440007a140d150660204070304028094003e142d0342000004525a1000010782d0050880c0a0100d0303105034881c40301d2601c10758a940441c0707180b900100c15001480420301030a05100203c030305800c042620386029a01c0c00d5600b000580450250f9110502039459142c20b00441c0da100d44482030411059100c5001d09403600584200079006020010480020b0348050000b01d01141d000300a0803803150283c82c1c413200503030203031248466501512170743c6151b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 700562068 1250 700560818 700560821
    0xa120506043f1701060c1104020a36060c0204050a02122814070801150903080d0221040c0b041203081509090d030506090618040602040e0a1b03 63
    0x1c940625007540c02c1102007900c140104000c07150a00c50038801002c845441010f4644207584c081c110700c0c0c0d03403030001000d2460202c0003e9114240c40e071040340148890f1507041d0340150801ca488890590b189418490040c403c148138020018071070f00b2050496000c5846a0424004491244262000c11159481096081c100e000380c0036016550400d81c1d000c20102c50500d45c08034420082010020f50a80d0b03a20140301c00c5841408a040041060404100704e4130341040000e40140071f171f0009070b003100c40c49031002850f84080b400010211440800d45500182c8103905865014001e0010300d02d020090050052200404035030448214003409000304844a0490644d4100c0341d203108150182691503a0584a03004010f1458041142c0c03042005504d0752441d481e80d0007036140d0780c040c0000c40f400480080c08d079440200b5460103007075144103020b80d6446011150121035a200441a080c3d140ca1804401a100b241c0c41036500741710b03400c28400340f02490b9002c004c81e880c280181008040f0120700a80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 700563318 1250 700562068 700562123
    0x5190e030a020c0a0f060c30031506021905070b0f0c1204050108072001090b070210090b010306021c0203100510170424140702061b04140a12050604 65
    0x10705c904e01e0b41041006501890401002a00c40d03070b039480c1d110380321641c485a41e08013940d580514648035140142060b42520522001d029031240b460358031407d0040117543d9098040440050103c01c1480303009000c814444c41024024031071905582c2c5145408006840d0080c1c4032884d900e0003540031006003081c1c2a00ec8600320358068482d60103980d20f001c01602c10030036107a924038080817805000c43c0d20043c02e214110480c0d00c44d500022050521590080c0762070300000e02c1d90711a62070000607801048415442ca811264010005070352040001d2216101c102030024401c561400401488050101c41c1884001c1c2d0340c003542c0414407240108403c40d1032020508040f015034140d031000c240030030782001000e400a41040c036002d8030080c262f002e0303108403007102180401e464243c2c82445445513041c0241c942008009070100c540c1d10144801510074405c510a0180c98116100400b49940b0b072800700fa0300503d0003442e034135114096800c02e1501c4001c100c4040f01c105e002e9601004d404131840d15803c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 700564568 1250 700563318 700563329
    0x8070602071a0a14070c09050603030406020616110706121b0503160e030a14010f060803120402041b0309170a020703030804061d070e130b060405190e030a020c0a 71
    0xd40b4400040e802081e40740d40015030860400c1107034003010340c1890fa80e0009110b80e500c259003051180b440d14400342c08589000d010148a504100000c12203242d001070000e0700b0600c45404a0501c0742d00300300595420f5880104c0101602400304000381305034100f007c210700960042c50074002c102c22103104064246617070a22401080c000c1c070201c1c02000203500e44900d00c0185040c0030014100d088002480c0084185044400ca0740c54200e036206a00c0a000301126030746080070500c001410700c1581500c3c5e0041c0c4101c8944100c040002609540c0c50340c01100c800d44003803c2c0c0d54000035004000401808084809582c4210b111840d400150340580898000110b164041c011981c11a502240e40103030140090b981c1507259101d485410144420b8620050840f200810840b80b6210b502c4007541c00041070244022104207850740840c4120502c02d5220804581c0081e0725920083e0176010359000749036114601e8074020700ca580304000040280300381c44282e000c0f1f030100c180f008108081c500702070150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 700565818 1250 700564568 700564589
    0x6071b030c0809040f11090a0f030308040b13020a14180907051908030f090306100b090904020d0506240d021003020a021e0a03030c0507050703031b0f06060807060207 73
    0xd290120303940101034643d02a006102140040920360382509a403041c07040200543c00c0091542003d280c10070289000b08080c0300300344412480c584014054103001003003d082030460384002800c0850702c01403c03001a0707005291201d4a62034500d030420703c020441308140946905040000900c0080c0401d500c60030b450002044018141001e00c08424003610540380c5034815003001050042050019204444039081c1042e240c1014000301480c0500103020f40b490310f420303c1024000141090201c1d01c140d0000e803079001c000c0e29680b001ca242507440f540003130303e40c4c005c000a02c5002000c84049502d010301d4520a03e4048e45170300100714a00650ba1742c002e600c00409800d829150b8001d4001d0001a1310b2401614841c21380c40143c10075412494101240300d42114502c0410150035224081400c0110318244d8140103096413526a621141e000c083e007480b078140b4501900c22088201c101d0a1580903002c3d1044552503c1d000015000c5401250041c2c011072401045681c40003495504943c0403462 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 700567068 1250 700565818 700565837
    0x507020f090f0103120e120307030215070f03021c140117010b010822080c0609010533031002070803011724041e0812012106020d0608070806071b03 65
    0x20740501030300c1502e4212080c0461b4003401411965000741c540340b801e6040c3c01640c7d4410701c0d890024108503030965009117103c40d210a000c003169201080b0908490281401607803800148805103500314444880403043d07040c8100d010440741400c0d1000c0c100c5041c0d80b041d481b90084d649116090310718241b0b0880c00524001e00007031052408408408203840c46400b41c00840800b62102c00241c0d00c2843d40000b50ba100d0024071000d4502485040d5220080d40580e82440c0301008040e41b40030345c90404201c401049650b6441260340038440440c60ba81e0310708045648a0041ca0080c89039002407081c25000b1482241e4030901007000329502c40102031000d0017444420710507480c16040100904191201c502c40c0000000f188044507042820500480c102c98403407501030200042000160000780c807088104100410742d000060610300d0a5a21420250f180c000d0002850300611455028107550302c907031040042d4500002c076001d4080c500c0c95032000b4600c0d0010650070241c00000c500200040d11314070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 700568318 1250 700567068 700567073
    0x4060309120906120510030501050f1e010b09010f200c040e0607052709070305010305190507092a08010602060f2203020c030a030801151d0d03021c0507020f090f0103 73
    0x3d120503032042d80c01c4840c1262507182e45502d0308440f0100c40b00c02030262f8002c02e014035894100300712010341c480f2080e40681036040614544150207150042c44c140a443e5091182242c010031500c00c920b0301441d008070a0070702c1c8050701681c40313404883d024012858081074003001c0101088542c4a2800754036842d1174042103003860180d010400c0e80c0b10304030400b0102c60310801c1d0344840455001d800f007581d000c40c0c0c950450a140707081402c107d044410b180d00c181010340002d2030125a08044030030f20280081d1400100251004898050b00d01c140c12a0b0301d4840c10704182d410210b114181c0e161039088660300d07a1188940021382805540041144003400d004104500c8a1001031100310f01c00d205540764801101d0200e460548810812404104520010300003402d0039082c01241c9c03140e501d82941c6e10100c841d210f00420f0389200e22a030240345690100c0e0103050080000407500c4005209007005a91600401002078000b00c804078400c89034004a11154034004440c030b8052800c11012640a9281d41e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 700569568 1250 700568318 700568321
    0x30c27042a0f05070503030a0605040c0507020f09101208030a06060c05030f1e0d0e0c030d0503060904081908010603050a020a0e0f01031d0703143f0406030912090612 73
    0x2600c08001c003d800c00949000880500145018460104000c80c80314104020403050b200300c1462242002014489507015076100c2110103490300f4103441080241d11010074211041c60540c2100d141c2194074a60101040050001544250084903042000640740c10701101c0d40c4031a00340c068a01e40c018012181180c02e4000100165000b103461410781484041162040741c0003582c44c4c010480e641c080510ba0b0314414040c00500440803400781100c240c00304006042c1e808064480740c041c1410000150030058018121148684620040b11140070860740080c403500c802d00035440040e05010205981036000d00945070120000c0c4c64664040d00d0348810300030001001c201e524105030300c2e004a40036115805442c020b43e0382d29100030b86401419411301c0348200051500e040c240368070000e011035110601411060307090115050301030030b0004507010181c0440d11240d4105a5200011700021080e800d62710030300c2c040740b04620034180071031600700517100071107207110703e4011461000e810342e0f00da1200d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 700570818 1250 700569568 700569587
    0x61206120c06140904050a020a02062a090607171e030c071113060b09030c0f15070f061407111618020d0606171b090105030c27042a 58
    0x3c0c0c00c04542007208a0000030240d44066405d55611a800a0640c0c00a0b605000c80c641c4039a900ca100300c4a603a80b041c008203865201c0740c48400d00324003c03640041a58a40d01101c049a4001410301e1011001e10080003566000402000c0241042c4020031326041700b207001d481c4034000d10701d18642052010340305c090103076002c0c1c1601c69014030074211303050074076000740b140c0b201130030151103942c9d103581d052800d0518100000c00c41c0c0f03100b40c10595a036103807030745c68001e0b004012100490f0b103601c3d016140b800b401510100d840042c0618148071a40068505c1c001c4c00a01c6486660788040041e40c000d8440d60301c4185221015419105115082c40070229102036450300341c8031840b00501d0005500040c0c0300704c0740242c101d0000503d03076440e00c40c580c4071000034035034108110011008031210584a80401d921501450906011003c0300107501031002c0415a1081424016142c071030103005203280030541052041c2c4c51065107043c5104001c1c95036044200512f0211208000074100010740942e10000c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 700572068 1250 700570818 700570847
    0x140604060204171b041a090106090602070905060307140a030f050615010806130b0a0909050c01020f031204060f1107140d020d0806120718020415030209010c11030313061206120c06 79
    0x417401120542c1d0700c47c1c01e5880e00819456540c41540760a0000c0281400b00c8c2d940a007400c0c504242c1881003030341d800300b0404101c5402c5035507002804207417004654140060781c006000d12034042860317024800302040399841015040301c0b402030007031301c0401500d442d007082c7c0b065508480448041680307061075510508144c6001002002d1032582d82d190403041c0d9890038005c84054100c1100c1188558041054080400c1410043c5081c81001e0070f00c0c2c0039080000704082c01d60794803406054214440741d40710504840f42d0100081d50fa0b41e0307a09114a050082040c480700c00d1042160b50480e052021a9020740b550403036a5080b80c0c3c3d110001004000100c5101141c80c130b0103000c07000101028030211055151980c01005030f01c492030009a045e01460804800d07080c14010030002d0000e1b87d014654000c41980100c4a915000c40d4a000c42d00e1400354090f440500b00c9003c0000ca45c480d0460007103c80175040c0f40050105e1610340090700c4c900b00d88520001c19010000320b0030321405004000481917400e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 700573318 1250 700572068 700572101
    0x8010909031e02030c0a11191805060d02060f1321020108190c080f01062607030b0405010b040314030a23130e040210080c030c07140604060204171b04 66
    0x144099002400e05091b4401200e80c90086401c04469081c85040c0d403000f6103c030300c1e01c0a2581d2402c0c1c0d0f8208c400c41c10949800403549d6a1001468540c0c400c151240c641c1c0d0050280c94613401580001d042c40e134404148241d62142030200001c0d035140c100005032803030814180343d805291840c0d00644941c00c0c043c0815410b110171581011b017124046c4150451150141c2d118412804c003511350125048040e00b240007001300c914141304d40d4403009071081a81180b00c140c3c01c040c0e80d484e5102100101520030700b441e48103040c20000a40b0300c0d11200a4002d03280180c103001040d02a483c0c1c4141d4a10400715884045803050108800c01c05050b96406083c01150042d14645184000759000707054141c2c0283c91165034441c144425814502c08000c3d103907100f41402482402c2c03051020b80940401444041318400010b041810040c2c0000c0e200e203900c285a00702d8800741480c0c900358010303401a0040c4161a0401042030b4018540000c00d591056222000d040303070250310b80180000380101c82d28440856 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 700574568 1250 700573318 700573327
    0x30a0c0303020d0218090c07050705010e12100e160e06060304080c0708060f061c08130e1302180f070507061811040c02010b01020304090c11070f030308010909031e0203 74
    0x3d40750004002040070b0030507481010700038504005076414058050303050804103101d80f400203500060344c44165502400d112001d1040c420000700d5024901d01c0341050b5000704107003061409840e0f00010161004482965203a40403842d030078610b141e4500c900801481d140001c200542020002183c0041c01140ca161401c828500300a2516840e0ba010007101d074800307020030580558040038030f50030440440c2c208201a6940750006103156510700c010f07007038140005240400c80d1002c12004024052200100500c2c64030841c1d802d0a0226400c00f41c0c029241d403000e046040c1c7d40ca03940c19204140007400e00d8a651a41c0304102c400b9000040e0440d451681c51007040d0308c5075144c1c001c14a11910402c0b1a0803641008002c1c00309880a01003160156810510070314106c0e0380102c1541c069401110b030004000d1105201215410f84280f5071101e0303802031030f1000c110440c4240d81c00c0d007503a00944500d0810390365a4076140468055000c0500000c000d4070203018407102c2240310403546031440c8100d9050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 700575818 1250 700574568 700574587
    0x915140a0c0f0b0402010818031902100e0a05070e010e0a0506030a21091707050f0a0510050a080903041a0a0903020910030b1608040221030a09061205060102030a0c030302 75
    0x105480b0000c20744200d24200104021580e016002583c0216039035800200342c422100030944e03030b00a0302d0300110000940d41d001303607800e81308104007100d001c2401414410f00d45003904240c1c844888a4003919140654980421902c0401d410607040300e08070302500489a03241d00c0810028600030740b031941e16000d04220600421030041c4a240311035660010f044104802017009401c0d9000d65000385071240905a44012403007011540c0012500305170f0742c400c402c944141c005414520345801050b4000c1400f8400f40e001680b02c0054030990780c440d291103015403266401280d8a00403849a421500e84141c003e4111410480203454a42c01504225000c5a101c0d4006800050222032010724445051401c1045c02040c000003500101140c14a91461048001c001c045040041000e40110000740711100341820607440070342c44d200d841058039250313800070340c00a02e83c0c01c0c80d10406002440300c208440101000348107460040c0c0c0140c009514011b048401521020b91304002541031603803c5c4070003100b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 700577068 1250 700575818 700575833
    0x20732010527070b0a0e0604050406030305121806010302010f1106010b0d110c0d110709020a0201050708070201051905100503030309010608120301031509080712020d0915140a0c 78
    0xc00380345031401c00e240c1c00b0070350312101503004400c00c01966200380c00070400c4000c000100c4010110310b162110034a140000403420307030321483d40450b07002450f203030000040c554013001a0640d038140044500254a9502212100542c035009407810b1703030801001040158025078807604208a241486000305d8065102c160820802340c5c89036045a00016401070184994480c1c409035810048601c0e04016980c0c031100d40d281c5400c0e400074140322944d4440300c40303480c04001050082c10020b20655540c44d20600080c043c080c01d1b035480012495100228152a0040c022030784241d0340d001e1100301000c0c000388104c1c098074000d0418000e0152210000c00d60f900d00b480154462681000041065454034a140c1d15002c12940b404c510900140300500014a1202c9481100350141401150306013490401144620490100604105441c1d82082141e5008520952451426160510303800d03600c0c0306045400e0031001170840090240200000101c0c00c060241107001a5803411010140030b40d0780310030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 700578318 1250 700577068 700577071
    0x7020d051014071112070203010204051f080c03040f03030c11010e0a0c08010b0918160603090218190e0c0306040b011401030204121509020a09060801050a0207320105 73
    0x248581e1142840d0502490000202e9005042481e042040c0104c0c00043d50b00c0d05c84888814908510002c0c184040d59025010b440140c40010301c1d0362003c5140358054004481d41e5820130001c02c94074000a01a4220341095a208541140c0032407050001640c084008164095109090250800003001c1c082002d1041d440840d035000c008020503440d82c100500d03010050303804640b041e0f041024140d02031301d03502c450940001a1940381d44a040040314100d08010701c05800030a0601e80400010356903a01d40c100340381840c02504c1c1c00d2051240d5031b00200018000b102c20101c100d86c840001140040254810710900e0842401c5c1d6100f5101840001d0405000303440c1079030b100e00d00303100521410300c004c0e081429402c0709080852800b8500300b82c01da000c0980480280c204000350410f102c0a4031b080c1c00240c0b145074020101c1900503120b501500007000c040c00b5540c415880c160004400070f8151003203880060308284006101d6101c5140e902e5038100365100065030f85920070100d10006030901425 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 700579568 1250 700578318 700578343
    0x3031116060b0f01020a0b040303061a0306010e010903030f050c0114010e180a050d0807110a06020a020709020306090a0b1219030305090309010f080a0207050a0b0103051504080f07020d05 82
    0x2818118441c10010150703051080824031415a144100e01c07242e8001810909030759100b403022142d80d8503424243c0080070309900c4502507840000160b0480d9010900840c40340100b41c89142c500c40142004607414005400000d0110f005c1a201004490181000d44601400c2100211300000003544d2002c881c4400c0e0700c1444d10301c01e0101480901ca58402c004405c0c500804020524850b90b82c41c1c295562088a140d2002d21061340c002c41c803c02c3c45452031551035a0608111040c20080b441c02c84000d40c427907a5a8001402400400b00e5690954021031340110402801501e4039211142880003e0a101c044e40f54007011842c0641414034050284d0200e10390700c08c0100b5481d03c10380c18040c1c01d580d8024000110380e041007003040f0a903131700400140d507904c0c2d6514080c0c2050365002c00c01c0f4001e2184150160603032080c4020202001040d0544038140d134032031015545c0100c40013101c030300d180009642c001c090800c14018600d101030300c5005032007082d00040c8082c415078640d8a8290900e540051034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 700580818 1250 700579568 700579597
    0x40b04030b010f0b191b0609050a1b0b040506090111070f080616020d110c060c161406040605031902070501020a02011407021b150c07080c19060309030311 68
    0x420000c070302040c0583c000c2007000401490070240001410452050018181c1400180038101c40000c1998200000c1d540e0300c100c007040810708505110755100c4400b80304a40381c0c0b1100d0180c43c00000c650f8120000ca40c6040485400c4c14201000c00140c0d40010b19414108659400c181c0d102020410401c0c009180ca40c148500031800d10310041c2c2800c0004100a94441c103188910500a50002c0d80035a00240380c0307460320f4500101c1e40303074a02703058050b50a2a4008404645044130103c003080c41d00d070700d0039042100d003e8255511200b84010750544910f41d80180188010007046000e48010f42e48450318218a68070260704034201d030200d801000f400c2c0e90581d400710b10b0414140d024030960f0140043d0342800c08183c600204025034841807059074103078081e8901a140034075221000d04041e07030304203117541c1500d51710b000351003903512000761207807443d42c1c8640008010b09040110507011a950721107402c0d50202d050010590260161120440402d40d8590a00903150810f0f0003800403111100300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 700582068 1250 700580818 700580821
    0x1d1905030c0715120c0c08180a150207050906030c120102220509060a03240f020309060601090b090901170c0d05011b081302010c150c082203140f040b04030b 69
    0x41c003c04c2c000748030068050807403909010545058102c420f005985a0041c41d00d995804d0050100c1e445010780004180c01c01c088800108684144400103441303149613600300c1d43c1d0507943e0310421016440c281c840a405030007609102445d404c0c4950312a85002c459000035150540b604800d220040c264860b6410140c0071110500c0326141864200781c218204441c4d428020b411902c86084961804100820715540200002d030002c405400c030070303882d2400500442d102d00d403086000d522a84e040f01e0a0380001d540b1000801e186064000b42c5003ca240030b0898401a824182c1645a4520008000f42c01c1e200d40600300900e40d55002d1a008103611600c0080741140204556500c10990602010306120045040002c0810300f0b450524015070246450b050b500001e08209500101c841c102c62460780c20000900692900300c514240100040582e0300b0440044185c0400800340504000340042c9644100280150448024050300e80d1207108162419a03501c56141a5511079031045444014150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 700583318 1250 700582068 700582109
    0x16081b1c03230c0a0309061509060b0313110d05250504110d020d0b060c01061404050c0d1508010f0509060c0403080324040f0207061d1905030c07 64
    0x91511160144500c803070068580c505611180c60000780f407180406808541e0000c400d100e5001246460b0b00800b04200109034504190000c1c202030055403501d6007004800508101c074282140c0c42030000c1d000b08180c0426a903603034500b0f6103140300386581c030a00c02e84608012800c2440b00c0e40d1585036209249034490042c0241281400c601d0b441544110b18050445840c3c1c80548101c2e044490400401a0744003c140c0e103540092800c02507440d081100440e00c060b241505610010650f48030401003e2106000400c110980e41f007100c401000301020b00c480c108011160f00440301d0703000c0c107041504403603480c0c078240c81c00c4510403046200040c0d100d4042c42061501804074a401082000d40c0d0ba181c2811619109410301c0083c0020480b1003503a5801d02c610440e8180300102c03000020400d1294801000c1d044019401c840780170b079511490809006508003440a50b00001600c500203086403808008400d0100c03030000109469501040090903480309081c800340b40586081e4003000c00d0f004494 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 700584568 1250 700583318 700583321
    0x201022d070206030a060b0412211d01090b0d090b090d022503080a03023112030c020d120906050c060613090c03150f0216081b1c03 58
    0x8002109002030003000020021160404075610315405030f85250b6130751119000500144901d9200500d4a80301180c04101c042800102540b01070181d05080e940030a4428003240078801c40312080c01042d403003000c03424030f11090350740c8a031007060504280ea000ca680d040090226449a50220500743d41c3d21442c00400c5400b200103030300040b01c20000e10b1a1048114045c0d500c100c40001c241c42c00c4840c0b0b0403044001003d994003009141d11001d4182c9a41180102501a40024071640e4266100c10100e440008030191101d108260100400480c18549602c1d003101580001c02035003080a40c20b150b03009600ca038010b041c2a00d11541d200400c1311b081c200020070414494201004000c010041465079680010341690000c804803a800c3c1c480c8031900103d4010310b071403400100026582c0400000703008803403464001d440c0655000303100b80742d116030300d51080381310751100d0250107424507403001c001c540300c08050000044c109400000040b0036016480c504000407400c500e50003100503030744590303e030f00d07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 700585818 1250 700584568 700584607
    0xc0708010b03030703110a0503070f0312090c0311130204030b160c0302250503060f1b120103120c020a0806071b031b0203120412060b0d0503070b04080415020102 71
    0x120001c0108900d40800661248911a001790030403501c10045402c01034103110041d4050351003401c4982c0c03913055152400f1600182c520503004a0b01030302e00390190954600815401d00d80c000546a03d00f411a51003142d02c2403001110350300006440f00240d124680c910040c4007440c040c4d291201c071441c00d510402d100390b88941340103007044560507460300020b400140300e040700340004c842424103810f60002140480d055920941e0b1522943c4203208096102c41402d9004076003030f1010603945030564a54400c14841c00c4482880404480010000f140030b071000c5203403512040c5054951809203070001030300840b444d001440e00350002424400c401d504030082c01000020038425803504030417a00c000c3c10030030000e10100450043c0441190071560288007048841c100510350700c2e1240e84481d002c11601550140c100c8420740740c110003e00524003c00c4848543c1c0d880b800462801845a98900d40064094400c8941075070a00005c20b2100440c0d4817010141003a900060301c1c1c42da03038240300031011031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 700587068 1250 700585818 700585829
    0x7020f06120c07171204050c060310260a05030a02010c0c0f03080a0b1e130e12070804180212060d050c1507060c0503040228092406050c07 61
    0xc0800901140c806951011a440605030380c0840d1185410b08280012000a0000703903c07810000445000e06081450010700550061045409170010401800300303e10050310100f45a0030030400c104840c5c03201540c48441301500304004402212003100007898000d90a404440381e800c0400c100b680a582481403001106452600100c2611380c2c0e140d00002c10100d0201408008920300018200c1e49541c114060800c0050f0140c001281003484504030303900010480340c80782600c441c1c4c0c1c03d1101154080e040c640c0010801410310a4540000203403c0c0d40050000c503081c42d824040014449005254072801051540d0302503903a8615400d2008200c500409451040608280b40404250000380741c4040b01010b0b19000360040d000c044484060180c840018601c0e13040032844400142c8c02806540601d100341e80c83c012a80741d5a00100d1001101b142d580110300340d5040400070101160840d082483c03c0020031050301201503954040c0240680084010450006074100d034110200007401c010032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 700588318 1250 700587068 700587079
    0x11030301060c030c02060912100b12030a0e0d0b040606060f050c0627011104051906022d06070c230c04090606080f2514190b0f07020f 59
    0x606100c00a0400b40052001908100c450740780c0104549a40044424101c802070036850340c40c5031702c20095a280d12440072a01c03010b081c0030104600342400b034103101d03405510401440c2000c4c139000044808e040c5800c951503000ca01200c1840100c3d40b211609405a8090b02c0c0100d500c5d0304111002d0050704450701200c081282c2013201d48066803003c40d601c1d030401c11503c0c2c00e00044425045402160b01c5282c00c0031034a518002d40108a44240402401190020740b0280c074820360301065020822800e11030440542c03c1a11005440505019100500003122240d812688900254140751040031914074000c00c000154031014441401034061034590a26901810f29113070010154650390020201c50048e501c401b030702010400070780c0041d00641480313000c403038104c0d41d00c0a41c541c0d034260320b40c1021141c0c9480388601c0741d6070b041c00301d14000340c2c0c10007110070250210100501c0403a541102c003154001043d0300010600241145c010200c64034800c44907500c46400f0300400a200303080c5e02c00b140c49807 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 700589568 1250 700588318 700588321
    0x120c07020a050a030b24060f1c021e03040611160c1a0d1a03060f10090603030f08041b150314010609060f03020c15011403010623011b12110303 63
    0x80c21780320801d54030154030003440d0305501208803038030034018000d01e01030303072203000031500d02e030460703041300c0a00920a600001b020078541f9114811049105071071300b454036603942180350102d02c450100110780080c818880004c50490082078040c95401c1550750000850800c040d04060045a19181025282e8000400440014020108018031510014800007034981c031984074407098147d86001d0040c0c2c081e0a0f00d18600c2c2070000c0c0207100404031481c250400710360300c0204032003240f441600e080d039605444143c030020103884240c0792050020400c0300e401c001c64800d07a502082c290304c44001041017175034600880d207040c034028042e5006007443d0114080034900410480b5445110601100c16a0410711018804060100e01074400c04451000314031518003005000c042c021801030489402d124400d800750100b204043c00d84100348907442c0400d0010602e0414043d103402d284102040c14108030a0300c040f443e6200741c40901d540401d6900183d0804d01c52105038000d40420709801480c0007a5185 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 700590818 1250 700589568 700589573
    0x40905010e09060c04140307080a03051b03090a0302040b130908041724090f16050406080a0b0a050c04030213020304060c09030f06021305062706090607060e03120c07020a050a03 78
    0x550059204001b150320079003001c101c0ea600c1c28800c11000c0c0c01801e068035402c68140c10042d01c84d0f8445203010840c2074072508240c070502808005d546007014024903154000d8956000c0101a00c90750850036800904400c7d0540841c031070740304640c0c49500c6100030701e40343c40c60302d0741ca81a8940b1504100704903030080c801400c401c2c000344031507110000d41d07001107c400c0e403203208130b0310b2a04110301e11403411481f480c00c07014a8081e5055002c812110220b9041c4002611600080e4413000300800c010111180346001c242c00e5001604400da100c03502d01d40f8907090540d650006024800d08254074a0000e80c0003040c0b006005440c09103008031051410014055813079a9940c00250201c1000500702c50307404100019044506d210b110002c043c001c080c01d480b19140b501c0c441400a8555407000e45030025840a00203041000c190703400703550018407080c01d258160715050054400b0404c003031204c3c00100040e641801c140307a11540500c82c60030269890381400c0c03061010440711a04038611070704849008000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 700592068 1250 700590818 700590841
    0x31104021902013e030a0e0a03090f1a092b0804090516020d181d070f09061d040f141608040213020a0201140106050c01060e01030302031617040905010e0906 69
    0x69900220140565941d14a4850390091040040509a81c0510640c80c000d160f07000c0e82e85010380d880504144d90580d13940d000c00443c0108cc2c40c080760412014002c0c000300340750008200e07585103200e2440b000075508040e0440d2400b9900306040360401c00200302805003280300c1c030807540c1c4400c1400c2900c602040c00341c006980c80e440c0c101c0100420207513442d502d40f0001c0c9890300d0002042590302110b01c4c1d008800e216107110b842207498a0000b0f9407100d16141c4035104100850032500b442c2c440890640310303540320301c1c00425625620341d0000c0e151268440310011f184074014002106c000d1a800d90b040103455045000140c14000741007010359001c0c040542d0382d003401c04024003403040d0010b0340c508421a081c0d01600c1c14a00384006507407040c00000340345801c200241039801036000200842c1d920344400c009134031000e02000e00103034018001a1464103410040220440c090030642010b82866082c44015a2040e00011413480e01c640040051a000c5194190007010141c054100d6207801495640b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 700593318 1250 700592068 700592171
    0xe07030507030b040f0b0709060806030105040c1a07080a0903020a0e07050f0d140712270b04080c010513020901082e23010e060a0f03110402190201 65
    0x200f002e4000c01c045420000d4044190401c180c0c80981c0740d0381d5240c9520090a081428420710000c69039020000e076481c07074184506c030700c20360380100d280607214140a60780c801c8507981c0072110380f11601003001102250380c46010701600040c0d95603c90307040d030442c4103105d00d000b200e9011180d00c1760b0318814450010340020075120030500351a8071b0f9480d0018005614050900c0048808200180d1018040b500e80e000090b0341c08041d84c10401d001c10002541c2420101c5c166041550441000f05402030000b400c080c90b85030400e0249001c1402c0010130450142100e2041e82c45041c1b00100011840850801c82d021600401000026024075040c2e40f0342c11052803500040c0152480f80880707600380c2c1144952200d400190900c40020b801000c1c52952903010000780210041242d00200069052505100804c150780340318603407400b45440c41d0340f003003400c400e072007407a0758825024407201e61140c00d90459003a5041181e030020812081c6000000009054180840202034050300d00804000f50301c0b1554 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 700594568 1250 700593318 700593323
    0x70b03071e0311073c02130b091f150503060f1c0b09010e0307120c05010605180403080105031b060d06270c05070f0210170702030a030e0703050703 65
    0x20440314055408800525080900085500b4003042c2a818080d40100541d000c8104c080810f08002d890303055044c0c03c5e18044408000348010102000050614040e00031709002c0c003100208180900e0f00005050701d00c2243c1102044c41100103030507650508000030002014001000c1c0035403030022800134614030000340500c6c05481408401284ca807541041400c903071840d032001c1544100c96240142030302c80300752403003400b96090601800700c1450200c00c40740c0e6194040c01c1d9280c4000401000d8a0310186000c050791340355a100d90025182d10b0381c08001c03c2062040c80d90451501d2300d07203409890f440d01a0441d501951104100c1f2521412075614040074a41c201d81c0251200310246442006e044c003a009055800c0c8203100c040313024240b50711060084202c2540c140708010828008442c80c0c01049009001040350801400150030b02004003061078409140c9940c18014541c035941a5a000ba42c41d100181c0c4009410800142d16110700c414842c00c42001d80f90341455611400e60b1603280340401b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 700595818 1250 700594568 700594607
    0x30209040212030307020c03150f0f0a020403122109111216150f020105040c0302040506040b2d06040b0a0f050c0706020102090108061f03020d020d0f0b03070b0307 72
    0xc981950380e64103003118403140910840b0f90782c1c0313070056000752140300302e6481074024801d004590304c486090309045031041902007408245551903a401c202900d201410600c101d540c204808004124556007000d5040d482d0784a40f02d1402241032024400c0b0b0181080b030000600d01100c03880000c1810401110541003290300c01c151021610810303042050410340c020444801260026401801494107242c480b030340c3e2140f080582c15507106034280c5804544c000c00043d0346a1041c0014a010307813046401c1180640300140f081c20440100c0d09030144a10801407840461814810100072407071055004d19003524094103245c0703005180340550140010b00b02c1400391180c005842d4a1180b400d1f03406034000d04045801c071550710240603000b50b00481c3c0e543c0c0000d45070310006559042505040b00802c03410600300e4101c180d26030089000350481031601c14215001c02c6408090700c46e90007100c0b14441e0491000074a44905010580b40900390703400544035080600400c40003d0708500900602200e0000d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 700597068 1250 700595818 700595821
    0x1e0201200a03120e0f0616020729040509100e09150c0d140a020c0607030612030e010e1e030c0d021f090306060303031b0e10120f0203070c110105090109030209 70
    0xf0918003a045000a035001480b9120680481e2107000522600400b00c1050403d079811480c40c0407600c0354498041c40ea0803805035400440e00d141c03980064484d18182840407407c0544580000744090400d540e09450705c0c145580c248a0319102c50304250b0404e284400400391541e400300c00940a41c2c0050250a000c0c0002c40c04080004054000760040f4508058182d41440e100140c00001e42009d110a8650312820b80041d480e2802440f424040d201510031745a0509404e540c04c0700c2d01414102210f04115802c01e10300303907031740380c4410303007800c45c052800c10542d604000b80c1403610b4a1041e803210303442175084224080241e1112482424801d00d000d9829001182c40201171b1000b880c95440102500d2400000000b4142c0c10f500000416110306094988902d00302022603104800e0318945a21001c804500c0f031190b80036401c1e4202c00710f003201000c82c1c100003407894201281c00c100c8070603010130b040d00030200410254025018003140b090802c2c41c01d03d0606c00000701481d84a00000f4090400c810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 700598318 1250 700597068 700597097
    0xa090509070b031906180506190e09010b03010e010f14040803011806030210030c020d02070f140d060e1c08010b0910020102090909551e0201200a03 65
    0x1131161090700200c82c090000b1581e828400d084480014040e201e8640f400c40800c02c185401080400e400e0f004d61010800103080660007404400040c00c4880c00307640e038400607120354900b03002e1000740307100c403a0000440030000400d040c1540d04c4061305040c400807213410080014800310586e815500c13404100d044003100e402484000b003000340c0010750b1040051a40000ca140e03d03411191803450700d9400e0310501c4c95201820b030b0396240360b801189840020248244000c0350385195082d02130701c004150b500407489585400b41121542042c61410f81c01c8100b84d900340c12000040b9a20107007581c6000c012540c034100403080e00d8060301c680346204656510721121107a200750140c0c0c4031520024080a2142010440d07039172b0720307c850903900c040d10003401d40306803411030419607845454002c05454403980e005054600102000203d0b0701e03000003007040e55140030600350503040741010005031210103ca08140005010b182c210402082c8007240e05144482190740030031911141a03142c00d10600409925 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 700599568 1250 700598318 700598341
    0x509091504141209150a051e1306020604020f043b06060604140607030306031e110103020a05040330080613020f16022d040b0414010b090d0b0a05060a090509070b03 72
    0x10400088c041c01c0181c44091a049503038001d00c43c00c00030541c91000555a0502641c0b9182d0842d000b83d4003840ba034622206908040d0440202800340a8854518900d91241c4446165207107140499a40c2c040001ca44920340c108503403900301004a440340e003050704e4044031002704400320307504134000c0c8030215594003018000c3d00070001071a40010100e490000401c9400d01c24a102c0c0d009a8104245244001c4035500038401c030b520003611030b6140ba01d0300342142c0300c1c0b0345141000c10301d101744030744403015004500701e50122100010644d40e54580d00c0e81420b20801c080301d5820402d80b000c8600c10006603040788070400c11038014840e0342510a07402d0362035000180c3c4440c60140ea200b803803002003407501000c2e010103a03404000c0c0c20403102000b074450032809000c21161426411070a1460301d40c014070001c1c00d400702404030107031b008080040d42c4c035050b540e11410721025128040500e4030f91091001034a41a00888051312800c441040307246088118659105614480c6002c035000010200e0182401c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 700600818 1250 700599568 700599577
    0xa121b0503102d020a0905090c070206070c080d050301030512090a03030e0a08030a02100f060b04120503070618050606182202060304050c0a0801020903070509091504141209150a05 79
    0x10202c0303c10344001d45100400113548140344800004201a90104084c5003020700b0a00403115460030320304000c4540e090041a6009440c00d40b80754214650000b40303000100401d170540b040581c1c4403501d9500d1850024030f401ca002d40b8000d49000203001c0c0c1091525801a5107080b2605031600da070592440c40082248107031542c00c001c1c1903004c00103039880180e0b000100290740700f0200700100116550a26250304864142c01803400c045800c100c100311a0418510260840740107606507803400307c5558a1604880004e41d142d1023458845510605000007880001c4e4040b60586010076030941885c04601c2000c00103001000e21594019030180900d20715020550007640500000e13a24180b50500c190740388400c03242e01d03200b0180140c000c04c4814060003500d041104c00303002000f095003032204005e0040001440c05107148201901408000180640c0602840c0641c45540c02e280d014402c03981405445543c0b556003580030890304101c0c0d221445452942c0e9140111151107404256003119035109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 700602068 1250 700600818 700600871
    0x60e060f0d0e070608090c0d0206070206030c0409090501050114100207050118030b012405190c06090803130b070318020d030306180e1902030c0411090a121b050310 72
    0xd10f000100e146038004109038014201142200c1045086800308000c1c61076403940203401007030501181d001810702d100035542240c1801291400e00c1e44803804101110b141900599a907034645004001c0f401702c80604109014007520b4440f40c4045103000a59600c270b00e8400c8030304002c016000c0708440650225504c003d55400203029005503510300311020340450111a1201010401f01265415806842221403600100c8014288401e40503020307100c0080046064071a15201d040342e60003e0220350003588500b074580c000811007040b500340b1504d801c1000b000c04003030501d0004c078960780c66412100c05581941c1143c0d501c12000407454110040c03c203e034001e000d0000c20032010b10200b0b616400c01c411000031141203542901700410b9030a185144000003070f425401603502550f0320700301034001601140001e00c0c5a8644151500810320a921960003800500324140c20030007001211304048061428110704003028030700380380c0001c0c1c5030030748403001c039054582d1242d84120380010102201c90000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 700603318 1250 700602068 700602073
    0x20a0512060a05150d05010e042102160603021306050408070e040215070c03031e0504051018090b090c0f3004150524010507052104050901060e060f0d0e 67
    0x2c84c00568016070002803841d4010303402c210010400300041403090740b00c0d94002c072904c0f0f055191221000e07061090020f400045004110484810001c1100580f0080c02550340050340e03004020303010038203820f10790001020040104010050300000242150a5a01d4188404130a0310307988000303010400640c0f000b142421003c295032007071001180748101202c0c02500e690309102c001400d0700035020000820400072034402d0106110505050b84c000030405c05600b85079214101d0403940d18a4482617510000440f07849400800541c00c14011003500002040e401c03074203140c1c0da50540c003200d01503901e1100300040030003403426603140c003008610340f60f8180002c2c03000780e03042c14101064441e030b5030b0f561b515030b0500b00b0000c1014010500300c0f0080801011410360071259010004440c81d500c5208240c5841c450010358940807030404040510403803406201c1580c0f50700e4042841010070059120070248080c24070075118a444900c112103489081411943d9918a0059400010303d102c084401303403803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 700604568 1250 700603318 700603339
    0x602031b07030f050c0907050903030a11160f05120a12050a140406021c02031201052106090c030d17190920030105061002070b030c04150f09050103020a0512060a05 72
    0x10034082280b83d420141903486d00c0c15503483e41002d40e000d100f03410340160035610400000d250760380b10f84405022100c80b0b9050b00c54007041c002407600402019005040c0d04000030008028070b03e08403100f80c0c0008050740c040c1a582d403164036100103404c0143d41340c000703100c0d0004d041501217110700188144440707c0840e072a255030303e8200080d40c609040e402c10b4810700d000110b1106007400001910410490446514030681c00c0a045c0300100d56200e00b42c04110700d54100071403250105001c81ca00c03401e0400014480c6007103490426180001c150025818054100cac0750044241548110703640c0b05d00c072868019500700c0b04014000c01008905405006074a039145100340000e846800500c1c44107045000f400551a00000c20411400d407030418005a0b02410f802c020f04044003014643c0b0600c0a14181d0030b040d943c0844040310845506903100141c12542c1000c003064120303aa40c0090308080c68114140b4200043c00b80c182d1241e03002c0c00446e43c001c1c2c000a1100d980d101c00e010301030031014001c404e04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 700605818 1250 700604568 700604573
    0x20c0a1e05100212061311040303020a05061e011202010e13050406050a1a041805150f0c1204020f040605040c03091e050c060a030902060f19090602031b07030f 70
    0x98210001c8840340036034103074003a0340c0c4620700985070081d090007014800d5441d044104132401e001004168080b40c1c840c15040304c2056084050b00042d802900075124402d0325141203810200001c0c160fa03a0303401500c407154140001480b165065903445420000110f50310b000598480c54800c403d2a032200d88404900011032854004602591203004144440c1c3c0398802010b050f20203003401c100754000c01e10020189498550071026a100c29020b8024185515881c2c903420070240084012405071410240a100b204880b01ea940c40040d44400504041d0000d1b40741501040c0036201900c42c000703003100c1d55956030780d40d07011704020140100700300b248038080080034010303107000300080d03a00801e410110303a48a00d0301491101c004ea844006804003603464000c1100329000f00083e0130806642d0360040740140c0f290070080449410700e000e0651a6500000d04d000b00142c0700200c1c0301000f0460740100f11040e00042582c1e01d48084103020721049480c44100c52811400fa03101400814052441000303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 700607068 1250 700605818 700605863
    0x8030304031d03150a0b150706141003030e01050f0c100b0a0617280905101a090402130f2306010c0b0a270302010509010c021609020c0a 60
    0x80000a07060b00700d10280400b0030107880d80b00c0030b07001d034541d0b03402413000a4202d401640145442ca40042860a11850154140c0b0060704000c0c8111034060740d0300745010703242c0310589500741c0c01703052030002d02101821658014091a5181d011605200e808101d04052000362026141c2e450607020445104000010383c030303c0a00318094426020720044030000c55618490440f540c141017810000b809103403241054510100e54120074240e0000750103203404102e941900500c0c5482e030180c1c0c010081f214400c2d250804440b0a58501c0c01e00e00020120b0090b51389400c0c0b007440d0700c83d40441da81d80016100751245d45c007404d85902005a821300d08400d04400440080c0c0050004a50402054040d50707088010758981c1c4803000090180a4544002101c5056541180003041a1903c51000301000c0c2503071011803101003003088015035110010080100000d205950145107207200401142000034409a0141100c1c0145902c0ca600040e2024001c0070030408040700c10380c4200440d401d106030751402138 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 700608318 1250 700607068 700607087
    0x70210050702040e0724051603021203010312180e0609190e071703030c0313050705060a0305040501050f01060e0d210504030c0902180409111504081e190c0803030403 73
    0x7401d81c0315104481010315a110100041805681c0300c7c03918004018800c40c0b0f00b8000c21404804500c40c07001c000310302d605800e010314000c0d88036841403004d030101c05402820503041ca202000042084280812441c000b011030720f03805c40742c20b817426002c940390f0200140440a80c5c1b126022998107194120584180020b01c043c201c2c3d1161409107014034104682c50384074802074a8980500704144003182c2c03c2950442001e601d940300d80200c50039103580f80b0214581d5003040140f140481e94a004000c02d0050a0190661100d85880d11f000c440d0b0404d000030342195003031400e160044a14071a02401c0001d00c003080700a040c22600c40d510400c0d04814001c000d640207000841d00f0740b185680024004507140256400c0c40b10714a10001040ea246040c48002d0015100a45007040100005d0780541c03241d000907141106c505404507aa02d040000c1c540c0b80c220415040c1d1b4010f2a0701171955080140810f40c00301c1c550200d00900d554401e01d0500d00c55030700c1d01d600f02d010140800814001050703000482007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 700609568 1250 700608318 700608329
    0x2120f0f120405090f0c390a0503031803070c090209100207050a090c0e10031a1c021507061103060418030206010605131805091908070210050702040e07 67
    0x45a090740314060100440c040c52281c0b0390402c14403000b180f143c4075074101c0300d03030f22600c0d03210384a00780340303107411000c134401019400e601c8070a0410035040c0b9003460468946491611100041804214590f94141d83e488010070488004000c0e072900036440001f030080350034241d00071200c030b26007544038224100217500c8410502d105d40d0f20807030912001d900200f22142210b400030100303090030780f518110b031000e0f04456002d4000c00181800c201d03440d940c0e02c002e820b000440c95a0002e484150380f8209650303582019045845550600c0c1030407400281d050f03009074000e605440e41c001c81044492002054010050024030035030908055115034007407200910b00c10801200c06000c0c140003a00d85100074070910b031b40500141c10140042c48154002c2c0d00501c1036565590820114540d41c040c50041d503038014203041000c0380c41c0d038148072040c2002c10a01c1c45810581c15215800e003070135550307241360307101d100c5000340a035650180d800c003994083c0d001d81c2c408c07580240c82800100c4950003820f0316202e2a0085 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 700610818 1250 700609568 700609573
    0x519020c07171006092307080a02070c0e150405070203131a040302060d050405010f0608150601230408010c0f1209030c0c1509080c0127080a0b07140703051602120f0f 73
    0x6801d1b02d03003c00d4406000c1c10b50382d11941c2a98035a64100c0000e9404080e0907074084441c100c00065a0702000240c034862440030b454040c001358501d00b00800c0d80e00240c200001c41d40b05100b1180305190788502042107aa80980c040404800254041401c0c02541d00103507220b94041402c4d08001c4180d000103204900c01c000800190003c00e14441c1150000d0280c0051030f4004040c0300714000844680c950050014100440d184c1d01402c40740658421041d203101005270301141c100f0102009000d071f072090300c2a5040071110058040c0000f4040c0080ca0f240c48211902e407803400050500800e0044081500407c20440c180d0716000c64a004250f0f442600300080c1070500001110100801c0c3c203905890705035948486c1442c1248040305160a081c0d0211205070b0f40c40000130400f10401170b142d0704074890740500482e4070700313070501406000c0128015060349008010090000f5403040c100e0300784a6500c008040c0c04245800401e42c1e40c0c905003d010b6103481b4540d02c2c400d400c00f00264400d11543c7c210708 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 700612068 1250 700610818 700610861
    0x914090d0801030308041b170a0219050616170304030905010210090b06060a02280b07020c062b060b030a0b120613050a06050a0519020c0717100609 65
    0x807250700d0400d03c0003030b0001c3c1140010400150814107034075881c12222910b1411903446a101c240c0000314021000c10a50143e40c0c0f44046013040c2011000070301940b101c4075071562511000c00c001e40300340d10030104162451741502c001c100804113454220081c2d54406600c034a001d26002c0c0403901c0a005a60140c8103e80042080300121f0081032070490f4030540155854076441d0500c1041e0300940c8910342580114040c180605402e0500810f00d032000706081c0440800f80c0c10001902c082c09071041d03007150046880260540c841c501120710000a14a030a501451003215041002c406001c043c4402810031400042ca0405d181c0950300030403024070704201c602c0715001040500d10000c0c504804036003080e8000b41c5c400c072aa11504802500540a0301d070100300c5070b0b4410046900840e9404c1200e46c0d80c205014240c03c900105100202070003108500d0306954000700c3daa02c00e414840e0700354400a1003035075680e04a00740103002c00b2040c004024021291640400c4000d8219075007441b441111292 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 700613318 1250 700612068 700612093
    0x60e01030e160603180f290c031f2607270b0105070b0907060905010c0f0b04050705190503121e0901180801050a0c02010b03190606091409 61
    0x344880c07100c1d020701415102c0c24540308094010f4140c1c070300080c1d038180614a80602007440342602d200b40520030747c5611a0301c0004c460440800008100401030070a1100c00c0003140c0105600b100d0b00429000c0c008801038025400b09072150003660000f407102d981d203116228002e0342d00d0f602a01848404010b40d0b14654480494500d624865810056182002d04c15002c1c900f049501c98840781030185442c5207001c000392103504100c40259403059840d44006000c01c805544000c0000c00361000b460075020058850700c40c0d85242048003000740001c0c00c0840810208001013020000600c070140c0b518418a01c4c0d81e0555089881078801c05000340a0500f03801950036140003101c0c10b0007e800c03910700034209000400b52a030381191030702c03c1c14098064039410f02e03101d40c18603c3d4001c0080100104544c0b41c28450038050b0ba036000300c0c0301c1c00e5a0400560809a81d0003207a000c00451030701c0d1070b0700400407550420401820569002c2c40d162840c01400b0201c03c5004800544a1803000301214401341110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 700614568 1250 700613318 700613323
    0x110411190e030c030a0204092307091b050403151d010c020f0f06011a04030f06090510050103150b0127051002030c10020903010b0301150612180b0c13060e01030e 71
    0x80c0c44e40c190400a4550010b00e0701d40c0c418070040e030250f001d14020420f8070103800300c91340200c4c0c800c001651009404100401880c010000341102d103030480071224540b940082c15a000320b00000b0005403030070380f00301003007010303684880b10070001c20b55065141c052825120780207055131203002005000b42d010030900705500060b0b80600e0514100201010ba20f485142c0031070106041c1081201901000000301040143d94640f11242c020000003c0405081c0313005440c00600c1024142c2c0d1300e040c100100701141816110b00c07003e500c4518045070700c218020040780c10b90700000c0428142c7c04002c1c030030340c8500440c030031140584509540314640d52858010503a5240195a44400d50358000d9010f002c4041294004c0c01e0f150401800100e0111010701c002030a44a40036200a8080040141000408e0b4401200215042840f00c100001c04101c402d0820180e0600005011900f259021a050070060802c23a01c00d030800796100c0105a8035203078002d215400b420222030001e0f0816420340315000f4003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 700615818 1250 700614568 700614583
    0x10c09050603070e0d0b07080a0c080403021f2315030a05060619080114090c0a12120c0218040b060405240109081e1e0604110411190e03 60
    0x28103407815030b5607005049809007250704c1380c9a040540c110591002607800a0000d00407100e0303465484452400c40c2c0c4480c125a41c4002490400c9040703402d100100750086106a16254012844091000704c1c54078900a000a204411440603052195200900d290384a240c042d2190501c181400900e250426560b51382c02e54001e0010f410410218200780303011151040e01400d80722092200546c0c03001c6c907a003115903480a04150407000380420514200900080c111420201c4148210300e04040c800980c405103918010900e01c0f0010f018090700c0d004d079507009030003036000302040c206041e4220003241500068070110742d2190441d010400034546030050501c11542c40141c0480b2066034440a8040b000c10304e410b03130501c14049000f041c0b003001444203e404054440e402c404e20811b030203609140c103100319490004440003505104181d40c0116040b80c020742c00482000440490200040040c8501142580c04040006d4289a0190606e5000444180a8031100001240c840905844600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 700617068 1250 700615818 700615829
    0x5090a09080f0309070b0c03090111060108030d0b030307020d050703171206061e040815060301020f0a081b1305011d0616050a1a100f0e010501050903010902040c050903010c09 77
    0x40034007045102d030145002942d8071544070401c0716150b039519815030741d003548000c00d00d031301a410000e8440110f50700071080f041080348a0740107200c6589448026600c80c004c02c80345440d00c98a6550086481c2d07010420380b80e940307800a011a940c0c02d254500643c0c0c2d08414031007102d0484906100d84100820030303041c0da00000000c10030f1405607807414200700641e070040100c0b0025070f1042c2c8120945410303d00c00780010b00705120082c030041c284888000e2144000074407040c8240c0c010420945541d2064041d203d82800c06d00382040d064070b032220f0666032040003000c0d002d81690302080110303205060700b10342c000300e03a400c4c0c036000c111003008070347c1944034400381c510f0380d40048041000c0c0d82284d5003003261120050140040d520b0182c00780d65110300345401c803001c500042c00700e181801010344416080030010b0900320703841c85220f850200c0320444240144a19810700401142800c80354500303404c508412a40104100084021943c0c00b610710b40041007001d029620340b81d00328020301c2c0100d80c49000d848 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 700618318 1250 700617068 700617083
    0x319060b060a09031b0302063f0a0605030313090b0d050d021f0b1813050610050f091303180305010510090605010c020a030b04140d030b040b2722060605090a09 70
    0x4441c1c40c2602c3d840d85a07841c0f007451440980b580f060354280340c0020202d072740303008101c450306050000502c03040d9a6950052842600100943c00c17802e0f15900050040b40d41c1c421020a242a228000070034900b40301d83c02418602400e55904140c50380481c450300111081c2d41c01c03400b031101110810b81100c0030019490b030081c110070784405805592420b00303548000c04581d22985005030b40d44060038880161102c03c8402c0b560907050016117091480700d102901e00752500b61840c44c03d645451002c04403440081c007800711101840c554905c040c081c007001307560400000e21140c24604035564866442e445445500c5241140110340c40d845484008202a00140311040040c2551504070855201410407515140340c81004a0312580501040c5114042610005081c0070a11b0900090381d000d07240c114465102410344408010080160319524440280c0358540750390344040081d0401d00300040d90b04401b00c6040710303034100255900a84213540c000d40380c504082d110b41d070090060700c007010300040000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 700619568 1250 700618318 700618327
    0x110c103326030f210621100608030309070605120f060f0406031101140c150c0909040c1706010605031609031407230303190909140618060319060b060a09031b030206 72
    0xd000c0803042120700e543c450a031090405000c1f8190b00703c41c00c1c1c0c2d00c0081c56400110403c040aa0180305107002405641003003881c1c0222810454400c3c003005040740c0041250101144294071000c4c2014a03030b560240c0100169030300c90508210f001c050818007800103901e020030448850311002030b01e00540507003005240c4030840300e4842940ca82c0042140c20b0503d005e000080c01d80e5601c5c0d14103400703240070b4040c2072689810407103000d080b411259080d013040c1d0320200040011550000031264013515a10901c994010b01203c101c420300415071026109038450407510300c2c654400714525040354083d201c0d00083c900c1c02500504602c6a0891070385e40345c0c01c01c0c01060580403501c91200300c207194030328058183ea07848640801c06c0311309441032000380b800740204020f4141000c01401d1194448182d02c55140d1508030300003a500c07081201e2105000c00d9204a00040101c1c0d80c03c1002c07043c900421481d283d03103100368002c190503c240301c10341300e03d40301070500c0b8051401c4840402c02c0d250040c250902c2e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 700620818 1250 700619568 700619599
    0xe0604141e031b15191b08120c0904060605222301020703050615010f020303060307090b040f02030a14100b0706110c103326030f2106 59
    0x64084040480d00413035500034000420304160020026000550f948551000321580024810451204041c9100403050f140e00e000c02d07580700903108070303800b404019059582c60000b00380041c014070034030b00d0b0418102900030400135088006841c0b072580014008d5024005031264a03400c410620402c546101041d850000f07035450303542c2146845006004650700340355203036110340c0f0b0300000b11091f40840e10544e00f5070a00d1741e480701c3c40b08284070081c4003c50442c10418006078549038544503803084e05541d4484180291601d4009050600441e801191a8507056803a00050b01050f03107403410204026001400114004c1084019100303d41c40050421046555880042680c0034509800031000d000f0300444007020001601e51075842c0e480440c1107034251040303407001b03071343c120f220011418103c4081d03550584583c103a100f1954a034130f005400400d204074514581280b22822015030100041c1201360b90304640007416450b032500690f810354108441100042c1c0d00c1640c8159105a5008901a1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 700622068 1250 700620818 700620853
    0x121b24140a0b010c0507081c0f0503070f0207050301330803040b0f0904110903010f0203160e0f060a2006130221061003050c0306150d030e0604141e03 66
    0x103102d00c060410f40101007194807081e00c0c0c0b1400340e002d0001a4418410445400b030550107443d0741c002c050400c095140560702c2c1c0605140002080070b8100421004021001da20801882004040142c001c03c90200c204140c0c0305840c02c40d400901b01003000c50000b1500701d21540b100390880b4036401c0614109420300d0010161980000510307010b03030310300f4010b04030680c0d02d80c41040c02e0b045034109841c0d078800c442c009240c01d450108854051141c03051040249001c1c00311452138580c105803420003041d45070140081c107860113032801d46402c9000451240d6202e50011204148000c06c0500885002c0320081c00d540d4501e01281e224020940e0741c18401c00500b0030720a10050403520398458250105004105031a1650444200241280030701e01002070040c02d0040d400c81744000c0d00503242c1841c158103022064404003005c640104070315080a01414419000410350110051003507655954507003000d003200440b05c10740b52103401035210303500c00000c0300070140d844000c0103406008000121a90202c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 700623318 1250 700622068 700622081
    0x161707030b1b0a0e0f04090c050114040b1306020708070308070807050a0b151201141b0c01050916080a0c050402180301050c040608160804121b24140a 66
    0x5030007110000c002c60074011803001500d2021515940c40e107080d40103000308952116001550fa0050340f8005050011600002c014802e5810a081034501000102402001c510996100c060000c0010440300c0001c40c1035070600c0c04442440e800c407882d6030345404a090311400a881300801c440410440c4000089101d0054103c69000d0303020380e03001300b001e5103070b10885500c02c45070210164440c86062009141060700c0f103d0070000d600003000b1080c0c0d25208041d010038040d02081e0403070340b00454460b0a00c40d001c211441400c4403002441030b4103004510708ea96100401142518425081c8040b511400000d002c041140e0401c0c41c20525a1600c000d100c003d40c08486200c0c001404259a6185e03501c003400f50b107000e1480e440c2d110781d0300c03841c019000344584002707800034901c80c0c0030420b9203c0c9158451052908640c20500d0390301c05e420444c900f510b05100408008440208211109091094050603c48121244da664000310b22000c41c91700d0440c1e5130241e280c4000d0071000d010401d4034560f540042c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 700624568 1250 700623318 700623331
    0x5030c0a08060a210b090c13050a090c080604060516080601030c0306150c050c0303040812131203032004050109030f0c050405040c14152203080c161707030b 69
    0x1c40f40141c0301c80c40305081a8501010710032104440840804128022145560044449020b0301000304c074040040c1070a001d50440040e01e640781c1000c6440111079601601107650f010325100c2e11503a4580e0082e0712443c0c200d40c2030b2100303031806c0002000e1414101c9001c2c0300c0401955040300640e6400019030080949011610415030f94642c046800d50410480843d0b82da1503071074001110781c1c5854101e14140c9542e0405009400c1404100701315500000d50100402c440314019440c0c1c5052194200316401c143c3c0021041c00b801d000c1c0c0030600d038056124001c2c080b100209031600c1c5c54200101c0d84640710754403c070750000d0407160040002c035120281901a20744900d00c072150032503842e0005401e5443c2950140d0307403001100401c000c030642d29002c1c0e4004800640750b90048903600c1e0020380d500d0040d5280c500d200c5440b152111032000c0014005405180d0105200f0740322140c00024999407690540d0304d100b000c0301c07003a01188004004040e070a00704820030003015160b0440e501c0e0809400040c00e10b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 700625818 1250 700624568 700624579
    0x4150908131a07082a06010b070308060901080601060c031704230105010e0c030a021b0304050415080604060c141801030b0103091709060d05041b0605030c0a0806 71
    0x5500000344048001c1031014a1001c1030071003035040c00e86684039180d50501c00080741d4400c001e0b92000850000a407807030368111010b03a903000d09048111094020300d09480e003200b4081c03a80042555260400601a01c42c0203503940c40c078542c0c0704408e10031480c00c2806104100da208200411186102d41140018039210749013500881141680611000740103807030031107405010044108900c5149105524000380f654020320079540351603038440390311002070140444e0010000009130044280e07011541d0200302c20b2114070035111805c0c54903449402070300805110300e06014801440c545044400c000b601c000c0e401510175500c45554400c0240310100c6c01c2800d000c800020300b4584c01410002c0d1540e41c4840d4000b500a600d40c50006086651014045050510308000c290100303003260f0300d494803881035400301507a40001000050003030081380036000d0407601b020200b104011320a61200101920428000012611402e0031b43c1c0742c0c0001c60310003414400c1401500c002c40d01c03440b4102e40040c4040c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 700627068 1250 700625818 700625831
    0x90105040b011b0c1d1015110303040b0103150605060d0b030f030c030c070b070503070b070917010b030706020303070203070b1b03011e050103060b1e04080d081510080415 75
    0x1007410f400440c1003000e4a00004030307002007044a1640b0802d031590340d07400b81c4142441c6003c0b160280b240710a0300440742c24040061042d110b0b14026103080540c601418210384c3c803441c1c01c0c640f03170354116001d01007111241c240d440c070389848a0380d50254400740daa0041030b050401c5a09080c081c0140011310800350705216510303a078200c00030240000d281e09000c1e5005503a60308401070010740f8029081d400307040046400c101c9013000c14804019111602c1d0300c41c0032500381e5152031004940c4401c0c01e401a41d040c696141403c1c010300c10540c00000d49910a600f0707190305540d6007105070388a0004540c00c2d07003d608100600000128030070001c3d9846101d2a100130252111b000030400d030b40c0c100b40c00940103403000d056502c4480c411201210001c000c00d01e0280305490505840070414007685001d641010703038581035000000044020b613070141c0b4000c403c460908072052001800d48005440d04101c40031381d041455038600305101c44404091311600c0da4081e50711655285d0400c540e40c01c64080b5695030b90758 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 700628318 1250 700627068 700627097
    0x40b012015070f0e010207050d060504050f0601060203131409040b040f06020a030e0f061902130504020703020102040f1208070b09031210060f050c21070804080303100b0702090105040b01 82
    0x14101d030168606036100c100c041e0350140050302c01c0301e01844480c1954000d050401841d0b0f02c09060381c08280e0302500c082141d41362454694507010724566401a103005610001c503413194000040c3c0812000d04103171112072640c03619480100c80385581d6094224900c0c00001d00401c040b807041d0ba401074070071b0309072511040c41600c484040740c0112a411300002e447d010399110840042069860380002c94014001e9410220001003201380b0481208642c0c1c0e40120f07022102001e00011840200b00181c41075503a08003500d00203000358460f000d01038200043c200e01090003140711010440c841c0d409400c09150801d0740d1288907050000900c8455144000c004214440d81c0400085004005c0c02a0602c00c00d420301c60085c2030108294441010043c00b408600007011000501822804045014a4040d110000109200d101d4920007900400c80006d00003071002c80000107511034010110700e174203c19105c80c40e0003800c3c0b00c1c0c1e0002a61141304000140101d2500e40d1201d41401c8050602045207a82072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 700629568 1250 700628318 700628353
    0x31a06071e0305040311101e2001020703080718090f1d0115050d0f02040c140a08060103060614090108150d11040c030510120204090c0e09010b040b0120 67
    0x641e08600007400400c040040101114003001c05100444468005002514004104108011f50546103e1014800c88242409107900961201450080080c140140000140070f50b0024108800003158000010101e074801c000c0920504280324100d01c200749800b04038406030240c0f50010200d95503c41020942a5522000ba14000c030844004100078035441d41d10305962141e0b9004500070304094101c480000c00035001e190440d42c0c12600019904c03403200c001c6840848034606041c40150005e400141035420010070b074800e0609a0341401203a80302e0008540502041002c148404001d0000300c20940c015405181c0c0309a42c404100c000c0001d040000c1d54162034102d040c2c8403101d0769881c09440d13042c00e006100400c4420b0500703110f00d050a400c5014818083d104221812405880810455555402511200744c00584001c211519099003d914080c19141c4404030741c40c0c111175004904207030080c1d00d03100c1d2058407030b0f00ca00745503482d404107881d6942e01c581841e0b008048030800c02041c0d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 700630818 1250 700629568 700629623
    0x130b0108040f210c0b0c090d080d1805160518010e2a0d050a1404141219020f120a0c0510050108010504150b0a03350c0d031a0607 57
    0x290f58605103013203441c0c1030042c1d0203040940114681e03001004051000e40716030f080ba00300b1640c40501e16a5410030551b040d0010300340841c03203010b1031013049002000e11000150844007081040a11001d5a41d1881045094940021801040c1124000400c00c600d400803045601c03511500308030008000741a0300c1d040c40500b40300308005d907104c04a03a43c4560f000741c1c410315a1183c8280c4040040842d03880b919400020014002031400ca03140e4091000140e003404005400c0c140080e520b61203580701144103241c07086040811006120307103803120280c03c8001559028902020030464a061a48031040307a40c680c40120613280e601c80c5c00800b4020300000d201e003070700800d541d000000e11418180b070844c06040d01000307040f00b924200f6071140d050395942da035448100c0741d00242da030b0300c03132241048420250308410340b1068554200c2d5404403982614000240780343c8079170348180c41101e40c0c1e00001f50110f0300d1b404032004141d00034800380030103410000b004203850b07401403004400c6901d050304281102c00e03a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 700632068 1250 700630818 700630883
    0xb03060106020f0705010819020a02121c0c0f0914010e120c010905060403030f0804060e030315010e061303080f0c10060801060b0412021e0d0b0402130b0108040f 71
    0x25110840c040401481951302400e000d10300b00300181841c801c000021503291960a1000b540050b18095841c001c10403d01400b03483d4001a85070b095602d80c041c642030420581ca84940d00300240300807618032030580c81c104c40d103040d1101202d96003000c0d4094030800710808403905001800040c809580c0d10082c101082d045148028142d202d58040010036031690303a4016409110306010500c00240c010b1886410240c40340f4201d070a69440c0c3c20591701401000c0d1304100c03180800010300c800d550018800b45c41000c0c0030780303402100c03615510610055109001c02651140c942400600000d600c1d00013708040e000c1a005a023080701a800240c105500024500c64503035803907108109187e4280180390007010791844180c00c1030300d403044117440e000548000030300c502e28080c60040ca5808202e10352408400c02b40c42c8138260940c17031400809640084c0e500303a01c0768003009204a41004940210b41c800881a034581d501030715103903034101121040c004100c0729203992901c0005004424240e0040180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 700633318 1250 700632068 700632073
    0x161d0a2013440f1b0a050a06120207140f2e090627120207031106090406090f270302030910030603020301050c0409050906090705010f0201090f0c1a0a140307030b0306010602 76
    0x410040d00c0d01342158000801d80600c0855030200f245aa0705909541142c2841c1019142d410245004400030310400d0002461110340d5a18011a404006101400c1480c44803c6030b0303211055075200070741b96114410318000d20060280d0740d01402603070740080344e04901c2003501244100401d00d0b8070104041c0d420302c0900c200e42c548888001c1c4140aa89601e040c1c43d0303400078000c2a82152038454080d4402c410060042d540091440302c241c48c0d81c1e000100500c2103403400c0041001956000c005000d401903909400f0312070001e408a0f5010b150b006000307041c0c0c1500110319281500061091440400c00c03c5020316a4411000015860038020303584071f104a00850fa60b43c0f0305250f2044101d4001420300381840d800350b01000113015002800303800742c800900740300c036102440880403030141c02c0282d0010949050280224100850150100c0c2942e0a422064445030b4910980314014041e8090f0180000ea08420103034000c20004021500280300b0b03d4007191030841302c00800c0c60450280d00c6040141e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 700634568 1250 700633318 700633333
    0x120e03041203021f140f0c03042a0602060106021006051f0908063310080a0e0106081c050a0906050915070311161d0a2013440f 56
    0x10743e00d030860541c485141d2006c0c0806042461f1501c0c05800000c00c002c00201812031100f00d031301000d00c203046030200507411201c0201d88881c80251154000c0c4220b00140c400c0b01e9201168003103e02480e0140c403406003a00680625501a800500210304215001c0c0402803401181d1030742c00703101c1c51388545440e044007140b0000b003110f0400c1001101040c6140702c0f0081c00f40d2082030f030f03800f0b000680307c0501d031a001100d900c1d02c8540400800c4800070703030304056203820300c00500c40700003088640d6514420f07800c03002c040d48002d03015105440b50b004400001814203000b840fa48e4042c0000d403290041c00341c42e882c00242419510b02590344043c0f4240c0c0840c404450003000450104059003810315107100e046502d47c0707030100d0b403100030b2450543d8a0098030624002902000e00354019610a80d04016414122100c603001c80103681c0221601c090302d4040c0c0310003003541e10420000900c03003185000c046008a50840104044146c0306e900049610b800b205140a0503804001340d51061084070090300c200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 700635818 1250 700634568 700634591
    0xf040308070c090509061504110c0a0b010603151203090b180909070b0d050c1e0301080601060806010906050702030c0310020d1404120c0f0203120307120e03041203021f 74
    0xc2d50341c40f07209254204020000c2141002c80d14542040c507003d2a5601503030101c00081c050103215075003908141020038110413107600010710002142c040d04c80b0b1001039032901f03000c40a076201042001c80c8a421080e0810200324a0101d8400140c02842c0a09010303485000103813655020300001c2d04096142d9a1002061615020b1113070440d400c1d00051100c40d1900c0620403403401600802c03c03802e591040001c1c240180002150140c88405086c00500b4140e00e100001782c0c2c000780200195407013000004100740f80155229409001c05071121880b161506d8021240c0d503002c004201e8060042124590180c2c80800000451200078140540c40720b20b0410341100711801c441555452009080c00e001c081101464244010506c0745401c42400f0358508002d01009d4107054029014820144c90035036800c68440510b0080402d66030324920440c0c10b0300b005d4203898610201c25115001080100035080420520318900342c440e005491038107104403200000c240605070103600380d41c0c860310303403400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 700637068 1250 700635818 700635833
    0x9062a03110d09141302090406080f100b090c070303150e18071202091b0304060f1a03120a210e060717011814040302010c180506030f06060f04030807 66
    0x510ba2414110480c41d10829207807406110180f24003c0c401d41c041c010100c41107070100c500d00080030303105000c120f070364100c0c15590f004100324040440c0640035002c0c119038121b0080315406130009140071100e803500c00100010b580402e20031020303d555062064a440b8502941c60300030103031084e003595640b400540d150f0904192a106589941102e1002d220101c0100c082030b44154041c1c038658031030340d940c44007515030f4914807080c03a99011011042004000c01c3d50000c04414400314802e10200e40c0703840d40b80254803131000070158142c01082881e020000e02d10080c041d030010a10385119068441e4000200d443d01140c10905142d0700c60802aa80501c10400c20303400181e98500080c0c2c00041c1500c4460029043c041c1c990030501c3c20302d411442054542003c0103442030b5039442401c0d4142403401900900c0701d110300e400800c0400b00300f981c03001303042d0600d0801c48201900c0246160748100d210200600d0081c03109034051b8007840300b4016000b0140151002c4c0d0700c9042c256039162101d080041e03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 700638318 1250 700637068 700637083
    0x1080d030c05030115090503060f19020c030a0e06090406080a050d090f03031202120106030207020a09181e050313090f05040312051504020d0c12090309062a0311 71
    0xd15051621603010554042c0c2168110303405429100030311482e1440031550f4803103540c40301c1d5043c8100c10a1001060720000c46c24041d802028509049022034010807040e07001d410b160365565003040c0440385940e4065a03220fa240c0d0402020390f45400442e100041c12502c550300681b15a41c4a42c6082c01040020070030300b980d40d1468140300d41c140c1e1130030380741d00d856400502006080000c1c80100000990198054031605c00303200180184540e11036100078001d402c07510080e481050a0403000800448178407503078008006c03600c04002400c0a40e02c0780c00500d40d007510b529035008040758500001c42d00a201030032030550030106002c0706a20b0000c07024282e40040b54410101e524110900c00042e0b001074000c60706140840300031440350b0b10f10009020250501c10120742041c0002101040541594403000070080380c1e031600709001108505800c215084860010086020403c3c01e00c2520300500f071000c5410014001180c1398144403403100985821120120041074205280080b00401848081c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 700639568 1250 700638318 700638343
    0x31302010e0d050a03140c0105070c0510060e01140d140f07060e09060904080d1b1713080306150f0405040506030a050a060b120f0a030306050d080301062d02060108 72
    0x310b41001c0d507141d45403695a07000000b002d000c42400c4041c96960303020140c880188015008011900d010344018100880e2450215043d00070300700c0920300454940314401c00e036001120412860f0703003000d002206800c0400c4207103902004000c003440000c0e218151802c1d00d05507407409400580e0300d83c4451450000c0d0340c0c000e18240040c0001041d025190b0300d400941c00f050407608108035880b1414141418418010481d680e2420310516401c50003900440007824203440e40c9000540a118210040d032520650b04140d121225810071400f1402510180d0381018008100c03000090000031450895071184698070750003a030102c1d08120381d1401e440b9450740604150003400d000020381d17031002d8680b10401001014580d646c140c2c40a00d445010680b64035004081c1100d0240c450040ca40395504809001100000e0800f40082000c2c1800c201140d007103948155503034196403d01c0d6050f87ea8003050002d880c88150011640c540b950803404441c1002005500504041d50406004504024207003408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 700640818 1250 700639568 700639579
    0x90203091e03130807060e1009050907110d050a05070807030e0604030308010906060519031d0a051513021014120c03240a260106180606030c050306190308031302010e 73
    0x1000295040201d65800040031100c0e00d94010423941c0aa44030f0a0390f80060b03070042c00315020408055004001c0c00c00a40401c01160403420784000d003101c0503c0341c40e001100258041c8909400600c24002402c00d95103c0d0600b403050010b039002181d941d4000342c0c000d500103100a0010010006503104443c040c00d49860310510344040b00411050b40f200e01c0d0894401c15544041014405040c0424002c5020601f01941c15040480c14019070320f080640040d270340c1d03580607404602c3c0d2006c90100e2410255000d070031100013030703210300c000d5500b80a5000e1284407118104030f1074511030110b00300e00ced00c100824072070141c4030708115001c1c0c82a0a459131910740e011298204500241c1e8038000050110755909000306042c041c4808212403c1612003008903241d820300e00042419401c002c3e6420114203180710401903e542c8881c101c05854100c2c40107804134000b0000310300c83d403d003031541c5e500c1070074440c065282c2c0c03984d00c0d81d44201e0740d841110010200381d41c03900c07030104669000c02103003c5803104994 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 700642068 1250 700640818 700640833
    0x110f0a18050f09060d150209040e0d0e09071106010b27090a02090a030b0a0b03060919140a14071401090b0f0c1203010e150405040b01090203091e031308 67
    0xb282d8030700ca0030141180f244401c0d0001a040e50303685080c600046a10200e0b10b064040700300d204201a41000f065188038a0a01e240e04000c0000001c8681980c045503860000144900003441030450003d0f00b00304c200801c001c003107500640d04000090080814140c0c8a60351141034251640d04820244604003000440d090302d1100e0b81c60002e4550082c61101c030044e03460400340b00140020303040b81e100802d0b807201c0f402005aa2550b0b49e010741040c0e1019419604640da4025102c2d403140e202000002103c50288c11290102c0c0040e100e00b1240c8810100b1541c020000b91660504441440b1000c0d4081c2d001f20010b010280d001b0440190342c0100b0f0804403042420000c0a00d007900403405000340101c0003091139002c1940030000304008070000001c031580c81d41c443c51041200700c000c46071418542400b254814150800d4816180f0036500070404030216400c15080c00301070342c0017a008203100e20440180c1d000d9804000d50030001580c102c0f004642c1c40304c00741011858003026910030300c0d03140c00840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 700643318 1250 700642068 700642079
    0x1d0703050708070c0212070302030a0c0f0e0f07050a090519090c050f0f03040c03020d060603050c090609070309030e0a06030b150f040b0702040f06060309020316060212070501110f0a18 81
    0x5600e21308842d412910400f8444071607207014a03290f0281c4c00a9414450001c45200f8006c60500c25020b64081202d140141620380d038894414810035900d039441e01c000f100003e121030344107801030503200e00d1501d0101c2e4865900d80008040c0d06100c80c818030408002c0804100160082c0309a050744001c40c02d10750305154030a0b42d03001c1e040c018000302941041e00080010200542802200051540282440526005424881c1c010711550108407040d104581d640b443d13618041e0f29851180c400180100c0084d51742940c104e0162694160071414003103c146403580542c1d8401d14000502220fa0b40041c100e00c0d0f040c1000340090b070b00144002944400c1141d601d2010704641164195500c3c810f0740b590710016480420010701c03c15aa01000e245008400314007594150400e03411540200c00311064201d549041a1400301e01f07104041c09680004001244036048501404140340030300d000107001400f000e84000d15603c0915200c80385e480024411a015404c000b1541d0b16a115a1010f0400c50912 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 700644568 1250 700643318 700643327
    0x60d2406150c0f06020405041d010507050403230f06071718061b070203031902150603030d180b040c030309080105070e09040f2f0d08030a0b0a1d070305070807 70
    0x2c20042d025090b803208000c240704840d0101c800800001d071003005146044103000a500c007075080c8040c115400c01c5d022500d0148240240d03070a407a040a400e500000340c4910301c48180c41e0991f100e5205000d074410805049005001c014407a040307640360094680440400c030b0b50844001000b1220400f02c03180c400b50228400150300d07520603102d5101c0d41c0c910740075096034030003802041d070000d41c144070025100341001e00207074941c101001d640d003c803030060f24000ca4110940000f140d5180e0180d2090104d8000380b1000e0b000781c418881c0079071340a079100c40c0382c1e02c5000d89007104480680fa5008078460420070564800410001450030000030059030404010003004809030f00d00d02440f5900c624003140c203001c01a00380400d5075a1040c0042040310029440c1c0e00400f10001c5402000d8050143d030044a08062110142c440e504c1f001c0d03180b865a4080d10f907402480309843e80e42c3c21862451002c1544010038114858501d1070284281c01840c21003001010b03204000c020b01c003084800c405115005411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 700645818 1250 700644568 700644587
    0x604150e0402060912030c030a1407020d0215130b040303080c0a090e04030e1201060501030f09020114032e0302190302030d0e03030f040b0c0c030c0603040b060d240615 74
    0x4032020b0f0754585811000640e1045001a030701c1c100d010007d180aa4007400000900c401446500c3c0c001c079542ca030041d2840d09000701100a50400c0d80710058000503d802680c444040005204481c2008114005018002c100781c0100202080001301071081c10b8001c0a801e90007035403c010716140200604009101011503c202c400e4440060085805c050080c03200c4c4102941c054030741c00040f1000b1801501a08547c840e180c046072400181c22a4003806000d244001501a10781c50804400f600340b0b660160b100800407107004041000e15111410014207401710551503d841100341401e600402c03080c400d85406001d0000ba440c0c9040005880c04600c18802c1030035030914614207061a40441d055100303105244d1610100020301050781f075071042c00f60200100010813900c900151206166550f41000180b9500090600009000461140b10158803c038050007e0600c003005d5a1403010070040d001e03003c440b4541403034600b103140602d80b00301c80c010802c0c2025811041d2510b0b070090103142c0d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 700647068 1250 700645818 700645823
    0x4060902070f11030106151211091e03100c0503070206010b0715020904110d1a090f1911040e07031b080703091a0f04030809010b01020d1d04090303050604150e04 71
    0x180852469a44c1c01c3d4055001048903000c44030400c152030708000e0030508204509002c01d480c18580c0400c494648064854005000e000707004105102c44001c500490289000c40d450b105540d01080c464141c5e000b0003907621901e86542d074880c01c04d0342e0040d04110050b04900c803400002d1140f8404903020100c0ca0320041034042c401070360780040700e0209028040031f550303101300b0650001d02000300b000641c1c001005104868402c0d00322141d95001c00ca03054000b0341c0c0224900000201181500401c00d200149484503044001040400f403001d0010640040d408107040140502c100070101d038240c0601000c1001015400e4408589070384094003004000d885141015a240482c0c410000d4480c1d028614292195041c0d09605d400c25403400008001c0307408900050000f80032562561050056a6034000140c01408418a0000044404e42c00d500c035105aa40c80701e40894001e0b484910030085c003035000b5076021542d0302d0508140b10540707403080303d0310010252082d0b0030041c1400060341c1a81155 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 700648318 1250 700647068 700647083
    0x305032e030210050d0501030b060f150d05100e1905011202090c09040e01050a020703020d1115060d0605090703061503110603180714190303080412050c0304080c04060902070f 77
    0x1645100859260241200c0d17806600c0c074210010082c0105518450f210300b20803901403841c0b40608062000c405c014002a0325411014441c44011340c0280d044254080010510403042c50780d103000b51401c4101c15100d82c15a034010011621596a841c000c1c280942100d4000304155222a400b0560818004140380d00d54000480c0310045039540f600220140745c10760000b8041b03030402c601068001e5105010803000361191084e594619409044030300912558240038085a20050004149500e0000c0045a100307000c9100040010740c2849200d003e5406c035002490300314210315140007251007440e108a40c54030000c8040000075400d06c0f8040b01c20310705a4116440c0c2d02e4105098030040f601c08421413145c018a1804181c003480102d00301c0024008480c82c0004841040c01c9000c0c0c503420707000150015200d170f00014045010b01805000310011031030078510303058801c602103007103030080e410404940c0c1100c050307980e07589400c3c01603401030311042c00c04516088007681d48408205918030010b2081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 700649568 1250 700648318 700648339
    0x10e0a051018090e0f060609010807150e10030504020f06041a0d0b03301e0702131b03050906330411030108163c030305032e0302 57
    0x1282c03900001c03001402d04203814401c050141c541c0c0d9031030700803140624100c1d1144034000f40e450300e80070010a04840981014112042c01d19900c0320312a1000701400741880a861100900b0f0303103940d40c1c59840d00425a400182d03d0070540f04010083d0445050b20344502c105000074003102400394041d50000301c4c240703c0c0640e1907200d1180070000e00510000f01d5030600400346504504d0b03110030000d02007100780015520303002121a0349980030b801000c525140510b110250301031112415401403000b14002484103241c652107410702c000352201114048080d00d04400c0380e8060716014000c0c6074008003036001130303d014900030700b0702818a80c2070161400032007140000080c00000c10a01c0d002099070141003800032800200f0000ca042d4028031480c4041d200300c00412825040301e0117160141c848113a02034442d00c1012402442201e080c1195950200290072410341d0b80c1002c00e0003000651007610b405072a07180181044807218170088080d01c40307500064ac1030513886000500c41040d41d6040390a80007a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 700650818 1250 700649568 700649597
    0x201020318030c09010b031015080403030218361e18060a0902120c030a06020d0b0306040515060114030a090c05121005090d0c1709061305010e0a0510 66
    0x14800003d4080c0d4101050500108407106420029841009144000820681c2c1d0300c075040c00801d4090007000000d40280086000244290002c0100c0c0b01000e81c82c42a088110000890803090700c030898810500c84010107e0f8121700101c40b0740c00e1038032020300c1051803a14504107491881d0f141d6110350341c02072350b40001d00e03482a84404880400408812a103007450010380c12001000103030030591060820301001102002c000a00011900300a0080c0c201100c0070750f0340303002940000e100e000290380c680600b00c0850b10200300c060b201e9030142004000e04c00d03182032070380d450343c01c083d001604101111030f001c9103d005000840c0c0e0071a4803020006503111980c01c108070032110940000364040c101e07503500c52072140000b425a0101214520400094071000e159590b0f40c40d4082108004c103a102400c200440e05203008110300c103100403842031403d409c040008034558800307030044050807070760741080c405544e101c044c10324103080588080c0242c0342064000b17107001c147e03006010100030058007540705 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 700652068 1250 700650818 700650823
    0x40809030a081201140a1412010b0301020703020307060b1504030b06030c04111306050301050d02010509040f0626030301030218070e030d0203040611010501031101080705070804030b160309020102031803 89
    0x19400c2d00311060702d4680612940700001a142803003480d2403540180c210088034584201d51008454001c1c00400000d43c1000600c104070075008030001c200d56850304070041c02e490030700050152034401c1d0f02030b6a8a02091030100101c889040342a4060400488150351142d5210220307410340f5080300003079181c0e582c0d4030000303480d11805440b1560814182204124059a018007521002d140505054086a240e00d030459180c082441104e51050f0441c102d200954040c40080c0b030b046102400101744c1e000b2030a0420300780c6005a1103844241d94590303c039141d65540e40722918421a9401c06545103515540001d0464459602041228900785010604e480d00492034409122005419103404055101029403030fa08103100c1c583c0400d00c0c03c403551594402c1803142c18184d9230711400601d13500c4510070045030002e2008000318184942000000c1c04908120003410003544145510720f218503128129002c0110440d0303200c024175003032911060040c0c1e008410303544000f02d58183d06840300c5071400084e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 700653318 1250 700652068 700652083
    0x9011e1b1407021f030506040504050c061e03010b0c150603060c090d060e0105070905041806090c0909050120070c030b091e06040203061b071707061811060405030604080903 76
    0x2d44c010b100c0b0254812011381c1c024104480e440c1c54070304100c1076840720280812746500f128000c0503608201800303599840c00a0161284a20020000001446d10391000713000d0b0b03200fa042809441d4020070900140c2e01c08001e0032600d98110806240b036801e00380d001c20345d01c1401805a012900000c5910346e02c07a2148040314022a401071800d0010401e860351650081400740c4100000800d111400f0800741010f0188810b20000c161a929001c0701c00c0d102c00f001810300041c11103100700f00900000da06102d41c0100441540501c0000403e01040e00103181c0a00e0384031011002c03842c0c24841903010800c8043c0d040c040b250001e07200845581c4011070f550a000b907192120104813056001c20041050010301984114425012a14992560043c2000b1445240702c40711031280304002501c0040c03046030000741002c035003100c40c909046850f6220015620252540c2e5400c8147d096000c00307000c0b01e103110802c0404241e031441c3c80c19003040c2c0466100c410007403000e041c0160005209106842c00c1020131f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 700654568 1250 700653318 700653323
    0x1009080f03040b060901090903050d090204060806010b030f0f060913020f03100609061a03160207171b0913140a1e12050901200c03030309011e1b1407 66
    0x4035a203260030703d890303d500d810a4944d81c2c0a422110004a4407034917901c02d09002580581f02c141c1401c00c0c0c0d944220181041c1c00081340c00546444c40040c60100812030a03000e02074004401d9183d282c400d4a41c41c5d245001050b042d0300100c42030a0144ca81c40e00c0c01115080340c024100e4105c84001800800c0518020030802d580600c039001000003240b50941c4035105903442107074288151540c500224103030165040d00e0860b904000c00c0454190490201000407079005401614059960b40341c0c02c3c0201e0b189600b820308560400d0001d504034010404000840c1c41d400c52310b01f601400c2500e030410568a002600902c00a00340b814a01043c030100305c0d04c0c0704140e00200100d13155010701007440c5502c15400c0100c0d406042c0d0001307501c045018400791440102c06a645070010361154040108107501902d03188403034054880c0d15941500c2c14001140f08440080c004110601040071039080000051080880c091611910300e0549005804e4001000c00ca440c004400081407203080d1000d00c19042c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 700655818 1250 700654568 700654597
    0x70c060603080d0c0210020405031e01061206020a020607031a060a020709110c0d080103020f0409031b0c0f0e0103051e071206050a180b0c0f070203100b12030a02100908 74
    0xf1502d1904282c200140b80f4101c0c0e07081d26004d0b41080035007030a0b40520b02078140c1c590018002420f540752a09850b517410300100c0008104076a640e201108442e007064000d03030702035400061b505040f0b034040000da6004509480c003040500d0344900003249078074010307001d140306040004080b011340744208a00c0b806007a00050401095002c00c0001e0241d900a107a41d90345030162801c840f0500f03001f42c40150480784c020f4000d511040407082040010b110004d000c80a02009410134806010000c0002c244c152255003070544503070811005e10000c01417540001c0c040300540f801400001c40100786d000a000481040078002e17594900b8440c1001d445804c05004444002052018410150001401060028410003507031140c058144000c500c480030150556800f140800d001003000401000d86d440e02000e15801c1800070f83c0041e0030013038dd840e00b0003400c6403115410182461708040c03202d15100110f00451030410582c01c044d40712501401180c003a01da030303111840300b40034600c0100d9000030b814040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 700657068 1250 700655818 700655827
    0x3060705030a062c010b030f01031e060216020f030a0f0f0203190302160e040f02220e0703050f010903120e1f0c030522060203100801050408030108011b08070c06060308 74
    0x15607400c40140700c2d0404c452150420000074181030200440f03028000500e08018203a085848031141510b10040703140c1a803146448403400304a403440904521083e0b81c1d600b800807540c60042180c6c500e61103086510a4000503054400109207400b074101c0d4030b80c0b000340e9811070502800001c0c10412040300703100028035100344603401c0550203c0c071080e80841e500c0304403244a454015120a01504860080028102050b01005890100240800b01106007090340381c64003030f031080c130f400d4440c0743d1b981c41d000713034000c46c170a2040140910110901c115907800811110520351002010f003450400801e4002d9030703540503807400f41001d20034852015112500750754039101e184082c40c001c1005c00e1580c80080e291001280002c1004c0031100b8140744009040040140c03140c41e50703002540302074155458181c2c00075000980d05401c0c02954492802032030f8007038580d80342420b854295a030302c00ba00102c2035820903141e041c1c603070007030700c441c0c0c03c41c402d072038041d032011002d192001c001c0c2171541000d0004403001c00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 700658318 1250 700657068 700657109
    0x1a090117010c0c020604050105030a111c0608210a030f1a040b0f0915190e10091104031103030c160611070b090f28030b0c0903060705030a06 62
    0x44514150440d420001c000d000180c00003166080c5101c0d10081d40140308000801c100e600c03d6020359000010042300044134011318000b44a20340c09115003080c1410581d00180141629200d01d1000f082c2c090042e1400e40700101000c0c60345000c1c0e400d02090004041581407030244242d100050b041226142003160240794084804a5006003100c540b0590800071051340908000c819036030100400350009140b600e40240c4825003820080046070005600d03030060000f0400c0300c0e0040024461000201104d0510b40c1c00c1c24076014207a00f107c25a142051840c54020b007440003100c0440340c0101c0c03080700c003086a03400203007144038840180c09284a124410b00103158078000e488112141078840101c6402d01086290321a5820310401181034030a00c2034031b55604107110b04560700c1c00014000180c0c4100c01501502ca0340c0a5900001c520044910520401c8005c410482d08294031101c018104414100040e0f03a81c0002410401040404008103d030008641c1054000c1c20044140100500ba200c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 700659568 1250 700658318 700658339
    0x1906050402100e010f080a09170307030e0a050a020f1513050f030109020915060f0307050d0507110303070e06040503070b0c011d12130906060e01140306131a0901 71
    0xd5905921880c690b00440c4402400b4080303440482d041a1213004c071101140c0c0080c1c032062002010303a001c054507204108001240d003090307070044001c444046034584c103125030020210344541200c01030980c4030155403000f1820008410180c40c1c5e0454510044e0b40e10b0601141010707002c000c054800d0316000c2260700c5440e00c80300f1488282d400641c1c40728041400e0004150030703580b00b010060f4010340c00f800807650f40c1c2c0e0706d50b04003a40305401900c541d02d8514100000141c5900c02c40d60340340007a20115501c410344129006a90b0408020310300960044c8040304003a48900c0040c1901082c40340554040c0c0d95500c1e000c06640041000034150f41c5030507981d581c01c1601c3c1e03002e503142800c41e5107003000b000b681500d200106096200108010140000d0f04c0c0c0c030021041d4070284c04003c240030f00400000d214800b90084001400759a600c111510008000141018224200760148220280200300054407495210b5040703910b204004945940c207602c200d00549240130f186900091041c00205040010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 700660818 1250 700659568 700659571
    0x80c1606021e0d05160f02120a140d1d0d061a09130f030807120c09080f0d020c0607020d06060e010608090706050d020702010e03011d1e0a03050c190605 67
    0x2e0b100144a522100c0c500341d21040ba24241e0000f081d0144805003020000c3c541c03c0d90304a21078000d982e0741c0c50040d000280d01a020315031a441540c002039071a4104102e516010000d00420401822400850312000e440c1843c2039049070103607104a44c0d0310500c2da8600346480e81d259001181080a1141300304400c0118161400c0107000b8500310022802901280162000e00380c0c0007880340c10300019a54044540704409042d80301000341110382c044040d14140700b9900d1521980e15903582e00d81c1340103d564240105100d0000180d00200308540c1c0180e000728807041800401c488136a0794200d02e20015074034200f6214081d010524105021a00c8036443e59141c2c140d80301c07900da0001035900c0e808929658115405030f43c00050301404009a0b20a180d0054100c00b44141420101c5240d40b070003190840300d01804030701d603207101c6e059600c1d5a80707000c0c41820312804c4040040756a00002881095880b002660001c007004070008464404810078001c0c800c9806061031542221815810300308043c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 700662068 1250 700660818 700660843
    0x901120f0507242c1c080a020132040221010510090b091f0f080d2c01140706020d2a0c2a090606030c05180d06060506070b0a0b030606060304080c160602 67
    0x601500220b000001c41c004905160103000402140360000502c040114ad010748101e800a005407d840a0038905514541c0c41e0b0740e04000021780341c80c1401d04030b215441581d0020403003c1c9800120111501c600c603030f0907804009000a2103404502010708610850242c1c8900119003203c100440d0703240000c00c50b00c0d011841503643d100d4400d05985000041e2140703001e0001c4d89228040c1007803141d4004e003030155403044d810b451142059070176180c210503031740000d8281591690b980d480103200005c580304583d4200303001c6140d40a0050440020700b00703a60000b4048e200c010303009411190300384120810401c22602203008896150307180c0242c40588034070301400c000302e801c161007101c103207202d2400c4d503c010030f060920f024203000703032010302410b50340c0c50300103480507900c1c2c010114603a00e44000070540284a1400140f06281001c0c160b021642044040d9200c0e8002c2010700c102640c511040d00c0c0c0058003e400309648025002c801890541400b5017141c900601103030008080c0d4020815020448 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 700663318 1250 700662068 700662071
    0x21903120c090807030b090309130b1008060a05010c061b0c0308090a210c050f0c0906040606050702060a0e04380901120f0507242c1c080a0201 63
    0x406444003600e00c41010b0040302c005030704c080c1081001c60744050404e500700c190741d800ea0307103400305000210b180b000d910302e40d18194503150201d07820705080030012081c0700308072850414100c4c1030600000b02d0219081c4169410040107020003000c1c0011584000c8508080c0600d04d10796051a24001c0d014481c2c052054000c2001540044c0d0740d100d011524040c0c2640c0290500200345ca901c0d82072041e484da13229203104200300f031f03c0398134001002000495000081c480007400c81031400d07810000c031600024040b50195060450400910b9001410385215a0b812070b82261074680400381120310780825001c0f1588142003950303040c1011219500d20380840450010030140c081d0703400420000303040851119802c80c5000c00100424001105045100c1d84107081e21081e07090543c440501d0456180c02021840300000b0511812080c0041d1103801214282401850960840b01d90425030051041701c041441416110345c281c0c0c1d840705040140c030703400689480c10964445c02c0000741c90f00106a02005903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 700664568 1250 700663318 700663331
    0x12090718050408030f131203021e04121106070515010501110303040b0601110f031b0d020f031c020f0d0506030c220f0e19020a09050f041202190312 65
    0x2800c50701030540708a030842c558900e591103110200041400050054039190500c4002030f00084d5807400419504020b50303400368481e99101400031019444418040326250b040108001c010b10200034894000d801c000d082c490a2500c20100310031f841543c0c00140355014002940740032001150300380303040e12402e0341d440c000005c54036109036030f034402131390080e003401c0c0d605001402541c861202290f003000800b003540c440c1100d0071580c038610341040041000d9840c0540140109401c01c2207020352224a0b0703c010040c03940c2182003030b034980c0f0590180010743c02090598020101c0b580c1c04541c81c2031510300003907560300302c800e5000c4004c0100307032401e81c0b0a010b0081c00400914083c00c8000c4403421000c2a1880c03403a0402c1c420000705602e8041559a0341c44814400401800b442600a000b00541100c0c4c08940b50744100b285903c41504000d020a11b000140041a01c80d420f580358002e038440d403258901c00b0100d00580c039107401c1d1103003119004181780072102015803003d407401841d0820b01092114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 700665818 1250 700664568 700664609
    0x2c1314070801261c0e03060f0103080d11040f0311011806120f0e060907090c05031b1605121804140403051305030d030e0c03011a1005120907 62
    0x31407400e1254045030304084140c141c03103401e24100c10480c0b80d2208100e0311030502000000380a0070700710035080c0204007041c0421006050070700103664406070070000c00c0c60315070641d0b0300c1c10307818080c070308110113444c1e039075908014044104800c070b0700540300c683d0805001c0e0740d81e03190003a1200055116603001918181a0003031a00c00c2070004400d445141e211403880080c4001810300900380c40c20110360807a01d4042c1150401d2040c00180d0040d44400017800025092103414801c3c0c400190900040203400c00c10401c98a20a8110084010302c0a8586549030f843d80e046c4d105c903104818000d8500d0164803181c1c1c1102440100400c1100c0e2840500039031219420200b01c210340300301c081c00c010b40c200000003a0029100350014808003512000b00007000d52100d02003490100000342500100355100c0708001286001c012941030403030f0032402841941030540d020303401310100910a0303005d100f48070451041c2602841c1079400082e140841c41704949003800c9165603a100030722070555201183c0c50034404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 700667068 1250 700665818 700665827
    0xf090c0d0605222d080a0302040303020d0c030c082a030c010e0a05120903030409020418050a1b180b030a09030908070f0311060409090f1b05012c131407 67
    0x3403164100d802e4000c11100c102c080c24000c0788813101d10b000708210340503080005900c200984141c5801d59401a107603800c600c0d01902d040b2a00400e42c0900c80030341c800100096000c00420300d92030780306e0130366602c0d204150740001c4c1e4203050030b81910150105030b0b9285501d18002000c4c141c481c4a4200a000c4452503510054941d240400045c00035007054070110720344000300004181404028044a00d419030354002c0384101d821a4200b202c2c900907020281c001f0309414025070f5000806160100041c402c00060944d44602d14071080c001e100025a070040d07108800b0756200014244000140e950f841c0180010b03000b0090a1400c50109580f003d0200b10000c1c005004419602c0203003003200994203640f500c058035a0b00c0400e0540c0f1140401000c601100e0034010403080034030500c035900f200d150034605041d10010155103a030041100c03c6003044507a91180800740040032150a8100c04a00011a420084190127100741c10070700401e840c0100414560112004820028070490300c0c0d215904204c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 700668318 1250 700667068 700667131
    0x1a0604060e2b0506041a13030c020f0a1d0108070f030816150e010c02010e03070b2d191503080901121a15030402090f090c0d0605 57
    0x100184020707400640358101055000c100082c410419403103540c01c400c0031110100d12141c115001c0d0031880901041101c04601511107080e4201000c0703203454500300d260407103800550301404001904200c181076440e20742010b004000041c1991400b140c698584446031000240905003050110000103122400810240e09685c08815071040543c038544030360f002038020700c00b28800052080803000006501403541d4040b40c018810110b200100082c0d0503003141e09a84110040d641081c0c0740d004010300201c11280050b40c84261001c051700c4030b40008404101c105800c1c14503082d020f1217440001c1581c40c0c61482041d00302441403000044040481c280c8480461080f0031180200f01400011a040c0282803c5401031500361044040740039200f0030356150303840d041000c0440c01310b1907440342070810802402034211100a840c6040c81d074040740031400004e101150400c0b4503004034908034424040035a0b01c0c80300800121018030182402c00046c00241da0880c48107610406825071031035080040c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 700669568 1250 700668318 700668329
    0x1a1503060102070b03090327030d1404060c060905030705161401020303060d03170a02040f0602070302090a020705121206040b10170a0b060d02040509010b0f190c151a0604 75
    0xf400d85628015107022607401c05855070b56540000c4c8188000c0c142035840e00000003209000d80d0000c0e2002005150414081114a500f00841c50010000215514045a040312443c0c40c0014410381207007403003070090421000c002c00382e010000307002081c8900081c21200501c1f40380d0702100c0160303072602450200d98840d0001805600244001002031800074030740c02c0001c3c040c0c2021204040c40b0799140116020489202c00810b501203070034040340c1800d40400c0003a0030503000910b03078281141c002031000c203001094103d0b400d0700090361400f000307424420700034441c3d10700c4410741d00c6088000256460080c2210840d000d107180020960441c03400040001346140c0d5922060300c80000e950f072586048070f0003009031240c0c03500c621064103d52503c2c001050091694000103844500b031038100104000b06902039901220103000c40d20107060002e0803070b01d2004a921182540540f49001543e40d40440342001c3c0035814a03455145000e03040e5003102d0300c0e106950b89400b2007000701808001e11030156003d503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 700670818 1250 700669568 700669573
    0x609050c0d06051008011511010504240b1c020a21050d2c120d03050420100315090504080d1b0e1203070b040503120907030b060d0311011a1503060102 66
    0x4102e07d60201c1c08682e403d103003074038103108d4000451143d01c1c01c0da101030350100c0b131601072211308401c02001c0840c5140003103440706007030007004100000511180881804e800851130191450b03411582e80c070089400514044104914810040e00d01080d0521030500548050144190892105201e41d01202e08c03c2481c00800c0c50b200710021112203503080140308103400c9400c40c03d40032080c130000c0180c8603481003590b40c0441d0501c3c00e45881160320040203884042e0000003801c012141d526841600380c04522803030005020345156504d002d0a41e0031f075110f100b0b81441d05041c00140001e0500412000c03c101710184540040e9040c2c81001070080e40704200010341c1455611554a800c4908040d00741d41a42140d0524410344c035098600401540e00711402d078000142918031151004001d41d00c01c9080010f40082072942c0c41d140c00090000702114801c4103d00c040004141c0114030280190404000802803400a4001d4030035040c1c00d0b0b140301e031250300700400100582000d201180e00c02c1c04182d02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 700672068 1250 700670818 700670821
    0x91c0201050c0d0b0a0f0b07060e0703050304120c090c0c05010c0806060306120c0303030c19050c06150301090507030c1a030c09091306020a08010f0b0a021f0609050c0d06051008 78
    0x4010010318084c000968401c10a00000842070080e1401102074910301d8103c3d0f58a50992070b0250880305070300c01c9901290440036041012520100c2903c08550010329906c84000e51440c242c1041441600a11007051a02c1800c00515500c403170301d43c0003144510001c06c024883c4040a40d1110011568258024030400c002030150902240d0340c240e1419003001c8548040b14540001c1c10f503002184c0580c000c0c1c0001c50112507103201600c0c00d000d099180e040183c0b82504030008561500c0c802032003040000c002c20007101f5281c0b0250320101055030000243c50500c2d03220300c1c0c0485207040074418941a55030482c412001140c400040701e01885060741303100d242114000034419140d4004080f5115955075a000d00003085090004101c5001940e41f891025810080c03410b190040d542c02200c0f0b81e840a0095079540c1d900000c00c00c1d024200c010415440744000140c88001c0e001d940c0114222908001c20b0101100d0000090007011400f2141842030341c1e264810301c005c0c1800b042c2d040c0009450b140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 700673318 1250 700672068 700672087
    0x40f060c030f1e0f0c200a0f03050a0f0f120f02070902040b09121204150201050109093504060e12120f0a0e060720010503010501022d06091c0201050c 66
    0x300310100c1c8130742c0c00d004070318217100d0b200c0d0111250b030701000300c0e440000304030089194500004280043d04502c1c190719880381c02d545520f5542c450583d40203000c1d40c0d00c1d44003d020301480c0190300e4440307544000001a0342040240080424100c0341c46000980710761000400c96100300e0090b90241c0c0c80c0c81c6803e80c07c00c01e211040001c882d0b9402c00c15405030083e6001410701c07504d40002000a0088440354031000605100000d0861f8030513409149038034a00034580002070b50704180314003030009100d1180d10100c010407510369003610a00000017a410001400111260003240316282d01000310b0b40c488900641844858890030500e081c1d59480da410055100003080e124040c0004c0103075450001810324000300400d480f071784009020390302101c01c07045035482101d00c905403242001c020303e0101d0440d490400080c0d0740e01d00210700300414994042c010800c1204942d5050b0200300308408803444c0d0f0400d0140580c0315400545107845684281d41038407007060050140714000c034402413a0501d80b039582d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 700674568 1250 700673318 700673327
    0x72111030f0a02061e030106090e0c0a0813140d020c0a080a08030103081804020d0e0606040e030a0c03020a050706030b01080c1c0209041b0e0f04150506030903040f060c030f1e 77
    0x8140d1070f00d6002c05e141490001c10084000e103000c0c002c5510780b0040141025406c0041c61b030001c21a220040040007041c1d441d43c0c1c0301da841600882e0000000302425113514002c0f0108185c5c21409400d441032030700d1010013507400a542140072a05070f0701041281c4d00c03804e0090302c60a0405c0d001d4003e03c005c20042000680040041007240c86248200050038848000134003642d104440007642c042d2102c0094861304428456283c020350121410030801440360329039500c0740510310043e4140100c08242c03c0c1031500920070969459804000c0d2107645032030340b0703000d00180440208940002c200c10009540c04a6210880e02c020710740e0212180c4020003200080c01a40c41201400d40241e11803080508949002060818075001c548a51003500f50b0302060100340c0c00411074462180e0f080000c20501c0702d05611080040d80c005407001a80d0b6940d0710b05c82e07032861240341d102007a44c41040c503000902c90f90040b50351072603c0c4030f40d0302d1131003940075100115060001d00000c0b21105a24044118459019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 700675818 1250 700674568 700674577
    0x23040509160c0c09200c120a02010b120105090606090906060f0a15080613060f1404090c080106051905090f040201110d0305160c051905072111030f0a0206 68
    0xea182c88031041c2440d0f61400c0b000003469200704580c40e1104685104100c2e032a01035a02254034181c45818005901c000580d2424a00c002120f0140009105401d0500c00c1d04810020b0201400c09143c0b08000c91002d40200b104a603010544d00662002c254a843d000c0400c82c02a14404024521a21054100480015507418040e403084110360005078086003c024409140382d0340d11241014038202c018000708541d030740315880d444c616284041c000082405001c0090b1381c5881116010582d00c440400d000f44141c3d000500120121500095805815041102520310685910090301d0540048400102140c0110340c1d0042940b40042e04502100c0c16440d8098014034108440d1203c102c070060610244204560000351241f0410604050420440406044a1400d405181c11070307107400d511115419085181042001c00741c0061000070090b8034060168080018090b0016890f1034050010190003151000c00c001003510303892030b01207846005907104001501468800d0760030030816910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 700677068 1250 700675818 700675861
    0xc020102070f060203060307061e03020903120408100c030506060d020d1104060908070821032d0f090a051209010c12082a04170c1023040509 62
    0x600344407030320104542560242d086401000c0050342e03400c05105050402140d074004d10140141c038480e0140c0c4202000c04240340e904a03217030040e00c6140903c002800c0c07a8007003515132403000c03000c00c002c039205d4070100d003c2c2c001907000d80b410081c02c00c03110000d8050319800c13aa6a82c0c020030078414a5004c25060300105803c000282000600c114007100c0c0300400d80142d0403003000120500018010900c0030080e0788003030614103000b000034444d41d8040d014a051401d1060410400210100f50580c00340829a03490000071090b640c008003c141c2940c660540441da8202c8145814000c6800324034041501d140303a90b085009040142c000c0300c20002130b44d104034003071410404030040d1407000c40d00020550031100c4031035985808a040201c0501e102d18a210503002440b1240003200d03401190b108200c1e421107168200c464401414a5846801e114845442d142c0010084048050f410761060312105c7c0181c9251401c8154012442a51142c1c005c60169075003103900324000c654404440100356100300e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 700678318 1250 700677068 700677071
    0x151116030b13150e070b0c07120203030408010608100c0c020a060509060c0a1101030e2b05040305102a020601050607050712060e0d0c05101a10120b03031c0c0201 71
    0x10800d035240701070180c0b10710032000c29660b01c1d50106400c4c14244004001420740d031002078240209110304c961281070f90300c200c4841d00d030558858011900d051050b900100603000082104aa6031000c16885020b201c3c80801d605181c2428044014000c60003003281c01d40103090020b8041c01c01070295280d03400308100a030300040c240030b030f1803d481d4100701006100b4440d40785100400500000582642ca4031417219903250041c2c210082c80145100f64440d45440c4101d0700000c00003403110585880c480da82020708180a070b18203801400510b0381080c001c2103001c0369100340d015003100411010104160441c00181c010300d0040006161542c003a1810501401c1030301c1080391394404d425078906c808881115425110303040d500c00c100c4240152040301e0801c3c01c00c001701030542c3e590f8503280c0a4209801e480d159559140c50308488070300b40480c18814001d07012510722000700c0406051000c401a0310910141014041841400c020055440341d024034110150030134040c1c48284040c00341a00074100310b6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 700679568 1250 700678318 700678351
    0x5011a10081810090327051c020117161101110d0207080f210a0212010302011107350705030d0507051002070f0203060f012402070f151116030b 63
    0x90244c45200c0d082da02c139490b0440107886044103c000340d05003148420250343c0b0720348200580d45545440c507036107648540341446180300c2440141e801300039944a89801d001400d04100e04404281d074018101045038944205107401c031086903099884e003000c0c0600711001800b01d5801d110700394000d0000c0c148203009113418060400d5259a1582000c0c40b262203c0c40810604c06081c080d103054540c20821601041d494001c14821554901d82c0600c8002c0c10003400e040a540c0c00070091112030080c1c01007030034a0640103803444910722501588058800f001900340450f1512540001e06582200c0010f0049d0800c00305007107090301c01e034101860640d62801201c4090428060a01c014909544941103150040501d0300601d450034000412846402c0c581d000140006e46203200b00c5030843c0d0b280e1908004076040c42400300e0409840d54802c031110003040402160302d0300072941c1400094800c0d078440c94604031124049669210220100c200d82c0020001840801c4064000607440a0149043d5506 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 700680818 1250 700679568 700679593
    0x9010c05031e0405010f0908030910170412020f0118080304081201060815040504020a090203130807061409060c070b281401050114090607020d0b0405011a100818 71
    0x60740d01100d02d69074600000101409950b801c4102180350809500d400c1e070394282010704466580c0300300c04140380b0600e00d038611141e0080c45803400400c504111020750b889800d0510b4030303149030003042280310051700441c0550902c50005200b646103602c0043c2003e03085040070b40355111103500251040d21020800c01c9003440080c52844010300030440765070b6040c942c0c6071018072006041d158540d003501c0f0360705050a01000d40d454100c4076042d5442d2210045c0e42e915110820306e030074401418014503203100428840280100b07a0b110480701c0c442555000417560390452101d40303c0300c048542c5c141021042c4005800315440c3e407030403075002441a41440301c02d00b45010540542c101c204202c01000c3d00e600121501e113011056042c010304003800e280c6d0000610b074800000500441510500402000c5501c909559a180807045041d0708032000d0b9100f4141820424040e20508207400c0c002516101c0b01e403800c0c100111107440e081503554130040c841e180c02c0c1e00042d6810001018112030710466110614 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 700682068 1250 700680818 700680847
    0x41103030310050307051e010305060105210f0c0403150e0c04050903070314270310020406090f08030f0a0c02031f0204060905030a1208040807170403052109010c0503 73
    0xd21502c00c041da03034072072400b0101860005c10fa000603000324141c950207030004083e083c868103164001d0030b01007455034444004032402c0c0030f00840049002d15109030701e00d00000c0520003902a12400c10307004600d94410140500b1440f075480b00415840215405149070f0803940d20040500c100c140a0b103c4050250700040c090f610b06448290550300006007520806410601c01016000c441d0401030500c0c1070b101140141c4032410303428070311364190640140500d42e0107000394018100c2c2c114007103489a8888200800c880c45034096907090302608040030884000000c1034400441d000001c20b898405480c0049400043d0204103d81600c5826850398080c0f1080c50000310994003e4001038480b80b404030014440c1d4503642c09140290042a242c00101d0307602030340c1c4c0ca1480034508100191f501d907464244e040b0f01c41c8450203840f0541c0c0300c50100d24483c144000744102da0140c8212480421119004400c08080c440703c0805100b040100700310071f5014003450700000307004600345d83c00e2525a024000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 700683318 1250 700682068 700682071
    0x90512103303320601151e08010521012417190503070501141e010f151206060c060e03030f04060c03060810020c01181709041121011a030109050411030303 68
    0x911480001e448012a60b01c000340c1011a517080d800d4001c0c41a0044008d0900300060284070b004540a504068021a0300f00182c1181940d150003002001041a00c02154002c1c0b0740d0070103d090aa000300207a114100c560000f03c5403000c00c05003143c0e01c01e11044007944100d003101120503004c01e21090300410003e2003421030104041c101e406a074582028200040d41c0c03500d080d058003d0204006001c10084421000c040d100540b503492624040300500707485040000900d20501c0d424000301040c09540301e00c81800c2d9500c18041442003254256659480e170000302d03001002685440f00040114125030000c2000220f1070800194068440407028106110344540410080c1c00062480001c0024803c004503100c01c2032030344a425013213696074010b0021422008100c0c19022400340a596216809070403280d445140d4590303502460b14048030107400760180000070291074400012140074030f062042c1c030b02c01480d240c0352550b03080180b0703040181303806402034411003420800c013040d41c0c031700700001c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 700684568 1250 700683318 700683329
    0xe0a050d0b01170a0c18090b010f0302030d0509060d0c031503030806091006170a14180c09160311090a030b0a0c0e01090512103303320601 61
    0x1000550705055603c0c181e00c024103e183c41c1a40700f032002c00b0201d84c60a440710191124451004016070442044001a0440300f4015005000ca01c0c00000c18241001240080b6442034003035890180583e071060380c05004801c0056044030702004608002e2120b50300240c0c006402d8140081d0019403a010710400c1c0751903030000c8012030040c00a03c103440c50400d0300d0b0340e0700c59014a1701c4500d01c1d0400c0c2c1c0091a101d4064050500554040003103800740d84280c1085401070300c0320800c58407910b801c030312412010920341102000e5019041d041c45003410405081c6101c5c221049400490b0400714208400030021608600140d0000303103c040d225a80e080d1403540150300441d0540c0d000d0030402d000c070341160300101c4d00c5020300c01480064107250360000c05a0f4101c601c212103030000300e4086030300c013800d0000d2040e0328011146861141150001c04142d0300400540341e010940b00245e240302002e580c134100d80000b404889000c03024a25800e0342410b00001c05115800701e40076500c001a4191921000b030b00304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 700685818 1250 700684568 700684583
    0xa0902030115151103040308191e0503060d1704090e060109060f12060e12041a1309110c1902152a0f0f0d18080309010e0a050d 56
    0x15440c0c240628980c89080400408a0a20b8000303200107004255010301d05203c2d074101c0c1c10352400ea060094800543c4c10400d4a070350750707203d26030101c0400840114030700459201c0d04044202c11327001c04624120007090321001d1440d1100b100308030414802410403117003660030481340326411002a0140c0000c29082c40041040b92440881a0425074142c000c2440103191920420980d20841e041c1c0003101c01c18800c0c00744c1a006407c0800c00b40c44c418402c10018400c0ba11200c2d402c51401d0014811100c1c18a52010704610505401d07101d4400d00808582901c0343e42824000c03045243d11444010080f00450b81c6011800d074a254204002c0800e80c00c2c1c1600c03940c0007c4254240050103120009002c8812407078030144c2441c1440c2003040e84c40700c00c4c80010721590120402800c00140000c5148a0116020909600d80440c0c1e00d1410320810030014011078480070318040720182000aa0704100701450404e06c03403900450b1070307148442c00c40c0d610920003c030014007a01d8420310b1f000540d024101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 700687068 1250 700685818 700685831
    0xc160c17070815040215190903050c01020a0b180c03060103080a030b06030402100e01020304090f0506100305040203030415090e0f071805010f0e0f040e03040e2d0901090b0a 76
    0x100c0d582000040e6001180941040c43c0f00060340526010b8294065412503038616a01054100980c3c18014180c2d0b80e21407804503074503603141c2c0760000c0d08081160300c658100e074030400001004907181c0100b5240248403030f0f041c40104070504003074082c442c040b0706648111800725440c800024508030b001c0c0c2c0300769001c03500001c4001c0320f594903014100b1038140580d640e42c51b5007440c0e4003061000900031510001c010000b18410340b280e10900480b0010074109806015504020708802c0007042c054038507521400400c0d88481c0c2043c0030340612481660010007650605103008070340d40a07070f003000401500700040c6480100d56205580c0c0c05501a40b5110340205003440d0840300a00100700e0390a2995850581c1c500802032603901c000f030b080b801095031609042503515140070440c91800c89032010303030243c01c2c504010340114002001c1c104551840c4a502c2c801d4444403486070b21080b01c5059030001503031440080e46060308100c1ca040d00094420300000b0345040c0ca40315031600420a68100e114a601c0c0d06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 700688318 1250 700687068 700687109
    0x51810080a0b1c20040c0e0108060406050105070f08070b0c07050d091a0a03060f06030c020d030b031b1215060a0f0f12020d0c1e1203080c160c 63
    0x10603001c2c1c0400507a581c8846804201401c1548418600000d00341c0d07a242004949040e1200a4078081240c0500103000b18441701c170b4040c00c0c0d04100400e142c00600c400c80080c1d0289130038000c050807078906860300361401045445104680500020580d44010200007120028007101c0d0454400c0b042821443d4071000b003460902d0420010138800000c02c4625001404940c030100c00b010058101030490596403540d03484150050040c0c6d6000391031803241090000784554050300b004c0c090401c29801c0c0e6858000d0820160100c952250145070035600c00b400500325420450100b0411103002841d90820715081d00d401482d0200400401d09800c003442c040c00402d003040d46c164000f03064030789101101103007404009101407042d1700c5111f50114040ca0b12200b90348800031a108400d0301318511032401c0f52140c08440c552500c1084002c4100380c1c0c181d00042c254207140441c1075243c1d05684801468440c95942c0d0102d40110350802085580b1100b00303000211541d0707004006041c41020300300c0d16200784 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 700689568 1250 700688318 700688321
    0x8030706060e0f0f061903020d0602120601080c07031d220515011e11030703080906070e060703031505030706030e0606010f080f0c0708030a0b030c041a01051810080a 73
    0x30f441c2c001e80114030343c2404408a0448401c59110f003040d030f404203806c103120210f20032052040d0720183d080000160390906020b4143c0090182c01d0300940c51850903100d42004503070301c0f282124a180c5500051007030000203071142d090542074030180841c0808103c48600043c030040c00000304180307060020403103aa8034040c103000d03042d07011500002c50220342c610440044c007070f000345030304d030f04401144200015526401566107040808440c0100c2c0d403501000c2c94081c0a400301654804d0142c45003c001a10541c03040d80f269007151070103010345041c076406079415001380041d841e203808007165805001c1038036101003041c40b0050a560380d02091415204540f113041081c0985090304000c50410301c4405190040815030b0080040c200c82c0c003541d1b40741e40440e001400781401c003c012200c0001800200b03161500960840c69048098868208592081200700c032011904560060b1000200348120b40c0118042c104110a0300385e8035014a80020000c0d950071103400b59800858107080c18002c000300c10303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 700690818 1250 700689568 700689571
    0x61806090506010c0f0c030f0807030e0d0312020901110f03041d090c0105030c19090611011e0f1d03041701110d4a01110901031508030706060e 63
    0xd038010840c80c01c084000a010445240000c1d040180001c1104100305a80a48900860b00071600c0700b10603003a0301e007a000551001030141c2c00905998807049461400341d080b680072aa140c6c44210003124548945400703500700955003414070240c80c8900a00d48028003000090000660145942d68240850610118621590f20555140d40420411403a00000343c1085510007420080e40b02c0c2e0ba25500c81800c1d10078100c20180480380a030301d803141c070b54011000c4030580c1c069072a050820005101da4600b200e803404484000c1040319601d103103040c401c551180808641e904408184e4109055001241e801c40441c0555282e000190811546100c000083c00b400340308002400607401d00c207407010807800b54400715442103540d130102d088050b4003800b409690541c00301c5012038802c1c050f90549807a00f10f9a07104e07021245030f0a00f181101c60184101e9030000d20003210036090990b074400441c02004d44d04201546410b800c1d00c00300340035104201a1109a20800000c20007134100907000350410b60 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 700692068 1250 700690818 700690829
    0x103030207061116090e0709111e121819140c03030f040b130504050424020c071e210201120603020d0f0501150305010510060f080f07020709061806 65
    0x84100d101383c40d02e8030b20822500311141c0b0140030410021050780982054a2984003038115860005204a40401040680300c90140310219034017032000c0c249125054402c0b40401d10400709508009040c21140f41d400c0342000c460001226140304c03841c1c00d1503000703010300e01055400d1103c9850390b0b001c054003002040700a074001e5006c0c0d820306004190400741d50195010716049488040342c4c0c40c4054103900041002000e00070028006414075003440b1410101c189118040202c916040b521b8011460086403814001c0000400c83c1070f00c1c108050061902100000550715108540041d40c040202c0310412031554643c81001e5260381440090010403c040301d83c02107078100401000560307200003204606030f4102c3d8800c0030300d04081c508a4010408403419071312821000c8004014044150b110a03c00c2100c030600d106515100d100c00d0342c55a48a085032000143c1c1c8000092a00c0181c0a4803904118a070049130800c0352a030100030b0a9032003503040340f0452104908074007400345a50042000030403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 700693318 1250 700692068 700692073
    0x305010b03030f0301090509030913150f0f030206030414070602160f0b0a030203040f0506100302010905030a0809060f040e0f060103050a0608120913020d05010e15010c120e0901030302070611 84
    0x103086410302141c04141b04499155507038000041103040d082c0101c80090000400000303410500e000b410008000d034091f07803403e50383c0c4942e010900d02505260702c41510460700c1c1e10080360746160b003000210b0344014001c46240c280b40700c58403036200013007200700c020340496006042d40c0790400c910640b0b046002c2e0b20071901c80103283c00400c9640c42c000102d540094651030056503a64131414080c0d448c03400080024007600c03500c2d04201d80c5c4450a4044c10541e4400da0320400040da82d6001c05030b0b135030042003004c0c0c07591a0400901e4501e1520000914200031070207205801d280d40c40d0903581040000300c841c0e424110f90207040000c0340d83d051145035403111900104208650500040c145e541954403890540210005a69011942c940040d05a120706000082d91b4501c07400d90001c0180a0071322911071795640f6400070500880c0c0c241d1000302e0241069581080000c00d5032102c80c20380d07901c00d0b0005c0078428a034080c0c0b055600c413610301c40d010f107001e42c008141e03035031404d0302c01403a850051800c041140c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 700694568 1250 700693318 700693327
    0x204020705030421110d1103070303121a0a0509060a0305010204060203030f0702010504240e1002040501020d020a080306090a0e060f0601120911040507051303061401150e04151e0305010b0303 84
    0x245c0c4000701001c02c0b00041c1c418030b140780e440d483c288448582c03206000340e2603c90030000104140c0e1150a2040c410003041c4280118034055010403002440d086401d944a86038000a01c05402c0001d5800d92226000b080d14541c41d85d41d846485c02c80e80b1070303088103005030800030800400405009815400010700d10007001540b919132507950040f4a0b211031403c80205082d81074800f8685500315051090251041d24181d140323448118000394030500c59240980103001415000e07500101d030740a61140c024031258a10340e100380400208640041170300b21180d030360340c0c18021044010808544280141c280031062424894000740094504407440c0c03070b6403400c003000c0d003000800104405c0400e62041d40c4c003003002d4503184815a824001c50703642c081610b44050000040c00b1098104655100700e8001203202ca036220022031415000880000000c84d501841400140c20541d018101403034010408050b5291240c0c40c1804685445801940059a4120920078400280f084011040c002c40056140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 700695818 1250 700694568 700694573
    0xa021903051611060604110c01020d1a0306010e0c090a12030c03081b0a05070507150f03050a0b0d080c101a04061203080c0d06031208041103010b1509030a0204020705030421 76
    0x395400101124080c91303c41054400c0c5120820940310000100000ad41d10380928194120017401c0036443c06490303542c0b05031564014200803401505076000e02d00000306d07a903039812182099620500711560019010640000c8200300e142c20040400d00c00d03a02c40340c8410741424020308205010304644007213a220072004080311030100c100c0301454200e0505e191200000d0806905102c03d991190004080c07265540d445075601051400c400805e5403800c212780d40b21420100100d441c1004c800f40c1114030b1015040116a1040261269602c0301003240c9050055070301c41002d40e0154a040c0c1007100a03021800c1c0035280c107018660161404982c100394801154030004d25180300a404981810700004a4079001c000c02d40090b80a150822030403e0200740440008021550444c1c0542c2c014050540140240c40d041c003610102081c021b16014014003a000c80520301c1d0712007485a6454820b5403800001611140054282140603201a584491400e00d503c29881c040c81c1e40303000c940007085e691000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 700697068 1250 700695818 700695823
    0xf021209070e01150c050601060c051213030b191e0e06040f060902030316050a120f231b070e07231e03040b07110c030a06050a021903051611 62
    0x46851040303200380003007000b22045e91002d106041c003a0890040c1d038004105c1d60f40005104000c0b40c40790040b602004440d4081c00004c0c002c0032501c446507601200c0c1080492100c0c0421900b044500e80c103603102410341200503045076070b0324903080f00400811000300d00c0400c1c0d910650020010307000141c0242d14255448080000301114000d02d400d030b48403822015524204140c030b0015201e000d1007880c1003198240b081d0340e1062448101c8002030182032600c0387e540314960380800c0ba0380c15126080c60313815805540040d5102142100c0780710809006114201d0413000d00c0780440c1a698000e8030f81941030071200381024030004d00078806c1c8510015000541c2d4400c029010998040340c00040c0c44140d02480380304404854071071040301a20100600c01401171110411f402004035881e403406200461040703503110301001031a15899040b0942c0000400c459402081c0e005900711001440c1001141001e21240f860b200d0040004e030f40d0b181042010b0f82c0380800080c800d002801d184c00b098108010855 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 700698318 1250 700697068 700697071
    0x1101120c0923060708030105040f060302030a0f080d150f0611031b0106030209072105010b160f140f07050312300c090102120702060313030e03010f021209070e 70
    0x100340c0311400010400c2c0c0c604160200d0312010000e00c2a5607132040c80c10488041c0d0020b01406200d18900045007244a0440c4102e0045a81c0507000d407a40c1e00c03160702c2c0e1303c00c0b0722030b40d02040c0c0b52504100610140034203544a01c0340a4603102d40303200000d508181d040042d05076141c01900034810035400c007004d40c3c4800010b40b42d14031000c01c4c0c0065050081c14000d40035240c640c0c0004d410510800074841025000300380079600841c0e10a00c01016a030007441c07182a44c8080c81025804a01005440b503041480c0d00440c00085c0280082d60009165540c1d0b0014840842e4090790b0035005002480343c05041440101e0061000b1002061181c0c001c3c58506074a200340200801840f0903020b03520805404d40e073b1150f803010340141c1e000d051890156003180c4242e00403404c0750f0043c000c80042040c1400488251803c20f50050010390950341d41d1021010001031800d001d50602c8042601001640d400340038480f42d0511082c005600d40203501d03001100c07180003900e0f4501c641c004079814070442c0c03003610646 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 700699568 1250 700698318 700698329
    0x240a0b2701300216030e091b160f0305031905040809090702100c02030901260a02090d12050d051510050906041e030c0b0c060c1c091101120c09 63
    0xc0c0c420500340018484666503030b035410030141d00120b400c0301d03045044001110041d0003030319440781c0040203034100450352000300c07843c2c141c0e40c141c10020480d0300c10110140043d8041c0805614081071103849858000307030f04600c1200090703000010020390b084451503a5100400b558010702035418503070340d140380c58050308890764001d020500000e01c15610030030440f41201e0030b0000030022101d01c01e000035180d51286a11501188402406120341c00c00165650a0710749206601c0315580c07102c1c042000070390b00038004250b2100d0440e00000119500100315010904e0710b8440ca56a482004410030035100d00500004a01d045407862001ca612b50000910240186180a40d0345240140020b501ca0166400543c0650f000c80b490b4881c1c654030480c0b440c181c81c003400c8920440c0e5a20041075491340305201e000700040d00708401203410031031840c02030404094402c410001203042001060102c440d042403e50341080d10020103103003941c000914207030448140009203c1005800707030240005080e031007803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 700700818 1250 700699568 700699607
    0x70810122a031a0604063c08060c070201050f0d0222030308040b0601031d0a0b0112022404030f05210c070e15030706020610050d0209240a0b2701 64
    0x10f0240c1d03170386a200700c0203070030050100c854074201c0310610154001c80107100120b00c031480c80b03808043c81c12444200c04891848009010591302d03440500015000020100d05011003070201c45900c65606015050443d0044401a16a6408031805444845510b40121440d009640c240003003584036040755449504040005500c0e00c0d040b00480c0200741d002c11182c0c1040302c01c1003503007017644080f818641d038a009030000c00d1143d80b500d1f500e8052901a4000940c00000c5840c402010300d0810000701ca04400308600c00d042c02d03501d46601806042e0f01c2c500b1621508402c82700004800b012034640304a20060070403905003142c01240b15920380300380c028202040d141d2030009000040b01c0280205054024060302c282982d5008040d5503140d0682c0c3d01eaa10388844840400c007400c100c08002601e44d0010240481c94032000c50b42c0c45142c5504a80001c03012480f00c0312041511861a03c00051082c2130f00c0743d5440d40c41d00e1406030075160048a00541e00118401d05205a0740a40c51150502c94403c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 700702068 1250 700700818 700700821
    0xa02030603070314030901121407080a0209090c0c06070305011406070809030f07050306070c2d02030f030a03060b07050601050405061c0b040c1d070810122a031a 71
    0x82c0707410700e580c2c002082c000d40c00c1c40c031908804d400f0014103400700007038036482040c10f40c000c0c26800f41d41c01d4000c03940740d4041000000c0e40c403c0c4540e01040d00309500403001440d1103681d03004581c1040040710107502a00000943d171510540400045070b1013030031172038200207650501891100301c1c00a141c080e44a008045220b01c00c6c00196422141e11100007004c49112200d45440729403103403524400c1a102e03008613800074407014002c2c1d8500d005a5400200c2000c2c25060a60140508104068241c1c0314101042e00750300607117082100480b0b045104004540315001c200c0000c056a03ca40c0006040d000244035041c0021800209181500e5046501003503e64951000c6000c0800c8101101401581b907144182880500a003190085014141602817941c540e1424054241080d2100341c090120400091241c1e10452400360001040c80c0c08520382c543c0d072000c440408400740c0041c0d80c1c8a2901095141081215900004000100200c4100c039071454981d0b4a03102007210000e00c1120300d240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 700703318 1250 700702068 700702081
    0x40209150a18021218010c0c0305160c121b0b07020a21020a030b060f060a080a0507090b0d0204050301050a0e031e09040903050d0b12121e0a02060405160e0a0203 71
    0x4041d0b6285460001d1055030918051502145c01c8903200e0940103507501e01160f503929a0b10403030400000b2034140d205c071890b019202021690100043c00240c854000000c008280143e8410105e41031601500350310241c2c90015000f518420610b52050840441c200041d80c01a140d2140c92030458402c8440f06c1c1c00140c0d07808540c0070060710024001d501c14400d4001104225851714013500030001610910701200d6883e06201c018403428800102091441c00018050b90080d00215440f10180c80c0c03180a031590740024201ca030b0000d80b20701115039004182804142000d00c03506070f02014410062081441360000c07540c40e0b1140060344100e4101a22903a901041d880080783d001c0da8018008201e07031400c50900804540010081c0c80340182003a609586d039251a841d0600d07110100c4001e4010815101c031014207580c00000b140700750241d0f081c1c180385002000c0001d4880c2032810f80182c2803a150900c0c0060034004d040e0f000074401900aa03051040c01c0e100940da036440070500c0001070f641d490b400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 700704568 1250 700703318 700703321
    0xe091002030a020d020c030a0206160c0f020a050603240a030221120a09031b081c030e010c020d021510050d0f150b010908030909040b071106040b040209150a18 70
    0x100c001d030000c0d4000141c0340e1b4043d00000040000c0c0301c0c6542501c0407070726070640401100345840481e2000498800c112800700324440390000c4c0b510310040c0080880382d5030f0008100c054208441d2034141040018510380c44c1c8040e400103070583c007070032103003060200d056a0028041821032400900b5411607410b05903021032040120713000d5036542440b10364030703003034450701c002c1c9810a030b07002c00c0b10511561940465050740c8420300005549110014151040101c4140340d00d0b0070a5441001c00c040e1074401035107070310800f0b100fa1141d03c0b072a41d01609006401b0031b000f0f8540710b0408130f913403611100741003040681c44080210505580d0119035000f00820b19091028205900e44005483d407100400155903654440c1d1064612800a03201d801c00b01b541c48609030346074020141c0d420f42101400c40018002607402592a51040b1142428400e240000307a0352450440c04503011101900500140b2041d464600344641c0d00030400605403091468210226070100c405e80b01d8004404028542690000e606 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 700705818 1250 700704568 700704577
    0x1050a0b040c0e100c230a140c0d060510030b0405030301030b090d02030d051b21060a0308030a0c051306050307080a0204060e12121c1104050a12060915020a02070e091002030a02 78
    0x1140d16a016006d01d2074905601c4080801040b214854050b888017084600407070381224404005211003c1030240d41c070396801805000341402c03e500100440440064828134585000b1801080203645030340c1146486803201101070a01c1003241d0008100c0e104165000003216440c1c1e88501010880c0e444401c0095100c48012114103040c0c10701041e50300d40d0b5020b0000e010280007403122140c82c10380300c6c8000c2c01140f000c0ca000c082c2245500304000740e04905581c10102c4030302e94038035010340b520084095010110031a80c1003a40000c070700000b4420443d9020b824550442c000d4070086243c01d240c601d0240540000c40d1801c0c3c09106032210030400c2002c240034920fa20050104003d94541e00b40d0b080a202611907030b0400c0080b40781640786205c114915041e5400e0f0f4030068100c40c90603013468086c1c502840e041300d0448400f611208050001410540803d445041858000d600d0b81400d05019042c21203513088141c8411050040098201001407903240d4103001d00401aa43e40300d8148a001034445d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 700707068 1250 700705818 700705853
    0x1f03080901020106180c0e0609031018020a0e010305101803030e0c0418020a2411031908010302120d0807030c03060909050a030909140403050f0c01050a0b040c0e100c 73
    0x360b44900028030a042d04205d446d000660350710400306441208111032400707040140398141c1d1200c040b20600c0710350b40d8051420601c1541414031300c1449980010352111903034219007503402e200001001040010440201d80c4001ea4500307005421007a50303000c104449d1040e0107070405468000c401080744052000d00300c1404084e01c18040031780400c502d0122341800030001c038020f1071000400250040714510f645401850040013404c1400d00401c120b0704010f0040c00e8442c603000c10041091807003001d801210901140381c4400050750f01d50300400c0643c4646100141c8260400e404150f2a07503404258294040320b103060015a11250001c1100100003a400211714185403c441000f4488002401c04200e4801c7da19107441e9a2aa1043c0055414010150f091203605101081c0003078003602c0603001400c141d1419a051500c0010581d080d0351003a546426000e82c0c0f25082d01041c10a4000c00d00914640d05114501d0a83d8002140002202c00c0100c000c01035460755035401c2001d19041c1d28401e0701e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 700708318 1250 700707068 700707089
    0x1a0d0f0209010e0907090510090507022506030b0402120406020d020f0403050102030f070c120c06090b071805041406040e0118030e04050604051611010e01060b121f03080901020106 79
    0x10385031903d4884050341601e26075010b2107080740004a180c10340c0a0148201c0180740075900c140d2a000b02c080241c14041c205070b00354001c06080414035030340d1100c44400304c0081145250614603204018040b84e80400c00c0034000c07030040081d0043c030b80081d040c0f00c5d0019031040005035202d541501500080c0103044041c00b408400003000002d03ca015009103000d40722032184400d994440360800d513500c030a010f000402d448400302c8207404550242c440144403034082d10003c01c0c502c140383e540744588132040301d199002c0341c0b1004000700296054501c00c8003909017540c0802c6140720b066003030520900000e0100e8032884c0c90f02c2000204540070340080310080c08055840f90b86c04094603003c0c01e0410410007490242d454000000d032a4070f0140140340c018000d0808500d070002071010100c2d901460b0410108440d92034510b43c1900103400d00c00d190003088003410240d19206842060f02400b8005054044550298010011a0400345031084104e9500600c440e948080000050b07025240036408001100b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 700709568 1250 700708318 700708321
    0xb1b0c0a0302010e33150d050a03121a150d05010b04061112070204021303050d05090a09061a0705010e010221101a07030912050f0607031a0d0f0209 65
    0x5405400000c1610403070001d0300e4407a410364404900e4074a2604030b001400b8221500309170903031096131340f094011011901c02c21a0400c07000211300080320b00d482c01c590320b900c010300751403c1c994041d8943c0e100080c1030206000c0d0107a5070080c00312800e40a000c9500c582104070819010320024011543c41c002071507010300581d80e5a0610441c95081072243d20080b520f0040c0040b007000021900c8941070440c98025400c00c2c1007502488000d400010060400301c030700345c80100204038100300d02118411140da038540d45040290a0240c0c400483c3c1c4002483e070b051410510010030220641900c1c17183c3c07041402d80343c09072420314901400080b103410f5100c0d4400030f58580168500380429661207817031040c2c40083d480b03420303c80720207200394807a60087e0348848038540c152034182402007001602901e40389071000e441e180e0072580170003601000c440c264002841500611828403e0b650701c20394900b420469504918070140d0640b00307040405100d90162001041001200d001800c2e480da0040c018070801d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 700710818 1250 700709568 700709573
    0x20406030c0f0603150614070b0901050702010e0c0306070c02180c040f06020a0f060f0b04020316090e04170307050f070c090b1e0f0103020405100c03030506010c0b1b0c0a 75
    0x12500c0307030145140b650381c1200c011840314024010701e0450400080d003000710340e103460760448110340b280f40b40c0540358604008100c0451600d20310075026000b1400005410b040000c03001e400c403030060342d000803160814108000107960204859030b00000b20b06201c01c248140d40f0000d85007108010210721041100c0c0300f40708000e52070300081e01c00d0f541360781e40308580244c4860303059035240320184000307240050f00c1010900164168101c150b0043e140a0080b420740096000502139820071a010300007404034800d209a05540190920010040c1c00c0c002c8100f82041d03102c0d945a000c0d800c0703040e805810004080360015104008840800303000c101f44d1031b1074500524298030b0805441c03250240d95403c00c28045900e240803601c54180003020707031000a440454005005080d8600141a41496030a20002540d41c541c06032451100000759120f008039010703807030302030110341014001070b0400c1591400600000c020420480e004031113010b00c0c28040181020501d2244541a0008040d00946414004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 700712068 1250 700710818 700710833
    0x6080a0b010513181518140c1e0d02011e0201150b0f040b1c0c0203130f080c0103150b030f0f101511071502030c060609070203090d032f0c330702040603 67
    0x40947c0b4415901012000c40c100018075401c0c80c041040741c25424121481440d0070000211518418181800d80320008400f100c8030102d114000f5001d49d455880541c443e01e042c030711600240058004c0a41005420a61070341c150045025013a0080700c00201d0700c103c1d040c81004d80100700b40041d402d01401c08070f100000c2d10f9400c010040d080c0501001404107c011065070014140c13102c0750000d010640c851001103000e07014418040408a65000c000304981880d10020361154030340c40040901810a002280740440005004019001c1c41d0f81c0c003840390b070f04018440810401c551401c018000e0012802c1410708001d50301140e041c00f6580035003011150040003074008848028207460941e0346000621004c1d20044420900503003041180700d02c103150141074440b18a00038902014050041c00d443d9807140e110f050301c202541848130130000c0c954020864241d44150031303100c800102042c04076520b40d0700001c017245100780c0d00480301e00c0c55030441e036415254001c0c0c0040041c04440d0740c07402c1292 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 700713318 1250 700712068 700712093
    0x100f1403010516021c1110020a0f09050603040212011b0f02100e0d051b10090c05010c0b04110f0405040c0f053106080a0b010513181518 60
    0x5000c1c0d424074000403101da6460005516078180c82e005400b2510158280d202540c0f400c184c5c02040c02031400039503000c0c200170444640158144400165200030303800004d02228031144a41042060417141808581c03281000d4942262741a00c0c201550542e0394803a602500d0950419806151100121740005034008141e002d20781254003641c696280c07a01c0c1500503101c001800b0705c5541e1241240001461040e40202040b000300307c2e100d80c50032507411a850820120301c0170400d607252690460014441a400e0043c0180024200102c000003140c0d5220b0006030010300c050036406040071011041d4595007081c2e008048001c0c400c000078506851b00c241607003404c0c01108c0d44890080c1010800f400c0c500d00c01203001941004140c0d074078400c4115061100014a008030a803504c4180c001200030b0704000c50800540b0610700c01480c1c0d0705003804d020f024000c40000f00034540c1410000071080348215000f0706e502d038010003260040320594040c031003c0c0c210001507540d01603c005840041c051208c1d16071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 700714568 1250 700713318 700713359
    0x53a0501091802061b190804030303050708070807030b010306080a030810060f05121506040e04150209060d09020f09010b070b010503151602120d0605280e100f 70
    0x4114a400200c2803038221084980c0c02508013a0800400100d03042101c041182400c455044489180a205003142c0b028600d035402c0b2214003010805104064050003401c0e404000782c60485554076000b90000d0a0f0385010b060501410344d40c200c00503160b4030035006080500200c1c400c4031401109890000d1102c4800c4840790055100c500003c50f010b440780c0d003500000c03441596010b00302000c6403c1c281d900100900000c12420006502c0c11907900e994020b0002011442000196803a1138104009000718000c200540703144100308016155a45030103a88250100350300000e00700540d4070101c3e1008003c6500951b0281c2881e00025000103070400400781507101e9031029295980ea0420302d0303652103800721540b0480c552000001d0408510320800924040280704680b000c4803240d40e84035003070744500312006095860300003d000c40c0c10480360707119003441c0f0721000c5201c43c00b102103024403075401030003610401700d40080030a1019050300b64110280c08507070041e04003103940302d070240307104a0f059254 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 700715818 1250 700714568 700714571
    0x10140f0408150c0f250f050f060906012601111c140c031e040507060e0603061f0c05120901080c34061b080610053a050109 54
    0x1c0340042003100d41d040c0500c112500c0d4600308080c130071101401e134101010b8030075810800340308101c0c0441d101e420f0214850050180703040081507400c000d401c3c1079007080c40e030606500071000e000d2850000510281101d01180e0210074001c2c0014001041800c0c1405a542e00e60070010b81c103100c038080344010040e114454a4210340103030314bc4040400d5401c0f41d1464901c440480c00012030030b00b1032000456005003640f40f82d20300f98800c08041642e01c4416241520713107901401040c000241c00c1142c00c0c2804808684032400c4d40380c130b800024842403181c0050150b000c0c0d40d8041d184042c0c0164800f070045036000050f81c2d20281200410640382c1c0242c1c0e00180018880e0000c00c6075001d41c1000c45014101009903101c1107200030034040c0c07071103412484030214001b135280110302007001d5101f0048206001005429001d1a6040c010115030f00906187d1042c2030350400c60500c0c0350000c080312110340f1101c2d00c4032100144c2000070035515000980d10780d940010011513074114581036102c541a02c0c440d150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 700717068 1250 700715818 700715833
    0x60408040603150b0703030f020715090203010c030e0c06160b010b0c060f0106050703030b060d1d0c010315030b1b0a0816020d0207031b051206091203060f10140f0408 73
    0x2101d6284601403140001c600d104018290100b4802e0b08a40d1110304098400350ad8051f035503680400034090701c050002801c0e81c607450b520442c0780a0141e40e1103031180b4a400e000301014015400d0301d541010911328800c1100088a20b141e4801d2484100c55640084415005695441130b0301000d40c061a0300c1151402a00c0c0050b060b07117911000e01d0f043e03481d41d40c1d07081d051011607035041c1c0013483c403240c8840e40140140140c001381d030300303070b00880d4015040608200030307503500b2400151904945000c018140350034a00c4d00c081080102c0d000d070044a40200aa02260b240d914080003500ca540212400001c00010011007154102c0d544500900d01030414102c0001c0c61502282c460040b100880300503000400104007084281d0705513030124015144001c900c4e9515000507106404142c5400c940d40c000d40100050a502030007814103281040b41101c1c0740d407406000080152a5084203d88601070a050701c40c0280c1c82001c024440300c007807422107952403222961200c1950098400c8042038800c002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 700718318 1250 700717068 700717091
    0x1d0901150801120b190b062a01020f090618031b0111070e0a0b0103061206090b011e15031e06050a050406180207170a03020d0b0d050601030b0c0705060408040603 71
    0x19462940144c0000c40b045107030b265151410a60201e05040042054403001c2600b034569614000708150006207600040318920b413010f60344070b28411400e0040991061200754014401c00084031100d980480303d85580e00c02860481c142494082020ac3d0180300f4241c0c448000e03981201c0201d0752034426260300c03001d14140b124407503880826005400c00c42c40f4800200b4088441a04802ca0300b40050401060154461108200f0001125000d895541d2501c4150042c003950701304103805480c3c40d500450134038546c20000100d108061040c00c4400110141b0446500c0c480c2e40324490307004000c0c0d050703003c100320700300c6d0240545158064580715441004002030a490107205440489038146075944000c00341e0b1034804001d400101d0240e0b8440450701c0515940c50054000b44264407250314016140d60080705080121003900301003901038801d004004000ca40300041890440398080d4085020b655050b220301c2e1507000e151801021b0788252400d10081029040141c0203949143d6010415407841c2d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 700719424 1106 700718318 700718339
    0x6040b15040603060e01080a0b190203190501120b010504050c09130524180c0c0106030b04020f01020705010804030c030203250201090503011a011d0901150801 70
    0x50148002c0d0740510441c40034280d181800e01d00b541c100304156035600c0036640e0203858512400001a07090300c0780b040400703445d0500b000540d168103001c0645000c91450721a21000c0c1e500348400401d1409142040b402619003003908120707207900e00000d1100404019202003495803042200b480d04d0745502d11105030035444001700041c41d25104251000b401d00d11b042000100c1c0310b100a40700c0300e60700c41c02d1107007600015000640f45900e4800310303400c1d64403c0000303032551542001000001e0050410020344940c2c0280d60b800303250070a0724012600e4074154010a80440c107100d0108003c40d1140b80704c8600b26101c0e00449181100c0801a4440c0740c008400c1d0000404041c0000c108550748014001d00500c810340c0248224840c01054a130b494134040c041d6030402401d01c0300c004ca0416101080c0603980300140404030030b0351712800081c41d084064034070030b008100620300015101100 = true := by decide +kernel

theorem cover : BRFrame.Cov 700539568 700719424 := by
  have h0 := BRFrame.cov_init 700539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 700539568 ≤ n) (h2 : n < 700719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
