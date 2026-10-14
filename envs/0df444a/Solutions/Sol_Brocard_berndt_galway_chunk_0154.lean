-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:08:42.42499+00:00
-- url     : https://prove2.me/submissions/fb4b73a3-e1bb-4e01-8f34-ba248fdf248a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 27517991 ≤ n < 27697847 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 27519241 1250 27517991 27517993
    0x50616061a011209020310050a0e150402010c06020a031b02030a0e010503090714120607020c0f06071502090105130b040f050303030f0604051009150e10060c02060c01200705 76
    0x41641c001e508a001070885412600007002c159480701504071a8202c0c0c13007280d01c0a4102d88041c1010704c0c03118111982661705000c020b4440103d61182e0308101700c210f6542d21a0703291020541000d60020f40304040e801c000078a200c2e0003040c020f1003140a940b100c060842c0038000304400002c0031000a4999200c0c80280c004601c070885d0b40d500c1c41d40b00d42e055034420f44409001f003840c182003c074503685007140260700590080d10002d940d00585010700503e8000c25082d001005e20000c42402c0150212102111302d008207400e1000c1004a590300f44002000c20f0503041c0160355650300c0004031124421800c040d6940210380b4000a0740103c0303807008008440b214050040d5241d01c8038101600c3e031000b500d030035040c100400045090391620794007540e00a4103518142d8040c0340c0d03030f0000d00191030701140c14440c05000c0c07007010000300c14006c100b280d1108160070700210043c1401005021584c0a100103800f540020401e084030000c02d601000d4480d080254100f0011030030112021a94400b02c0c0880d41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 27520491 1250 27519241 27519251
    0x2010c140903030d0911190f0501030908030f100b0408070509071b061802040501080a060b04050105012a06020c060114040504121209080a02010902040501080706020d1101020405061606 81
    0x206100840c29a4524031004028520340740c080340044001d4044034000781d880351103a0025240350361314200400101e0841d0003d240300d1a245c0702450920400743c0c0d000c0303070526042042c2c19001642000c1100c1e07002c24166000080c1d070321001d0110b00b6425940e0442180c0110001d8049010305000410000b2078500321040b003e6523841040c103c0b09101000300650a0005141d800c50004092b60005100b9900e0140d14100320401c0e40c0000d02594000e9001c0c04040e0481d00740a000c0c00618080c07403082d10b0059409003c039500d4440002c10710480b02901807a08250310141805100d1040c0700040200c0d0408020354035900591082501d40c00c080c418100c0440030307c45000b0355400e0500400f032003180c02c000d8030b10075a01e0b516000d43e00244045c1b901c2440950390b800080c00510464041d100d01840c903400051400c4080c414001240c0c01a046001c040e800003200f004050360001d00340b0040f0406180c810b0f07402d1101414140640180e0304a81d51200d40401c01204c800c4081035602d41640c066402400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 27521741 1250 27520491 27520517
    0x507021c1d0a050d14010f02070308010302030c040902130f020c03030103030207060206010603050c12040305070c090204092004120f0b010303081006170606090d020901030f02030f070e0a0906060803030702010c 92
    0x841402512a144c3c02c4060019030324080382c0304a0407100310100380000400c40922040008040b42d000900031004210303c00c00600075800c5c2040003e102200c2650100b0043e0b155400041d1000a0280a905c2d507949503007842c007090382160113807016501010b00322a1656120300c2c0c044e445201501440006125030301c000a4214401d0003981d008280d6003480c9480e061250752030140303c0000910035400c0c05020489100021540100038009107003c00c0c0c0161074606040100c2c06a603100300b4214160140751a03405101d205010485046507c00114036030000000d103424180b180076035101404102d1014000010b0580107041c041c410f180b54143d0540850b15504182c5480952054002d040319034040010107a050030001410401001069078843c16026800103005076404d0f082110f01d002c0e000ea546085080404c103901e2103c2d42c1102801001d810b216040c140c059005002c0c00006444201d62000c0c01407550042000d0700c0301c48280c2c0da483ca401e42d0041e018040d0310200d40000303201e52041e2a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 27522991 1250 27521741 27521749
    0x10c0206070215221a010906050102150c030a110d050a0c090303021b121204051002070602150604090204090503090901050901060c0b04171c200d0507021c1d 69
    0x80341e05903044046000903242d81244266031a40c2c0c580b1a80d02d03000d030a1101c0049035011706000318a8054100c1d1400c50341c18400071801b52a0180d2215040d503025040d00c40d65549201c9540764042032018001d0b45a40e03404200201038500001d10303800801c1d000450080d090915080a0320035140c80806000c8041e1400c0c040710142380610001e401608058403030540344090903c041030001c0700410b1161114207a00c60241400d016010510040000090801c40d81c2003058107400f00340c034580060064140341c01030181d04d62150a100506030b80302c4c000000d001303a80700d90003801c8060700600b00b0400030724076207006507891348400507251088007142c00015032440c101c80e013103040c0c8203a030f540e2442c5a030315a903500c0c9003500084c200b111440700c55410000c407403c411000d05800c0903207800c10001c2e030311942040c1084804c44080d00a4900041d00c0003a000c10425048807120300c82010001000c0e80c99a500724248480c0e928601010002d140b1044402603021745807002040105c01481d140c440c1c0c1400304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 27524241 1250 27522991 27523003
    0x20403030c06140c12071103030a0c0e1206010e0405070305070b070b0604050103031d0607021512010f080a0f110405010618060305090a0201030c020f0d120c03090515060307090e010c02060702 84
    0x240501a20030010702c0c1c445d8682c0344a0503041296800d007001e007400200c00356800c1d038000300d4000503a16512180075050641c4507142151005007511014030b0044002241900c840c5c05000301c0d403500345c110300070a080220401c4001c0085800800342c0301c005843c0c40301180d07680d00008058031455100c10100d40c082c0b500740300e0607040307e90640b5076111041582c0405404100c2010b262940314900340f142c0b0015889810713510000080a031655a5500e18603050714802200c10307000141c20100c541800d1280032800510003204e5501b000d07003070858007160303c3c0c802c91410500342c255030880e0800e40005541c075046020715800c031182c00c080002258582c5e20450031150200c4005800c1d501c14426080994025405400480380c1441614510b9000b012400c0c58a0341381c400050000789000d00c10134004a19224410548289103400e0000c684203480b041e80d01ca5100c4400703092641044003140080d030301089107100400c6840c0b0207000c000b40d80720641d4000c090643c440b20140c01500c0c0060300310352000c104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 27525491 1250 27524241 27524251
    0xb22140601180e060a120605040201170405060c1e160302010b0303090a051215040f05070905070c060f0209040e03090f0402030c0f030603010b04050c0d0c0905010c0308060310020403030c0614 84
    0x5452a50340f810b2000310503008054505030b000303254080d0200c2d07494180170741d00855902511003c100c40c02c0500c001040300d407100c1c00c0e01002035544414440001c4000c903c0c070781c02c100d12000850300d9090030b0007459030140e00940c10f03010b0318900084800001180e0085110403034025002004820b0b8044c0c14581c40b842000007641c0d000f484200c003403110349019225456180f1158045035071480381c1001010039100c013990140c5420200807140f1080148c10060180544030811080c422030800c1c10303018019030b5a466004000036250b9940c148040c950380d054460300b00008000b4001110407207985912a807121084a02828691461020390b040c603000b264051600c0e003103081d1400100040b4103038140c002600550b4195260250104980d49a024543c020102460650340d0303a110700c5002811181c0d004154030138402d2030742c0100400da030007250503144140c15080200540d5603440000e0f081240401040c18001c0c80414080207059215001984461090004000c0d81c062090028000001154 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 27526741 1250 27525491 27525527
    0xf0910110f160f0c090609020406080703021b1c0207080f030403170403060603151401080c040207021f030203160206010f030807020f04060306050603010f05040809040b22140601 78
    0x300711582400800401c01541d101c09280720700b00ca03603a076003414000100c8044d036040c001d000c030920524506120303035801001c42ea401145017030318005000c0e1500c10000d01d20420305a0200d10441c2c46244002d446510b0158181610040c00362100e810000f83c07044003101006201e505004120101c0010340d0100d02e55a0b5001182054a560b8610718a510068281c244400e020301000001039614082c0c00003841c0300c0c0c0c00c21041e020080600d10308032011b280f03122030b420729098010000c0a6001c5000b17180c828041d01c026039a095240040369580d03802c075a4101501c2100c400913609103034141d002e1030003032121400b01c00c13203805001400c0341e80341d0080c081c1c4001801070748410000200400010082980b0240207502e01350074480005044a099610a54141e42c582040040d0340c80c003031042040000d150807041005052644501000d80518540c0301d02965a07480110306654404020500c5800395500c110709600d275054120300948a54501e203d030483c25200864010b6002c1d05001c01c50b114106 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 27527991 1250 27526741 27526747
    0xf070507090f1d060f060102071802180102010902090a02091503090604030f17010b0307110610150207030f0b070302220302010305060108010305030712050c010609200403080703030b010210050f091011 88
    0x3040340340910000343c1b8181c1540701d4240001842d140000f040816030600720b0005803550703030190500e03003448120311955045901d40b02d00e031001a654074044641001c40644016200d816080c0130030b400340f4150520140c50f070310100030050070540001d0704601c1a446945c1c0c205041520017819210303c0c900180d0503040316500307c018081d495042014552101d1280380403510701d100c00003488c0c1400e10070380310607100d8051804240f02034984020140d00e0020710780300070507480b403841c2c90f03a826440c1c0d100d200030302c0c2c0c8200d140402c1c43d00307100e07405a4480455428070705c6c0c00d18000da0284241d4941c90300c402c901107400d2800042d4a98010910340341281d40107000f035880e2041300c0e80e40f8614055601c1c107020905c60144008920b00e04240301d031002070145054009a1542c0c41030898001d002001107860402c1c0c0c0401c0f050000070320749010b84004642c98280404d039078000a0050341014014510409164034000c200502038080076401c5000c0c0e00d044041d14008001000da29041d500c2c3d026400603860f03410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 27529241 1250 27527991 27528001
    0x102070308010902090406091802040501060203040f090902030a0512071502031605070204062c09190b1e15010e040902010203090f061306020102030f10030f02060f070507090f1d06 79
    0x1580090030305e08001000061507686840200301100c013446214218001d05500072000c504281c86101d0151a030b81c0001c6050524081140318400103502403400e070a071311260220b0464400300701007402c0c0365100d416102401050040e0240075040111309071042142081d058000b154144210f80c011910030718241034100040106403110790060703e0883c2c1150360781c040065886e07000520410038240d82710740000c11000c4104081c0a22130081c040044039004180d80703c44400303480c441c03c1e00341d03544031490503102c0d583c8400c00c2e940450101c0560000b40100410015030349803901c11851190b4090f01c44600340001c0340300f80700407070342d04e000300a003d40d0041110649600d443e60071341d00340c0380f8002c108601e4141201083d40c038180ea80c0d80454003623034003c401d000c0520211001554090390039204070310140c1c910346400e030914292407000390094000080741480810004100d6450607005011140c0603a66048128020a051803008103420700d040d6055003c00c105100903174810600100070811500c1e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 27530491 1250 27529241 27529259
    0x9030702010819111801090b090d17070c06120b090f06030705061204021014040303140d0213030b0a02070c03060c020309031005040302120a08131403040e040c08010207030801 77
    0x101410030300e07102040031030084120f030305405402c03040b0b40c4c1c2c0c0c2c0038151101d0902e00091054841642c1c0c0c103041c02400b8506000c40c041b92825140101401c070303042d046a99103401c10a0004210402101c0002d40000391002800a004216804c491007582d52542c1d9450320389508007160615503070543d1200241000c9605031402c00c1ea010340100300141603032101030747c900c0010101e60000d0145903c04141e0401c0000b5442c100a0a01110256050910700c0329100da5a80c1c0107032150307001c02014400b0100c46445c02d80c401c4429070303449246c4480115661480500240110010b608c81201c11030740000005409074645c1c0255045c440d0b21901d200f4943c0d055641c0c90018250078590001140300501c25440c07181c0d000c100040480f481c041000880c1d090604001342000d540903120003080400f080100b200507889501c141d03120754045c2e04081300c0d4020303141407107503100360101204441c13002180210304044040a40c3d8010343c403c00411100320743d9010b40600343d00071107a0240c045032103c0010080080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 27531741 1250 27530491 27530507
    0x6040908090d060b040507032705010b0d03020a060c0302040812090f040227090f01050d030c0c170705030a02090601050a0c02060f0901030c0806030705010c0201090306050c071a0903070201 83
    0x84030389006401e001ca140040740e044480700ca000e90b1060386801c0420711a040c41c0c454903030890844c0c68107000408a00d200380028004440790580c042d60324420702d0042c414290b002c00040d0750002c08118014500d030030025941c0343e00366010356115161012201c100c60080c400c46046440d194050400d400d424030f03259030710340c0011000b950054a02810200c90707940da8070042000040301c4c440135441865515250184146403410030380601660000d000e44002d158807094111801150b0207800e03210540341c2100c05a0307920800a00c0015103100108680355000070131454007041d4811680829620010140c1e5030881a0b40030b90802c1d81c5802065145d4421001400410141d0900041e81b40342c607404240158030603152447c5d8820003188050b429039050003443d00d0300040b407614040d142000000241c8902d0f031441000d0510210390303480c20031640541c02100003160085800c12441ca043c0b0300c04503803a40850130443e0b1010150710301034002c0300701c038190302e01032400e0000542c10100c8176401510305007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 27532991 1250 27531741 27531743
    0x1020c09180f01060603020a080109060e010b0d0b04090302030c15040f110303040f060e04050c090f09090a0f06200f04060f1b0507031b05130c090e0114030706030b09060409 76
    0x70040e0b0102003201a000d01070103004109a40d00180c3d9048180ea000340f20a074182c03c03011003142400340c20016025000c4000d419509402c1707030141d03a803403003118400c001c149a240042c0c1007820001d820040c9034005c405002d4581000d01074aa11200c20b081e4214400412035004240e08600314550000c503a0041e95043d840e4805000c0301c1ca090389038070000c01c2d2590646d1000f8005428008611799a090600500d9042001240c510303041c218820009070b4040d078650a264002e0503080005502c0020421210b000d1580140030b004015005003442405080482da40c0781511201091005001c01d80c5012141385685190b481400d0a00b0b09108440a28204011000f0001c40c1103240d040b10102c5080310102512030401020324501d5442c08504281f00c03071540042c0c8031201007042103070f602e41c40103519151000003800034403035507401401d441c01c41d03464101c002060f0243d4000300da5543c0c1e00302030050251084040b1416940c1c1c6400c11000d6449125a107030304201e104020131101d080c10b402049940f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 27534241 1250 27532991 27532993
    0x1404110316030605060c0d120902130902010201060b071406060609090106030e100f0209031c051c02040806010e040501050a02090114030601030906051003030306080703080417030f120a050601020c0918 88
    0x40f641d50760005d2001e400103414188030343c1060718247d10a58211001c0000c0d45c0f00c00c030090110702115000589103c0b015210b240841e6100c1650781c1c1103a100b0750000015105420005403194002d0900c0c0d4a01d01c2815004c400a1040d030000c54500d15208090b21100075009203140d44a0b0b0901d82c04034090003080c0756001032441000d40d9054050590f014000c00c21000301030041e121070200041501c1c080505841007044804030700d03c0340c0300650000031584188600841e1500b000080005100240328903400034180b809408008640108540549c2c2d02850003403009000f41d46807007920381c040f4420111040d0100b02d03d955a402d010420f5405550b000302c05040005020b125a11250f013618000c50310611841080c403014020140c041c03082c0e0b00a0b04500c00107150480c02e640e6120101c2c401c0c0d000f031020511000243d415400c2040007160009140352003819168003403403141e05858041501c034200350038204030010b180b03548005607280c02c10000801002c0c480d140c944642c103c5010f0411071f502c003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 27535491 1250 27534241 27534251
    0x12012a02190303020d05100501050a030b0112020a020715080903090d140109060e070b03010f0902030c07080a08040212010e0c0405070c051e12121504020d0510140411031603 76
    0x140789603045442000c580251009652500f0b01c4042c40e048400040400d1041c1d40d1902c0d00b400705907440004d070340e00180d4034240016510304940c0161040d5907080d404006007800040c1040b480d60b404200007041b902490790040c60344c2040c14060798400f804907030100540e4414400f0450500d8903440c0840901d02419042e410110442065400d442031440c05448841c3c40e81006041160100442001000e00d039074074504550401d00c0002d4088903622501c20704540210204181285a0b0205c1e4100ca510030b0309140d407580407020141c103500c411901640320b00405101d15880c0141070080c441051882c4008d44131180000303007048018a4041c001178204103a04420340700064040009445018202043e0902d028420b024986040c1009941290300c2500b4088101d11081c0b0b060941c0d00000100d1000004140300404a4000d02684225030041420041400107254180362542c1c1901c980c00d4143c00721000c50006e04c0160740c100710300c0c8004104200000b482e402403030001d1000584003840e0100d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 27536741 1250 27535491 27535513
    0xf0807090b0c0703030206010503031303061d0703051612030c02042f031909030915170109090201021005010b070807020d02040e100e01090201050a0513090606030b12012a02 76
    0x7809410081c180181640850350900901d60100103550041030120021890042c50f41003e44684540b13100040156423510081c05100010201c1300e0762130b211000450740c0c110b40d05c0c2031195a03414107041070104104003c2c00441c0c14044018511010354040e100c40e15101d0b02c40d801c0c080101244842d50039003018100c0261070400c4c10b01c802148462072214442e0701c1c4d0801980001341d0349580c0c151aa44039141c01621000a5045110002150b0240140d0b08590408002c19502114504101103c0d84022070000c613540034030780d0000c8100ca000381e08503221704044008001c1110b2080c01030001c0020107121000001d00d400000f1704001e4030151045036240042e60110b415155495804502074100b9141d4004520f0640302d03202d031040c5410000d11040d405500060b00c1481210900340401000003044a0b040c03005044900052014000800501e56a55030041c0142443d0210070b208498100c05c410003200c05010f0444840282040d10840c5001e244c1000888100d203140030041d805030740100c0c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 27537991 1250 27536741 27536759
    0x20715230d0b0a053a0803101e0605030105120102040b0a05030402090c030c030a0c110a0503090312030f0106030903020708070f090501050102150705030603070e0112110a060f080709 80
    0x1200301031041c1004540e00110b0410442c40c42400d401445c0a02058643c0c80d0094000726460360a0020b11a4881180382c21400d1580c1c1489501c0c03070240c51070100205100001d8600c4c1e0a00d0304641c5107019041499000140c42c10303080300240f24490000384144014001454140102c0d000685c801000501c1c0aa0320004408940c022a8860010950100c104010341c00e03d8500158845040880b2a00d5031504940c503812502001c2c1c03080b800300350340b261b0810700c0030f0050289144d407040301c80407107915080900c1c01959a51110106d14024010450010307003006855041d00e0050f55002c805038056130070301c05c0440050000000580c2148a804c01c0082d0082d000e200f65001f82c5050003003505554142091b26040e60750682c41035045511114008003080c0c0c0411203942c00200c540341140c2e0340e807502c0002030b03e031032034039005070143d180514000a04494520010405030303200780340e07c10111035850200043d8804611801000c41c069004c0b80c03108a2080200541c000b0986c01c050808035181c00840d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 27539241 1250 27537991 27537997
    0x318120207030615050102190b0406020306040b03010906050a11040602070b0904060b030709060207150206040f020a05041107052509090303110c03090a08070f050d06020403060c05030703050702071523 88
    0x2220110031303518018020342d40d0500c042e04078001503000d4124054101d5884502841d40140007404060740800810744942d1682c1094503e00300c000c00074416040c00341070202c000c2a0a4a180d110302d40b500f40ea043c6a9443c4806a40888503d42c0140561520304003000017181e100c2c80c0300c50351095880343d0100d5020450406107000394001c0d50307521405401d03d03001074030b4060390340c2111005144071980184002c1e400240702e0761041e40100d0a591014451021075030400b11600219403043c24110000040b103808005881d80d80e005a0880d20132942041051200c41585070310884503800c1403006021582c00341d080710101d01e20034540018028094080b401803500301480da03000302d802c0020841500d20302806207201030207200001e000101e00e44066884400c0b03052045034041c2400c00d15010511419070f06640007550098814440316140e100b0042107603200b184d807140801d28013030102d8a080d100068080544502145820140340543d8040c0d406040640001401d52001c0050f0300c4880858005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 27540491 1250 27539241 27539261
    0x2031c0f170411040c0e04050a090201090b03040b010b0c03090306010b0d0e010b0a05010c05030702040f05010513060303021b030c100906030b010309080429030103080301030c050103181202070306 86
    0x111122040d0503440180803508041500710703031901e12418000460070040e15061100c0003101c000582c0b00c180d51040d40d41d036441101031580b0521b00740400c4039170105600041c641c05d00c03d81c0c40281141d200e00c000352150000351030140a00c9441e00061016208481c010140c0410302030032030b402c1c40340d114006032802000341c01c21910403074080340c4e249410540d40240168030805070024850320101001040d12108184591410000c1005001081c07250a00417103446a0700900184001d204c2e450700d6002a0a0a00c101030140c00031280036040415580f08420951b41d059016140604030441d103501c1403101443c0341c503130502401400b403907680e0301c480d010070780c010b16525681070360f61030064040d08441c402101141458100600300c00001d04138021501a030305116044441c814211001c200b0100ca40d400b0007400c4040000003000b40140d24001e035048910841c01c00644070380701d100460694000b10400301c24200340b89100340006a1100304194054040d104499a0035039984880f0142c400401d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 27541741 1250 27540491 27540497
    0x2030c04051509010e012003040902090a06170402060d06080d020f011a0306130816050c0f061c050c1c09050606010503190c0216090c09050405060604030201050702031c 74
    0x64200000e0070302d00400c05a00b28800030483c02e060721140081d05119400b61440c2c1044413400d03c90340201c0c01c1252441c110700400d400c9a44441d280c001c0e400003580403c50746482007081d0103001440a01c81c241c0a100c0010000903221030307444690034050340f5000b200c010200d2541b100c0003c00d00010030003081c2c40d01003a40d030052120300d2030b03403907003a0840c4d11042950b4410395400214003815103000900c660410080c00013002c146801d400c104226000d042001c08074031008040c443c00f44000007a80d040140401c0b5400c0c1076908091b4100129841140780c6040d5482c4450303569640307208664040c035404400204002e00d4000003084a00d40c41e8060301c0e94900f84c03a541c00d40c11060080070080b0540c00303042800c1003403131401c0101420202903103460a40e01d01c5a256803138400981c1c801d2250000c0100c44000c20031394071b500c0d10005006070152080800c0080c1303500100060a10309070103000d0260b640684103602c1d05056800440b019030050005036014410851304500e80240784ca2242000784e1556 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 27542991 1250 27541741 27541747
    0xc04020a171501020309011209060501030309030c080705010801060f0309020312040315090506040209040501060b03010b0415080705090f0a03020a03050d080a09020928110a020f0102120a020a1202030c 88
    0x200c80c01c2540d101605502545001164a00306a42c0000450304c0001d02400d08041c40d04100c00480e01074031502c040100410704000001080581000c0b0500039a849010520041c3d901c500700309559501c1c620a1500148444004000450103551100c0e00e2455500d00424060101d80200703161050812121002c8400003504009102c3d21400da5a445c052a190a014040c0c0c02d8441c9aa61800030384064401c21314480880d013041380c25407100c4000d00c040ba41007502c07983d40c1ca2310760015400a1007040310b041d0b000426a81c0f01c40c0704800d0b00b44501465124503040c0f40d4085c050002e00052401c00e26000014a400840036a9500e800c500040d44958001e101d14a40c43c10300410224000d04040b010b14144a203140042e40d8440c80540c0c0b05006128520110404a02d54115400306050800b2041d11700101070346107030409002000100741a80841e00705a9400b4441800c0340304d81c500360b6400882c200e0121f406020140c0003030502481c4d92410150610301e40440e007007203a00540d07444c203000c5000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 27544241 1250 27542991 27543017
    0xb06041b020d031406030a0206210103030507060b190e09010e030408280b040b06060d0507030c0305010f0b1c06030c0e09010606030504050a060b06130608040b060a060f0e030c04020a 80
    0x1405a07038140300e1a001c0c0381130700c0d09018005c6540e55003a45002480ba03007020a400c081cac01b0041200b032282d8040c13654202d40d00c0d6501d082c06000755005c0041500d10500b4101c4c01d6100d400c00840c00c0c614503030300000105115103020001e0388a51009403c030400ea540743d43c0d12030344030281000944040c049240140049407a030f43c008802c4144840d07485c0c60000e400841c1000815800c58281d070b403040e0044003040080d91940300148192040c413042042d190300e4030b0181310080d036260788211110342d015142048580d0701c40010308084012840341d01d241100800400345620b00d000928645401c0c500004108aa01c81d0346100146a5507004506151171003409c00800303202c2400340600030841420700b0420760401e6118940c070741101d420017508964407424440c9083e1104021a180e1104203038294200c2d40e102c01c0e0041000400f6501a218103000c000850850318000150300d0894401c4d865400560800e070400355960303525080b8842c0e260150310080b02182d1101c1c0024a02c046040e55454900282c2c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27545491 1250 27544241 27544247
    0xa030308090f0606060415050706140a0e010203011a0d060b0c0d0e060403020f010e031609090c050306060108070c03020c060a0e090901140c0906040b040303030b011101180b06041b020d 81
    0xb034118101c0b483e5004100740451034172100b007120140c86c0c502030707200400800030f0b1050b2a14446d9400003800f182c504082a00f01c45042c00303401d030203a00040c60a01030b00500807441c600b030740000e004501c0c066018892030754100060b0b10060000d8100030350042841fa41d0b070051540c0903082600544102c1c0c205000310b240481c0d0020a007070090b5011100c2a082900710780205118904030105030f81070100c4650641c01c0c03075804000d0200e5000400c0801d0104940700d882143c0a00340300c05c4101c8a080ca00d80000c07443e40390103da0144034520694881031617507650f410407100740d10510b00a906502800174404480d45a00008048003106900c6040c100302c0c41409214460b50020401c03030859261560090001e1198001107400443c014111501c901c0c03501f0001d881841a64004401c00000241c00810540c054100404c0d608090320350000045000c40d00ea42a651a214945030102c040c694010001d141c81c00b0550700a071380900300065022016a11000d40d40c004a03181c00581d11490007003502541c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 27546741 1250 27545491 27545503
    0x60c0f01060603091505010e0105040509010b0907050c0c01051206040213030803070c0c1e030602090f030f0c0f01081306020f07020301020d0e0717031204051504110f04090816030e0a03030809 84
    0x70305c0c800304000561400d09000500c9506002d80391041e5120804960907140940010005100007480390040f03051416003c0d205a0080c201501d10f0300944821607174a4ac0210152044120305418074031499441d4000c002c0250310001c1000411b03c1c17591400f001141e8568041e62041d00551110b14400c08182001401d200881d44040c0508002e00c41c80010784111540c0340701101c0d801300025886428200c0050001182039080315014840c0310309280c41c02d5000078000d200507030156041540011800300460744038004450a140c0300041c85400c0000030110b81c02021184000c01c1200d08048142c0c1c0000d080e0f91043c50400d40184d15808040c4540b1428041c0200900c40700201406c00512007240c40e4881c0205c1c0c9001c0002400c1e003000506208060203c1101d50386000c0444c6203924042c50600010606c0c82c2407a80a19110301050509051034442c025480b50400401800c15001002c0d00513001240790048042249156243c4125215840c100c4051486a01e510810380f0f0b222542ca07207410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 27547991 1250 27546741 27546773
    0x80d09020a091116060b1008010f1202030d110a021e03060601030e07060c1109090f0609071802090f04050108011d06010f030210050408070e01060e01020607020705060c0f0106060309 80
    0xb450250383e00700906034441200c9070151450f800d0f9140b900030341080c600521030f994000742c02540700d0003400409580301000505035900501d01106e800d440d010014124009003c009401d684280748070700085005020030b65061550108896561140340c0c04554005600340141c0c03100301d400c0c02c14078401d16042c0581a80b015080ca420488003034044a440da07510749074480d0106200c080018003051140c00080110034200140030b030300da11b00f05800c007a0342e100c1a40c0c0c1e149015010703500115184c150041840000c0740c16841c0005110000c40ea201c2e00250700030400d499004600040b1418161114000d2034000e003002d07000094402441304507039008000c017681011517074204100501c4480510b0589006994042c3c44103800c4103002c8230f003581d5510031508402d00c0d034413400000103540081102214180c55a69540f4004a8507010059076101d1040c1e440300701607000110140f0142c00d00801070030054060300205c401d60102000300c42d007116816040301c07002030789849222084c415803810704030340c01d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 27549241 1250 27547991 27548009
    0x52407030e040c0c0b01150c0b0f10120201120e100903050a0e01090e0403030b010c0b010e071101020705060c090402040306061206150b04030201080604020712020d0f02011401120c03080d09020a 85
    0x304c001d545070121218140500401041c0c4502001d216034429402c1180c0d80b5070020103020f180c10403c444003490201207500c2d50341c103628901c012699541c8a141411180e0f8103071602100301d03144d407201c070001d03000780311130b00c1c2140c0b04030038560b00c0e41901801000c131140d010307844903591051800c030021700521940d508641441407030756040240d4015107030445d0740315400d40381c00520081c01000484020903440c2c4c02070141c1e41002c0020034200e40568400c0e004040c0c82d02c5d0440c04503620b1120700c1c01d03405980400703449074020340000b0348400700c414000c10200100800041c6031a450b83c1c0c03950101d541c15003040030f017a54001c0d0324a041015500c588001401643c1198449900c2c0803043c003001c1c460340c00000d0420020f0400705403540c4441d0190385050b58081c034a2228203030031240082d0741b082e00f03548007170010705904c691040382c0303006215007a085800d205070000582c0c01d020080c030031074007000d0048070015007022000000c40d0354200900101000c1c8180440c00744850b004100c000d00d1590418825 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 27550491 1250 27549241 27549257
    0xe0307030314010504060f0902220305030409050f0402060d0e030d06090501050909070f03080a050f0f09090a0608070b070804030501020a0809010b100e01110f0d02030c060906060109052407030e040c 87
    0x200a40310341e4003408a607a8140e0241e03848200502b41c02d1540c1c21005200d904010821001c4100100400a0010b07185002d070104450ba0b02c0d250b032541241415540a908902c0401610365681800d401045124046030f003202d14000080d003918048541a41c02030581e07980d94801401035150000b5076a070482c008800038047ca40c200500500c0305003280c440180744200015401240f28080c6094130205400c00c1f52180c0c07202250409024986d00102400d0b02c03941d250400a5683c0c21640b041d141a250148014070845041c80c11882044d40070389030680391b0b9a001e11001002450900045c240380020f9039400900d428003103542806e4403822070307280388602d003408000c64005a100d07000a02c02c0f1400d1802040d03502190b1b0712a030604030030344d01c03c0ba601e014452076426540d400000910403d4070b03403803c44096503078410725035442c4c040a58a190024024410402c03603490054000f000548041120038982211081e0404c419403145d041200070480719503102c00305240500c120303e601000b41c241001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 27551741 1250 27550491 27550499
    0x24030503030c0c10021902060a0e120a020c06030103030306030b0f0403050910050702030a0b1f0807030f0c0f0609090509031306030e0a08030109020c070b0414090601030e030703031401050406 84
    0x203103901004145420000010902440e6031004009210450201038411540c81c180039428000305a24040032401510408000c10180d010622a902d0394056a4001e403941c1108082c0304a0f00e0784c81440900114402e801641c1c0f509e544510080d0f0086110b92000280c461562404140d6100020805400303403d50303404001c0880d41080413100900c030115880311400004c4c0d05c0565042c044c004001c0d41611843d4144000c100c0e4112075103004900800e108034882a02807480307490001c03c1c4c01485000d420101c81000000c0c03480ca100403880d827084400c443c0c41038885681c0080d5158a0b44000001f464907201085540107902c03e01b90000d014801079481c1403e42031000c41004290700c00d440800d5a92005105489400c0c0402c802c00c6501c112113503500e5035980701715406500001000d499034003c1c490000b910000d040211412144407027a1000f9400a200800c214910000c01050615031202c901e185914824001800514401d031800110309074a07136102015084140c0169004a01e000001c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 27552991 1250 27551741 27551743
    0x50c0705010c0f140c03010615050d09080c0f01050103030e09010e071809061202030f2e020904090501020307110d050906130b27030106140904022101240305 69
    0x40140c410a0901c0c1e62115103519021038020300703000f005032240c10144103504040c0e00110f002c0520f204101c00900500740c84030480d102c0300712041c5800e40441c0c401c004a00c8021500c0d0410421710340190300c12820003228a8680d410080155030301e801c1650360f50018401c05821003105209803005903005c26156060141600742450007410384d1045c0f00c0018007a070b0801841e1155900900302c650410700006030780d564144105641c2e22001c0b80301c2c3c09600c8110102510000c0c0a40b803254a520020b030045000d48c9000300e440513110300d02e0105903002c210442e00c54a03070303008000306907101c2c000044e0741e49017000d402402000c8045170b00a40340c0118a15410305580300c0c4c1aa5507080080720026501d030001140c60f0503200d000d1b03220f03103101c00c40070407245070000b0800e4142024650100022a482044401301800c07034589000b07100410391100c40420139810100c045503031091001d80700388204603506070807026000c0c905650380a5a9150a0010103400110700741c1c8001d0b1900010803000b4a096640345 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 27554241 1250 27552991 27553003
    0xe010305070b1c020702040b060d0605090a0c08160504050301060f0501120504020139081b1203010303030209040e0a060506030c030606060f03041a0106230c070905070c080c060603010c050c 83
    0x3da88140c01048440075907465500000100c0c42c001d2419940302a4100d50b4005050300c2d2003003c1c0320701c100c50000340803088140100ca040342503075581ca4031140d8440800582828500207401c003088414000410a41c50034455900500740030301201e40602d2401e000140001500007a158002e81440148030060340c0200c3c4c4030294001400642c8601c040c0200004c040c42da2003104503940c00040c141d42410720071518001d02146000d00025000200415101696100c0c0441c50202c0c50030f0800041000c64420b9020b800804d07001000886d110380c0d011080c502d8016020701c29078400d555041031014602e0200090b24110000354040d1245141c0200083c20500034040c8251018500200040411901620750343c444d0007620524510355844142c000c00b20480e5881c10320550501400c01c182c521003a40960f00f000d490000144501c0b402c005401e00541400741a10003480000e451003000110850003034042d05940d807008100c1807804504241c25180303841d10b40c10900c40c0030010203809820100300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 27555491 1250 27554241 27554287
    0x10b04260601150c0b0a02030a050c0412030f03090b07020715090506040e0a0e0708060a0b010c0506070f090b0403060b0301060b040501120903090e09010203060103111603030f020c070e010305070b 86
    0x420b0850b180c00c8001900c000b070300e0000042450f2200700401c096400361f98003843c01810001d40401060350786403c01038082c89640034030815102c0d224210400607100e0003403240968041d2501044820f01907484103a89030055812101507044081c00303108040c4102c4941401e451589000d401403840c0102003925031190b0f005281d241070b0340600188070b0000c190000c2c0030004481c0d0483e07203d00e9603907440f40c1d10f610054411194203814400346031070543c4202018403006403c10302a003010744076400c083c6e8220488050f240103002740b0010001e16841400e0242008501909012514082c25400c25003160040e1700441581c030f0050000b8880d90340c2c490004040f204030040005444070042c14255645032180c1e10494070001c8180030007403c060190051406034100303803003d0010310074030210301d2040c1c028000d0b50048003048420400209210341c00004042104260051402602d034240d28200002030700005080b0481000420030000b080214500500580000c40d00340031041d034889510b0401c0b018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 27556741 1250 27555491 27555509
    0x307090509060406080d050a08010b04050f13140711060f150d080d02030421020c0f100c0804060503010f08010e0307080304081b070906120809120a0803010b04260601 73
    0x1000500b580c4480d1302080291a05070101d464403800b441009290303a0000003040c000401c500c000003000e007028804d0300d00b41c0e60010902c42808480d10181f2000e0103030506105043c40d110b4100b4205070103a400018061640c2d0b5440c1d00715050a1441c0c180b40c02c50244c10300807441d07020b00c03c015540b0590000450080421110880c0300e007482d081c841780380d000b0000c405900602c00070030300c8200012040f504008048071080e44444007030034a01a03844040b90340d40642c000341d000c04c200750146410110002d04500508014954203041d844e01c02164006420040200300b000005202410310155424020482d8500034000c0c0c6a44c4014580c41f409407120060140c44040b0200d010400c2040075a00d00405000110311f14034941d1442965624440c425407054070700d0144081100b41b510414200030130b8000010b6858200180700780034501c00c4810018140b030254503012800248458011030003446945401034079036007003240010f07142c8440e180404d1104100e030381c007a00400e8086050781c11150354003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 27557991 1250 27556741 27556759
    0x61005010c050a0803010e040c0e040b01170304090e0f0106050904050d031d0604050c04050703021e0d0b060309030705060106050403020d1502040f080102070b07142704091109060603070905 83
    0x4585246850703003c1030020a000400b00010a102454100d01445a4010303e040e0010381d6a941310412070740da00307607800b8102044d10401844031034200f0080c040c0da65044000c0307a14107680c540000088400c030740c52404903030300801030b4007000c0c1209004070006000d048510180d9401c16941b50303a42c800c1d200070042e06054070f49020440340c901101e06101c5201c180801d80b84549014502161a01e07800c03518035100b107161001141c0c0c0107100e417007030f1803041e007510036206c128404800c080c6410b50841c850314140706464082141c9280c68010266010300901c80045480d049c0030310700a41803c070143c02010401009000404c0540d40e80c40d0700c0280b46800c040881c810581c0410f80101a20441d04941900e1507921070004d00e583c415401441083c1c001c0c04410304584542404680d5446240f0b102c881c1d444e400c0c040c0b0004240814500040c0248070800004243c1245021030250380019138103036a443d94500002c420303824000012907004404540617841d5140200e4050000c440502400c1c3c003a10801d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 27559241 1250 27557991 27557993
    0x30307020a1202100c0f080a05010609051c080714010506010c080313030e03120a02010b03030306060f0a032405030616050d0b0d0f0b010501090f030f060506061c020c0c03061005010c 80
    0xc0c00840c064140f840e80a100310b40c0301c61400740524286d080d012002519500c009111120f0b14401d00e4141e85040c0d403134103d0542b07800c0820005941003031070000a041c50200607000640b50307000074220780344940281c20340c180703110101d5401c40d0001804207040c06052500740e1700240304241101d0b40141c0100014464440c03d0a0885244454912181d0140304a07461181d00c600280040c10302440c1d103034001d0007580c64080c14140c0b02c0c0400d0b250302d90081018444a0740c505403038405443d001034a440c0c0014034240745c0c000e08094204100c4018250b12085005102a060502444d41d1055030200ea210f0114590345008000f441070511408100f5075480811403240e81d01d01801a03c40d40012031007a10030000d0401034940c610a108450214034140b400142c1e1005841c00401183c0e00100302c81d400c0001902c802000e480010a8580c1c004410005600580344009010201909082d001a1510403011440d0310b0091500f04ca0740c031a50040c01005202003241d401d01003070300c0c420310f0218456202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 27560491 1250 27559241 27559243
    0x160b07031d0306040302010b030d181205031606061a120f0a11030f070905090108120d0b13060302010f1103030606070f020a0e040c060504081b030708070807090509030307020a1202 79
    0x24201c00980e06000b02e4081c48281a4150406051801d04078295004040480e0040e1103161021050701c280d225542820041e0680144c51101600d0045056078a03002c03101c480c40503c45911340c821100f503176840704244082d04621840108521508070f04620308112602d600c8400980207200c40d02c01058040050000800c6400510b103076200700300a1a00d90511411122907440100e5150000890300100064285000c08025040314142c002916400301d02c0e6000310010b43c0202d40d1100d0341c54a54611012a0321640741150b201c0c0100c2000054107821840011301580f102402c0004104150318111220100807040320340142040350070a41e140d400740b801032550340c10034030041c1d8441c140d803400244c207014079150a032090b0f10070b03a0000d11880c1c03100d5041d0743c10301613800b1310700c035680c012107185103005801244031001600040840350040c1c0c2c0c030880240340450b142c028004079003003d50108200d10702c9002d1250000c8025001d1401c40c90100c000039500c070007042000d8040f510071802e14078a140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 27561741 1250 27560491 27560537
    0x90e1b010e220b0609011b1106070302030307020c030d0e0405040204060906030b0106031413060e0f0106080d0e030106050102120d1b050903100c0e01050a0201060801021204020102160b0703 83
    0x502404010384040080d15000342202c1038041210341504100f0400d49925094003100e0042c03005855001d034420741c0402d6040608400f0004403043d4004200e5250503030340799400703003c000348254010740d07580c030340940000e050000c0c01e403c07103000f5070000c0d80d40c1c0c0415400900000d1100b40568001a8641e5940001406881030794001c5c1c040b140390000210502004403543c5040e80e0140d1014001141b50348045908000120b400601c40d100090400000a4050b048007240f1400700e0216240082244210780c02c40702c8644c04036100390f00c84524900c6e203039003005000134251411002088214680700000c1c0d1180d0b5454031005030080002244a00340072258002c1110103a90b0b50700d00c036101440318020f0825030008200500c648201d030217108141000740030301d01d401062a565040180c00310401564250044400e80041d55220f20002c6508c103801d1000c1d04032008079030442901c50a15000290a12102c3e00c80f51483c00601032050040e0713102c0700110344050703500d46002c40f24205d122851070030b01c2c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 27562991 1250 27561741 27561767
    0xa150f1202040906150507170918070203130806010b0403120903050109050706030b040510030303020307050c010207050a020a0e0702070b030c160606090509010c0206040602070203070509040813090e1b01 89
    0x244003140100d40e0746001c1d80304130140d60000c180e901404801c20310a07680f5000300f9800901c0742c08603000c0c60300745e0701c21000a8100340d000504050f600c403040d0301101c40b40001c00c40303a440040e880800c806004c8900488000010825500034091030750500c401d01c1c20a128500014103100c80f1910408845c034450700101c0010368100d0300812044820340782c09600d80f441441518000b070f040c01148212458180b00b86401010342c2881000c01e6861a68140d001c0d4200a000400b84030040c8070b01c0780420802e00040801c03500c148050a0b00c000340c0e20401c001e100854004041d4452a1020014490340005504050b42d031909039081c5c6aa460f024030406520910004000140710b4400e66420480542c0089098450102042c000c030340d1600c4001c1d00b282d80039800724005030301c2400800d01040c0d503a40240750ba907001506031280c4030345440100e050440c0548003295603141c005900c00145d40802104409050020005e2081d010b58130f00385552000d00c241075111400d8482c07201c1c44980e0052500000788 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 27564241 1250 27562991 27563027
    0x3030304062d15061b0b0403020c06130e0a050f010e0405030708040602010e010c140f13030204050106051c0204030b0114010917030c0c0d05070b0d0204030218150a150f 74
    0x1288119241000e490740a9108403841c00e003d4011400601038421711650441001d1a43c50f40001038882014540d0081c10030742c150b000301c11001145803610300007009210403006a03000d0341c518000308542c414000a10458a1601d0881804000e403000055103045032035400d5039015a0b01c59040140c04d502c2490402420640c002900192442d019048902503000c03590080205040644065a4216140000c03e08600040010907103107041d8201815400c64820a00082e4035180e0303012404940d002c2c0c1000c40420310128804214044104846a082c1841c103415424246560f864080014040c060000c0003500c641c100078403a442032990301c0c0100315910748654009001c1089a850341e010312440c00031801100205051414206420388502da8058001c0500d50f25000c1400c0d003031307000882c2c02d0f20140e40810000002d41e451017128440d046047e542c030495400c0c08004419003a00c0c80800e507014149048040003140c1032420401c044600302c1c2015400340701c200000b00d41010640d140d510302 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 27565491 1250 27564241 27564311
    0x30c0904030e0d0c0509040308010e0601080702030a03020f0405030d0203031609050f0d0201050904050a0b0f041a010503060321030a060504090c090506061201080601080f060f01030807020a0302131413020303030406 94
    0xb8598030540d270a0403595030240800304c64481b44011a104c3c00112401e8003d64400c000c80704c4114801d034000d03c101c44502610605040c0c9450000b0b061402044c920030042e8404070500882e889c194288030149401c1c2e04160340d0782840c000114545080c0c50110f01e1055404000c0001035901580482e180e08200034010420b5143c00c0101100600b822800c95008d4441900b80c100142004c8c401d070311002d441554508501c80b00d2038011195a0300041c07002d6054002c1e201002021624600c01c028066006800c4130344030f1030861260012500390b0340c400c0b0701c1207040407a4200031480403070400c1c1c01d0311a1610041842e07075941c00464643e200d100040e40e00643c14000018122001090300f42c180c2c4c8240c41504d07451540e00c12a956518015644160074500b06401000095201d0307004280c4944050500607500b9542d40018850114a0b8004980c00c1e03101c029a04c100c01c2880d84180d0303c81c000c1d81240c0f90150740c0f82c0100b5664080100002d001c2d40d0344040c42401000d900c69468113000c01e69510000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 27566741 1250 27565491 27565493
    0x306010617100308031f060512040f030c1a060114040605030402040c20030c0114040c1701060b0c06070f03021e090609150c01050108060f040f0c05030d0e030c0904030e0d0c050904 79
    0x561080d003040c42d509030301b60958011480500c034008440414500e210780a4003038a403074541f04104111314000701c0500110b604d503280000e50811390422441d119080381e6030146801000900f20b24413000282800c0002084188512500171041e29080341d01914009140001d42c0000c1c1d03010811766031655103000d08892044649030b00000109030700701c107040081c400b1030201c2042e18161042640d00802c4903007900414402c03030101400310305018080e040040b5040b6a110f181c2e08131948090500000c0d90050820461081d4000c508402400030520341145089080c12308080207034064210903020200c001104652030362071805499214174024428051002079000f510101d9000c00c5030907446508200000484100c0420424401c413030384100c640e03859545a841807070039001c3c040d080b102c160700d49201182a4404005642e030316910354440c42c039410120410103140010031a9490300c16003d0b081004006503100707640c5000d02d03d060750444080082b40c500030010080e05d8205513044602c44013004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 27567991 1250 27566741 27566761
    0xa090609111201051c1a070806030604080a180308040803040302181501080402010c051605150315100c0807030c0b0903120411040b0a090203070e030601061710030803 73
    0x2022510055010030645004140880300390042141004203100880d004001504180100c810382c155100308a28001da102d03980c1440e008205501000301c5a00842000701d025007008401360400c508400030112031800d541d1b005c51500c02d9100d0b020400089010b60341140b00100750340d10203507078031003071231071301d5036218407140b03680307800c075210983c0b2640c446510a2008400d400459008958800c245503012003090019550442c2c0940100d04101c0c40003a404082030051208150804002000c2c0e2001450001002440b03011302d124500030842c1042448000d91100c4142d24082500352500c92800403440e80a50380f035100d410010b405a02c0c0003a9110402da4044062440d081c400c00884400b82c84075100706940c1c1c0207010410700990f06002c042408501c00c81d440750107c8500601c00f1403410b90101c04900c41401d07d034040c19030a900401441b108540000000c0c0355590180c1c005c00c407540c5400c2004040c2480703072107250b03c440c04180110b001c150072240c2c2980a19040003550f6500e0419407000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 27569241 1250 27567991 27568001
    0x6011502010c140a030903090b1201050f03010b030c0d0204020c150403020d050901080406050919030c02030609060402060d050406110403080a03050108010507090515090d030906030e030301060f03020c0109020a09 93
    0x10005520b41a5518007050268110346900072403660200d04082203c1c1040e0000c2041c00300907418011070f61000100950160300074100c1c180c90a16620321545003c042c40300484094284601c2641000c0101005840004801c00152011541003240000500105009208078100015103005035481120140ca00030ba416005900c030394201c44071324001007800c40300f42c01110101c1d130004001401250100fa2640c02c4079411800800556001182015001000d50014402207001c1900e041c01c803029171070240155544403034460041c19481c9066030014217688543d0320090021582c82d40401d0501c8850380c80701499081400d0420703076032912030400b07000941264038010002030030b2400108411006008a40c020555030700d4158070141403d0411034400f0b903000602c01c0c031090038001c0840380c1d0b542290381c42016000e9295040c155040c020018140c0e000e05031742d0109548204010050140d000c000503107101c105190040c2c54040e10429503015007400240a13611508140c804100c1f0001a40300c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 27570491 1250 27569241 27569279
    0x504030f020705060703120207060e0327040501060e100306052707020f12090f13021201080303060d0605070e0d0309090e06010b0703030c0504120503270a15110601 72
    0x1c0b40c0d41d07543e6403804c0112034898400d0080001750520000800c220480c0c01a0000d46e1044402140f101041c00d030340c500d5a040100c50450050aa0010040310045056946060a8203a60174045581851005020702c07110304403441c01a580c4407404140c00f0f100c2d80c0081d0142000410380d1401e640070100202c142100b2030062590114180701241c001e034000280c1101514480c400740c5000800e82c20010101e42102c00b0b0103810002e83c280700342580e42c41c82c50029078200e9900c00141c8507020b8140401a49005030001c01c4694810402c2c000c1a80d0b0b00d40b08520260751086c004111961040c0040745c1c0500c2c83e0000a81007048080d0580402da00721203460107070f50032400c0400030401d400901c0da43c0c0f09028807a1600544080100f040403034420342040340400b049007800341c945991400c0862040f600c81609070f40a4002040358804409803044a04601040003800a1110f046400040c110465407099450003441c907800911554010744901c0d10395112a010740300c031582e46802100c44802c004103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 27571741 1250 27570491 27570493
    0xb09010b1215040201080901020d140a0c020304080c060904020d05070309020909010c0e131b090302100309020f0d140d03060f0e04080a05131205160504020c1209040f0504030f02 78
    0x416203800c20307000902c040009118110300916480f0b0390015540d0b040043d01d10b1110303540070001b041419070307c0d0248030005148031100e046140341000c0b140040380c0701084403a045400401c010044000300040d6154510b104440c00c40c2d036682d09000050003481007440103d05241000c0400200d6034041d442643c40702d0094445200e00c0c0e42d6200300718200c8404034040000725911805080399410a01c41d50003100e001020001191345140c0521702d88020706500c01e0002070303a0104d042c821810200801e21648049007024092480d081c0d001800005004000602480c0c0c9800c0b0311040c403010300424640305251030107030b601c400c010040040140c411342c041c50024022540c0b00099100a06a032684035513000720031a070405c5100b0344112420740c80350b0f2004010007007003080403c801c006d00d8180c0180340d2081e002040e48103030380182000540841d604c00d0b842a4414040d00d016814085003031080558400400d44c0d0720044100010001e150080480d011149000204801c25070132500c00c80d00704900d60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 27572991 1250 27571741 27571759
    0x9011211030c010512090307051906060603110301050f01030603060c05070b0c0304020d03080901150f0303020105070804050d030b0102030f0c030301211e050c031501090c0c05031206010c0b09010b 86
    0x11080c581e5907481080740720f000410401c44070352141800c0040e10b41140c01081a00c0c540314243d01e586103400011005221102c22640e40042045207030301c201c2c0c1c02032005080070b00c10022624640445400148550703802451600c002400c168400d60113a0082d55105404205500c440c1000521a8008440490307400c41c40301c000c1001c0300b10000c1540d1003190b0040c00d1480792507440d94202d40300440074003010515900c0b1312079400906551103004000d0f0101c45440c616203403841c10020b0075035001504030703418000507000307000100340e001ca40c1c600c600c20303681400310341d203001c28004034514030800300c1c000c0c10008045440d0b60a104c0200083d8101c0d681c10358045200c9100c0f6244a5007490308010081c0243c40d50000d095160201c144440c8081e030043d010740324400030300d5000c01d080458402c440001c12591400601206000f03200e01305a5081c145001400c1c0903869445560300d21a08451030303584030482d00010350b268403030101d400f0510350007100044c0e1400c12048039800f91580100503440740d4442 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 27574241 1250 27572991 27573023
    0x6060406080c060313150204090f06051207060f02150c120606120a0902130e01090c080a05100b0303040f0605030f0a050405031c0b030a03090807080a050d03020a0905090112 76
    0x168070302c00501c0144010f246445004082d103520b03071101c0b02200d01d40c2081545102a2126202074002003080003c0030510f141d113050361b40100c1d0030540129100326800c2043e003940e1500020114240d90850500342e08603a0100c00603441e25000c0ba00c06404207007850700b00001c0130b402002410070141c19060400041d01e41e402001030500520624a20485010300011181e4100390814002d40c0d00152441a102c842e2810440c00d88000945065850b07445200010400825446043c0202440c90190a10000d0707951002e0b29a03a851035807617040d03501c0b40e2001045070f40910446000b0310b0b92013007aa4101d03503100d101030681d030002c403500c410b40d003007882c00500707155441e000340c07407140e6880300103940b802e05a20b069610340c1036100710740819181c4d5403100801d1601c0400451146070701a0321151802e0b441e1400507417402209800211254118a43c000001100084c8160f102003950402507141c0361900011169944141c4c00707654094010b20000800c908440c4e149040c940c024150b01d40340b9104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 27575491 1250 27574241 27574243
    0x60909050a15060803180d060507030207140c15090315040b0702250306020309012720010c020d050a05010203040c0503010b010f021002130510030c0f0305092d0f0606040608 76
    0x5403103000ea40390170402c00e075190b1072201c0002c002c88000040840354031b00000e480302e1741191402c8452101182d400a80e14090100070b81011940201c40390050400d6505000441d43c00d2030050002003c011010030404142da50a0282500f0fa80e48614843c1c1e1074505030400308134081040d9007003009401000403400c00c00001c42c1014403049116140b010074140381d0b82e180002980002c0070382e40b0315561440d1844420f900e080401440c01c240007140c00b03801106041ca102ea0080c2c0720f10221240988130a05190380c1d800000741601640c0440300145144001d00b801410031904000c02041c1e5440041003100700410b40903103030b0035214150300811001c800c080041d0b801c0c09107410f80741d0141c0d1084400c421051314540040c2500c44201c12030700415a951404940ca0007102c86c00c20002c251512141c110859122074545107190ba14542441141441640c05864040d0b5043d0305018a070049031001a05c91484003108028000f582180c0d000c10f030780746000d07445c0c403400d41d6082c0c03145050040008107000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 27576741 1250 27575491 27575501
    0xb0a09060b03070c11030703080a0210020405090f0c0412150c0203070c17010209060d09031404030f030f03021207020a021504181a06040807030201080a05070c06050406060909050a15 80
    0x70701060092440d140e2840aa03452103819504480d03003081d0003991381c46620140300c00001036108128144d107607500f450020b03003001c10302900c084030076105100070081d550391081d18a401c0801034520003219210101d010800b1301c12500306181d070a41e05101d050400c454043c4d081082d2031258402c00c40d00c611424220b0301ca02ca40c030400b42604001460034400180040001c50105003102c000514200c108404907442d0b41006880070585a901c09036036081c1504104101d018810f01c04050f03290038110b40c0c0e604030300076420710090200248554865801c9000e50b040368943d034240c4c080002c29282118001b0764400341220201c0c060b040d00d2017814171540c2c980c407e5030191404072030b444105800c3c0b00c60200041c421a016420450007002c9a4242515298011f102810106024084007403e6000140a00d00c000d020f080e0010710b40404c1010a56000c0120000f255000801150340d84490510741c014101c5500702d0070300203180c2070030b0f01c0411600003001d01c4002e11038030f8150040c052001484041360 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 27577991 1250 27576741 27576749
    0x10c08010518060307050a060c060b030703031b020a050603010b090f041104060c05070b0f03090d020307020603060d060b1203071b05010905100203040f0b030712060303091e030501050a0b0a0906 85
    0x5540d482d041502050324080d0964400805030440e84400c0e968800690000e07041d6008002284140c00c0d0002031001c2400b4840c40240194002d00b03509107180e4004041d2001a803007109070400d83d801c400308556035a010080141002003526440756112102084540d0002e0a02c503c0b8a10038645944c1341d0516005000d0400000fc0c1303011304280c686581031351004107220044a50b409440740c0840d106e0304501c0501403031032400c699a52249410885549000b440c1206e1800750f6005000140c0140c0d035600889520140981d44e02203600c0040c681040581000d003a000c0d41700c207803140421100f100c0000a03207040d6018031140c40b1800340340d0a0862480c0e0359400703581d0004640001c14001d80c2005004e48451070701504c102c0b882d01c2d940c1c0d00902180500f41e0002d00042c4400414000d041d680f000c9410840021024204502c13403441d038000d043c506140c462010013040512003c03900c81d543c0b403481c90040d5000b600a009603d42071802000510004664610916000d1300108850040744201c10034bc03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 27579241 1250 27577991 27577999
    0xa06031104020a0504031e0201020f0609060703110714030a1b020604060e06070807060510060f08060f010903050105090a021c08030a0203061c030207030203071d0a0906110f040503010c080105 84
    0x2400c469000d1101940c4040d80b92010701204220000008682d085220840700da40c54040351411720702c0c80024140400c01e0500e51107540001c01b80316181e04040307415030300003a1604001444e1900c005101000e4012984058141c0c8400310115503000d501100808008003d50b032031a807400000a20320b0fa40305071410000e90009400e21052007110702902480212520040107103040c80242e40e01c039002503000410840d130590303c6600b40325910f07165441c0703d0080c080c141428907203001000c2c0c0042080800034403040c4511040c0c051803085900900098002d0b5800400038000d600d041105540c2c1c038005808200d00890000310607442020440c3c03201d800707259000c01064a90b8a91140010103500040c0c00c5a0784081152407141c46a00c1121071044003501ca034000d490710b5851401090300300795455000d20512120900558010880c038501190700042c540c000144540b402c2c10550000e188164071001c84038000100c1070070b680044400381049402c100e000303010144600800701d0703c41d0001e21400d900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 27580491 1250 27579241 27579263
    0xb060301060305030d05060a031514060105030402090f04210207050a0501020c0315040305040506070f0b0601081501140f13090b01021902060309160b0703020c0a080705090903090d08040e0a0603 85
    0x280340c006d07085284c00580041400c1c0b1161b03180c2d01c6807107410117803a01c2d80c40300f9961202d491111080c9641510752088090810f58151301c2c1c5600811110100203005800e00c80c0b00d0300000c2c3c00c2000d40790400e849a94100402d01c408224130030085d40e030b07501c41d01826210b02800840024258800540c4a41c0e005010b009803c00d03080d4012086404100503104400380303e030910020903c0d80303e0328003500203103020300140b0f20000c40380d003806128032102424040c10000c4180c2089010f40e1000c0f481d200d014001e1800800c2c40020200c440c0d03442c01141d01820090400055207020b0403644010300d02a200c410000b00300c01c0034940e005aa48200c0b9072a29035a1000d070500202c0980740034805903600c41448801c2d200818a4030001c2e41500345148c11071a02c034a004a8001e00380355042050240c800c50036520202518107080049683d00c202c0c0c03045c1d0380305015030700008500040c248150782a903100900601050302080c6032201d0560498080ea0000140304400030716010500d0049200700e03500b012034815 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 27581741 1250 27580491 27580507
    0x605040303080702030c1b011206050604180f05010e06010801060c110907110709051801051504050403020a0c1503050c0901080a0c0507151407021c0f09030206160b06030106030503 79
    0x208442e005018609601085c4102e00303d4110521100c40c4100f03a00e8051010500c0300000034040204c1400d040b032009141500900003616540b0840d800e0310400c043c03041815160014032800b4089500c81c10b10010700701070002809002c80340703125020b0002602c400d1400d07030f2078000032a122506600080c10040100c0c000d192241880d50702c090300302d00145000c24204400b01c06480c0b03041c140d6401030003030b44c3c2e44604010000c954a40c903140014181c0000f4056420f00c480080d0380d02c1c050791300c03040c4110b90ba1004941018002c201d00c00704503a0001503d001542da44440c0d44030300c0468807402002c41e040200062031924041c04071680070707505840d0105107440c1c42d48414020300c1404101c005000c8104248004165145c2c0503401d03928103c070021519500c2d0308105040303000003414030420741d171101c010000c01550b15034008141510524103404018000001143c030a03000da800690000c0002488420340300c40b81c080c400e240c0740120041c040710744456062500300d0b1418800a00b80d600140101030f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 27582991 1250 27581741 27581747
    0x18010309020d050109030906030e0d08040809010509030f01060812160308040311010f050a0c0c050a03050918070c05010605030c03070302150f0a11060702060103150507030e010f02040812040605040303 88
    0x2400500260150b542c40725181d4a02d0308440c140340c019000b15100079000c2000304d0f454001c09003400303003a401030300700000c1042c0051700c803280c054401800503401050040c03d0f6403240b0142d444a40008088401c0c075003081d00e006008150601803001c0720301502085c0c2c400e24086e0740480d45540280400c8403021040c544007190603034800780003102004400802c0c44210701d0240039429610130310000000c0d0300c0c14620152421600a50303403604c1881101c0c060600418004551074100c55094140990b80302e041c2800104546d101035103030025461001d003401009544114040e5446100384000c102c6161a20704055680c1c1d1002140c0381d0560080001740010300384580200142c0004110007410180c41026100346904911902c0b0b0008000900c4d15614507002c00c84c8980218640c00504255410341d00c411603045541c00f0010b40700f0b0744450202c0d01080c42135100c1050020035a0003001240f44065024020f0b6006128000240c411681d84903c41086076089600322901c07620760515140c03450f0350079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 27584241 1250 27582991 27583001
    0xf0506090d0204090c0617060a0b090d05240103060b0d05060703020d0b040c0507020907090602030d090201020c0a090506030c030102030f0403111207030306090501090b01021e010f060e01031106180103 88
    0x4903041501c540300c090001c0c0070705c034050026090584980e01c4004e440072848a850300010040d501c2106104030401c40103406a003110321940e41074901703015840050800502e0445100d51000603148429154181d5034412440c0d5810307284a0344080c4500b000d10303003c00544102c0014044e003150840008034260364000d031300800c0c40c08140c00d00880c880032014001070460f1910034a001c080f61001074040110300d410942594482c0660404410540c14000025968081c0700240e2100d03541c0c41c400241036a000f004410105100144084601c80d100c0c02c00c5c3c000b4080650310240280310b40901400f0314a010300035203124030074000c0d0790401d95a071501e04851074138220b100440b2178050388848000c5c10034500c00802c0d442d402a24081005498010309000706c40050340a80c40d041d1070130054005c260b1780030800701030341041c040e429100f2680c501c0c111401025a1105604924940140054004c130800302071030413a801004128940031008003803004a1040d80006c040c0102d1109100d8840d6020ba480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 27585491 1250 27584241 27584243
    0x6010e040b03060108010501090b0105070b010e0c04030506150a09060b03060607020d0507080102030708060409020609090403030b10110d050307080a05070309060e03190f1202090f06160c0f0506090d 87
    0x40807031040704040220b070503d10207812982069445000500c28501a802440500d000c2840d28510b04080ba8542903243c40c0103000c4e4076114038008000c516103841301c5003550091034000043d40c0030303400e2261b07058101010000440d4010b10030b5410008040c540f40c49100202c40b04a0802c7c2c0c61075582d401000301076404444200c0c0e10403403071503115010800401100000e0074a010005a4a0a007800b01400c54100144610300ca107051030504030050312030b1030540b0410b15085d2110503081d04c441c0350a03805009844101d42e01f0543c041400b8000300d51040121014240b810180c8a040c03040c0c0e07a00710b80740e20040319010040b88103c0c0200b951000c40e83d00032640450303285000104a10700d6a642010f541010b480035000760b1020030300540e0561108907500c03014049040c000aa240704101c040e100d140c1a0f0036406480d42c1c0480d912555495000d54001d64a0005101c1c079502c2d80c060300510081c0c004940142c80410005601144802c450f5911a05445e4010207183c00c1203494410003c0e60b14a6201c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 27586741 1250 27585491 27585499
    0x503040206041e03030e0a0f03080c0a120504030209010b040e06010c06060801020f07060f060e06040216050a030504060206130c030807060f15090b0402130911130602030a08061806010e 81
    0x1000090301e020103800d600b03083e0309440c84071418510b1400c00038402c1c400422003921071442c1d84001c001c0551114110300c1101d5011091544401e04d11a125040400b01070000d4103003007004035500610341d8040300410030790348222102021a6210002301900c1d010300d00410f0019410b01020490300d41c000c40503802c41a2081d600403644580740c001d51402d81e04911048160701e0004251101044924002c07210b04444011040040524102d9030303000e4800003030409030240c1e44c00901c410f54a88070240d0007400703a400130700316103000307400d03107001007143d84544211030040c0204408900d11500030002c507500c0e560000b1a40c5000c0c1e055441702d410316400603004a824981da103480c0303a0b01a40502402e200c0003c00c0500f040b00c985004102010380b070342000d40c9446540304104800060722207411101c281c8084404c0000d030302541d440003000c10310807650744116140082c040042c02e00d90010041c00d80b8600c079a0360781e98580781d038001e1104903d100c243d501120380c03000000900300c0d40301d0b05051400d000024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 27587991 1250 27586741 27586747
    0x4051804081e04050a09020313030e030c0901080a051908030a050a060915030204200f09060909040c05030c010503091c02160905040b061f03050606120717090d0e010503040206 77
    0x1014641880340102d500140c2d108010404104900d4010894002055005001d51a42c80c02801358482d001e440c480c01001d020841080280a4a04001c20354503223401400745561543c4613000740d542c1e40740580c011561849501c1d0781c01d001030101c4d81034560490340440410700359200d140c501c0000d07050081007562417954540c400070321050345015409995601c841002019811401070005482c10306001c83c410101100c142c800f0380442c14100c50402c000c5481c070603103480002d070000e00310740310300781003540e003c040300d410711092028149a84e4100c510440c01c641004080c800150703442e02040307440b003241e50440340142c0c81700200c41800740c0462130700e441918003200c1e03031880c04911040980c010b107280366666000c02040040510384c20b0f41202c0100c0d602070741007885007200044e441110400740b00301500ea001207040d0b074580303000b903034039031a0035445034561481c00c0c17940103100311410007001c00082ea0b00c02c00300740c50b0600402c2c480c485040b5591024091808000150790560025004076000031b020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 27589241 1250 27587991 27588007
    0x303030b0d0605010323010b031b040905030f0c0105060f01050a050304060603050706050d0510030206090112060b030f07020d0315121401050403020f070b0c0606131407080117030405180408 83
    0x142c400e4034041d5108400c3c200b00050a1088030010446d40481c440b80c5a2512080101e150303000500034410520315502c0704c1c02909400c02103000750182c1800140684404107204e26001100005040300918030002000b041d620082080a0461a003c4041c08103000300050070700f46100340000c550090084802160407692640c03468607100d00382d4801d1000510101301c05c2d812030075501030b043c0c014180c00668100a4295000140f140c0b01c0c1e01034081c18410b15956003003001460783c000b0401060075145541d143c1ca08581c640c40d000c101101c80e0001809080103843e01e85000b40b184505001441c1e00c0c000c82d43d414180c0c0243c0d031092424050760465035807074407540001024010903100314801d5000e0034681c403128109924003181600140f00e144014402116107400001d881580540110342107820b502100c0303444001402c805a0b581080c00c1c07101c0405c103039240c01c002821304071941c4603440065151f00884e52512409240035182d4089102214402c90351604c40b01c0340d80250007070b24003038940280 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 27590491 1250 27589241 27589253
    0xb0d0b03060a0c0207090911010c051002070807060c020604030903111203190e0a030b070509060d140103050d05040b040b0906120702010501050906040203190e0c100509040506030a05070303030b0d 86
    0x400c5554810032919054100c2080d5411711095006040c8071505012500b5030340d0b10b402c81c4090111009042200c482410b42c24400d04005038402001c1403d405c5650743c01c00e081c9030070164000b26003a51554142200380308000e2002613018411380c1c069035400b0000d4256601c0c000044075080455a01202c20010305a06960500082482c240c400307044100007010000d000e0821070202c5e1805109540c440002c03c04540c154004c507510004502e4280e40d28403402c4005502c0c3d02a0f9081801650314015020103106000c10b0454141c3c0d000701e0482c1c00d403160110048900b48158002c0b41d5072114148000c1141034555400303056281d200a006c103040001a0404054001080b1400d000503911040100401c0c100040000d410100c00c1d00c2c25480c61900e40d4040301c200c500e04008002e481d80d0b507004000c1c0c407001440b610080d41e200030720608504281090080c41da400040b040c3c0c1c810381c50a008100140303400102110714030350250161061501e0f68074180d0040111100d800d0304090000352020000340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 27591741 1250 27590491 27590503
    0x20102040b130518041203050702190605040b06090106090303120902181005010203031e180d120b030c030613030507020306040303020a08060f090c0a0201020714010606020d05130b0d0b03 82
    0xb40c800302800e903030b4036250403c250a0b81940448003840681c90500c004213803069141841000079040c046080d4482c414100c0c5000a00c04100344242005081c000401202c2d8000c0c034000e50003003441100c59101c0f1030030000c1550082c8511030100308910740401c002406907400c0d14506030203170000180f100046d0080352415400160a1201c0503141003000010101505000c01601d000c0c802942140f8210f83d103216002e12000b25007030b4440041d00000d00c4040e46090301000030601c1c600f500c407d059092400b414111003046d690750034078180100c104483c200060f440040b60001001040340d512441038407905191901030640421a0402025025072020002640100d01c00e81d401a50744a4451004200c0c0c04041c101c9403081d1501c1e03a071101d04d5071390b400030b890700000c15803101070f42d40001c404160300a11070080002c11380603003002e0f191806181903021008603030054096854440c40e03d4000c85461150141c038542c800c000c540c05000c0301c0c6038880508240c2003161000510030b07040c00300081c5054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 27592991 1250 27591741 27591757
    0x15090504060903022505041107150203090c0904080703050a0212070f0c0b19080603011503050705100512130213020711010e06130902131d1e0f1303020102040b 70
    0x7500d40480d0b200705a8100400c0c0080190114000b884041806850a80a6551041c41e2003179868118401c00c0441c50421518130503400384640e2a43c1e4450b50f400d4000e03400886010541e400780d0540340722682010380480381b08940c02801d0340c2c0b41ca1907507a41581d094104003c0b200452060030030b282c4180801c0c0c0c00801040d4010200c0c42100e0741e551802003500d51964108200b86082072041e40c00809184544800300b0949081503541540c82502080c01003000b1404000301ca58a48000020b020010a100040e54030a030313682030403031080750700540b0b5620441c81c00007030310007511000804411182030032844c01071000340021680b401d40c4560405036042500c041e2820000240810490741e001200724805650658a00c3d0424200d00c801c44c4201ca614411120f076641c0000381da064582c1c2c001c030214050300200400b40025514403441e021040005c9078000d400c100402c185903440329542c8451880707500044d806103159950400e100c00c150f55002c40480540d03400f0700c008640f0800c4100030740514 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 27594241 1250 27592991 27593003
    0x70312090e0105010c020f04240306050a0e0109020a03061505060a0f110f0706030203040f0b0103080315030102070c0302010507020312041403010b0909060f100f06030507020d0e030d0315090504 85
    0x55420195540c010300c8040c0e10240c18005c41201e504e00584800e12088007070380c821640003649408035840c2c2c00d1082c0d448009956242480140801080710030340c4814001e4007400000c1103400040d150f4a422154020006980040a10300c00c00c001111a0048042001d4422040032005e40e03038000320b0410740102c0d8400c0c3c0031405002010b081107910640140e15152100300500c01200c8000b0210344038800c034091b46082580000008081c0843c0304120303056030380d20a8503600300e513a490a295030240c0098035a0140c00c0840c030000d01c5140f6050081d504115080303100380030301a1540d401591150701503e0100c0c1c041c00707850507402c5c0113070458010b04018040030655542034400601058212141c102d00c091051b01020240910008005007566000395041c0041c03210303484403168140d501066520500042018140104081d6450b0b000035004031301c642c00b150940702070100240e5848918600e5648c043c0e0002c0400ea0000d4407a402c508061058025800344181e1900701c08410b8034070032613003034941f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 27595491 1250 27594241 27594257
    0xd020a050c010b030d0504060f03090c0303050408060f060f040b040b030601032603090d0507051501060203040608010b031302130209030f0303010302030708030309070b0a030f0903090302040c0905011b0302070312 93
    0x7046000e024100803100114003501005104600140003805240595010084448a6103403001d019070b005002e000c1d00140101031455992400074007540c03250003106d9090190002095290075040c0344a409000010b00b000e0600301154280001096124880e0750b01c140c8910080015403001d1000a01071801000121030000d80d04400500072900b9443d0384010b184204104185000c000c148100108824942165242d0590400c40d1070031a4261014a03040221400062400c0c3c001000380122003803070310340080e580c1c1d0311451114540070403114282502d15107109180180380070214540039043c040401800d219079480481d1404021300040708071544008010b00c198641000250000e0940030000c52441c907240301201e4032010507108054491802040d00e0b81010301941016a80c260f0b405020031040c101814010b040c2d00c410b1000740d02407454603a1103012540f160001c1002e40390185c5a240c000d414241c2d0104480781c800900f54114000d203240400080c0800c15006046da6040d540c00035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 27596741 1250 27595491 27595507
    0xe010506120a080304020d020f0a0b04050a061d012001090302030705100501120b04051011030604060b030603070302060d14010303120c0206040f02010c030306080105010b120901060311060f0d020a05 87
    0x1012452812401d9019480b02c40359100040890003240d038060340c1501e0340c001c000098400705003540c0d030001240da4800966140826000c8088020300200c1c3c0e0200c4807540f007240e4410064608440700180410a8009140b0741c00e070315401076003400340040010b12500d28400000014030300f1146141d502710016040002c00f4020f11404100709000303e1082c08042100e035140c10142a250803019900402d020001e10005003805402c0c0411301c915401e400c024000b074904081004025031040311458800d40c581000402c0c200c0d041d0042c1c2c3d00c5120040c0003803500c1c038116000c100c8031380c0044104c0200591142e00940c0c00014440c0c200d402980700c0c1d113a20802500d841c40807400d80c1e113103424450441d0300041c100004284121000d40c401902801c0c00c6088101d5401c049002d40a41d0304a1209503007084000a4001040c1c40245040e00580c1c008017225150380c080d040c00c0e41c90600c00501954482d400c081c40d50300c1e2550040647c0d4070940010341c60a4020700e40c420907078004482074404600c01049002c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 27597991 1250 27596741 27596749
    0x20d02090108181f090209010f0510080906180a060f0606110610030201030c02030c060108030301090e0303090a030302280804021507030c1103070308040f0f050a0312030b0a05040e010506 82
    0xb40d04240003a0180c078002140c0c40c251541c1d051500442e40c040300c061400d99900340c1c100d0b0320000d481600030700500d40030741e10f50580d01c1403c540b40c4a0f65008034808454111030502c2b40e40042c2c01562602c01500c85921258204403c0e46072040c600b001c14000d01d42400009131040c4200e01040c03201d40d03800709085141040103810b0000f440c9200712941c10281c200000c24582c03440941c19294242000a050304524404a1440c02011054a00d500c208000420411360000c091412505d04d12010b10071500c0c20200a9280e020946251525034804299440042d00940141c0000c1d0001c1102d42c40d003e0b404a82803440448036402100481c81ca0820300055042058401d943c0d4192403032524600345003690010204410382e2400f400b85080921141d034603036410302518008580140515407105e4a5052440ca4002580310346845401805e800040d142080580d501c11241c2110041300409802c400c2940a0b100b111002c0d40e00007400400807440b039a540c800d04000c01c00c924000141498000184 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 27599241 1250 27597991 27598007
    0x5090105060105040f091107051006030203010b06090f090a090c06080103030906090e06090a060807140f0405070f0c0611031602070b13090b04020d02120a0501140a0308130801020d020901 82
    0x52410040104410300c0740c4050b00b11030401b20740f00d580340052186040d040c1e8030114059440300818a0042c41c420f502c90301034a80240042d00c2c022002000421031400c04c2042a00c9038201c1d00307030880601d0b0b81d00f181e2484c11104842d8816180d44010130361030a2541c80b004002900d0300715501003030806c8014810315602c0590280580382c80d04150307a001d070501801d603010110040149110b41040400125101c1498120b013005150f1030040360003c1d6200c9810040c03004440d5403a500882141c12000034624060043d0380c00f4110648070b2001d402d641c020704039940c001d14070080d80d03031580300d280360494030079100b0041d03105001d281a296180054418001c2c2007032a551301004004109005140c1415400700303031203040340c5540700009250403044000c01c019010340d681411000c0d1010544041c2c400c00259443d208001180d010440740c0c2c3c86003001888c070310095100c1c98020318100401c2c0b0009030080700400c01c403021104031003695a0740381c0fa042e0a9a02c22600d0b52011a000b00d050307041c035604a140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 27600491 1250 27599241 27599251
    0x60403020f12031f030b0106050918040b1306090f08040e07030b060405060a03140a0b0907020a0b040201081302090a06090b01030e0c01050702010c0602210f0702070e06011202030a05090105 83
    0x240500e440302e201c2c41d4006000c0580030070034542100c58220f0000540f041803500455201085848540e90703102c02400940280b25034034047c6510280100c60303440d14032841031059510011845440d12407110204c60040c2e550f0003118841c0d07640000720045880842151103c3d440340110705c0d40c96080826412404502912071810f05081c41d840c040941d1342c88050750203840003581c8581d1900302c0218200c0c064203102501c0c0303103680b0340c00302800148081d03900440200303041581e0180207501c9180c1c040b81d848034000805880d800048000c10015845040d03030031b4004454403600e006441d400c0c0c0004172050001c2d03484030342c1c2c50b5480704100f14454542c080c41d00150424241002007a40040680343c07101c200301035040c10043e000803c00c04580c0100304410030907400c0801191241e240d01d401501a0200586036140a03042d140068440c506000f101c51288456034041e01c1484e1a106806250490290003281840139507250340d0301690703a51005d0361040c0c41d625008a168105040c10500711500644 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 27601741 1250 27600491 27600493
    0x1110d0c020c0a0e06031e03040501090e09330a0c0801050102010b0a09050c0408060c04031704031a040501020405030a0b010f050f0a06050a0201020702040906050405100204050a060309080f0705060403020f 90
    0x2002040d58401d0f0442c01281c8503004007403a0b941e01d20340040d04100300200072400301199040b480c50000ba001001c0c00680c0d030280c84542141c0e44a5800d04071010041303906081c1c550040c00b142d555030325641c0350301c90b910183c0104200f46045540040c400b699089907260002a942c01490903050b41c005207442c01404280002c100d07403001c180100380f0300100b0f4065804100e840d6008500d040b05401c0855005080318402e40741242080c60700c2818a034420310056804500c1400910802c0707079a00c088404607540444000030100c0d221840d40c581410040c01916907550900001031152418403400082d40d10030356000420b58140241501c034801d082e0403050055480d41044449612002d2054041e110142016a110121080100d01900c03408030025005404c1c00e074048100003054020300d000f2440380c41038844912029485a0480c0110b20030b1540c407130400c02d020001f150090b0b000f011114060700c1100d2034060b8007400201c0d030741d00008046449600940410041c154184081051400154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 27602991 1250 27601741 27601753
    0xc080c0a050a08090a050109080d06060503010e040f021f05070606090209010503070507050a0203030a0c061b0e040902010201060e040506041208040206071103030d0c03020309010b18040b040309030501110d0c02 92
    0x840014818001c09400d101404010400b02e00f904204000705c40310309a0101c0280040d08847c5800016500040006035a003400d0240116081e030180e000c1c0c4c0d040e510322080703420b401c0d5901d84417800b80185000040c0d80002400c1503010310803103200c0e04210180b51503240d03a544c070a1039245c44812501c2a50050103050303c144120a00c0d03a900000701c070b4101115250050302d0b0f03003560170102d00340741d000f400095240c800000c042c9441600301100c4146030340034050402602054805000d2002c0000c882a000100c0c40080150245003542c0300b049098010f2000046490f12140c840f407150605440688640e4860000c01040100c142c805811a1040e80b03051002c5007059804110b0790301810030001c0c14910313580304501e0341b600c0400c01e980d829200300f003040c0986034080b40054000d50080d10035100c15400c00c0c0344050141080705001d4400b020803e0304042c01d6484bd1242c904494028000301d040100382a80000422002d000d8508010300000c440c80d0703030309003104c041c00881c0e20400000c402c0d90060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 27604241 1250 27602991 27603007
    0xf05030a022416060b0103050105030f1507180b0c0c060403080403060f020d021303030206091203181608010501060906080103110d02040b030d030b0f0603040804090b01020c060a030c080c 82
    0x20420351000000100d102ea000303a0951200c5a00c0b40680700481205549450303852040c0701e5290802c10301001c00f0780302000307683d072a0800c1c1504c52284c1491030100e60b000c1303100b80c5010601c0c01c1d611980b02005240c44207a40b070880544600c0c002007a4402c2d400900d01142040851205214554882c401181c4140c40c103495031340d0340804c9000c0e0344009050940d80f00e1000f80258110340450750b0f0b01f94800c0c402c40d511154082d1510590701c40e800309074014490000000d80201c0c0c001381c00341c4148000c1c00380358219030f540703003803106002c50043d201c0e40c060103051303c40c198140491a41101130401b410010810390704000c00207118001e16480030f420403003003800400200e0145110b0099062080d24047d0724240c090000c1005000e08042c0190036100d1800ba800c1110342c15400010b020b501100c152481044890801c8602e0209503405402880f0400c810041c0012a5211450580307040c0181c5031100c8510000644c5508030b0001c0102103900d5036001d1500c268408034503a44054184800350401c9a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 27605491 1250 27604241 27604249
    0x14030d0c39060c02070e0a0203090f010209060f1b070b120702010216030309020406050603090114090111120702070f0902030708070201090c1e0509070207060f08070e0d0812010f0f05030a02 83
    0x1074100241200d541c481040403214030a0007410060698040036050310300b000035000c0d001b5402180c0a0415000c1c6a484822040040c0200c440c48070000300124140043c0300611007003584500401d090f00e213550360121060603c00c0c000400244102c4030501d0f20b6000751180300c821890014807100841e4410881541d1400d0441c0410045581524000800b0240c40c03010400503c596000142d0004021040008509054001c00c900c218922112452500e802c0011800c0e658402d2601f1101c0805118020003003c0400689500c1408c0380704680603035684100d9100c017280c1507000b00b90a142c00104100700075410404464003d42e8520003004032400c603441d5206010064020020030034012802498100c02e81d41800300a04402000c0c001d40d4100700e030002e591a0068480c10021034440000d4201c00790007201014480d0345141c80b40030400c0f10820803c0540400418202c0d107500d001c1c001e0561a815090455006c3d00d10300e0241c0e110103050070004a044139a81c0c0c84035210f41c1c40a8017003401616 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 27606741 1250 27605491 27605597
    0x2090403022a03060c030703020d06090b04060801021e0a1403040803040605060f0d080d0e01021303030219050303010e040609080a08060307080d120203060402040e0c03070e040b06030414030d0c 85
    0x1220b0b88174035403030707444070f81040740a80704e011860070001d401c0141c0851602000e5004241440c42142c041005540e034600017802c1c0e025402e13801101095510f00362134105000c030020a041009440d00f03000545a040307224240303800580d4140c0b500c180120401c02040110302c241d6800c004101c0b000c81501110303100045401d210035a00400585000c07070790307a40d001c880380c0184410861803c02503465040d030161080400c042031000750014894042440a80d100320702c400c5908a80202c05103103940e0070701025108455000e0b00c120341a41d65421080c000c111028003401c140462030ba18113400c0d0030a4800c052070710b0050b0300100d02c0e5801c00c2c900e84032101d0b000741d4441813a89505501588941e14907002500902035640900a00703000306081248401c26800190b00c03038480c5445029084028209000c101e0b0307800443c035600800100085000710301260088001c5800b03890880b850f25400317203022001e13203c4a408100c041001c40c0000148a54000345410710300002c554009038103141c3c00b800e200042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 27607991 1250 27606741 27606751
    0x9080a0609060e1f050c07121409130207020a08010e150c090904081b07030b010b0717130305010506190608070201150f050f030d08150d02090403022a0306 68
    0x5a034078070710103042002e650404015816104243c0b4462101108954218642c54402074101c0c1d04d06000922032994810030390701070390740150741038222180c0b490058178089c100c0154040d0a94040c000f1050035034400d030a03013458200085003d46c40d50302034030620409201a0708000300c5079044c80450140640006043e03807452050704000305048e02c0c0c00c501d41da010300c40d051025800c102c1440030801030047d050004c6c6080200302d400d1400ca001e95510403521014107010082140c3c0821004120804400d270142403207500860840b007180c0740c0044021250360240c00c05d54076031120003904006002082c4661a4000800d07a8a02c2c0d540b540340da5041014012030007160140801c043c0130950b001d02c00d501c0b001810103884d8104103025290840250f03034a46901c9911710601c5517150700103d500b000f01d881c14aa1a2580311030740e0380d407201a03d4292204059200c59002002e82c0b0104c1d01582d240040070780264000c0c0c0103489810390351045555514450040034505010503844241103441c0094216408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 27609241 1250 27607991 27608003
    0x414071b06020d0f05040506070e011e050c0a050705210303010506030903160f0b070512010b0c01020f0730050906070c030501091101030c020c0d0611120f0103060b0109080a 76
    0x40180d619201000b401032089203003030740e890111510342e043c00961005005078011011200180c0e600c3c0021900c0640c61601c19000800c15403000d601e400101c5e2180d150b5040310300303215042c03040c01084203182159044041d146503000100030011414181003c0c420151b0700307455840440d044401c090390321312045c812240519800000100304000a00580c2c3c00c0c104041a400400381090030303ca60031400e00c82042d96041e01030030109500c2400381044038041a0358818406841e8613009548a10b41c022404885a65400300040c0b2b12011824009161503407042d10658030b00d0340780038200b00c56001254040621a070b2900016210150007005940480a003228050b075130340000c1c90b06c0c060030189030340000c11641c2000116410486482d6256407070000030398003040300c200704a030b04a03a1031241800e8079420500c4d8030000b0021400a410417a40252040c07034507841d000c3c055004042d602c100310780302d03040400818014030070000c050040f544d800d00d0929003c00700a04054545498130010704000b441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 27610491 1250 27609241 27609287
    0x150e061902010b060c03130e060127090603210207050915130606080702010506090106090506090a08060705030a0c0306030c09020c0c060c0312061806010c051603060b041407 76
    0x2a100350884103500e0f4028107100d80b654800d40d90a5640e80003441c00307511400d040d40000c10200c03031541c00c1a104003016500c400c10032000c0e81501c844c1c8818400080d000949900d4040f4290119005400046104a010051044071681c4018080584902000131034106d600e04100660b91100c5182d041020300b100944042600c2d4002000010901200100340d414010000f0b5000c0d00030700b009100741003a40091103c0c2d41d640c0b00300074034a0400d0080d5000f041c0118000e00c000e00b41172003d04032540300904007030446501d5034180c52400c10102c9050001590002c200f00360a1700714029074a4540301c0d07040500c01e550651341ca03d084180345009039040a40d0100300c0c0c200108040001010407803010f410180c4d07911546e0713401c940b03035802114a8005003804101061240c00d0940f40c0001542d06043c081c021520b40d00d00450340002c040d101a41c01d03102e50400e4140b10070040e4031041c0114401c60780000c1c079514030703400d100039113181c041a0401e041034203003003084581e00314407904030750b1a446203000b113 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 27611741 1250 27610491 27610537
    0x20303040e1f0b09030c0d15090201030f060801060f08010507080c07060209100e190311121501120605090606030c040209061c060306110712080612030a09150e06 71
    0x1404052074000140ba07000d02c00c078009240d1500c903000781354200b0158180d138581078001d0306001c00c22903078100080c400c40b00202c003003204030001c0c2c0c080458988145008925903c84d5a2500c09841054110007403695490500300301c04034602e100300d4000c2c44002c00902a5140c103980140100900805011180100103015010041c083e41115200007000300000319807001a400200040d00c1072001314007580c0896540103080a03203141c081300b180d83c8074601c09402c121241c1440764080600c5400440e500c1510b02c0e2030910030702d46403058082d21107460048140c400c5810b1400941c0d002510f10303a100d410020510011b0385010074130400304141038801694801c5020086513452042d01a5046110903005500708500015049542103d0250405106044414078000080d21035200020b01c161480f9000b00c0e40e0b1801440b0055000c40000d1020308088001220300d41140d005101803000504c50f28024041000d04154044401c100c602d4540030b03c0c0000804180103103d541c11240015030134059440b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 27612991 1250 27611741 27611761
    0x4110702030a05010614010306050307090c050403050706030c0305070306030f030e03030409140618010503030409050405210c0d020106080304031403092e0c080d09030314070e0108010b07020303040e 87
    0x41126034054100c0c0e5401002e810700b81e0090100303002e44000c02054880105503907200c0e01881045e14001800340054504e0800523400420300140c614007400300512002001c80c00c180440030050656440103e18003480c3c8200030100c0d44000d04650900d840c022040c000f050000c000843c031203602d420f00515613401c0c200040e255001c0c41d44041641030404145400110341603000e00e00072041603840e4400709050701a0202001d00c240200340d05a402800100108050368010680142c0280255041424801407074103d0440c4030020021200c4002103112410310708108500885a052000700f03c9582005080b60b22480340748405040840605c071114500d80052044450f5010002c0060304999048600e00520b2600b06141601444210301302420150103081840c04035a80201c4492038240030003d980014000500280c0c2019075800062820b074041c2440540070b5442034442498001d0000001046810305070000c01d044d40052100c0070050314000107450a070307888070401c00143d5545100c24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 27614241 1250 27612991 27612997
    0x10605060f0304230313170a1a0c041a04050f0a0e18010b030618100212040f0f050d031e06030f060b180a0c090e0601090603020307050906030c1b1b0411 67
    0x3e0604c1340070004140030480301c8100708030111103c0c04601000b0980c040c1070913444403041c24010b42450000b4500030000c841541020760301c604503804d210304003612010489104040b20740000086400010140a00c0ca01001800e5045c00c0c21100d00106604080d5041403901c0081c01d421841403454046070300d854020742050a0410001c0c0403200310b40342007076290b5441c108185a00300b6900a4609031075250106008884014900009401440d20786699040301055942c1c03040e0b40200c180e030441000104107005001001103c1c3d500417a401ea0b040b12007401390315419503210070803854400304100082040764250f188540011000030504440000725048401400521101d80006000c104190362680d21030401c58030a80c1e91000403948036001211242402e4824501181c9030b08410041c0c6803103900110741c054020b10340141030209400c00300b0990303041075555401d2080082040503034084440f441d080352100300002010452a12180120b800000c00646030290b500c0b0061051810054011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 27615491 1250 27614241 27614303
    0x30c030e060f070f02010e0102030304030207060f03020415030902030c010e0117060301320a060509040209100807030f06230406090f15050a0b0906030d031e0e0708010605060f0304 79
    0x1102d590b4120a1400c80c2e0710304a03244080380444c1001100a04951000094910131030340f58008208080c102001074074120b40c004024810981c0800010858244881e28245044400c1e00c002c02d402000b407042500740250990301d1810401540e9100c070035070f81d010f03e81c032a0500580c900c25840381c99543c0420701500340c60420707103c9a044640320078950204804640c2c00f0280603c1046080d8842207200401c1c4d0341c05202d940c1c0e0120024000c203000d440d15030b0000760424065144442240e0395440c1c034a08000c0158170550f400554900c0031030074080c1e68052415140494100159110980304240310340c00300140016102650f140c0c900010040300c6403429800c5900700e2408101103072441c518002070082100e1219a060610f200b00c02241001d80b001801003500402520000c0c4203144120003e104004a19141c100401c20446d5070001d94800c1385800c2d00d0100140a02505020100d401d4070320390f03840207024810811a039410781405505403900603600c541041440f0054001c1101281d0100071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 27616741 1250 27615491 27615517
    0x30509010f0c05030f0f070f0f032a080903030603030a050d090501050c0c010e070302010f030b18090304150c050a0605131401060906090b0a0608100f090606030506030109030c030e06 80
    0x2211809a40c0c0103005188210500070703013140c1e56a60301d07900281846c42520345401003640c0105612082c0d001700c1009542d0042443c00003041241c20b03101440c005260a920000c8000590b0b5a4074100d5109404035401400c03c1c00461440c2440700c0425a02c0c031581540c2d004010002c14640341104007504088550354001000f80024180b62030140ba0035030008810900640c130f0010f40f01d034003d6000c2114000c494050310707285204000240e0a40c0900015101e1a910442300040a0401d200041410303000703001c203100039501d5600b001c074600e0100c5160100c8105020006884500107100090548000c5500c02070101d4a6140d0328442d1104803070035040104520f41d40c0c0803c15010005612103011034ac042801030207480d036506420011111040307607150700103000501c04d004043c080d180ca143c115040802440c02c20781e80300c1c0c440c882d0030f0658010300300b582e4564404100301d236454051a9000710049008010115140d9009012903801d24001400d1221084030702c0c50030342c0d540d4284d44243e20806 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 27617991 1250 27616741 27616751
    0x306020c03030a0c0309020a06030b0a0b0f18090f13080408030706090506150a0b0f09060309030a1d010f0e1f0206040203070e010e0408030a290a08031306030509010f 73
    0xe0102a225001264148490303844c0c04c0d240d2130480e100e8003903010960b4001c0c06600c22507007090000c8004d05852950103800c003000d000c000410703050311b0f00109001d031060703a01d81d034456841e03103035200031000140d0398584100070b940103200e9421041101d01d0f4004610341c0e40a45800b4207881c1030b05290007641c0c401d00a500000c42c070300e010300400380c10030b4a001d4824400d85420360398803200101c8583c8035803945e6800c0028041c080c40071640c0c043c001c1c03000441c9070040ea810f007440440020240d07030044130003c04582010070912407260300449003090400020400c0b50001140b540000c0078410301100f940d040080c0b90013840081d807105221150048a4034006c100042c01c0210080d5403a20f082d40c04030701074811843e00041c2c007000f034070340c00d41680d2040c250300d841900c5580302c015080e00058442840d056542804a0455100349610842075000c80e00310042c0c40980010040c9856040e40001d082d50010011603100b41b01c00c0c00144180c0c0e02c58100011141c80f500c10b5603004010f00e010201a0a246c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 27619241 1250 27617991 27618007
    0x70203011805100c03020f07020f1305042006041409070905030f0a050c030307020f060a0e0901030f03030b0316150207080d02010204080d090b030705070f0506071d060403050c060f04030602 83
    0x200c0c905500e01c2800c8424400344000f04e104070708a120b100d0748440e038041c0500c08080140b034412546464010000d08501100400c550341c201110310540341280c1003102544035410004060203907040c02e0701c3c01c4a00505252810700c613040c00b1094408183d11030101d032000500782c0c07401440042e003e004040c013200c007100c0254600c0ca64980d94444103480c0e5104142e2400064540041100c2406501600b812041480c0034103103c015045219500140b1000c2803c0310303110344500991034000d50048004544110203802c2c060201c588a12800e030080e00400c00032020b50b0028105601103500036003100c0085503880e031080342054615000581140502981000300d281d05401810a465003081a1440310b40080e10544240a4600c1482125001400001c680394050009041007501601070396128140c0703680c495003001002c032401400b2484200182c0452100072107801d2840a00f52061450700341192201c0d0b03605c0580d00407203486000c001400840c560a1101a9802540d10103000e6403030b00382c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 27620491 1250 27619241 27619243
    0x14060304020d060e0318090c0d090c0806151c0b18010902060d0f05090601030c06050d0207080c07080606010327030c020306090a0b0a050c0904151205010209090c03011a070203011805 80
    0x11030714200707050300c101b4805002031610810712400341008a0a2500e0202c01103810405000c1502d81071780c02840c51040011200c02c280003580c0f01e40d601104003043c0c50414070402034440300502406510324420540000022030b1880540d070007404910f010303400c3c140b869110601400310302500a40003c000702d1040140c1c0f03080e410408106c11144414401c41c0c0da1041c000e03603182d0003488060401d44140d0010480395004400501420040840c00b61600f42c040d1a026800e5115170b03040d1000390710130304041009400a1140c2c1d034101c07109280a0005a500c0c050140640009404416180340304c00c801c4810036000d01607030212a0790180c1a10418541100601d48070401000240d1703118058000040000703c0342d00c107403403291b03064520143c1031800407011300004022035800101d10301915980866401c1d1903104d8180614811400540d0b60320201003442500c0d4030280012424450a00060024410100000303890030308500d4203940310121400081c0c05420818241801c190040c4d0b001c03014450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 27621741 1250 27620491 27620497
    0x1519090605040f0203060102060a05100f0602060f16020a02040f020d05100815060108040605070e0303130f170c1509060301031406070215071b0507060c0201090b0414060304020d060e03 81
    0x700c1198100044800c43c03a03448183d00c800c8412a005801c52000149030f0460b503400590805410103d904403039464007035414003043d00750490009640300d502081041c0a08049040c0d20202189204802030100b40b400b031750b16604c0c41c900038803a03034940240440254030b40d41078484141e007040781484581400480008100114040c1d0178050080c0d00450480d4055030880c1030081006035601d4140707541c1d54903020002c0c00045c055008004440d418480703070766403c20103070808a821032444141d50b0302d01030b50301d03150a01d40c0d03008501078018001c45170b030a540b01041c0d45080c1541600e88038046442c5001f50107440c0f007440542a88144084004000c0c0070704480200e40085000f401c0390129199104103a070b8442c25000b0286900c14002d0004003010301c5a5210a444c40084403515141701d2655a01030805074503070000f0303000802c8000104190740c3d22200340002010410016890281401ca0055030006110003043c0105000004902107444201500c0d20765078000c1d400308003510038030300d140d40c03654 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 27622991 1250 27621741 27621749
    0x6030603030f050307050d020c010207050d030e0708060402090f061306060306050f01030e07050402210412020c0621040305070506040506060901090c090905040f050a05210307020615190906 83
    0x1d40c0010b03500300090007481128080d4106403600c500304a000034095010b54070419590203655003d2280c1800102c080000000028140e1404541014211880342c0390401c554842c8213190700031011f0201589a11540940000c0100700304200d50762054041815800a04c04d02e446c2076151500018001d64580e10100613100c02305c8800d110511480b00460039101e88600800d0681c1207a1000c001e0b070300c0d00d41c3c006e00c848400301d00e8a1000c014160020b44000c00112800c0d5440321240144440c803590522030700441d400c046a0743d6040c04944e0100c1882c040d80c43c0b0801542c0d95400b00170070240343c003e41c103980e5080c2d440011110149498602581c0350702003031300c02500841744c0800114500501d4040d103e1046c025544441c0c1041c40c052006c00500400f40c0242c5050b40100115808618140b01c448080350144004100c0d0309040e51841070054030340041800300394805e01c140328030300c0c1d400701c0c0d0160009200045500c42c0e14000002407411440102c152529042c045800100004c0c2c940080b4121 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 27624241 1250 27622991 27622997
    0x11503030c0c051e040c23030414010c1b0305070b16030c0302090d02061b061e0601020106050915010207172d0a0b09120a030905060a06050a05040c0e0a0603060303 72
    0x507070725014854038110048100304641501c0544c100142440d40c400700083c801840d284503c0c1c1d080d0110070802164880707440065640000c00c200501c11021111000441205d0080088113040c0304000e25841c180c4159084050405400300d040c18031540c16500b507180c2040d988034103030602c0720041603a030031000506000300b8107140c20411854003074070035910ba914028040900700c1080740d003044040d03480707416200e207140c0c0b8032003030700640c0b06081001611440c4a040c00d858545080c000410300b55a00420042c11607041c44001c0c411074460346c040b26000f40d084c03403500d0080f400690060f414600a0f4001c9964601c900c2d528103180c103000901c0080725040e0135502d16600421442c01c0d039517040c60852441c90f552107522100d000a001d0a80154003440c2d10040d180d50705515450030182c1da04c0000c0100c0080e8580c0c0c0b40c3e0b8103101c024000d4a801c1500ca040402c196032030a008203410344403600c6014803c030755460520008038020f5049030f50045000b01140c10b01500c0c1e12024000b06910b000981c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 27625491 1250 27624241 27624263
    0x50d0302032502030414060c0a03050c10150b0904091208010501090b07050312181605120f06150409170d050c040e01030206070303020408030d05090d020307030c08070203011503030c 80
    0x90b034900500c80124001c1943c042c42c07a0a082005440c030510030a03030051b030011070400104c038407084107100d0000c103244250b07039855071120b05d400c0035880d00f03501040c41030029181c060284c0d0083c003003914460849002100d01502c8000242c0003800034280c0780c00c0940011001003035103052540c07003034010381611400d0320b600701000d03140c0c00504628045c0d11002050f03075004000c20907211001e4400b4030b9200190310703541c40a042c801d50302281816100c1c0310140c1b1020329541c040c041d0f0300c0c0100c0362800e20006800180042c0307080d0f20480e540e802028100e86140c00029443c03080603260341c0c120100098001e00c4005892440041050066112801011005103800049050281001c040342c04071001c1c0000300450b6400d60f000c00ca0903900c250300c22401e041d070811001518040510152202810108001440345440c06101d070402d0195564041150001c2040c0c1000a0f0491031150210b5080004980c8031501440030074014912292440303290250b200002041540c0041540001485140071901d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 27626741 1250 27625491 27625531
    0x90f14060406060b09180405070b040801020a020111090d0f020f0607030801050906040c020a03050d0f06140102070602070513090501020c03040305030c010606170103080a0e0406060906030b06040506040b16050d030203 95
    0x91341d0080c002d100d584a04159090100400040d100a4200c0d024800350341c1c03da550f85004a1a913400ba501c60407440e5000b141c198881902031040800d03544218102929000400d4005011007200c0c140042000004129680964035103c0792400031000140c0804c1c0d81d07212904000c1e0500c00244940b910a40c54200000d282e4246401201c0c03140c4861b400402014441d560b0965954005035244400241d03a5440ba1030400854080c5a009140d8103500360303c19840c4800080c14840f058001900790341c0b181000300104e13114000e001051aa462000003484080d6241c0070380a44034001c40005c01d481301007004003d004010000744120705400c3d00800c8134943d1070b101980c08003010b5030490042d1880b01c00400105414a00a124402036854014080852100001c1c01ca80310703a081100010301349001800169050310900e8035581048803c142042d00d0040011014442e5000f8400d0300c50012407140003040e60381e0000c0740210750206c00d88003c0d50144400400941003119120210300e01090101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 27627991 1250 27626741 27626759
    0x90f0f01150909081207030b03030a0806090703090b0a0906060902030f0601090f080c04050a090b07020303070f02031215180c070b0106050715150f080601060e03030f0403020103090f1406040606 85
    0xf44596014940320b081c4070861016079050300000740a90705150b200c00400f080c0e175400340010441c60404e500c0c1c2c0d0901d030800c80c09000216400420501c1030624290200c40403880118200390300c0207840a001c15220041e150400150426078004030102d4004010301550302601d0311040d00c181d4083e030314500495510303040780940c0d8146104044980d004a101113006e070611b40c01407a0f205500c0c9401240e6598241d4410741c1e120811659000160004028804202d170b003c0c000030382d24600351008504003900cc65501c4044840a440c1c6111459404c0c845202c5881c0c1295849000750480c200300014501ba400f4000a03501101e422142080e9040000c14072501503802d9030710300c07500900010740140041c514880141098000415040c11409000174410702840380200600195030140c652540751000c007410b0700070183e00d2507109410905c20510340004000546044940900c1d000c101301a2a05185994011050001d041000b12203000e040303c1c41c0010703626024922030241002003d540300b1400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 27629241 1250 27627991 27628001
    0x102070501060821030403080402060408100506011e090b131a040303021e0c01080603070f08160602010b060f1c0207080c0705010e1305090102090607030915050403020603010e090f0f011509 83
    0x501d000c1307040c408540405e20900d0303000c0c1c0c4144085c216500d0181c82d90f06943c6400c0c08001c503075180326214400c0101390b591001c07501015103542d03030351a5a030881c10748016040c01d0150069401c54840828001c0f0720501c2c036035101000709035007154a401415000d0008030558400d000580152241b480b168100f601c0d82a0b4103805800884060703d00826201c0044440200150480382c0c18442c0d50b10115105590210010050580b2402400e00c0c640a000703080070001960b000c80103591600c4070130150350729058100e800c0810448111a942d40c415001401e14891482000c6201440400d0722420807078030400800890320140300700d079002940c0b440112004051a014103400000c0320083c0c458009040d00915040300b1548005401c01e1003103804514030740c00003a019400204941810401880f841c0100d048241c500e10300343d450a81140c020525511041c4105110307142d5040020f542448144040e600383da1540b82500c01000003a4640341c0a49401d403000b5201e03040c0b1003000200721800b8828 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 27630491 1250 27629241 27629293
    0x503280e0a06091e03080c01020d0b0406080303060108040302030706050106090e0a06050105180604121a0a0903080c03070215070503011802030603120c12040807061704050c101101020705010608 85
    0x14046039141001c60410b10f04d10303814980c641d400c070316800200c0000c6d20580039200010402c0001130321201d00145800694440d105054016441e0030b0040c014042c001c01207a500c084282000c1c040f42e126460103d103503200d140406003c1c246814004103006511600400807100d01203103504060301d40300480c20440324140b04040c0031800400001322044807405642905c020020b00340d0f41000d969181c1015443c04100003120112551651010b001d1103110983e0f803c100c3d6040304100650003645d0151283d0b1026044100da0071000c000240e134980b08001301540c055810035115a036040c60600039260b6002070051008c10394020745e511110386140d01c2501e1240100800403e0131892503a943c040640c0000b020320b500f80201e1000c00b8020b940100140020a0800010010649018401000840801c81c160020840001480003140000440f9014283c04403948285280c65140654100420320a130308025400840d07200240901136010208545016094503450400510075114145032056 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 27631741 1250 27630491 27630497
    0x3200a05010f030204030605100f0e01032a0302040e1507020a030206040206031005030a03020c0301060f0315050a060503010e06160207120b0903040b04080109030e060f070f0503280e0a06 82
    0x1a041200c1d40c4200150044084242401454030352652034030001e5842c21111110007c42d00d44c41040342e00c03240c403003030402008a88848151541160390b00e9107803204140020411050602c1c420030b25000c1001303840001c40d80204200a4801c800000a482d0410548d80118090b41240013810b501d00208580e0409a8140e014100943d5180c0c20000b50360030107001c440022040581c04a0192010000301040500a4005002e41c9005008060a440042e0044104c00000160810010f002071100c2c60040c00040da0108081d03998a41d07510041c052030740269815070801645500010001c110580110b00300810400c0071800c0303000c143c1ea1401d040c401c2c07071412800003c6002c080340300a004660003107483c40c10751b407800c0e541e40c905a600d60019000318460340d658880e003030209a008142506c02480680b0007a0400c0140d03c0b101c10680941100540400c400150000801c0340034800c0f102d802000030040b0003011074014131407401c01210300024011036040c00a4948503d0f0508103401140d100796 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 27632991 1250 27631741 27631759
    0x1806090b03040f05120301080f01110313141b03060105030d052208120417010903120e03041809050601080307080406030e03070b0103081305010e130c050c0a03090320 73
    0x220302000c240d00c02001900d501651010a03800202c007403158013003592071210010b49a5060220b005d040900244003009280c2c5400464802e00100c5401d495000b8101040c00d0074000c0d040c100903904008005a80c0b803540212449a114400607012402c10075000364102c4042ea0703212005d140d81d07400d8491098010480c10702500c1c0c01c5c0c11482030141118440c20541e10b6607165105c01d858505680d055042510b10000314091280a030203981703400e15034107100001c3c0007070b803566100a42120269001043c103039494602201401000b0800c0314024040b041381c0c00c900c40c1c8180000070007841c461030100c2e424007800c800095443c00000543d8401a08004964078040c03403c4402e800900549107031141600040c0504d102260b10000b0084c001c0d0b000d402c600e5620040350081d60500c4019811407410f004007140c1059a81d00d80c0d82000c210b101014000007000d5a40c0359041d90503004004044245206e044611410980d0055410088034440e500464402100580c20709000c1d0703560500641080b208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 27634241 1250 27632991 27632999
    0x10b0405040e030c0d1d030c01120e190606050102010e070317090a03020402070c06020d11030403060b0303090a06020a0b0109090b0601030f0b0402041202100201020304081801050d02040806040201180609 89
    0x503a01c962080500704044a01d0221308a44840c14004081850301c04180c0303149020034002001704102c0441c0404a010b4003040c3e41000010b07040810403011445801c0c1d43d403403400d660701810400ca225514142c5041280c81c00c10b4607024024000ba4020f650055003030026590405d60b00049540949038003820768078910301a1440c00d9410380100134070f1603001c08889800000768440d84010b000305030285000700c0d216410480c000c1d1401540b035020740100589079a0781e0031a50340200a4605a03a84440040f4003050083d000070304d07600407440b48a034000010380001509079000a940301110740b0410100c90f0681c6d940302d80d80101c41c0030000241c81182c2150001700340d5840780e0311824030700150035400581400004041000c80e00142c201802a20707480f4040c40c11751610398100c00700c0b6503461000307500e140751507500d800540c01559070865413004d1440c2d1440080e0300030380c16159062000c0400b10f4455640e0441e03295224010b40d4143d000c5440b983d42461080481c0d005481604d0068036850512890 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 27635491 1250 27634241 27634249
    0x51005012709020402041d0f01140603060d02091f080118020105090301060b0d090215030606250f030807030c020a021c08071407031401020a0813060f0e0304090b0603010b0405 77
    0x400004101c0040e40e401c140c1006985501c0a000030303003a20800310000001941c10b02649840c058214460080c440300100b08a484200c070b03a8104030f0381503404039107944452000c0b030024241c6040c001d602c81d010208010800c0e404810195000280c0a41580f42c540c3d0741d810720b8202c446c407846a9158a91403182d00000d035000340c004184068000d000098241c6d624052030b42c01d81c01052104050719110b201107000e5142500c9031a90303c128449903a031540c140180060420b2107240b1480c6036201c1d041050b0014000d00c100d420072455040400c01103501c03d0303450001c0940308100c403d2000300c0d1505040f1041c551000a450101e641e0140100003540d03000c0c880038403200740d81c1c10201c5400e1707020812a4002600c1103008800380205100030704400d42075181050302c00713040260303444130b907881407242c0031902d584241e0b030300d4200f02e180070345450300e81e0070341400406406000a200c1100d410b109050b800941d0010041088600741c200410804c1c400000308425448203110302c0a02c801d06010510003468 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 27636741 1250 27635491 27635549
    0x610090b0901030e030c0a06020a020c010e09040609030c0b09010209120c0d06050604020702060409020c0c010809030405010c02010e090f01030209130305030109020f070b0a06030303051e150123040305100501 91
    0x548030704031783c108088118010729040000b1805c13a1015008650b00710001e40400800305c0710002400d00c1103011180002054000c240144094141503c0b80c1100d000d1602505548c0076541d04020100003d1409440c801c0c080d520601c100740c004c00d54035509104581d008511241c2903100184045034481d1135403110005024060203e035030141d0700304540c0740140d45180081008142e0030344003580721f1540c55021402c2ca11200c51582c18440329104101d961240070040701d058600c24200b40c400c00c4605d000403280c1001150425400c000898140f0044140d91001141200c0c802c0f11050a0b40d640d1550a000340c0c6480440100401c01c1400107006064198000c2c000400755448450700b07101280d201c103039100100b030b10700820346239941e041403046c5989800b074603a100000001000c550940f000031004070000042c5500120b80054500303001c1e41c0e1181c80c80500030519503c41200fa9080d030300e40300702e45a10512048030b0a101c1c2000340095103541c0d00940b4120b403c010100001c0c407002c0101459050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 27637991 1250 27636741 27636761
    0x5030613062d060f02070308160206160510020f040608060d02030102121009020f1602040605030f0c03010f0b01090b160c060c030f18050111070b0d02030610090b090103 74
    0x591201000b0800409000701441d030301d003507110352401c003007192103030510301008942000080116050522404580004456044036440001503030380d0001c0122100b01311101c0100298001c0700024030080c0903120080c00703c2c02c1800383c401d461031050030f480e02004030b07c11300d07129581680b404e01080140703c0c0a02c030a035074030401c050b00c0c031062154540e0010342240e100503a08d4005141440c180000241981e1802025007070b4400301314503001d0394070691204c41c09660003150458130310516040c215103a039000b1200a100c042d04032090800d17254581c2e40c0302c4485007185800381d8644006186119250300034501d080c007041e11110003080c1092039103840c0d544812400546142c1c44a00b40c80002e015022900040c4003940d04c1c0441c00040b85001814896041c40e01d4042151031468003806c0b1807052108400c403002400e10307507101418010020b003440b5866100401e03901001c00c5160115204e600154410182190100c1c000050f456003035820707407564001c0c0c071200001400032140b5940241d125003400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 27639241 1250 27637991 27638029
    0x16150201020c01090b01030b150303040e07110d0819061d07020a0c0603050f01060203190503091005010306090219080309040903030605190801060b0c062205030310050916050306 78
    0x21070180b82d810350a45001e520100c0d11200030344010000d101080310035a80048041d816005c0101c410000a80d980c016409140d00e42d5000e00d0208080700e00980070390840401000a449030080d06400281c000401141c0080d092032080482e418400b05511440007580c0f101020221008000c0c40c3c000f80114004200d20258402d45071202c02003180043c000c1c0041aaa56010604c4c0c07078080e15048103000107038041015035209000c0d0700d015155440403d440c0e00d4880c945180c896030740030306082c544540c403840d100e221458603001100384103081c1c000c82411fa000303648d0143d0b40581426901003012151043c40501e4009100710f401c036203000d410403c4418041d26021455a40701c8002900800d10401c00189801d400701d41044804002c3c001c03800184000c500c0c4509111a0080c40b50b140d41008200c4807150b5030071846541101a4038001000d0759401900300d80e180e203810021103040c88445d01030288504000d600044144200c1912042c141d0440da84071802d546400e414054200703464250070540e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 27640491 1250 27639241 27639247
    0x6090f0b0c0403020102100207050c120309060c01020c01060f030201082a0309100f06050d1401020c030406020d0201180c12020d060f090317041106070c0506071a091615020102 77
    0x100d44240310390360040c1c1a55448580d19460343c40003910b4900301c0c20403018418018060840031450210342c0c0c907010308094070720034418801d07a00c60904510900ba001c6034003500204040c4080001540a89140b515070002000105d48400d904040d81e00540300090003e40620005213403248400c09111480851000d4030401c0e00300000244c6040d002222000d10395840fa48003070810141602981341c80342c003c0482007140031f040c54040f503a80c645c1110060b00c0308105070340d01084e56409504960007150000240d1761901d4503103000a4983c90082d0500b4010343c03c3c1100c010140080d0781c151180c0d15407000101c124146003030010600d0b4200031000307a82c042450721200002c0340781d6014040b150005450300140c50161450041c010410003496065001201002c00000039115030f569807000f98100c406c55224041840c2c080641e11b4150411500483c0c0856150304015112949100e1b4100d0b641012200d41d031015240356032511001c2200112006610301040980a00303000c0112840343c81c40051303d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 27641741 1250 27640491 27640493
    0x90607050c0703061d010506010305010503030d110f0304060903110f070603091b060302030a1103060603060405040c090e060103170c0d18030503070804030b1b0d1802090403020f0606030307020d06090f 88
    0x2105c00d200b00b00c26081050990f0180c400c01e00b132043c564004000d09040080354108000309a49000d603914814115581d203200307000396440e40b81503c080c0045071003c241c1d01c0ca01403410030060280c0410440200b08180300c0003100303030b1010034101c000d1001640105196450031a04a0103805d01220640700c18520b18401c0100e60955080d50000d0091a00c000d0707501d00741501c0390000c94007402c5203454030752410b00900502e40d0b00c040c00c0342d812050444000c5110f440b5070501d851601c5040c2d0011f440d0328503016181012500200c4e440e81224050306511b0b100d8450002d0f01690b502c10090b142184e0f0b040040c10042141c0985241e8a03200c0110081c2c80c04140ca07542d0359451940707e80c1040e81c0020300440d04100b0005131400c840d034402e41044c41c11031b80110740e000c2a43c02e0300030f4162021340307543c0704c246615403017212181c6803104540003080c0310094101380c200a903c0300c8140d00c0011a600480f0006034041c200002201d1005602030a5034194882c1f94840034024494035800b00e4041d803103145610 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 27642991 1250 27641741 27641753
    0x3080307020114060402070203030405060a050f04030302010603120906020c01080403120e01050610030606020307060b04092102010501091109011110050c120f150405280c02070509090607050c0703 86
    0x188100c4654000140c001185515024948001041103205078010016100180c401100740c40481e4820b8070810b07220385059805440c00d0150792070010030301c180843c1c00014981e05421140403a4000d42000c003d0b5031072442c0c12142c404441c060a00541c0c42202c0307043e05544201b100d154060301034900520b0006200e444001600d20302900000541c1d11a0f05106c510f1800500c88002d80303070780e030900f04146454140080e40300e001d141d0025106030ba0740c044a8840d40c58980010400d158441801a1042c42d008480f8070800180a41040150f02c0d00001203001c0c5100c1c0b2900c03a89650030050b003800c00c190000111804418070030050420301496000740c8001199028280c01203d80d072035066125201c1e1b00390b405100c0360040c20407540c00a03080500111111903802c4da4034041c0181c0300422243e4640b80c400840f400c010b0b0f1404002c98244500c011182c19540c4600384060443c3d003aa25007036911002c00c59001070130740c1d0101c4d898100c18080b130394081c021402041b6188242040d59030b061340e641c48070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 27644241 1250 27642991 27642997
    0x714060703091103030304031b03020c03070603020418111c1401080309011106061e0303090a0f05040e06060907030b0d1e0606050103090f0209060d0c03050729180a0308 74
    0x42004240c0380c4681d0740403c040c4a501c1a00c0600650045045151945005040141d000451503840e0341000380b0b907060610034041c1854400c0c0c09012908421381d1480024025800361040c265015541224030007448154000c0300e400442441405041464100e2103250045140340b9489005554600900011004d040e000d4004c00307002c0083c644441c0200d0014203040802c9608130f070690095001c201e040d661300e118100a11143e0844100c540d071451010070b1a602c03034451803640c03040200c40001030b03172203110a2031803d40e4404d44003031000240510750269074040c02e0b5030555000301d07a0000540807501c2a4064040d0780401441680848455110f0300c00795507840c1c4141004641515042043c400d5500554006000a00e4101321081180d168400c000c040c1c0c0030000e105040460101e407495891a078440c10007504481384201d45592894903d0303480d0741900c1428096074001d2000c040c6410a1030034808071003600540315150890b07045031210003045018026900c07151102011020420710005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 27645491 1250 27644241 27644251
    0x12040501060501030e03040303020d180b160c08210310030c03050a0201031b080a0c02160b19050909011205010603061d06060307120b0a021e1809130305071406 70
    0x29045003002e0004003960200001d40906600c108010000a42d000854103040781d518601040058100c01542030000d14691250540580c0402d500401014000d903592910348601c210902141c1d5170989180c40d031250156489500c40036091032030f0456006001154001a40d8095840e0561250ba8220f1078001e01e8000740d50b143d010100800455800d403168505d0b00b1000030310200903420401c80181800401021804080d4484400b461958000c011003000c229000c100911069100d1040881030b07000340c0c00c001100790024490719241801001102c1c00742c103026005107210f83c20310b1440803050782c0c0c0250440700f5640e54000000810700d148290740e004880380c1404c000e0303410301c545034600c0c2400c00b41090b8840d8010310700401c161980d85c0882d00b4045d6001c0d002c01e0181c0e840c0c41c0300e0030080c0590700c00c130302c444008003018949802400001304000900c046035609010a0301091104074881211b41801001e0380500500101c0d00800241c01200e11035141841d040c040782a0b920b041c0780059030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 27646741 1250 27645491 27645493
    0x90a03020a08210313020607020f0406060e011d01020303061207030602070609210f030c0309050a14061b0d0908070f14100b0a0509090f070e0f09191106120405 70
    0x183d00b010b1020b40041009458503254401d081d810b0100c4048201d02141350020b10840000a40d40110b4460402e4400a107900070020040c099031414041c00034050020940d0000718009185180c1103040034003074070b288c8010b0f8015400c5a89085c00d12904a82d44550001a413003081b00c00400111140014075625101e10780c0030a54900a240c042110700348a869001d50103441d2030a4002194865119866900c03640307804542c1c0b45082c07005500a044060002c0d003e80030307030041c0710300b07000d07941c0b4440d038016805c90222500d0399521816085070b03a26148150514042c10042c400700404950403258001c0e029170441450440c4070340e01e644004004400450741c1c1c6108404802a0810905c1904414928004184800400340b4000755403416940903e0344202d800d2800b04603081300400080d40410b007a0000c480c40a522020f440201b00e90450361400007440e9040060060342d0003140101d100102191034003440902565182d6400d86881100c07034010a050024101a40078005514052800b0b48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 27647991 1250 27646741 27646753
    0x315010f020105090a080d060f14010e09040f02010f031e0f0b0102011a0904210504050a150c032001020708040e0f100b03090a060e0c0306060108090c0402090a03020a08 74
    0x50005448003a0310000082035900d08002c20400c25400b00d958480d01d40c1c800381c0d0642e03681101411000400c1250001d013059074081f903001c20400020714040c400024262155294400350f0010405004801c85005010343d140080080065009101180c442c203801c1c02d011075204202d1458000035507400c45a00122a290004c8412680c898880c800e00071100307200a000304511018505010021901c92030300401c1d6010015080c08030004088240a1440504203514010458010455001401424480c502d00f15000a800800e618030302500845034840b403140d107501c2c0d1810b9135218803203120324020b03014403e448030190000f03100400d170042c4030307100c11911107044c80064104060700601001c1145104418850400c013420610380c00c40d0101100103540e5a24500d0090504042060041c2101d003091002d840313418001c00c852075a40c10940c200c4510790b0754078004465a50041d11041c0c0e05401000d880d200740d090980040c13045100162a00303c5850b940d601242001d01c040d803144100390010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 27649241 1250 27647991 27648031
    0x150403020d1d0604031b0b040303081b090907030c02010917120903040501020c100203120a050402040f110301050d08090a090204060f0f0e091302090c090102010e03030906010e04030c060203 83
    0x8500a6489030b450a012401c8080d24004110540f0440c0406440300340c8007107203008040107040d03260300901440c030b002031344035030362454050030b895001d49540c181c03100d086034091622004041aa003510000900c005d100381c40d00300041e40240044000081155250100381011455034901c4410000120320086e54a81e02000e4951604101500704036240d001048108640d0303a0009410071190003ca90340c11980410b80002e82c654492248900c04400d58581008464105a400184514020f58081c000d2200c01c005c0e02d821900e0301c0503481003140061005010030b0030301c40b502e65002d500c24401b00d4a8a610700000440921559006941c0e10341c00180502c005588184544030403034582c11f000419181d0000007600c511000030140e40130742102c500040e02c2c508006404407550790003a02c2c00c211410070000000560384109405c43c095130800a4803428410000101c900c1480079101038001a404c00301c0e441441c1101810640070014103d02d1000464010b10065000710701d40c5034150310560303038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 27650491 1250 27649241 27649247
    0x9030d0608060901060608090a140f06070512060105090a030611040e040b01150c0c0308030a021603030b0f0a03050a12050c0303010608010f150203030703051008030a1206090b030d0c0203150403020d 87
    0x1203401c000100000d441c08e0000e0b4010000f51400702c00d902048084007010400040c918019090340b03c00500e00c2440140000303190010002c012401c5a46003240340ba503240f10065603030344a80c2561070703005107207004104049045503012050114114035840d14181c0d4405444070410305c00d07641070780c0e1154907000410942905500c0c410001100382070140c050b00150b207d40c1c000e0109444003030110600000041c419800c0369040700e842240c01190840c240e00c050070010010300d290031f09140201d4090700821418034205138018112644000105040d514036910b103081c0504144030001440401c1c01b4210301c1400910241d4040c08180d51303900c074a9031604403502010001544541010f00429500071034565001c0112a440398141c100460701e5190300801c1480080f45610103400c078080446d0030b48146030b001c0014070500006103014410f40380c40725089012207180d0300c0d00952603800141080d0600f80036610941070240024256203554000007c0782603024022078007100103802440d606140c07190 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 27651741 1250 27650491 27650501
    0x301140102070308070b041703010b0705070611030a0c05012a0314100510020703060f060503070807050a05100e100f111c0c06020705010f0e1c090e09030d0608060901 73
    0x180910050000c1031a5440740f0440d44a0210b01405d4603038a00b00007014007240c0b40c1c1c0b0310400840c4d1514180e5969640340c15402d11b420041d400ca441c3c1c00740e0400050701500ca60011210b404440000e113180c906444410380300384202c403074101c03810f54a5640b020b18015a0800c05010407002c070740c02a14a840e44180241281d890311142d0100060035020301075418a5101a1010b54500791201a20484a50001d900d4810150b00040c00582032607403030317500b46145820003011504242d08545c0c044d40c551920700d8560195014260300421706150402c11450074442000251007641041c010305010b00022030301c0c1c00f14015103a40416101092210010b50142007601001e4100c2c001d00030110507020b40c40810600100e8a10410a40716006801d1002c19412108156486802040258082864a009000051411203050003101024101d03030704550b904d850705810550b101003900c0d040404854005901030001c6070301c0d04c02885004081c0c0030900c074040203804448001d10703091814024660940d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 27652991 1250 27651741 27651779
    0x1215070201021206060a0c021f020f0a0510020306130603082104020906010302030a150815060909060a0f020f180a08010b010219030203130605030f010902030609040f0602090d080301 80
    0x1a1040050011010b540701c20581c004e4400c079074072a0f640b00c11110840e0761004400010354071803c50080d168a1210380c2c8a240d40107000754096031514400c1744915501ca040c20355020300f041d00880f001c4011101d90307078011688464010112590f5004000f81c500441d66a90021561030000040700c400107428812034074200d1010041d290010b02d41640819140f1703002a01e55414180c021001c980020416000311340d030581110420440c0a94a007602a5104c41b0b481c0e000224001600c04545942419481140b144078410005c00494a45880e403c0041c619000406c06036542400320360744c4070000300e00400100000d05108604080003100b0414011000e034405581689044683c01a03660041040000d610541c6484130f192006410182d05610481d401c407003e100d501d54011440d1742e004000303503001e1b610141c90900103030380341c104d004203d11081e90103035170002c0c03c1e00005001076864112110490301c603803405410265030102080002c0d11041c0200e4124402000521804c010850000a13072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 27654241 1250 27652991 27652993
    0x3011d010b0904090c0b0708070b0a0225020f040608060718060c0303050c0d05040804061b03090312020f071203110706051e040b0307080a05070e01080a021812150702 73
    0x15403408081030098070a402005000301d403144084c1d070074460f6001c1c083c1d008100304a001640c2d400d0303c1c94150704583c4102021960b145508001c24084142031003a204a82580110b007001c1856000690381c4091401d00100e80c04001c000d49141c0c0303a03c9a00940c1d0061010900410281c1496400a015101108180003030b560f0008000c012080d4424000343c00c1c03036054180000c81d034541e100c024017503204d41c0c03062104071410841407204001c00076009200329440d60b940c05200034200240306002e042c241d1001740c000364101c1d405002240480e0400600352103140112500300410440860400049a01c11003018010b101e5610600d80c01030210111802094017400950b410300c0c0d400780044c02003110f0854110b0104041d05039051040e0201ca0203006004011516031609040040106c0400c030342c107410440c201004a0180d50050840d469041c40c16110f11800b50b440b16103c1d0001e401a40e0601c440d4000b40300100d001d9100c40d0420748000403503201034185080b46048401021001501c10011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 27655491 1250 27654241 27654299
    0x15050c1b010f0e0a050d05070305070609030804031103011b1d0102011b031503050303010305061506030708040b09010b0405160809030c03040b09010e031f0b0303090d0609021203030406020301 84
    0xc90380e80b0100100c0108250300b05449601c402c0030106541c0e04103508040e400c1000000e00d1014801c000502c0c00440c0d00c200300300e0b890552102c0f01115000c449110040020500784420300000e07540f400c401a9a40019000142c011010309603070300220450083c0802044043c80003511901d2100c2d8400801d80007030000344480c00c007052940800715404c000c0803003010f43d40e494034144c0e01600340d2800011034003e000c81e0b4680d612410030f940c86543c199515005000b054410040c68200714090381e100d050f09071508500340e52a91610228030100400070b0066540c2c605c804000c0340c1e1603200d418028105103170300c42036191003400068511312019010baa01d652080c490100d0b80900003040340d0540e075003040340588401e55840180c0b2503541c3c0141c5c4d83da01d030013444070665004120700000e12510800e054180f1440b00e030340b01030544074410320740455000a01070b4100c10200c0d4041c0c0062441a1026040c501444040e036103481c11504242d50440d2825000001000030030050054411901201081329030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 27656741 1250 27655491 27655543
    0x501050103140a09080405090702010209100f0f0e010327020f01080402090408071b08010218060406050d180209040503070b1006050316020106050a0f061106040f02120715050c 77
    0x902c00d403009102d03241054076102c0b08810440c988003940e00500000c0c1111000323003000740000e4083d4100d6400e041c042c1840840b082c003024031a840403102010652603002d1a146040c0c4111542880205940d051507154146000c0340000e99600d80880603140c500854072940510411a00014000c042070411103010188009170b40c07580800c41e04150f028600ca0754502c031038948900c0070030b41c9100184540c90319a6001850326419002000c40b200b00c0c0c0c07030f1100d80014050070011240140d000b14000100c051244022501040d0310103100c9a0520212080b10030040c2d0010364150412901110160008207448041010050171140c208004c5000d05d45800e090035002049400028001d02440480b000c0300148607000798480c034050200604010b0000d41c40390407241c64410244220b10024035840c0c0c00d55846000843c4050180303922200f801d60381c1189808000801c0c2c19000b903941c040c09806800190005014001010b41c102030310b50688601040c04190b00340026010003115118000507650 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 27657991 1250 27656741 27656771
    0x30c01050c1213050c040c03050702150f010b070302030903100c1701060c170904090b01080f030315121009110f0301020702030a02010807140310170d020709050406020f1803010501050103 82
    0x2d64400e042c02c4283d050040a81000c501e0603610401c00350700701c0c1c90326070398204081e81600b04920401254084810f2006004800a10040c045030866004010100107000c46d079503c034001d2130081c0c0207204980c03c0c00c65040c002820810040c03a174410340c0e5a1618a414082c1e0005030340c03080d201c0003007640c100079032500740050034040040c80005c003d4a590030b440402420140243e6046040c09842000055407d01e88045c41d0f4400707004428540c03007903214076401d44d9400001c4038031402d0004850401c80080c14248503180e0481c3c2d190b071030a0b0041804503000c182c8144030300302c11729014002402a001100703051150400303910384101d001340d0040080c000580c400050018900c3e5080c80c0208044d80c0704030381202d00501c0443c00c400702140010034403414442601c119000e407500040c08000021005180a03560203a0210340c0d40540c0200c034040110b40401d80c40a50f0090090101618020440c002048180c0c040041c409966140c10420101400c09208483c0948000c2c2030401c403001f9505851 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 27659241 1250 27657991 27658027
    0xf15080307050706050a0c1208090c030109020307031104020408030a031a010503090a0201080912070f0c060801120f0318060c06060603020a0903020609030715050c010507090b0d0507020708030c030c01050c 90
    0x10b8040c080001b0300c80f80708900c15003a0140701034000b00d807501e03c8000c610004009d408103980304101e074441c91f48914400e01c1c040c4117107912164000c000b081040e00d1070341c4083c0c0002603880b40990041c0e0034080050b190005000810708280e01c0d80d400070b0b40e2001030103480360701c101c031002150411600344100034900c4c100140c405166030302400c045006a0396200240e01c0c100000054903000700300810210100045812042411841f4034220309005440b1002203034038480c24070407600314824180118010505802109410754040e20386540e1039034000031156030890040c1d1003500002d0300300300d420042c000c1c18403074500540810702c2c3c1075240000a038002001071080b40000b80c441d96000910b80c95696081248400900314504100e1788416031100141140e04900240700d801d50810300051040ca20034200401910768122101d800e02401c580d040000301801403104055114155000c1035003c4104081e0949033305ca080115500c10188440500307540c0d02520301e4003007a0742802070806850040c005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 27660491 1250 27659241 27659249
    0xc080703080d18060c0512160203090d08070c1d090106060527090403030203040b0705040302031005070c020d080d0e16090e150906010e01060804020102100b0f040f150803070507 78
    0x804254800c1107034040b440c207110320200412151030445c802c0002da8000b0701600d83d80f0201c010350f0341349070344981644902d0341c0d20410840060b041003002541d0782c900892004035072805001c1050515005d5554103101d00b142c0d41103000a0130b0842810300c0c681c04500c0880c1d41c8800302500034819030307141003405032950090030680401100e1505410307504e524444401600d5050050a10103182000c0c1000b070025403055074152001805da0000030a014010f10031501225405802070a8102c13a140c008002400003400200c1048080805e840c05a03880661100d000c5000341d001c0c6503160903021000c022141d5110501909810180d43d81c15400042c1c5581002c441c0307510740c0484c1050084961906250314401d8030000366202d00144140c00400080c0e090690301340c0d6000d44d241c6d90302e0b520265100401118001d0040e8805020124011a0390700251003900d0040c1100120b501c100d4001026180da00c15040041562494403481c079902d070300104401802c1c0c100c06540340440c00d440703107625103a032401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 27661741 1250 27660491 27660517
    0xd020f010201020d1103010302041409060703050402060c0102031e060d020108040f05010b060a0905040b01080f04021e030d020109050d0e0a0b03100909150c110c01030e010213120c08070308 83
    0x48449164001c1d0115040b01130300030410025041001c11440340740d0000e000c1640a02d140882c4450400070005103540034003801c2c0018807842d600c2e81411000303040010802c80c2c0100c002e01410388008001d0000c0c1d4012002d080020041a030591505251090300a044a10907507403000303a200540d030040381c0d468000340c0050640705401124101030f805070007035103a05500002c0001d1208040c940c0902c0c002c0c184d40003142c040c081284454011200c0b11400c2c1c07048440c0c0308009010500501d0b201d0421110821203500c00c3e11a24080d6001a042007070441c1c010026075121780200b0704000040c810350385a140d40741404240000400046003031007401d4080d1389224100000892980300794114140e000b0000d010080c401c080c45454441000940100104d032500c0c14408000700f05030260002e03000b02904000104000000d4500440c042c0c491024800f02555003003210005d00c40540c103044018002407115a80071034164a480450b44203280e001e15100d412900f42400064030490807102442d507400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 27662991 1250 27661741 27661759
    0x3020f0702120601171b0418150608060906010b090108041a16020f06010b180409020409050705011e0206070309031106040c0f08010213210609080301050f0d020d02 72
    0x82001000303200e2420042d501c20030701440c011100304000790309030507036980c04000107044100c2e429442d5107070800e4051102540031290408a981465804a064002070400c00ca405001c15118000c050a82d0403585403107580320f50084c17003000300070451140c121821000804607589400722129040c0510140ca034104205400800c050002d0305845080d5064034904506440c107040c0281a1841d07001d2041d20094003980c0c446100205000c04c403941203c1700f07000300074903003c00c2c0b000c0c1403000580012101d5201e80d59103941009a2910f21440d4136480c8504010407030340382081e0026040075408189032040f440403194485030568003140a030b40040040c100400d02c41812f1500782d0f82000004442c0c00d0ba441020204403e00540710313485012102c0b101512034950342c58584c15402d03071143c00c0d80110070840c0c0e90b00811035203a007001c20981030841044100410b650a41e9407100f500c192030300a0781e044401100500040c6400d41c100e01c0c40880403200118200b0499000c151600d0303452501034402d250318 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 27664241 1250 27662991 27663007
    0x1208090a0503040b070201090608040b010510050c0609030702090c040b0706020304060914060a0608070e1503011d06060315060d0b04030e060a0201060305070501020a0308010b070f08040303050306040b0a060c030302 94
    0x8001103041107a0000669407165143c0341c02507142d400440c020b90010341d1901d0006070312802006424000d6070810000c40c1c9a030700b000180040c0c0b044070b41119080100c10002c0414405081c002a40030341c140c40d02840c1c0c1c90034203004029020ba006003072a4488001040300b000000420f03002c0f038002c03076440503015840f90b4440c14040002d024150700a05050301080140081c0c050206842c0c2c030880d04810100001a107812440f5512541d40c003d50b880b81401c030010545608180500c000340340c00042c00813130042d040745090140c3c0c1801e035000b00c01d00d40c04007042c45802c1ca400d00005500380c0d0406011140b500d401c0c0001540c0341e0212401a01c0c0580304004201454400c0342451000000902205e40e520b101540c000c0c000c1c1480d2005651a00401e01e01140302d6102050b445c0c01907070542c2e1003612a0f4200048010203174006003007280c0402491034004001504840504000c0d80241c4a01d520323894000140020741d503a040c00700c1e108000800060040035007080d0f00c0c0b80115094030300184c4031110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 27665491 1250 27664241 27664243
    0x60603010303180e18060c030601050f2d04060f0507020a0306020a0309140a03030f050402090610090306060e09060601030c0f0c020f090a1e2c0a0b0106020313050a03120809 76
    0x2c9411281c91010843c0400c442c6030359224009031700c6507080040300d4042d610714003050b805d0302013551498000340041040c42d600c003890b4405004140c0e40c8580401c07040a442550400b1007010184001c142c40001c00d040115036084608600381861604109141044550003e0410801e50100a040590114101e101c9a00c80d0340b014042651007400100c03020450b6040541c0c1e00d241100460001c0d080a030480a21482402480c2c052a030103840003500e900c5007400c0168916010145208000a48000102064042c0203450062a01401c1950503003002c02c000c504080d00244414145030400313070006401da500a42d030703840c21013251030000c1e820080c0c2e200048050304000c2e500740e40b12001e5001d00c040c50100d0750007070a44000215120003021402d400000503146852a000c403900300404041d5001c1000b8802d00000850300c00076100c05518940d241100c0c44000e802980060380003048401c001115000814044d02c0115401c2405038510f950307900e084081c01074030404100c410000304440e080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 27666741 1250 27665491 27665537
    0x110a260d05190b0303090f06030403021219030605060a0206281b0201060617010302040b040f02280302040b04050409060608030d0c03050a050603060a0c020c032b020105060603010303 80
    0x560003030910050030700d41c0701c480000790400050500c03140b030007000764094940041110500304000d07002401c0e0401c0d400800502e80c02c024003d81c154040d9404100030107007498001c00e1014000700390000b00107000300c0003c08580070384c0c1205012b01410881100e149030000307800c542c03008108000c40000b03240303550401000000d18151000a90601d01985c20040444401607008542035008201043e41c0d1407044505c07040c03041241000d00000d40040c0b01504180d000000c0d4810080c001180107445250b061040f6400b4a414000702015914259640103003040304180385107092a0542c1428204103d141e880d00c204d2007007609c15a9540c01c8074042040c590000f40003442d5000503282c440c0c00204c1094003030100c9540c8800005e00d0480021040140344c4240d5020722005030003003285648440d07401c1c0050082183c11000d5100b003074140030b42507604110070b0341c24103600c0900c0d05100ba401164800d00e0340880d10b00500b96414001040035036122802684c0c110fa41629100202105101d80c01400324 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 27667991 1250 27666741 27666757
    0x421020f06070803150f060403030f02070314010504050f060618040203070f060207080606040911010507030c021e090903070512030403110105072001060b1e0c1b01110a26 75
    0x3160580512503d6009144104034094152102a05007002c2200d079020f24200b0aa02541c18801030010a00c90282e44203440c4c0180120340741c0d00d03281d8071040500c120042c006012a07440308100800c01009000030040d00c0180c100410050034400005040f9804a400c035100c800c09447c000303015943d0400000004101c1d001e08140000d86a4100a48409180c000c0d000c1c644500c5000c203120382000e11a00010607045860650100c40e08001104c0c00e903c05502941000080700c3c81c000542c0d580141c000ca818002c16681c0020850384e414880f60440c014402c080030341092100c0c0d0040740340400c0c05a03180381300b4104a550b0750369503d4262500c0c0481d4044144941ca0a010403e600360802006003803070180181c2c4011600c411b4200c642030b185540603400401409000344141c48490700014503a1036403e141d51030904e250104450300c1c00ca14070b0542010440d401c60303005002c3d40c1090150300002c1c000000307010340c084143c446504103ca0000d4807a18030342140000348910160600355042e0b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 27669241 1250 27667991 27667999
    0x619020a031d0105100803161101180603050118050c0a0c030210050a0b010e030d0e01050306030f060901090204060b07031e0c0204150501020f010606023406030f110421020f 76
    0x218000e009803500070403040300c4c9000c00c45c2494101141c0100c0010a550703020501f00b1418040404694440c00d490b03106c00540c81c1444881007141c3c000030f4210003040d001c0c180a50b07000a01d5803420400380249000003070400c031410715020600442d0801d000403035070380100d28106240c0f42075003403804a180c0245064045a6649090280f1982d05181e0b0414085113109070f80e4000c100c1c051104154070703240740358541c00228241d45500c1d44075500400255500a8009081c1d030140c00d80003501300d0a0020494080c40c50b43d550320403a1f400c5107001d120301000781030b1510000d81004400d980c050700c03107040440394011150a0b0300c0152049403055120051103940600240b111008418000ca1480040d000f032901500610b01e0746540f603803052144404441940c0e0040030316800c2d03182401040180d40861154080207141040070381e10346540800c0048c040390b5000142800206406411601100540038001008020030001c1e0400118216455a910b0a80700c000f20a580700040ba00b0310000551900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 27670491 1250 27669241 27669281
    0x604050901080303060a050402280912030203030a051305031210031703070e010305220c030501020c0f0709090b0708090c100509030c03010504051c020c030307060e0f0619020a03 78
    0x750b0040030001d10301a00301550401d50103a214000c1105902603514200b9620b10090361b03004800780c250703500c88801921800d003101c00c00d40b203400060407040241c60640150703000005001a0704d03210f01c90254400d91a66604216030500d580d116268800c3c1103030070401c9401e500c04603c46d0100340726440d00a551100b40c8030704c0e1b600d8000400c0604c2d00100c2d00440483c0d107000548901c0e500034052144515801040811131860a0b6401040560404019034941602102c0800040c1c000d1000b0014a174258000300060310f009882d0794540482a00240342071401c1100600008003244140e5803c40d401d414014080d5681c0d04410f460080c60500060703220702512208800f181c0c210000300a50081a801e49121268910926003624410f4400800c650311049181c0d40c0c00e000e00716045504890b0344149c81c14500c41d000040e1558002c5ca800f0b42d5410340d0b440740d07030b07008500420211b810014400013400c410716001070280048916103151520039a000a001059144070b0f80c85092108104009004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 27671741 1250 27670491 27670499
    0x70608090325020103050604060b03010501030216020603070804141b01030b0301090b01030605060a1d0c07080c06010b1309050601123b01050c0c0a030c0c05090f0405061b0403020f0604050901 84
    0x820340e000c48410384c08249000c000c00c1d0141080e00030725050b1103030302071402e117143d10b8840110000e41c000035003a50441080f031001001070341d50000a50081003266210b041078181400e001550000c2c140790b0041660180010a503074520055290700000c0c82400c00049080140c1d02082c0913000740c0e07c00074100e00699001000300100c0740e000c20300a00080d581500303019191680030b400d1000700044aa815100300001840d06000d5400409000e03100d103000f1400d15107e010b04616154007a002007401200c04034a8402d42164031501c0c10050100301e070140000e051442c00688080c0ca0b18440201441c0c90b00359406c03401e4a400369401c2c3c1030b0f9049015116200e101c8c454840441da11804072403081d401c05010601c40d01045054803031440c2d006010b000544940c1d034050703501c5161180101d0300c1c0d0051810000b000c0d65030f11040780c499002ca0046a40300d01d4280752050030a800144403004950b1201c42e181e60700300f05d40703095405486e1305823030041c07041c0d07001d0000981e64011640855480800800045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 27672991 1250 27671741 27671797
    0x9040c06141204031107150c0b0a0e030c0c0301290f010915120c05030c04090906060b0301030609140619110c01022a0d0c0b1305030a020c0906120706080903 69
    0x41188a17100c0b0580d50107503101c120b0a61981d103c00024800210701e0300d154004100002c14207a0440c04400e170020354491201c40326411500665000b0405401050600070701c3c0c1005e004205851004a10000000c52803220b0850303440c0484075614003d8841d210032042590044000c007024010000c0307a05a04440c2d40c00045c00144440081410542070000703c22215010b80262405000819030503400d281c20000140000c00d040780050f5111510782c8000520315405000840c080e42c01040049034040d03d500300380e50000b0155810208950200c001c210b00a0849480d100042c07400c1200800d07036202014825002d4001c1c185482c14551000580c00300140c04400414010f1001100651034407090a1090b0b0f12810403e802d40c010492544002002030550790a241d84403000d0f140c9014000d401d0740360a4550740152403503e026034401c82580e031051030040d0060b503102c20111111444190800161a102c5400e07201e640b060198010100f60b0580060082c3c42d500480138020110742c140710b040300e03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 27674241 1250 27672991 27673007
    0x6140306061218061609050907081b041a09010e030d09170708011401051003050105010c030507022d1806030a08130e090d0306140d0212070504050c07020108010509040c0614120403 79
    0x38002007040c1b120006100c0c00d0220b6040e00c100c061f600c501005d0781d10b9020b40c1e810b4040c030324841d95115004010101d405a80c1c212036141d0601d14405050321802c540001408800303408940398441d5200070700a0000030380c012460300546003002d1000c1c280c891074016051070f00305503401c080155420540c5480a00f40c003d80d486048890865075207400109041095044810a0040b240001c015280c8039000ca401078004281c042d10141421403490090401518400014030407002e9440c0c4810050415241c484c102c032103031000505201c9502d00300640003e68611801c200107116500200351803c000c0940b4800c11b00811031840d0140152405400c00e07512035003004001004245482404224441e940c02e1000101c08058401c0d1a00500d40d0200714101032625882090b5204002c0040f50741e07103940c001c550154202500300742d1116000d20004d480d001058012501950542003000041280100e111048490f142002001103111010541c1544140e01c0c90b4400f4284103824481055032007000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 27675491 1250 27674241 27674281
    0xf06090e0c030123040f030c0b0f01080c03070b030402091308030103030503060a060c03050d110d0c020109050d03050601050706020a02010216030203120c04060f030b0d05070f0614030606121806 85
    0xc206000d01000780d42c1405284038400403104c0159030016000580c00020405618064209000c2c44134940d46c6410300d445c1c00700c8a21804014010040044410402040e00040000c6020300200c508003a04140640070040000e8231403002640030441c4404120095103032a40c0055229070b40c0c0d80c4a04010784260302c1600c1c1540101c11031540020704c43d1281c1d00c0c00040c903505075640d615200f0f6544207900900712410248005040c00c2210141c2c164051080a850800e03c1d000428402d109007441030801c0e00d02a813903c249410201006a41d0b0380c02000c5501160340320100507180c107050003003280240150105600d4460403112079030285a000409010550942c1c1c00c02e003c65581c5921102580c0a18420000031610203540c06180078007036000403801d1007015100881032200ea0321818a00720540e4007003106c41007030380e400340040742d4411a52701e0034410803010b03e49107052520100300c0d544506031840b96211388030380218922200b10a030710905800d1610444030581010f0601180e81403485039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 27676741 1250 27675491 27675493
    0x60708011e09020c010b0a18051005090c160b0a05060906040c08130f080a05041e050609040b0301150306060f1409060909031903050a0501080c0a05040f06090e0c03 72
    0x4000903140e26200c0c41d50780e4550680754900703440e078035040000010350030a4009242a54079621080f2154440d00384520090880c1241943c0f2030f40303001c020008686014025143d507004003c002c1c04130391203001810b600100d140f208259215400d01c2e08010014520314010000c00004e41441a03000c1582c1043d8060201142c0c442901d40b40d8900b0401210032001da9007002c2058880011012883d1910260a0a0013180c6c05160501542d51324115a1b1001c840790b004684003003014020384201c2c003109a2550032040c003443c0c8aa00300400030301d060003940d5a10707200d507031190040f03521924203400c06100c0508007a8400b81e01500ca00d440c5001c6c00d01e0f80078450806a0410000481c901e10400f0030302e2801014014401c1511307498103202c2900c03402005090fa0b132001f00704030749003c0401c000c0c001500b0002ea4000031242003001e40c10b4144d07901039021400d290b1264001d8042a41e5184070076085400c112000039402e40c01c246100c2c0900341da50310015113103141080710365400c2c0010485d000c4c0c0c01001c1f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 27677991 1250 27676741 27676757
    0x70e07050405130b0306040809040b03070801020307030b01020a0f06050417030a06030201020c010302070201140703090302060a0801090b0f03030a0e04061d01260a030c06020702091608010e0108150402060903010207050607 97
    0x10b400c0604032030802144d10f505034020070125001c1034a8a00400c00c904020344045140800310010914000341c0ea030051341507a60000400400550510603000350680034805050011055101c1c0500004008406007a6537910400b10701001402c896141d4410140c9000c140c6034a17108441e01d00612035032006901501039804402d0041d0710070300c2180c4810340c1c16100c140b5101e541c200103151940105004800b84021124080090395400c0701500c02c0101542e6030400541c1403100041c02c1d135480d1850710380a10b103e0342750800c05903004416a034681c03100d1700c1c00b6102402400005000761513280e105e8500d40c050306100502810041c1038990590b0052009190101003515844082440700c50307a005454000352080b400281c450242c00d00410301940c3c016051102680014a040780f051390810b850102061081c8001c0b6003002040e80180101c1411044962400381c04648580060340c120741c1c079060060000b070440d81c0c0d03d0183c401c140b101900842d1113000ba4a011543c520040d40c1c9500424184 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 27679241 1250 27677991 27678019
    0x80c0609060c041202030f03070f0606050102070614030709150207090e0d090608040c1d070305090c010203190903060207030203040f140d060f091a1e04051e070e07050405 75
    0x92403805900c01d420102d160525082440d00358003500131040746c1c140120424080102c0042001c3d1a01300e004445001502460703151840c11034106a0005055410042041190315000707581c80d200d010300a00041e669503194003080b558182035812040c1d019000707039100401c00303500144400654580407410010025500b000968074210700180790009001d0900c2070101510841d102e07504144101e024081103501c1e01080d4100569550009510042c1e460411008650600402e600012090003801c1d803490400700003500d074414009041505000101130b03041c200e201c0c170703c65401940c0281c070071512a0800e01d8002c2d261f80c032900c2040c0e002d21550502046883e4060044039103680001d00c610b00000301691502d0240002e051484505543c460303480002c52542c07098401044802925038681340f0f07107241c202c42d480d00301800d001c0c2810304d2101004009100008c0351529101010300e0288903a11040c1003518000860f0056940201100180301c011500a400303842a0384040f44d030354005200c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 27680491 1250 27679241 27679243
    0xc110f010b0a050d230d09050402030613050903040317040905070f0203120a180f0606090b0a1809080403060603030f030203150d02060d0212040b090a05060403031a040504080c0609 79
    0x58403510aa00c141850000c005a21300005004070a0703101d54224051070320360f01c022405c45070140c040410b05070455501c1c080f0240d4020700c5800a080125021030640c10a0004220341500c81070b08a501f090307031030300030407020b003001c0043d103000b1607119801c8804240c084c2e03130860881d00144200c4403240d003004046081306000d003803000d1121440383d000358108010350010205103c00034245e009020340e20b400f100c0791a1910f50046000c54040c8451b114452050315041041350003e0f4172070180c2c02d2905210340640d0350f480d00c106049981070101c15540d200250311420041210000003841d40c0030000b4004200182c942000c42103038040e0b2188500c407509140b0550991100b10f0b4004101c0204001412542c50050181c10350140003400301c0381070016064a2104991240343c2454101c80d00c2010081009818818558012965030241c80168019034500342e42d100050320040c1816201d50f101c40341c0042c40f4942402810300188188040d0902d410f00900940c0120000d1300d1601404001030b0507500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 27681741 1250 27680491 27680501
    0x180608040302060703050703320f091b15031e060603150d0c080f030d0e0a12140d050c0a030c090302090c0901030905070906060f0e0102060106120f0c110f01 69
    0x505600a841251340f8940c0071001048000c0501d4241980d58407a028107603140680664100d0034018000903000314803840846d0140f00134805070405c550702c42000302c080070104140041910354201d900101945500081e4801040c52080ca4008004800c2243d021140c901c8000c070504100404003064075510180195844215403000c603445070820305c480303a400c080c0e04203c495030290992601040e25003540c00d00b0040702c0504a42240d0001c5103a52a640b107502c10300c00c1c4000b2840080c0103501c00e55441c130f090100c2c0c0b44a00418007a00300c02c500d5003031014504407800440c50703610401c55890841041c5810b0b40100302c9010002c0d103880741d58188940220500802d0360b03001040d0149079a1b0f014558011503220300d010504041c3c44030000320004030200510406400302c100c000c658942040030052400c00070101c10703400c202e04000b000d00b271039030041940c80c1510914a44010207110150301da40c00740075090030f0410001c0c500b650001902e0390000c103400c0c0010319a0103a030860a4942307406400c0c0c80b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 27682991 1250 27681741 27681743
    0x30c06050403020a03080307030b030a05010515030304030c0303030c020703050f03071101110a0803060102030904090c03110306070813060b1008010f0f0501080604020901090e01151707080412030204050a0618060804 94
    0xc0c40180051010855410140d07030b0141c0c8ca40b40c0454140940d802081c2003481c4140101d4041c3e4451044c450b020414452006000500f5001503003440e1171520f5083d0310301c007a84006000c0c03595900450500303900c00d220403400380d40c00c04200e61898400d2141c09540e588001c409446041c0d5407041c4014a42c8180c22810002c81c510008140e0f102464481c941e0715031014020f82d05500c003c12162000740c582c2c0c000c01c1c1109014001c400074151a50401c08100c91182c2c081c4c1d403085c1c0200301042141c40d0401111074200114400132549400c5520f0301d01d00170500c2d1240c0755405480680038241c415480f042c018140d81007814404101c50303994411301c503030074114000d140c0071910581c00220302c0e04041c6c6c00303040310010501d822807225543d82c0c1880034980e402c0c5c105030884800c0640040c41c01b600700da5007188030b410241a880c010301d40500c2c002d10841000e4001050042c104101c2c001d80c034800e8041c8c40181500520f03950016546900180401c0741c01c1c1640c2c8904040c3ca50002542c0340101402c622403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 27684241 1250 27682991 27682999
    0x60e10020a060e0102220f05040c050d110f0c03130605040b0904050a02040f03081e042105070e0a06030302010614150c01020d091202161a070503040b0a0207030c0605040302 76
    0x301880c2d8540d00034000082002070b0719982802046011000c0020b0781c1240c48100041c0801e071424090310303025050b02e40d0030290045092681c0c0c1c1d1035199200703046440441c41050001000490380c1c1d45902180f06030404168100000301c0c3e44040828080000c1040d51400f070a046c0906a4a080c02e590600880c440c0c210b1900b81800703402c21508042d041240e05c207824100044c44c041c0c5074507200d05030220355003013500c07944d01c0860301c1ca80c28202c1c0a910b2018805249410b41040e2a1009107043c2d081d12125600011801030b22500412504200040107080001c0b0852401e103442c0c1e40e200f004220901c010340040d07090500000700f0340f80c0c42040604400000e011402075140e81700c4800d0040e84100c2c10301155650030000c0e0075075404540b0a5210031072003800d0118840e4525a002407a000900c43c480b02c0c00700c0406000c001030b00c40b008014988080603d9180c0d119155824541e0031800703250320035800c0700c200148003080140c2c045900d0061303c1c450100705540715142c0c02c00311981e0180740002900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 27685491 1250 27684241 27684253
    0x207030c090c020304080a11090c03060f0d1b03050c1302070b060105090d15020306010801080c030a06150906030b010609060203130b13120b060411090906060304030c0503040305030301060e1002 85
    0x8012240d0009a0050342c20b00450f4506a55580c81c40e11306000d0000a4070740c00102d82c01d00485240ca0441213401086200c5060306506181d07001a07146404078041c14803841503140c0c2d040070880440840d8400d07041e03114042071020f6803800c04644554062003098802d10354021150307501e610758070980e07183e19040601c030130041c1e8904005440b40c0d030000d0400baa10080d250300780c800060042900e031400e200100c4016031282070a00024001180603000525a9088034000c0d0000d40c80003c0c1d0414a1500150040780740020046c861502d203d85030403445005041002c08028020851143c9041f51000d9845040003540c07144200c1c2c403802005920750007001034400c100007d00b14007000d000d800c041e83c030f0a00c02c110750343c111300405407084a104036590001c81040190b9803809118048503921038a180910b40b0304000c0c0050707465007008140c984103e002001140906215000e2450304e66840011070707540b031341c0b2402c14565a820074031892001840c0404102403a04106080c841c0c188503980007007007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 27686741 1250 27685491 27685499
    0x904060c030506040c090e070915050c010b0105040302030d0f110706021b060310030b090106180c0207051906050c15180d09050d021e19090e190b0703060b03040b070e010207030c 78
    0x3041f880141c04ea004104d003000000c10394102c8070418003a904500e84640d5600d00042d50702c10b081d10020342100d818003c0511081001d40c50102e190300d0b18034654600b140d51040404400d0b20011320005522290f40700e00440458072035000141c201e008072425005100090394582004141e00c41207802c418520380410040002034005842d070b030b42100c045000860465225001c120060541c007810a071341035242c081000c0425018880d26001d03043c141d92a02c5201d501300c0781802c060300144682030800c400081c4010104005010080c0c0c0f0712400088105035081c9011381c4002e006240180e442107014040e810b8030f2050040e0319090480e0809000036400c00036a400b0040d600711000c07103400e20181d25160f903075010760f038001c0c0d03a41c0800a11080c0402c0f490500c0500c508540012280c14a2503201c1c2e56849e1035440e0b402e0900c6c0000d80d01000b64245683d8900048019007030592112802540200902c004c00200c0030b01c8034414141079413415850454440120796070724881c88064500b410400d001c0c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 27687991 1250 27686741 27686759
    0x309010c110603042001110706050d060f06030501170f0604021e040e0303010f1d04020d03051201330c03080604060819111e010305070c020904060c030506040c09 71
    0x840040d01640c00714441e00e0041021403050350085a0445074041d000500d801003040601c1c01c0d214070300c028a000d280782911a40c1c42031340c81d2800d00501c000e105001c0780300113201c4010340203d8041c143c0c1d4070028a020340d5404015012f04002e0240424001340d80c20f08001803480060204002880ea000809094480b0f801340420a02544281c20850010743c1034801607407030b103009419071160041d00456880d85010b0410305202203030f4020000c694030346880c1c03558120042700280e8215404a0300942c00703683e24542910b84d0301c91a012201c200e0030240001542d0f612280d00d1041040c9042d51000c10001644a42140c440300c46900340302040082600401081c403030481d81d540100054400074000d5110f04c4080d03e0094403000000542c452410f11500b0000440c000440800041d20080b129489071032402030302c25000303003005041542d00c00000303400e5841001440350283e00605420100d06150601001401400100e480481c1c10400403a03641d04140c410649111000d51700c41c02001d017040101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 27689241 1250 27687991 27688007
    0xb0d020d0b0a240504020a120c0c03120b01020714060c07090516030e0a06050c0c0a05060a150503030f0d0605090c090301050f0601050904050604020702120f0c0303210901150b0705120c030901 84
    0xd5080040e0310000018048c40c904c14056106819240c400c0c001145e032034014074051000c0c0b1b0384080b01e41420b00c880c21503600002c01005580035199000c2058020b04007149043c05006035800300d41c071600c2c400082c3c29209900140c002c006003c414045a080c40c002903065548440d2022016404005118081110b1340d01c59900b04100f00c00740381c0b5008082d81300510340154580706803960380004041c01051102880707940c1c11000059280c1031601e20b0000000d8407401001460011107000050840c00a44c42e507120b00080d001c028440e0055081c1444507001c00d4000e4007156000798078240204141d0b0b0340c0410560310400c0141d45041c6040102e4003400094480a40210b070050703000d200180044e603c50780203503d0a020000102040b4103071120840c0b41c4401b55071614041d4008121401d00a1840900740b46607203040e1040841c2c03038440400da14014406101000b000b003d01c1c4601080840c6018000c0c0300440c0160304032501c2918802109049100d5145180c0d11030740108200d150b254042c0c501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 27690491 1250 27689241 27689257
    0xf05160204150b1b0c060a11070509040f0201020d090510030b0102030c060f0f010e15040203060f030a150605010216150909050f041205070b04060b0d020d0b0a24050402 74
    0x800c0d0301442c20b14000c80410079810540252102052a90740d00d1211500e03041440000001010701040c00030104030281709026081c1c040040c150340d402402482082240d00401c8094150782d820310741410284440e0074207a80403070042c012a40c88001c02849000751a060380c500900000d10320710043c0e0b0039001050042e2070070303040d40024040c00002c0042485544d1080ea100107620340315251009841c20303041c005800c0f03a15000110800d000200c43c1d0840201c2e07082400307880c0141c0e283c94900c0011070321440718940303542c5886500f929008119031040d1403851306240003c28004241c40703000581c3c543e0380520b020f02401c1c4220008000001d407038810310b0070212090800c254111b4a511503c0300351001190384005034800c3c41c0a0200b041145862040700141510304203062028641d215016460701510290400b41c4408404505a0742c4007150f50a01e81d0003012406d5050551605410400301102c02c410101e01d402c4800c0200c500fa80e0000b041e82403007000e140241c1e410701d02008002d400040c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 27691741 1250 27690491 27690499
    0xf010806030616200708010b01141204060204170c040c0c030e04020703050f0415080604060623040510020a0b01080313090507020a0f15050a0b0604030605040f051c0f0f051602 77
    0x419401020213a00ca20701c0301221000c00b510b21503080500813404d4a0707072a8805030412820407189076141400c107050b1610741c02c03510303060302142d01c036418214040d001da40c0000507040c1c2520040c1c40d09040000b000c1508075020ba80c00e0055400c480b5041d61000c169200c090040342d185401f8540c1c80c41d09031300500d440c40c46400c105080c6000c040180b0324036005500041c42c14404424445449604481d0190740280c048500b401102e05004008110402d9220010020181c3c03602c082e41100110051328003406000d0011090036000c0c4800135a0707000c2400303007036030349000700c20001c0b5410202204880d0850210901d600880b8500b01c0500c0080000030070744000c501601d01c414001840081508030b816024548065082a8848054048810141c800c00300c56280c200c00f2801b607115441030343e08481d0008000030b811b07500c9007040000e002581030003e1003400380d22480c852113581100540300c0e45400340d80b4000084401e05007624140b0080641750080340b4107000e040c00c0003280809003c0080e1000d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 27692991 1250 27691741 27691757
    0x203060d0b0702070602010e0c06040620120715090305160f020a03060207050105060906150c0c0406030b0702070803031509090a0203100c110102070b0103020409170403060501050f010806030616 85
    0x244901070154001d072035240050300041c1c030810520358240240c803442100c09002e8181000070302d00040b0345101c0d51081c401448040810402403405542c03c0e4100380441c0801d032040b01e0a00c26401070594010780c03088982c5503202c0512804150248103100d50503030300d5210246810342c50000103000c003031540310449402058246440050300c40020303050045208050143c0c65441c24a400c90940d40c0081030700d4003611060040050759910010f5a40c240009a001681c2e540110480070f801c0c101c042d07455a40050920000000b001034400c00144141c18507420703254010b4550340003a80b0383c441034540440f01a5844000d0000789800c0360501c0c4c0001c008012a005131890b940460305064050402030401c83d560003405043c0c0d608a080d403086d07082c0450003185840d10030380d50607000c01410302020703005580d41d0340d5102c00c01c0b002801040d499441c507a1600d07103a0b69a440d00c000601024041c59010702414840e251095000e0110a03000c1e65000f009402160780b11a90116018400c0320b040c03080040720 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 27694241 1250 27692991 27692993
    0x12030804050f030c060f010603050702071a0d1a03010b0109030c0302060d0b030a110108090c0109030b0901090804030f0203120304120e031204141512070309020310061214060606040501030203060d 86
    0x400c020004c2c110744c000600600c0c43c220b551340b0020744c016405841414100300420104603400320784441034410142a41d0405008030003001c10500a07441c500100501d401c81c042050146440500d0350344100310002d01034210020011a225410761100a1007c00f080c4401d00c010702d448406170403048440500002c3d803442c0340c030009282c07840c0940f0035503208065548810305564090415680040002c0081030705428400c0000c01e044403511000e000b0104100c04100005030a411584409400507082034880b610f906003a0340034488458224170910071800441c01d0004000c0559101351341059004042d0302c0480d9081d00c01c2d00100800680c140500b8024240581010340075101800034034140080e80820702c800e024440b502c0040151b4054424055420000282c3c0e8903e0303480b40b010300e00891f15004074800f00e8500340340415001c13110381c01c001c1c0105504a101801b8003460b40290903030b490f02821144182d4031642d0503110385e50010401c20051005500070b4005540001024100240710303502c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 27695491 1250 27694241 27694243
    0x114040f050a050405010605040b030c0603090a020d05030d0605010306060f05070c210b0108030702030a170403060c0f0e1503060f010e04140106080f01080601030f03020f06100510020712030804050f 87
    0x421501c1c0c5482d07a07615401d110920000344601c0c3d001d054244d404000200710400002e598400502d98540b00d181d00100285503002c09124400c80a0740c00362110109180a01c0c12a0300c80d000b40c4500480710f86050b100007102d6200f405014202c5d1a1512000040a0f041104072441e0b40b02c0302055407810821400040c072010092815a00e085518604442803c82454110000c90341030703200c030006620500000000d41c0c0c0100e00303d00d036141e02c020020f20364038224004044074025648068009450702e03107402c500c40e030440a54800500b1590305d200081c40108100000e048200c10100903110b0f051000a08608100f0120f03501c094050604258013440100007609031100e618423640100320000040180c1500844160340015070156410060342c10800d05a5452805200c0603241515414000b028580280140c4000c10032030800d40e400751410a069132a200203c0c46072500408243c01c4004903107201240503007e1b150034040040070141d964800712110800a03009a07010b0290507440f1801d03000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 27696741 1250 27695491 27695501
    0x71202061b0601090b010e030705090a090c03060f02070b060102030a0f03020f130308070203150f060409020d021201090c05010c0b27070612051e0f1005031e1011030114040f 76
    0x21004c6011860800700300006002d0b005410300c260007540041c0c0103003c02d6585001c41940a2014070000581c040c4906110035298001da001800c881d00e40755029589108580040000303600865108000d911940c004a81d64030030903000c0b4001031b010380b4041c4501031003500100680000d9000c0a400c2500345003948006074012b81c001c41e28440000303120011410140300d100c42c85035102c0b260039564a070002e0200d42e2048010240d501c076070360f2422104115036078102910641d50f0040c1120030758402c100b05130340c020030a8020a40e680d02614000188540c0300d80e404000c16503000a1a0a060701e40d03840303a208074032100c04450b00c1400702c2803081002070b10401445c4001d10169a6625107003888040d204101d500151606c249031049a00345618a0b00c0c0606d280e40010002074400f5071541e5036101e810518841d0b40019906000e01c6212018050003038181010580200056500c540d400019000c1210010b208034042e649040c001006540d8010f01c030310040380005040414510798851882c42116 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 27697847 1106 27696741 27696749
    0x50603031c0908040e1b13120c030512030a0b0102010b010f051b0102030703020702030c060a02060103030c1712180606092206140403020f071202061b0601 68
    0x42465400b20720035a4010341d0300b6803610748580c20540400029180b401110301e0794548054144028400c944a4224400140780d4071490030411100c040e500810a0b54080744005d0008042001030009a50208901c44005d642c2c6c64200300c440704848c4001a06411a031616010310060703600b16006a00c44580f6007400c50b224200b40008001072103243d00602c02030350003c004e00c00141c0e003603000f41550381e108406071143c0001c2134090026502031200ea41005a110700010404a400303001c10462190142c046c48030007110110051100d075004c08454121034201200300507054000b1254015002144005071500d8188040003c2e4030b400050112501005600d07a00707070040c03c0c0741426130805544964140a001034140200c02e0b41d0b50100c0703040d4058040c8500081c070920f0f01041040565402e0710a071070302e456068090101c11b400c51030742118031040740600000000c0c03080114500038 = true := by decide +kernel

theorem cover : BRFrame.Cov 27517991 27697847 := by
  have h0 := BRFrame.cov_init 27517991
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27517991 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 27517991 ≤ n) (h2 : n < 27697847) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
