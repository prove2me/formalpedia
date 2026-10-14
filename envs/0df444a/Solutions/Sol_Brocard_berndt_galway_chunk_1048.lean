-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:00:16.852194+00:00
-- url     : https://prove2.me/submissions/a133d8fd-2be8-4312-baa6-8211df36f589

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 188309352 ≤ n < 188489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 188310602 1250 188309352 188309369
    0x1120309090f1e0c0801060c08030705090604031a06190f090209010e130608120a1b050c1012111201140409061d0f0102040f1208070807210503130b06010e0a 69
    0x81d0000244001c2030805e05811240c203220300d40c0c40050002d04047d003100d80c03005403460259122a02c000008071144075951015089450403400456410488944e03940211000c64244040c0d030210030410320a02018841c7c1440004410820040c090700c0790000e0501900500d00400c6403080c02e0700088400c050b801743c2c0121240c0e101c0090046420800c40301d1052030211801c1414000034040041c115a50328400e089515544410300b010030104100c80c07512508004c04178604800122801007001e40304c0500001c1d0203003045050034802039910708440c8680501403200340c07580e0a05041290104442c4001d40d00146c0d9144227401084091064038488607000c2c2000c405508003032800f80c0303800b240c010b50008591041104008020081390316404491603040d48218059503130901802a0103900f0019080d071500003007400410681718121a95400900da005051210f048001c0390305000407141d03851100340d00c01441000c0382c20b50501d5940600145061000e081200c40494070b191110b50000c1203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 188311852 1250 188310602 188310611
    0x70c0e01030f060c0206520207140307030f03050d1109010810060822060606020f0708030c07060c14100b1c0507032402030c0d0501120309090f1e 64
    0x4000c0039028100c0e01505030700c000d0595003031407d810580440d640703441e59000f860341c41401010013400c062103000040e1543e050742c1c409480d10003001c01010442581d80050040b1340010903400300e44154140c00c60006070060140354156910880c048014400650500506100a0500b0f000e64064000084102c160454403004420009805010080d04d407a1004888030380612009a1015040354880103810442194806401004040b072480300c43c00390000d0309005001c1501900018031113284000241111200742e5a040050745034003804179400c0741034000701e5040108900c24a0140c042c0c07401039150501d1085d80c1d41420745042ca088901e0705200d501c5011540c401d02c3c00a1100c0e120034061b41d5800e000c079800b42d40d000c7d00d400060100402400c035142c1036100961031403216a001e43d89407081156079041c51031100381150080c030700035000c407410800003285403102c1c1c3c15031621580d8183c807440001420503f030400a040f01e40c54a8448540d01c4604101c3c0d0306144c0840d41c449201c8c510000b8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 188313102 1250 188311852 188311883
    0x1911010306060806030a11040914070e1311060901050d050708010609050a060c1401090218010e0106030b030a030e01050c030a091406160f02180106030e0c010e0607020402070c0e0103 80
    0x102900e40741e0384004207000303040081000c40c0e2000301d60030040f10f5101e610100000c01c0d00e0000f600800d80e1000291a155a00103030350b4200c00e00083c1501951486a070080c110360340c030210040c1f048400782004100c401c2d294030000c141c0c20000701403ca0408141081414440d0a1140400711101218140000303501c0800400059410075203100181c503065841402550500b6800307070698244043c0140001001802400c03684001c0d40210403540e030041c403170482400d01120a40110000707000e26060302e90f14800000d8500d0091081c0040854043c0240404210a0710103681c40e5204000050502c80704020441070221b003400104051699a150410042d007000103810051105186aa01034101042203070040d041e0290101103095114450b4101a002403000c14009220145d217104c1114041e0008603030700d5019000a1043e14219046514040d140c0004542600e00d00c070b02c9a8005004210300009418076400401500d4040c4105070030042e9030341541c0b40ca042c1d0991040d503510002c1e00c070b0758 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 188314352 1250 188313102 188313107
    0x4030e1002010204060c030e040609020c072d0e06030a0b240f0a121e1112010c091e0e0702012a0509040507030b030604030206010501140309030a03020c191101 70
    0x4051010481c80210704203810610007504030711550380b002d4144000c1c04204885070b81d4941218014004245046d92291201c9840c950741e8261070140c0c00303980c0c00c2c074420b084100d48050440c2c0d051a600301c00c0c03144a28a00503401200d45c0c03014081139010700810b00300601007003094004501804156820700ca01d40b0305180c02980d000300040c04036100c0c0d81c61203c112003a5842124900584080d42010300308001d580c500340c59480e0840101824155400c0c01c00d0040c4828115490f0500b103040d035180130035800c442c40c10345c2251105101100840c640b04410b11100c0e9031000284051400c040c2d4201031903840358030f20700008c00304842590060703440358101514a00d03c035005501c40d01030144181d102600c1007002614600030004000d0050b9994000100b01c1d80c8039420940d101d04020703041c2c07081800c050800940300e02e024052035010035044640c00c210407841c0c408503803041100001940c02c0c108011001c4000c1c0d4040703a1400343c0c078401c1048103109440a500030581c0c2d14030403c0306200d000803c5001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 188315602 1250 188314352 188314369
    0x30d0801080709050903041e09090c0306050609091e030405042a080106090302010f030f09060b030f0d120b011e050a02060a0e0c01030e032a1b030a0f08040b0304030e 73
    0x7035100307503013003205014101000201b0358098035103d030f41c501541203400c0c6082c500401c05910480f61282060360141c140102d00c03140006407402000144615541c41d41801100c8800f038400f0b0580341d002e01a16004000c06d00080c10b482885007068038038150380d030300026098403a51045013642450307540707580d00c201c205540d4000b482c0d041d0342400c0140e503251031005010344199110190500949070800360701d06100b070b40124514509030f5420080b40031070741080030091000030001c600ae0300c6200e218483d0b14000040b2406448000d0361101e055440341042503014040040ca803605000404e120100c9050340244400980c8009665050300c0300d048544c000c8c60010040c1c90b500da1645403001c1c3e003045da42c002c22035010012080c280817072001400c8014524520501052190811752403074120241c0c03021443d404849424002161000400b0408440784d80558840243d4540e0250340304400003041d034035403c0445e0340901c181a003090303a034034020364207a4401c9404400240303072050550490301d8610386 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 188316852 1250 188315602 188315609
    0x20d0b1215070507030311041e0e0c090f0406030203010603150b1504052101050907080105090d05070b040501060914011e180b0a05030d03020403050706050f07060209040b030d08010807 81
    0x14041c00da1040050010103101034000740c10001c3c0000c0b40380070316000783c010200c5110400300541e503946e6500140440c59010004c0c03074480441c2c60000144003080007408038000e407031103914145030264107410045c1c0220600189508541c50340c2000001d40c1c2d0a10541000b54020180000741d00081d160490450b034044071913500c240702400080243c03c0b2040103580580308240d40d54480c0007a003440c2d2024244000c0a02c1070b5960030082040080da6000c9840c0c0101d9803400001d1140303480e11442c1e10b4407600320f44044000204c061214502003a45603002c0c0c9d812901540002482c1511000d03540b041e1049070900220340104040104500d10810304410803030004040c0c1c0c0d0300c1441c242464043c4440c0070300c0c00e050440c2c0e116000b9011766694000801c0040400408076000241c0c40c480107800b9420500c010345241c041c2180000b1107030301400884020740070000c0854070381100740e981c4130000c0d00400e40d4250820355480c0c0b980c4c2640c6042004181c1041c050f03c4199441d85000302042c40c0496070b82 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 188318102 1250 188316852 188316889
    0x1030b0a02040b040506071109010312020f030f09041104080d050301050a0503011418010e030d091a090a0b04031710090e030f1204050a0c06030e0120030a150504020d0b 74
    0x400c1181802083c10f490540e5011202d582c0e613981d403400d14886c045070752880c0c25071000b52100000108050205540340c0303c211602a5422030001e8188641c4034020304142c1812420200701c6109986415801840c0c04072018405500b4151140c0d05289004c0703550840070040b910000060250f460b007181841b005220450003070007031405000c8035038000755001e418000d213403040b0301c8a11050f503401e40190392400c0c2450110f0707407180c01c00959040502940242500c803003003088070f01050781c80001003862007411994010305a030301d0707180c1c3c0320b00f09003c00810035410003440c80b866802500c0020f00700d6000e1011341c80540f400c2400c11841104542d00c02c10400c0c61907104218000f1100314030400c0e6a01c90100d8001c90300580d803503060841c00d00800b00c0c00100407000484001c81c0c2c040d00344c0c0c8810072460411008000056600f000e0312110000215100c08414007800020000b02807a041003007001510451580f40554500100d0180c0c2c01041d04072401d1511000030070442d045c90b400d044070484491 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 188319352 1250 188318102 188318107
    0x1502070b1303061a06180a051206060f01031518020d05040f03020c0103020306180411030303040b070305011d27010f0603110402070803060105030c07050d0903021003060308030109090c030b01030b01030b0a02 91
    0x4400080701072041800c1501c2403ca01d0303442004581c1c501f10181c00529000d040021160f00c191005500d401044800c1031240200c00000000c0394440c1c82101190f40c0c602c89050714403418600d46005450152414a42554003040103010442560042038011445104080d05a00360b51501a04000940940604040c81841048819502d44131658820b040c0242c1c1508a42c5580c18859044440d5080c1c650305484000309120070010380c1d500561040855913000c002998035002c80303641c00b00064013284101e05c2050007280b00d01d81c40203550080842242c074086042900d42d2280360030340e440c441c403d05940e55600410020300051244410a214040320214500031065a82c0c00c840d00014200c10304114001c03000580c40303214001190700403a044000c0b224008a0101c00a080ea403444c00101e004a2030329a9901b40c0901034002c40c01520380c085003090442e801c02205000400028805499020225800202042d10307200000d01030744c002d0340d19442319070450422004584c2c02074043e4190b01d104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 188320602 1250 188319352 188319401
    0x3050705060a110315010302192007080d110a020d0b01090e0303130602090121090c080606010c02040e0c130606140a051606060803120103120314011502070b130306 72
    0x9002200e45c01008111440091003010004800a01400c1c0494500f94000540929095040301a1004070341d05540401030b24140360305d225071500818441c10308658401d14040d0640c0780206841b8007034510520440d102d040198002620282c4008029558400d560006000300122406003000c1748142c60000c511b1070406c0d0628a41960074803001800c000e0340819402802d82c494069103520841120504400d1100401800001c3ca00c1c481c0c1210000c1c80d0000c0003800503c04503800344a204d0503101c80325030084030f4017800081e0000c0c1880c406503000c3c201001666503030b5000107488c88501c0c0d03480002c0c1d1a04051001c0c12620170125a5403081c0340034840d503002117030301c4411644168004450340400480f1854030402401058000d40154000891642ea03581c0c00803040394101da026001c1c000ca4400c004a0540480703a1200c410090030f240381e0018801850200610346000c0040d1040710035081e5100d80c4001282c00440c1c9180c102d03440b02030100140300003070003801e001d8003007400c0030b03d2150b84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 188321852 1250 188320602 188320631
    0x180609020a1e030b041109010602010605033d110a0207080601060e0603180a06180308180d030515090702330601030903090f092403030212160f03050705060a 69
    0x840c3d101c001c1514007508000b4081040d4038075880b000e0100070700084c03000d58441030302a01810300790050038000d100b020f1006d059030100c020300500030180d038113000e20f0f42c400010010601d44040403003200107c1e11482e4804d84118042e00600c00c413035003980901200c90402460320b003010810313841181040039004d000c0340c1c1da40e612011649c0004140d0001e20991401d07000c024200850394030007402d13143c0361035030624072480a07000c10001c861280c0d450111941d240d009a01e105031144855040c40d92001c0d003100e004901a511081d04484111860b02d03424a9010000381e034440200c0381c403c01600903400000d02d100c20405001e042100d41c03000310b030030154856489610044000c003254101038a41d07400c08180750007141140003828520f044c4c481013070385580070b05028081080c1015220131b10311202208901501e201d0340b081d03e915501421090754146108149a045150000780c00300c0014004800142c0c90031106003800d00c26100d894803a000c80c2451810b01d00018200c4001c50b007042035001070300d42e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 188323102 1250 188321852 188321909
    0x3010312110f070f0e07032f0f03011403060901050f042015030106121a06030402120a03080105120604020108041203140a0605030c0607110f04180609020a 68
    0x40d15140c040c50714804880071034600400d0b40310500c210b000c0c0900105420600b000c0050a403028482c50700410780f50580b00700c0c12207401e03141d07400e2007001034800e048160311410616000c64901081c442d042c5800010303148091382c000e9010400040d0304180c00d12041c1018803103150300c040c0410003048145840c18042d2444c02000300000c04541040c51240009101107026441100028bc821a559040040c1c0040715510a0280038045440c0070980444800d241c001c11040075140c09140300b50914080030b00031a43c20240c0200e0740422000c014203610031040041e642d9050203541d505e15154034182c20302002805403421051950030010030000942d8002194a801c0b5034050b5000420700d01c0f2a00444c001c0401400c403401d07001d980010b04c10032000325041441a1901103041c0c0c0c544d1b8031004104411031241400c001c107540c00c80d00310104507141a48040200e100c0180c008165000403942d14065203104d03850880e02c4d10382e91001982035007040c032034001c0600b00621038410f00c1c1180707502c1c031302149 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 188324352 1250 188323102 188323133
    0x10f030c050906040608011404110f0d080f0408030c0a0c0608010b09010809251a03070206240409120e0901050d080c1e06070807090b04050f0d02060f0903010e03030103 74
    0x2d0300e4100c00304446884690243c402070007040020040b620714031108030b04821301a6000c0d070b01c0d440100c0e402d500f1860500740d09a19164010030001400210340c1d26042a600a1b4811104214051000054800007032004240790340c000000b4100d81d02c0030349032004041700716400c20420444000d006114804042c401c5031035111007420100219643c0080d80c1d841d02103141d44604c1449044244204a2000c0c060300005542803a41846084001c4003403040c0c00c0d0104031061401640090003064190020621000c1069000c10030018003641c1000420240e0f415075400b201c160200c1e6145012203580510480c100e102c04036200d001c03e514020000b000416043d101a020000001d004000c207001006043d901c2c14050090f020340498841003d503c40c1c004a41c1c1d08003154203080054902c82c4228200c4083e1411161400d081a0524007032000003180801c8168005414006804c09a52881c001e000121a0341001d01c0c0d80340140000e05080d04c05031540d40301c00d9407050006200068003030101d81d140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 188325602 1250 188324352 188324359
    0x5040905040f021f03050f160c1406042d050c0402130302090711190c06080604020c01110406020c040b0f01030b06040b0d020310210b07020c030303010b0c06010f030c05 74
    0x2651240e08001d2403000002d00029488544484070841c200060f20141c250724410342c6040001756210802441611400ca0340c01807a400382e20012984140600b404841403401070500c82c00c1c80d8032080750580340c40001d0341c095482c0c06031890100e400340089000d0505240d4130843c0b52081821316a80c4a81c0c076512202c940d403066401056408a1003100303401c190007150006d01c0748040e801c0125000d00a02c081180c01001e900510180001d0705110f446a58030f43da80c0418903201c89454000211900c2c1c0c809001a0b5100c1c3d020060482c0e200024010211f6415a10741c00d071b0f03136551a142c00640b810744d018446234000c0c0d04180e0b404015590b0b10801101040003800c01041c440c40a2000030802d00c1680c000610040020400d22402859070b800b070341c4145048200216002d1300c0e03495001c816040102d10010482c541115840002d503035071440c0d908007007680100c2d1045a03011001a013590026000820100c0000ca00c0a4084904025107030050502d00c008100043c1140c075002c80c00122409098003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 188326852 1250 188325602 188325611
    0x109090b060d1401140603010f05220218090a150b07020a080601080a170306030c0f01050c07031103011a0a0b180a060305040b0c0a121a0a26030406050409 68
    0x4080d1034603002c444050030610310800c1001c000c01a021050f600a004800030301084040c240070904020342164180c84003c00800c101d45d18000410480380000c842d0502c2c0400e451400b44540c10b01400a0300440c0040422049019020070520584450081c00b03825964106016103248440b446060810b4a0310b54040c4d40c1e07100020b0000c280e041c03110307501c005860300c545c0300001088800400c3c4c2d4400b0500c07555a0001c0510034400100c298002514100c1c2d243d00700540080d042c1c50249109200104103062036400c16a0807022981041c802c1d034015030705990f13032084c1c00701146002e208162102c94000000d5052203501004200010540d0084a103002000602e91456003210141200700f0341e0001e01858945840e00e0005001c0c0c070040c0c808842640f000380209440a6413034054030650003d6035958002500003800340c501400c1403600003254084162035800040c0c03a03008548e401350600082e5190300955005001240d07200b00b0080705140d80090209110b0030358050212411540201000308 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 188328102 1250 188326852 188326871
    0xb04150303080c0f0c0304090608030702010915090e070f020f062811030a1b09080c04090f05030c0a0c0602280318081c05090906150c01050a020706060b09010909 71
    0x3c1441032884916800070086540601d6500001c0108203441d110101885000d0f0765206003543c038051050001e011645200c3c0c14440c807a20075041c0300ca0281103140a804050b61000c002e03c0044054401d40001902c0100c806a001d404000840c65080c0103c000c0844e4035140001c8030740c00ca000b80754104d640590507078100d0300c05030540206030300c0c0f8184110a546c1c2c0c2080300e4028000c0040e5118001000c4025403035844150048007003504494144010744140b46a01c4104401042c280344100c603a100d148007274602143d13040001d000c500813410024110807030682030602040c02240d100d1170031584500394400740c44142a04404400c2081c98140b00f4480e1342d0b190544900c00340340d51741030a09034006800901c00b20000342141c200c88060200c0251a0100e080465003481940140c5400150001c00720300315041011503800d2020500c1c107a1810311aa1070155829a002518059501600840d1007400d116044c4a01c9000701303580c0444500c1c10311801d001070f00700d00441c8110444070355581071a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 188329352 1250 188328102 188328121
    0xe0709060b1201030308040510060f050a0b12010902030702070b04080601060801050a0311100e0405091e0c0d39090f0207051b011103040f030b0f04080409050a150305060a0b0415030308 81
    0x80400000e49c00148112a01c5040f02c170385032580c0703100c0d851140040ca14001101c400c0e250840e4120341d1185071a482c1b43c1c2c00c290100c4017940c4040c12180452007141c4000955000b480040c1016001c1840039007120f5141c20b500510390181070700950304c145050881000000e0400d221148056803d40303003584000000e05003036a0400d068292035410134101002c20413000804214080000f01e00b44c070303840103503800280e52559030661090f03098200b4010f100c1000801c441414850403c3c200800315420000c03c0d841c56911080c0510f000058004000c40038000034020740640741903209110401c500b040250b07254a591504664072914802e43c0510b8181e400b64802c41d0900040045501129592a504d6054282c45040f80c40300755500382206011400c030055113000d0130300494010252a041c2401c0c012044010440030346829400d030385d0745120308c0c0c2584107010554011402100608118908500311100b61069a52090301c00d42c80c05404180e5100e0000f40d0390140c942615100d032079950340700000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 188330602 1250 188329352 188329363
    0xc0f08040b030106020a0501140601171008030c0304150206040b040b040512160506091204170c0d03110c04050c0d0c020307080d0204051203030603120306130e0709060b12010303080405 81
    0x1104200d078000000b18140b40c000a00100301ca208a008100200c50000d08029040341500c0c502d00054620322404428494001080c0e0002c81e4902070b003200c10360fa2040c1524503841401c9004aa40000c50200111120242c140d1194070183c000790400e403509596030001410000d000034105400d42010030180f110801802003400d140003211a61808200981c1c04c802c400d01e0750865281c031515002503a85480482ca00c80d540114001042c00c050901821400c0048414541161481085084c01c0c01d03580b003982240c04076001e40c94901e00c069000444904044182c125240201c5c180070900034841410822100c100d0043d030000984415910012400e40c45542000341a40740042680703019029150f00402c21200c00725203403c010314408100340d40340c0c0000c860b560790540052124501002c10701c001154401d2000344040c1c40340800910400454110328809002903022010500802085101d120702a00440840e18141480c08442c05808001400000d040218003004a020401e04011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 188331852 1250 188330602 188330609
    0x3030109021b0708030306280506030403110109080a260c0a140304140d02060114040b01031b18090651020105010509060102030a03110d290406060c0f0804 68
    0xf5154240c0d41e84254a640e07410940302a80310721407140d82d281081306d041500c440307038952480021855514090400c000c0344c0000b031040e8107000f0054910907105100388100100148280759072511030610300401003401410841e410b8808044c0c1d020030079140a602c0840394400044d460f81030b40e80350301c58400c484021340040300b1231400c1c030f0110601c810045e500b41c80440b103c6d51001124544c004c500000c9a588000b032280c25507458185910843c0d07401e194111400302241814046401440303040b4508180080b10b1020700012000c0c0260302000c1120742d807070f02c0101200d00c024001142020b90003002002d0305d545140ca12100d50740141100c4000280c503200c010f101d5000e0303000600300078440e49581100661104c0c01540380100125017843c10503204c43c095034042e0f00030340c00c102075800e0540c010b00c030008405c101d80c2c0703091008020308821030003440c5841000c0402c010810b5400c55200c1e801300310901c0c1c0e8911842c06d0410521001da400010305c10602e410407030a01038075404c0e080030406446541c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 188333102 1250 188331852 188331907
    0x3150f0c0e150c030c0f33090309090c0d060e01050f040e070f031203050606040b0f0307091703040503060f0601021203150a030b06030d03060e0703020c1e0105071e020303010902 78
    0x1844401040c02081d85004440c1d28001d07200d40070766020410001c0154002c00903e0029914074078140c1507e604149036004440204030303840e009500c07001825000c0100e5281a1700710303000400d44c0c0c105145008100042c01100100c00345d41d41000d00050042c0900c2541c9402035907208401000e2a4013040b284005007094540c0c1048113440e414141c4034006807102c8040424240408a9510306001c0111800c580c2400e0380c2c2424440340b83c08884007580b02401c0e02c000c1010101c00800d203840b09100d14140440c5d0b2800640e034031071400c0281410540001c22440004071000108035250340c000ca289140000400c80442e036a98600141c81380b48540c0380c80158000782900d20210810a0401d0f2a502400cc100c0c02c40d154405c9201c001c13416164140500d4041c00780790000300316954000c1d0043d0654030301800c03e503001d102d1180070288840c0c250801c074040c01d070b442e4018400c060340c0080480200d8078129043c4802d805200c070300650359200611176035404950000d80b4002d203002040c2e0300c03001440400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 188334352 1250 188333102 188333107
    0x3030a0f1b08130806070e010c0f150203100504020705060f06031903080a0f09210302040e16080606030c040e10080a1202010c020307030e040f0e0703150f0c0e150c03 73
    0x42c207214266030000d80300f40300c00380e140960200e150030000640910031007041d5245001d14403e807004450401c2c0103031080361000300560011000920028404a08085c030260041c1c0700d01d00701c6a5818035203c030354019800f0300d1040014a02042001c11000c3e401401280500c0050f114000880c0c0741c91b08541800c001044200c1e224070402d0f6000c00414010907070b061003448400c00300e0001074122440480010841c500d555000700d0b82d9018608490410112814010300302540da008151221208071480e40007400c913800368420654000c1606a00058243da40300e0642c80c01e105644070360f100b10b02039021860801c800040c81d1000b5502d01d50060034490003602d692005602d0007103103030344032000244059400c0105241c18688004161005603401da940d101c2104014001d100080c04a081820003c94803000c680c00040d80c01c105080085114070500740f41c89500c104040f00b04d55044800c0c00a0746e040c40e52091102d0317440080740141440450360420a6103e09e42481c3c0c0710300c103661a10301c007804003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 188335602 1250 188334352 188334407
    0x100f02040b090f180703090308100509060d0302010e010e0703020414131106040302060a020609010c0206161110061e053c040c0201060303021504120f0e0a0e040317040203030a0f 78
    0x560003494101c0c8c0b281e142c0ba51541c031805043c54042c400750045941000c1d80c0b40004103e8030308130f995a082e1500034000050300d01680442107003541d0541d407480741e5a901c1796030204210300b05845004450201d803215410341c0d00f401001600741e191001c601400114800c1081c0380240d40d202c048400441e401880c26030340f24140e403006520f45804891441517546441e8403100410700211700584650079040c3c0355054511031780c8080d1000b8040d03c82d05c0b02d10380315140c80c030002c41c6402c5c420f4101801d0b41d50341440e0202841c16081c103140b004c0c1e13000b490088040c0c3c900d88000610a801a091441580403400a1306d2103444201c05035628602c61541c1c42401c03c880080c00603010b620403801d0324000d500f034408807102800100c0c020481a40c0082031070407030001c00507140388a0711300518030544515043d80d012a074840080c080b001c0c03a0304000e0023009140144000c040d0040d201440d103120840812100e0314054000903101d001d0407961406000c0b601701500c0c2040e1056440a200c0e12100d0102c00140e00e8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 188336852 1250 188335602 188335607
    0x4021e0a1212090503030d0c1701080303340c020d060603060b0a050d0f0b06030a08041410031a0105090f040509030d050708090a03050f0d0c02100f02040b090f1807 72
    0x2a0141d094a0345080100e140c2c0440380700b115542c00750b0b10003400a62810200c1c0004100a1510b280c02030100b02c05a0044100851544100c9000b001500015912420b1000d00032404602c100046480700c0a1840f041c2c1c495074103400072201d000054148a89020801c0c004030308850a210b070018400e83c5420320103c01c000940d800713071703403090000d440b100d0b00f0503180d409111550b040302c100644031140c80200390f0001600c03800f406900044c050280d942d2580aa9590700e001e03001030b00643e01c0b1081d0081203446a0170300c03006a61207a226480d0500a0150321501514030300140400c2c0ba04100d0001503404d100d444880f01d421103244090010000da182071409281caa812413042c3c4d8a40c1c1d4101004209014405c5186070b0060030a10060044000291b8058905034440c42c103811022109100c01c203822200792040e052088102d030042c143c44d2a5202402d000c0300ca18807103096913141305101c01c1c0100b40000042e80c81c01181034a81e258815801e0002400880f44c0c186030f40c51181e0004100b080b0079a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 188338102 1250 188336852 188336879
    0x31505121f0207030503060d140a080315010509010807030b0109051203031501050304150e01090206160b011e0504050c070b0702030a0e04050c03070318021f09090b060304021e0a 78
    0x40190700030010003060906240240e20a00c0c02c06000a41c060010800038030385510305500841c815461011200488001c1c1400c001c0344c141c050fa0301d0540030003008808040c0e048050407884c0300f407810b140790025541c0082d04c46207000e0110b10406964000321050f84e4080d04200025000c010542070444004a01042d139941c801ca9a244c0d02d41351502d40c9402c0d95006c0d600b40c0380515405680c40050400d040031180c02000007840d114415034a41d02e5820241e10340c1001051030126075203d40004107500d040c04504000c0c1030b4070080010903001c070654182c855a1511000b43c0d081201e004c24661200c814044150040e208007410740c1850300c0030301914a400000402c411851500c038240946421002c00040302c80480c1e2071102d036902000026200c41c0703c1e500c0701001c150242e010043d5960990041130320b140b0200300b4280d501c0b03d8120107110b803582050403070006046030341040c07082c01c950401042c03e9010240009016400c5004c100040492412001e4007c50300544030109160382c40c0c00100907113 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 188339352 1250 188338102 188338123
    0x80c070e0916090213030b070302130e0105120c0307061404030510050f07030605011409010519080106021203090d1808011802120309010903080d0207081605070e0907050103150512 79
    0x10b00d080c000c005030098150080d80c0c81104410001d81c417a030300c0c50f241d54415120081c0b0500030141e080007401c00824000480d880540040c030010303980356040c071090001d0f007044000c22802170381c800d5500c1c1045980c0000c005041c0c94407480d201422110100341c6204a00540d04014201d01072007581230b4080e81242d1100340f080300400561100341d1214a030036030480351303180a83d80c0010403000340c03001c4440d0031100030042c0010614250b031402201c01c00680290f401d442c2400c00092004004101c0c099040003600000c0100402d66495400e024003034543c1d030b0b03414590a0050014550211882d4a0709540600c02001c505009006a10040304007000b10030580c44104d20841c1e4002241020440001c2541c1040006844416065040d500c442c103071a00251010007403250200301c240002800180030380920341c061072a842c0b01e000d00d03240090602d0165005148030396840c604101c00e911001800b1421140c0a007000035241521449008003406141c10958102400341d82c16904a400001c8110302d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 188340602 1250 188339352 188339383
    0x904180b07090b03070903030513080a0606050a090608071a0c0303070c05120c1b150a02010f1103040804030312090204060602030d2708160b0c070506160507080c070e09 74
    0xc06458a0a140044c0410b03114100020a1030406000080c082e2004245107980d81170842195541ca5450500c1c045e5608012190680c03034400c1000542005030704038000d400421010310046041c000482c3d80ea11b110b200350443c83d500c006071048401d00750012240b002c00c9500540341d5a1074960409440c00a115000305c0d000c0c401c2c41c00c0b92000c41080e00560710030780c41038000b80104010304944000c483c00c0c540800303607010040d1030369010082c2c841c50007000c00054a400100b01c580c0400300c4042111100340382201ca8150400c10400000d110404440c150f170b42c54100403441d004060242c4008212071140250801c0c94403001281e1241c0000181c10b004070070306010710450b41c08401c103242c0f002c0c499202d44144d6580001d6540050241c0e0003a00821541e0711000000c10a1603d030381c42408402c1d100d00441140003e15801407001c00d1050550054044500f580041c02c030000040c0188100703a4007030301d00d050114404250f841e09004410003003442e00c4c18101c840c1458400a51a05002c2550b03410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 188341852 1250 188340602 188340617
    0x6060b0c07080c0906011808030a020d02060c04060203090d0c0f03060902121b011b0b131a090a0f0f0f080d06050d05030a050c030d050c07140105060d080904180b07 72
    0x10070800c00a407043c0c8a85018011070a035403102401505c070390703200c500350340142509000c0102c3c207082d0420182c0f00c100c21a134020074954111600c0a0305080c80500681c81d154400c11050110300c2c1c00008650b017000e42519004060002410104010000e607001201c21410709817000050104a41016030454000c4032106952001203d00301c3d0f484481a800700d4042140701c1542e68590301030448041c3c6903010002c2d00408000c9644e4049a2600458440c4881c0c0c6800403a9800e100000c1e401c2d10b14003031404000c0c0014100701e8101c1c3d50710f890b8190000c26210b60010150100a2503c1c0705803c20390b0300c4030071040104043c0c40c000c41c05410848003d0300c02131600b0b00001c0e20346403650361100c200d500100511714121115504440d55800012803081d03d11081241e030301047e240b0300c20b080c8200b150300001501c0342d0301494000c0240f076034501081da10768182410b204030307030b0f0314440c002a940e5400a103890b40ca5080c50041406010300c2d1008004941ca02d4882c101071002e100304191241051303540316007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 188343102 1250 188341852 188341859
    0x902030106030b1f03110f04090e06010807301202010603020f03010b010c020f010203091c02031005070e0f2719050f1303031404061b02010b06090d0f06060b0c07 71
    0x10600c24500c100b038032141382a40303440072090300941c00a110034054030403051408065809083c00c0342d00646c4066400c550314802da0400390400d00041e03000d80404405002258580034010050f00b106c5480450064036103410f401c800d00c0380716400e000c220707442468078403a60383c0104086c0c001c2029100030317030107000b400c0c0c050b000030314041c8502c2501d0740c0144c41e04000203400340c090002601c209410303141548000c020580e195074a440307a20032401c0b02c42103a00000c1d103162040c182424440d64150102c00c2c14101442007031500301061030144a801ea032020b0840016000242e841359140782ca04184915640110505600441000384100c400d0250f0740d009a01c8040c048049031070413520340444827030a81c00305414440800c0b4203807406000b41b42c0818101b80800c1c19080070035064a048a05650314010381d030300c5a01011510050481500080045002c0d07080810410310903460890310480149481c00e080110807002039014a40004080011548031520500300344d0004102c440c480c880c3c00c5001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 188344352 1250 188343102 188343109
    0x21306020c130510030c0807150c1a060301150603020a170103080a0507050106211406070806210109050109150507090302060901051b0601050f01140301150c0c0902030106030b 77
    0x4011200042e0079141c10030a8901c800c8000c00000c0c00c0351311403c04110000004c590852180c801400088014010040c0b80c450003c1c06101c0101130703001441070605d482c3d008548006c099070344241c0302c0e000c07044080d5117200010f4010305140c180c10201c400c200c880401d019505502a000c0c002107a101e055245448050040c400701c4244030040c9011810000888054400c0380038040c1030b071251002003101c07521540d0380100d1207000d00c012001188140240c00900c485401c04000c09000c6c84060803540c104800001c18610004018600480505100260801c02a00d0080e0101386c240b0082006411070301c4c04501074520310009649103480740b10403020650b110703c05d00b40510b4441e22074040c01c5180d64240310451304007101c12410701509026412003140400b40405d0801c1d5913001411056040104100001200100040c100800b208000301030404100481e41942d0340c90766050750600400d9011105070320089001400c076421a207002800701520780156058607a682ca00b8042c90906c074050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 188345602 1250 188344352 188344363
    0xe03070b070b0c0f041a0d1d0607270806010501090b0f092403041b090605030316050703140a030816120906180b0103050607050c0a030e031504030302130602 69
    0x7030458140103010071645521280200079000a1343e01150805642d00150400700842c14600300c401100041d1042d41300c0440c0c890041d17480a80281f8505d4007102d0030115170f0390100180310205110351202d80014980c0c54501041ca15070581607035440c09616400311507201e070828490940828482032020a580f800d00c0e05949000d06452501030a00c000c000400150042200d01000110200d1102006d0b000484004500c114095030550b00500710034101449440420b51042d00d48514041051180d917801200700c5460206014000000d18a90b0500600b0316940f6030006059866603071f600d0710301d40000308202410300d000781c44501860b918250045042c1541c500300000203a0400c03c9502034080651150591a0244100041034440e0343c41010503030a41078000d8480b010440010020040c0030084a540480305103001d90910380c000200903a0360301d59580c02014000f01c1c1000c1c8070349880401050032440d81e0b05003e40524141030030082c0081d4040c040c1c520b501d1141176808035845000140717 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 188346852 1250 188345602 188345617
    0x11130f0918120e061902060612160303031e02030f240a03290c0903070f0e01030b0903071e051606021b01090302040c020303060a09050c16060e0a030e03070b 69
    0x1079981c450210700d1002c44000c1c680d0f410f450350108050109020f5a24500d444a01707012a0382c00620700c40c2004010002c010b01004150a500c1d800360100d03000c2c0d110704807400c0b01229854100441d00c1007010074481c002c680490a00785116101204210440c8511860a401040200792180c1aa01c00144080a800b00c203003074035801060300b0100304001440149200c1e011000d041950442c8a40c603040b0003400001502d0600d4095008078812442e85014081c00009000b000d1070300c18000c1ca402c072421610f41051001a14006c0c0079800207040c01424422140c001e644210204006010001e20a0741c089441c1c0d802e403802e200310001442158034460b04c2100f5076800d9001417066201e914a46070f240c4095001c05810041014400001602c440c02108070007401600078603141c1c82d01c0000c0c40f912002503400140824100010301800c030030b043c422034401000b403200b04456031101d42000409802c824000e54140d1107043d072150281513203c5c04103000144110180c5003403c5da680c01c100241d014158 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 188348102 1250 188346852 188346863
    0x7030c110a20040e07030503041728050703050a062306030c060c0718020706110a0e0108040c21032705040c1b120e0d030e0411130f0918 60
    0x180c000c0745042c4100000102c4200081002c10221002c04900d41091807a0b0b00448199001140500a500d208600b915490800704000d007080788400281d41d800c21460905403400046081011052180c01d010903c0603503044406c554646000c0d103498002005802d0000c4146c4001005505c102d680255a071350140c14018000c14403040b01404201303207070b444560440d020307100e910000a640da0a04190000d00751810500580b0b030700560038076a0075111140e0004055100c1000880c403081c1c1c0084502c01c05a200f880c14211660f00c40c60401d201d039080d5046400880b0b5902d583e26019507151600303003e014482d65400c07401c071000300c0c1e5800608083c2d04082c034100580100034031082c00c4c01c0e4040e40b1507042901c0d0408043e128041e1300c0c881291400001e5400d82c1240348540426a000404100c403141c1c1034601188150081e14010410414000514425629002d202c14400e1800b016208200ac08480c3c404006070755121810000c0500d1180d4003105080075080700f0780d2090203100907001e40e04071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 188349352 1250 188348102 188348123
    0x290408030a09090b030a24060306052202061c060b0d0b040b0f060f0d060302060a0804030306080c06030403120f0204151803111c06050112140d1d01050c01020307030c110a 75
    0x16a02c1c940049003000d82d02221f41d0480d0301d0b40034003054900a0400541c0140400501400d2464504204009050411085500381d16291005071994002c40d54080070000740c92a1141206100310007601659010f2001010089840360707024070780e03900c1030148080480301008005249400d1200b40c100240d02503078446000e01641124280c900002d01030018126000200c0e151680c0c0081c519402003080880040c5050041004254051282c1d0000d00103c000420143d10000001100392000400040801400f1060491242c24641001e08480c00000065407a25120ba403001c9110200c0c41890002411020a50740c4403180c0d8621001580d80081c20b10703d940b2040380c00d002800c0c1222441c5100c415805d26044042a0326204060282c80403401c0d8038201c110b0b030f0500c0d13481400c003d54100029003002036140381d6541c00c40189030398490500154502c2400c0040140d84500a81103d50255400001000b405a6142d030003015800c4464468549040002252683d00c0060b054014402e10310b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 188350602 1250 188349352 188349373
    0x30f020f1c0e010e030106060314010e0f070c020f0a061e030b030312040c090608030d0b0301020c0c040c11010f140106020a0c031e06020703080609070c0b01290408030a09090b03 78
    0x1614604035150b10604112400d540d200c07000c82d00311580c590080000a40d0b455010ba0441c10085a00b8010529042101124146555510b42d06da1020301004148007808010383c00f19220441c2c8403410100050140000c1039844801500d0045810000210901c10044042c03845000c0e10421543c03010140096050601036642d95040c2c06d4098400e89008540b490002035070501c6024410292207100c010f0b60b02da403550503440301603c003640340440c82a401404a031405010000b40903921010849010604044c0703034000352003200d501d080c0ca80b569400e2021381c80400955400003408200d603201c03440000e81e6541c90480c0c654000f0a00100412001003081011400310a6640c101c460310b0100c61406130300700e54540c01282e010080480c0411184000c0002c145010112075a016a081c20500c40540895544034041c0d82d05000f041c0c00000c1c0902040101c0301d90050300c0d54002003140c0703000e82d00c0b0f440e00507503a030300e07002405001c002034071140d404517141900340211a0882c6c0094024840250b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 188351852 1250 188350602 188350607
    0x15020a120b011d04091103060c0901090605091f03270b06010e01050f030a110c0a12030509071205030708040e0f090a0341040e010e100b0f120103030f020f1c 69
    0x80d170403020740700814200319105c40e56509100c0729014001c1125001d55070310600001510f00c40480d840300707090000c10f00c00210580c442c000e000d00004c60240000d003942c40c1699050f0001d240c80a403124400c207000d101400f6041d0100d1030b40036104c1c018007000405a0380e503001100c40c10f016015442c001030061140e100041e4035403000c1c54100080440104a8030809800c014268110100c940b03050b41c040e000350410710159030b07c05244690b55250500061070011040c5559000c9481029000070451a02009000c1c3c00d01c00d54028542c0280055a900e03500c403005e401640081d1070100071134101d6804181021400644890425816211500c084118075191030110000040750406104d94038240000903110040c4040c258203185006900d85042040207000460160808410600302c1000c0c403616542c404901c00c2255180d5009640c0c030340078118581c0f054007501409020881e1a040080205504880040d8060b00076600f1212280c0d00b007002107540b010380d000c07041d0100f0018201c8160062 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 188353102 1250 188351852 188351861
    0x60b040e0a0213091506180504020f010f2001090317240105090d050607020f0111041e03060e030405040b011b03050a020102040803030f0a0b0d0503031315020a120b011d04 75
    0x30b0030f002c4001030070000f5440d251144560210421100c80d5281c030248034026540c000844a807105082c204268607041c0d0104088031180e52659051000e104210301d100c0f0300c507203000380c04507450f9a4941c006003c40d40c24a806013411000c11000300701003600320203205540c41e01c00c911805d40254500d21301001c080310500309111001030079040000800005c0e9207a1144010122868071903030051a080ca046a0000d04103103040c403201940d0303410042414803100c1714009890546201c070303c0e26400306207402d46a007484500c5501c002c00e564200001d15481400c040007800443d0416102881000c0c580401112000000d55660b41c131303101c4494480c1b020a1007400030340078440060000514058980392100d240d5003023250f00500f51008902003281e050041d000d0840e103c03d09951001c041c096641e516a07c900000341885403260400c04a030f010700c80101d480b20070340b040c410303c00c40d80e0f1640180020310117140075000c100c1460400840342c0f840c0d44100381048880b01056001d40e45015084104809070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 188354352 1250 188353102 188353129
    0x303040c0b09130509060f16052205030f0a0213060b0307031d2d12030a020304051903030209090108070f03060209062a070609050105040303030c0c080a050403060b040e0a02 76
    0x49143c1142d44140005210707103805400c049000304070516040c03010202c2e110b0000c1811a414605140a440d003541140940b00b88124ac03003a0444214001c5406140000d80c3d6401140d0511624040c60000da03004a90303146094001d43e49801c0c03001c0400e403001c041e18550b01c603940841108200103528540304e5400350198014401c2c2c18000c2001104e240d07032800321190f900a010113112840c141c8544000600c1041c14518080038180d00c0c2040c0344c105203640070081207250101e400000140401c4030030302c4003034a04040c03c110001015140d003801030003074000c8106031340504864800402e10740d40002d285001c03510040e50741d4217400e0450b980c0b00003940040c2105a080743e81840004009207607215040030171030a007031100312002c0c105100986455540c1d8000f00038080300400620440e40d001084809aa0701401c0c041a407281c402000c54024082107405400741c1004544c082826a00c44024000c80340100010b10403484540104000c40700440c0000e6000d92010f4448401410b0070001d10344d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 188355602 1250 188354352 188354359
    0xb061e070203010b1504060905040e0304050d031710080c040b03030306060d150801020909100608182401050a0617070c080d05070302030601110c0f19050d0f030807020303040c0b09 79
    0xc0b5003850301045c04117072480c0103100518004070b002d014480e40703c0c500310000d00b01110240108140901000d03200e00c21405000d00a00980e81c07803206142c040c21a102800c15540e2100c1014030f000700140d65031a5003030054006e82d00400b60302516903e040c2c040d489400030000e000c1c41c9180c90307880801a07603034092401800201d071911342c60206d801d440b442c058001c1404070009030343c0d54120740811a1001c402491010f48042d801414031003207500881c1d41c0e07800441140702c0840c18402008071880c07c402500c9991100b4511845070690f500c040c26070604031601a5515080300da01e0708029100300b003182c54040701074100d030000611210300c00c0c0400880f2500401c0704034600300e50000c4400540e0000c80e65100400c0d00081844001d5030300403209560605c40c180580715900c4001c00040740107a80403101ca200721986a0142140c030000c01d20200204401444003010821618048502a040c00015404070303d190700000c4030940040120380c4603a5100d04000901410804458415004565125007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 188356852 1250 188355602 188355611
    0x5030601020a0203190209070809190303110a0e0901061103090607020411030c1c02030105220b0a0f180605010807030903090f06120c020c060d09050a08040b0307030b061e07020301 79
    0x36880178441c040d10720603107001c0400d10310102d0040c000c11400c041d000030108100e010810401c0000443d10140c003441000c254100c4403540d003001c030050500814403480c3d441c0001205d400607500300001d5008004241c680b41c00c543e0340e07600c0590301400101e12640380340e00200901000c510744400207001d940d10080000408903484030f825805a0400c80301e403a840d0b8800610001a128480c5502040002c11a4217503c1c40d810310b40402c0c11a01c0003000a14010050b0026000358448bd0b000180180c4003e802c8804044d612610b20550a40600c01d003c0500155503c40307030203503024011481a2901a15044002d459007101200244400704041c2d040125009000ca140c45607002c45000800c0f070f55643e1001d8082c10147c0070100c554400c1a1f005552081107889143c4c1c841c44140c40c0c0c840e20649000801c0034550070407509200000d03400402d0050002804a0f55441e00409940109446c2e902000500116010b0003001d11a0450324468403444032001c0b1081c1a101000f41a402d201070000b18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 188358102 1250 188356852 188356873
    0x130b0405071a0a020f03071e060e06150909070e04021c0614150a0f0b0702030708010e0a150b0a17030d110d23061203070b1303080114100503060102 65
    0x1681e08580e042c00c814440710000f01540020b40c1080603880700020300c0061842c0240c0341c3c1e1542c03c0810704442c0c120900310f4070380300602070140340c1c1d01070311841700344105480c840d00d0300440750b212034203246c07041d540700c1d00440021482c0340e4070005031344041d603944114054040d11540c00b0840c488070b0003045100b10b854400d42030070001c0c0d41d5008019081a1743c0e00050413504152401171801402c0360b04050083d08100410451180d61443c4401196070061640307070f07076405c5800482c0c141900d07900240890b40c240840d008668600140d41094640a5800c800f03a80d0b500b12000e200b5511044803403035020711520818480d041080000001c900b201c8000c880c6000b900b8a950802c2d03801b403102e42c0301e0400c40890310541c4180303c3c1c05040906406003407424000c00040c010000c0722070020b1b117614040c00712002c49400c048000c108a6501d550888981c0080d450001041442281c4004040f8001410301000040302e000f001c180e1400f040300180180070100000702c04840642004160034114800d503c0b855 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 188359352 1250 188358102 188358119
    0x2031303140f04030c050909060f061c14030406030608031c050c040504050f01180b06070f05150109060504150602100b01020715020f010c02030a0203040b0708090402190f0305130b040507 82
    0x180700440c4075001201c0046d00d003000704494460002d01200158011701c003001601031504400992001d011075a0310540e882e003511820070919920002805000c3c00b9090307040600d000000303842141c14039076007404455183c02e55241c0720f010381c40c03014581c0c8544084202550f51260041035200d02d03022060780c200703940c0740c0c006005d5842c107641c0e80941e0b5a1802c01401610b0300859a404444003c8606200c1c4542d1000850388034881c64201602d4160441c00030760030010705000344013105444140b4a161541c503506508000c1120b841503034440d5113007403055080c0d94000841041151441c1e0003400c8072851004840c4090030100d00316078118010801d02103044ad44600c500045c0001d260300418482d4224030b421421141e00394000001d6500500035042603da0001c2103c00b070751800000a61508400e1900c030505015480e007040d4000d0002c11552410007400449041400c1c0590b1580c8138040c40321000e404881040d200520411600c0e070042002c21410840550014411400c90f0007081da42d1207070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 188360602 1250 188359352 188359357
    0x70606030602030403110607020a0305072a090c031b030e0a05030c0c0102010e06010308070f05011512060507080f0a0b0a0e07020a020a080610090f0e0114091002031303140f 76
    0xc541c941e0b80442400f09055000801d0300c8050a00401401541032401c0060751b02c10b1a060010100103000500604000c0b0710700d81101846080201c00903401448600b800000304180142040b29107081404d01d84184680900012810311140b40640c60001e10300881c040e1001074240c030061f10440b940400040c1c010001400403480070009021404855000203007036606511401145921070341c014008038005004850040340e00000141c02001d051411a01418180c0b800d1085a8107584000030314180c6080a4501c5501c40c00c01004a80c2d00da800580f9160010303102140807018140010319241d289a200d0071480c1c4d8000d04c4402c009640d42c882082c0e0355021202c49005070022120b0904504202100502a100d054040e1446140c11800103d0154071440f980c180c0d10788440d000110b4542c1903111800441c50600280310f00b2512950318090312030b0035105040d0602c50502c000941c04018426a8082c419010b10807600343c4e1251801c03618071101500700894600104005011120b20200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 188361852 1250 188360602 188360609
    0x3020c060a0b18160305071b080901200c01120f0603080d05061c02010f03330b04030809100513080601060f0c05030909250e0901050a050907080c070606 67
    0x1281280c1e02c034091240d910355158464004603c09001d0140800d6624581c5412103100d140028895071254421070b13050b408100c0b001500e100c110040014440c04c0c3c402050000740030b03240c07054409080d2500b02002240c41070141102e40282003d0078035907102d81070005407101444404220420790102c6002129000e5001300c60001d40003c1d8801444520b0040c00d91102046440c00c800343e041003003044450008801c001d0401007e11210498940a0b030b0110300840c03807d044290400405600c082d03074940c903813a8005107420300001c0c00201c1601e090200c50a980c0e0010744035041009420a0144540c60300e80c1d0081400010b1002141c004808480344004204100051074071b03500d8520064032101c0c1080e0080d0420160a018501042000080340e04080c002c1c3c40b4500142d03a410416420032400c40c2e10280500884070104101035132003044036144140803140080745991728010411442c60740d1040e41c2d00700c2034800024002d18082c0c28082da0092002c1a07181c6440000d9a03050f0450b6860380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 188363102 1250 188361852 188361871
    0x60b040b03060a080d020d0c0807081207030e0d02070b1305030d09060e040b09180705060c07090b0f09071209050715020d0801050913020301021b010c020d050a0e06070303020c06 78
    0x1c10402d16181401900b4002e01c16040035045100c1c80d017000039180c0310039040d42002c0c0500d11014800300824402110307503054216100c2d54540b0b40310300e04a90808400d90f156000a401d03c180c031030a00d44041101c03003003007055800400007280b03002800a02070b00720320012080e89440c3d01d000611928184401320f000b681e20340c1c07a10815428081c02414441070300b11031034003d03468096002c07401c0c1c039003d14072504840b503082c2005421450074001458106581c0046401c880c022582d410340b01c000040070010f0300c0c1da42d002482003200701414004ac040074101034507804206680805c0805002c0c20a080b00411540000f046c203d080d615040d01d03001c0c6507407024460000180340c28050940c1440403804014007803400f00b4055140c1000a614000c014140640b22a00040c00300d04642d0700f541190200b060f00c00070301c10076800c0c1802c850300802d680003c0c1c0300036001d01600c18503014030a208540d0740c4c0f4429100d0340a040100024400d0a4106000840505030b0800c18800d00c03100800c16940300e0395408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 188364352 1250 188363102 188363107
    0x204031209030c080c010c0213022223030a0f0c030b011d0105010c020f0405070302040f0e0a0e030c06160e03100b0102010c1b0b070504030c03080a021c17040501060b040b 75
    0x41c43c000791540099805a165500701ca031090031583c0c0d00119039820f154045900800d480c44490300c03007000348a1401190881054201c600544003c013041810440e154015030080c40b088001740301d802280e6030001c150f496008440c1c12800141c18590003034020b4040c1c443d4100658407542c548400807403e0b00860f448441c040c0140784d00c9403000b030065001d1329007840c11404c0701031a41d01280c046074440f1a058031458072140022280c6202c0e43c181c40c0140322100d0400c1da11a560740504460340f0040d01d00304c000504018000300704e23032800402c036007034034124400902c619950080080610b1b82d80401c941d08015284951800755681040707600c58490009400050f10001c5500190845e01d00810f040d05000d001c180c00d2032611081d9410304c80035a0410158050380d99143c41c01c0b5854071440e04010113415180402209001402c00900b02905058003102d40b000c1c403140301140c0445594001d0f1000403500c7e80d170a82032401c04418035801a00c20300020503450f171070340002e0b01c8540103138028100c1000301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 188365602 1250 188364352 188364359
    0x9020d0902030f2d0a0b0a0e01020f0d0f0507120b0418031206060206060d080f0708040303050307080a020f0d090311010c02010e060f041a190f0203070e090f06130204031209 76
    0x21911310100d43e8824032004a0700e82c01500b003041d100c0c4a0b07003074081c0c8003070700f403000280801070035401400d000643e0740c008642d50454049043c5403030f003082e0103c0030850301c1c08815101070300c86032054600135a81d079101d9180507420001c5100241c60103140e02904591a15182100840005800d90643d442a00c0c1d0210040000e4a100102c80c044d84c4020119440030f000c0c400d040d01c620070f1240d840b40e007101c000c5d59601c88100414a40b4450140010502c3c41c00017800400d165100000e0b40c02003015954140e90340e25a10507883c140d02501160540300c207410000001241c4940e03021030302c5a40f0a003003028107030381080d518508664155200c40050707511101642150202404140d1340510460402101814203446110719a4125418140510040000b040b201e5030b9200c0030414040c3c0ca484180b04034040c0e001c000020f904144c690a01141c449250038a0501c1c00c2c0313070b0303a6124045100503980146e44100c10030a03101c01e101003c085459007000f0200100f284242070300f007408819256502541d18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 188366852 1250 188365602 188365633
    0x9090c080c0103050403050d0c0207030507030b070216150f170c03100e0c07030e010530090309090f1b030a06080d020a2111061f05011809020d0902030f 67
    0x300c00703207114100351920007040b000a4102082d50b1302c0c0b080020002031450071601050349000e03640c0d0005813191058000000410252011551080b00c1550aa81c1c0140c140b202d0b044150b812806000c020010003040b80300424400d60311f428404000d4582110080c00612080b0719465065a5607440e41e03100008000c1c111180d4072144005114013551203103640b40c008080440350089005c001e013005000b8104c1d0f80d40740c4c4202e094400c03422003040d0b12607a4260600c4c0e01c2d00e82000780c41e410707541f840c00f4000140c182140401614106c080203401e0314242c1d9074901aa4808107401084100043c10092031044005c002201451003001510400181c0b6400c0c961207618140c0304010400466004d44042e50006200103038402c01030300f032000d9040e07070015403c0701030380c42e1240c101c60a8694810f86042141c070850804131040c0400780724a00501e02e6854500441d80e92944074010140000c0c5000c08001c213100507030040c07145025140c0e000940b4140c0b80e000074141010b085d013100c5698403142242c000d058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 188368102 1250 188366852 188366863
    0xd210513030e0102030a0e040e010b090a0c031a0108041103010617240c0a0c1106030f1603020f040b0c03040b0c160909030e0907020a120216090c080402150409090c08 73
    0x2e090005604050603284c0c0104980c0c003000c220340c0181e0b10b444030310702500401d40280c501350400402803940f500c0e0400c1480000d1001c8111100024105458074040c0c25000175640958181a07407070740040d640310f440305c1c289405000c00b140c0c1c1540d43ca0746c0c0090801050035140c00c140c1c885c00080c01118080151940c00c03100358600c001c8800c140402401a42d80429040718030208031410700810340c00240c10075182e420704a00c8901e400c243c0002c10403260809840310184240c286074800082d00314200000c0307080340100c0d90354107240342c0d00f0002442040d9601004d04184c1c4030340c20890789003d480f8800340348030381c010400e01c0702240e006241caa02820364500c8440c0c0541803580040002160540300181144040d43d041401f4020b0040480e4a40d4400d01900b0002ca4000035050701c55034100710008d50701e03400402000c0c900c440c0c0210102e2100b0302030050907080c000c15904c403021341d01c40d42c0030012040d030020304c401c80d0001c01700703c0010350f400c0b10b00030001c580c2e0080302003101c2c05203400c5a06050a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 188369352 1250 188368102 188368127
    0x160803130b090708370c17120405011d0303040b0901020f01110d0506011808061501080103050c122e0f020a0c030503060d0519060e0a050d21051303 65
    0xa4024820501504d00001004032420520030b01745190880c01d4200c0368103422000c101200c03001402d40f1030205001c190103001088818407180740742e141c42401c11403500e07605810300c0d00d002d982c0b00304000c110640c40340b180c0c0100e078076525202c6c3c2001c1c007200e0000bc0c5980d02a600540722a0004135262100e5a010300c40d020a01a80d04024441c1c10301d00604141113205205150101c20790f907801103811648240b41d00c9003983c41640ca44e6240c00e8941d800580d99440072208400340859503c2820035075449083c4050403a0383c4000200032417101e182c10072081242541801c0640d1141c1c11a1100b107144036595070f0340f00c2c11485803212880c0c9100710840241c55203440b0103e140c80c0100704403d03810394010807410605400d854150740f261038800c00203440200104003d004e601c03071021465000c0d10081d40ca5041c1a2041c6800c0108001c1c9184681c1c84035610134000c0c01a40160050807074150060b540980420b104a501d6400744225040c1841100c0d002d03580b02c4030122000450104240e006a07440150303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 188370602 1250 188369352 188369371
    0x90302070b0c060103061109031504020418110d060b180106021509032a0a06020904061d0106030207020307030204050702030a02010608070f05010e03010204030605041a0c070f0602160803130b 84
    0x42601d40102c50340d8480040c40010710b525941c2c031080d0202d83d07260090355017100005080d40c13000030451140c0e0345000400c4e201648111b2600d00b200c1100d100c020b80d16550070f5400b4103401e850707001e10410080790480010b0306903041e9440c0c0300c442c8101d94403880c0c07905040742c1e6007454032955410084024a020b01c001e00c054006170b038510506c04041c0c2c00200380e540d03c0d0651b051030409101001080021015440748800c501c0c460300d007036907080001c150050316001005aa041014541c0c80d403090b80242a50030038400c6005052005011041c860b40040c88900e00140c2200c021540c0c0340d020504039172040340d02400503000031462000b116030a00884004040d444020503c0034203000ba03001502655104242c10322644101d0464641c500390180c4000710740011040200d85020708204105052421020b61200040c0c800511902d880d0b10a4072503041d00402a4040f81e282541c1d628000d50003400b50641c0c124503140c145c00001c1411000f1841141c841400041121031860000240341003d400401c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 188371852 1250 188370602 188370607
    0x204050c0706150f0b071a06030a0b101701021330030915030b010206010506090103060812031e07020304030f232802090c03102310030c1710080a0501090302070b 71
    0x2c24555148207011700f83d00541e47d2801c0e216140041d1403e40c0e1000010700c5004000200151400c0210b5008102d61403000718032412800d10360a10300300d205942101c001c240300340500340600c804507020030f038402140c422182d01400ea603480ba00e102ca01d0700c18044001440c078071810311041007043c1d080300b081101801d0520403003100c400040e4680905008240c080d180100e803050361a8425000b040040500e08141c0e05d000c0b98030701441d4072a9200300c0b214012000d082d0306c40e002c0099441036a0344501403d0740070f1801d00b42180c0d50030071b440e808403d054480c41040445048140c01010503440e01c3c2a5801c001c16403021140892080d240200300c00c081c14a50340a0b1010158444d00001c0384e01040081c1c0441e525560902c02ca03c03081422780003a00c00d07244003840c8404105011420560002c0100c038240d050b200d41c810200c090b103a6608008001454210b84001e04003890400c1a400c44240c200b141d1002ea1547c407558a0030102ca50166807130380d11011183c0c14140c05010b600301810140382001d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 188373102 1250 188371852 188371867
    0x1305010e0a0302100309201503010b04060c0314030f0601030e0c06160305040e100503011d031e0f070f060c11120315090712050f070c0204050c0706150f0b 68
    0x307201c500300b444081c1c010010042000315951207a84451a241c5e0700c01114080700e644840d052418203600c854441c007402c00d18003050b604881003000d0343c1c103c41026118514081c100070003200c421041500403001e103c91902e20f48405032911014520440003100008060320300b0b0000141a11a01088501140c004200070410382c0c54070b000310780c45001c00c1440300c14121518941195030780b103254403203603940160000780b001508002904500301c9100301d0080c00f6491610810300c0c4018029031401c15164010000030300c603455001d140004440c14411140c2c10032400e030401200c142c0c404c0f001110506000c0c524a02003000a10841103200d00502c3c01c40304011300c2000480d80c0d00800c3c40301c2c605000c400f00004407080144c0710400130422020f06130106d00d040807036001d80303011a40d20410980f10b0600700014810141006858131419aa66803140329070301c981c0030f02c8010040038000c09034404080107504042403060203002001001d036101c03240018500180c403c00c68400360404040c030070041183c070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 188374352 1250 188373102 188373109
    0x10f0c140702120307030c03030c020613020d14030f1b0a03020619020c010c111b060a140c010204080a21050315060702030115060e060313030806130906021305010e 72
    0x8a0000c0542a420396140140d000050045016400a080b42c0c0b000240741000c0661040d038480001e0b100b51001d010b000c503815410303030712480119400103100c036142081c1009440d2520b04041454024290180a64529800d072400c0d0303407000034044d4171108002a001e400c0015021444620740d0181c0150003a0141507500a407034001c00382030300d0700b40754080c24456003410f2035a044800d2006210b0082058000c40700018007035403645d804000d03890040644111901c3c0c1142030340707090220000c0c032581c50540000f400350b407440f100c1c0c54280c100c0c07101031001041e2032509200a00260030850300806c0c0e5989289416407401550038030303a0000c42181c42c001a80550400150390f08282c01c5000381c40e014000c1c0b07010404030f006481001e54150b003003180020301030320540d080d00d0582d00250f6075900e800c01c1c0792080c841d0303a01c000d0310344070030314034036441484042880790b11101d8200c82d00501d088155100784052905071282414155407640e80005c00054201000309170000505003800c0c0361602800c2038000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 188375602 1250 188374352 188374367
    0x61d0c0306010804051f05010603050f040b1b0c011103160203041406090f0d0c0510050c0a02040b01020109080d1e06080a06050705040b0d050402090105060702100c11040203070302090102010f0c 85
    0x403075040c01a200d02140070414280951000b1405503010b5030064903864610360054013080c400d00b00864a868041403242d5000e100c0386124680201e0020190781f40d50108250540203000f0201480f04203006e107040303c550038029a00982100515540c0742d0400c110141c0348042c40320540402e56104100400c40c94920f25a0980252000c581003500c0742c1104011911000404d07180a0344002c003041c602c0d00f0807903400c444030141c0e441503400114080b85603905540c0f62244102d01ca03800d074020900f680042c900741c2c02801c140c03141803002003404540f035541c1d141250804800d031940d090316401c6800860701501d07101d0381d400480e0442030003058a85000242c0b03902c0c0c00500500495103800c000348000b4001c901700c46c004c014203c203e0ba624007004064070020301041e5002c910651034100001500d01d080c20544080307940082082d010003e41d0355040d00c00742444e0508603808020f892465030150f075103101440c8074149617100580c1e03460901000908545440081340d062b546812514541d840e4402034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 188376852 1250 188375602 188375611
    0x50a0608071e03020a020c09010b070807151d010507020610032a0909140606060405100c02040c030b010305280f02040918030801140904060203070c15061d0c03 70
    0x410140e151500242120190700882c0e40e100b4064030740203001c81003a8198010804061142e0950360a110b40c1d40412024840070f04c01c1d001c14410a221500c08200c80034001c014092241c004030b0300044000d94208252010308103c81405000c281950f42445002e01645600a4003840506200d18249880388114412800050300010341010000c061000100d81d0b00e5a51844449151070566684001c00160412110071900c01e2803848d0051410580025860300030b1000810950800341848113004020181220850801419084800168691348207400c3d0440c5165000b088101000c00050103891004d0820501c02556200800c0d03100040300064021072802100401d070340803403040040c0640a690030a124a61400303000d440021030512500041ca8865100c03000c19030390300c9810128079141410242e410000c0480041d0000e00c05038000c59120b425400c0803641d000c035035160007281000300840d0600c2a030b0b4442c02071040c00105c246252484d180000021160305d031450071300c0460f000c081e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 188378102 1250 188376852 188376857
    0x10e01060f0e030f12040510030e06071107030c06051201060203071a0a0b1c050f03030403020706030908160515060402160f0807021215010b09010507030c24061a0301050a06 76
    0x1407100b003456809106011410700c021080754451840e069400e07030242d200c0d103c2d003445801042c0c1180038041c0640222650548400d000d0100c6659030308007074400c0c2203114a40c5243c2e0044150100020b02040b10040150410780d80d9580c5032910769480603003164042e040310017036500600070800001c110386034035520800350b610064510740342c0051030360180502c0011180d211048882c402d8134000c580a41c654042d02038411501851001841d980c1c403440143ca000d030058004100600c40340380a500b0802140c0d1280e0001454137241242d1303101140c159001c00c03580c9400180c100240e1032a2002803940080007200e003140b41412100c0c07400c601901d4602c000b81240d542d18011018030410b64141c458054015280c4501c021048040b030743c44480200418482804400010401ea010300e01500c850210684440740f9014441d1420307100b043e030784e4000700d9010034410be005964100160301340c0070341741e903c3c1800f1402904081004000d00d01f80c5200440c0e0a00074001041f07036130707151449001200c0990 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 188379352 1250 188378102 188378117
    0x30203060411040f0c020f070e040213050705090406061e0912020f0f030a0f060507090509010e0916080a0302010f0b150c01020f0403240c080c09011106070215010e01060f 75
    0xc101203400350844a8981c04c2051420b102010001d0700420038001c044c69000540d01e402d62200032141280d00c00785d9000e0340080880c40204c854000ca40e000703540011180c1020740c200a580c2d0b0001e026510359410500c0081c6001e450030b110342d500500d4207202d4075030b0750408404007070070281c1205585000320b4010388102010b000140107610f030140318100c65540074003a1150350049050030050045004400c0358243d142500050040344106840b50556000800c00545a403802110700420307040900400420301030181c64640e1401007030b00050080021402825646440d0b00300a82102d22016210800c03501340960311107281c1d24504100500ca0038501c40944a1345250381881c02070140046010742200001004414000400030001001c0d144040c0040521040d07001c520548128072050740c086550030001c15141c0920f540038011904042c0f514030800240c5250003454000203a40440241e080f001003100214030a00c0c1940c054000404807030717415450b04100510030605020390204002c2803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 188380602 1250 188379352 188379383
    0xe0f0906060409060f1401080d03050c1602180a052a0a140403060905011d031201090e0c0303040312022b0302030a0b0303190f0306081c110d030608070506040302030604 74
    0x11588060910500d6170000c2285142d0600c0502e00c000d400c0c0901100e42c496408500b02a5200b40a03c0d0300c6540f501c50507500382240e80e0b0255035070030100017040b40d0156449198842041c07181c00190300c580e40d940e001040e1030400d040003e40084400c0004048103003216004040d00112038111444c00640d4501030700078966214800c0910300841c1c2006003941d0508252100380304054001c40420481c80c44d50000002e040d101c0940e03a4860907011a0080241390010040c8607040d07409008422140019240c4612040c1c0000341180e015802c1100c030507640704c2c0501400c50b410040380c1040d074005640c1c03a40e00c60b5080e02100e002a0103c50000070540c0000014840b000345401ca45005074020b0704894075800264040052071780122486800a81d5450b00740850503c83e014420071605170001130400800c4601c080409a0101e0f0b040505129040060442c254010000020907281d140d40001d0030301d0924440a00b407080c03da0003940b04903400d110600140e41c010500350b0300907074032080568941c400b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 188381852 1250 188380602 188380613
    0xb060d080f03100e01030f020a0b03072c040c090806090303010e040b0912040602010903022a0d0f02060301081b0102120d020d110f070c05180705070c05190e0f0906060409 75
    0x800c4d00012022108a0b00000410020344c0c42030a4541c42140c2c4185010707260f88688206003c115200d81c0001d015000a4121045800600448000b504030842140200d407003c10140e61401c0c6842000400201003081040700600129800028800165140d54501206900c40880c064000780001e82d9210101d081c2c960100300990b040c2c2e4250802d40c1e2900c0d564400030340200303007040058025010700071030b101c01d42030002e1803456030034003210070f20268030a50b000780406d4490a100032651100713031001c1a00580d030b41d940a10700030194500140084038a5607500e8549024054038a4155413203035003414221340394035083d82d1426a038401c0058854610203072140c0641154001440300680c006418060310485000070900d26004a500c0c0c000c25643d8018048050700590b028142003070784030f0209019a01c200300505c06103000d940f0351081a40c0703c0740001c1c1d0f41402100031829428401d4001c101d500b43e498500c41e80000c0c0382c804400e4a01d044155951a00c0005210a10135030b035440d0b28204100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 188383102 1250 188381852 188381881
    0xc15070e0d06061412121606090c03140102030c04090902030a0204090318051203030c0a0917010b01030f0207050d1b0c080303041e1101031107050a0f0b060d080f03 72
    0x203002410900500c0d49410003000500890142440c2010303100a54403550416113080c4006892020050010410092080380e050700700c800c0c019225442400c0c0174002c80e00902502c03254031b020344140d607540e920b1494002280382814000c0c0f82582d00610401000021704ae041e02c0840c0c10754000172400043d00d01c0000d090540d003070700003580305250100080a0580c0300020403000946855840022a00e41c0100420010040d0700e0003020703442000040c614500c20409001034184e01c2c1026071805440c3e10b80d00405000180c000c00e8507a41d10a140700c03a030760b454062070758480c2d41c1280861030803046407100b546401d00002c1c54002c0c050071144914103040300c0510002d0982d00b1080000301c26072034090254890303005076001c0e142d00e001003501105081001e402a078046621440b001c06281ca124019070250240302400009107400384014004aa000d210a50099210b110030141d061110701e803504488001506150003217415124a40000701440c0480d28040e402c07000ca036440380e480444240020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 188384352 1250 188383102 188383127
    0x5060f19091a090d0204150e090703020d0611040b040810050c030103080a080405120d05100815150609090108010903091e06200a0c030302070e06090601030b0406082d030c1507 77
    0x511f0304500141c0301c40e00c1840241500c1003a195604180c41e42e107142e5580340b5442c00060351100600005a0000b40d050f070140300441808070440341070030742e5042c02d4022a0800e600c02c19064000752007001a041c1140b060503884007511400d0342c1554156120b4140c01e002da10000d02c10301510f42d000c1401e1050030450b0100c0c88091041d050b590b28040c50300000949416544030380c41000c59000030807801c0000c9002d100010820030b059001d40c1d40c1202c980b50346101464125002a410003b441c41d5440c3da4205901a002240001c60040084c1c03800510021240d40006a10251824080740711540070645004071807141c64422841d0040300501c5414101a02150b10b0500c2086440c004211401c2843d4080300d000b502522401987c9001c4000b01c0d03a001c4036490350000a034000640c1d1580a540520742401c809800010540c1d10351401d186441021481c044241d40d420074602a801d0b000c9506640b040b4414014600b40041c1480b0941ea1b100c00c7c1814040c60002d180016880744d1083d0340c80c800300d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 188385602 1250 188384352 188384359
    0xc021003140a06050102100e0a02150c0a0602190903080d0c0e040501260a020135010803030a060f050303090402031e01060e0f0102060402010e060307020705060f19091a090d02 77
    0x260500d03480b400000d0209101c1c00d809401654010403002605219807210424004068809050150700f040b13031001d14000c020740c0990040c08215145442000300903642482103000581d68901d0141e40c405201940d802401045407010b42480010f082c0025244103402d16a40030600c0105407000781e604c0b03691404030345d4025240200004004010030317144101001d1403000b00c000c000c00344245944440c030920000c3d0220354400413031041c41c040b900075030400d071181c0b291100d060040264901d1800704280d1140c10b103940080180058003900707101e10f500030190f050400ca500d034580404203460340a00300c5190700ca1a80800055403140201d504800c0307003145240d840206684a19002e0030061007010440d00590b403098a00101e540001101e60003150140c4405003405080c4040025961008040e18114010742000040a85900b4040c0c400d41200e8508180c40d200146104040302200300851001c01092201c2040018541007050401d400d45105082c0e46680140119660b075140e120300941 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 188386852 1250 188385602 188385641
    0x7050607080a0305010501090b0f031b0309010c020c18010b0703110d02070311061602191a190201021c1104031e120e030c01050d0b120a0c080d0c021003 67
    0x4000d4500d000b080104140e40b010000c5989070401101c002c1207178021800e0456007000503c6131541c1060166030b00481046050310342c1c0024224811217900150794400c4070341c0d103c1040c0c501054050003191000791099803a40c4a00401040c402115071040c4030300407422000040f004245885542000d0b42a0500012a41101480b0300c00039079900c41b070f00c400d48548a8500c1608020300c2c101d002c840f41100c06118103484650141c08110320b40e440720003141c0ca520313034055000400d0141410841070642d0881010b0380ca4522a1501e030040c01c04c86e41e107200459104008074070b02d081c8880c108100005801c40300044241c00e5030b420719041e1040e130704060043c070440c199100401050b0601c042005200d0f004085010140342d005440c0d9a84e07121f541e0f039050300444c1c854022544070b00d01610117154a0000868500c90100204000500c0140c0484154110081c400140104181640300030015180104040f03210000014444116120000d10644003e404018180e21a4121508490b140c01d01001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 188388102 1250 188386852 188386867
    0x9090c07060e06070f02010c171302030708030703080c030105010206011e0b0313051e0c121c030c02060f0603100e100c0207170102030615070c170c013e070506 70
    0x943d5030008032903100001da040c1031295070491040c01107a111a04036150445032000c8000707200182100100004411043d111444001d65010404580181101c0d006181d40d02d100e820018000030000700030000380182003004008036640000c0032030446040b1145103c9003041e028021910414540c0302d030103080c4011081c40f40200d03002540f1800980700704100da0b5000100744c6000700c1e10002c1a550001a0800c5045091505014002415200845007034490710b1442d1241d221000c400c0480a10009075112801c03804a81c0411000381c00100c20780d070401903458403800180c0d65941000060121507200d02c1a8440303024100540ca100004da20014402070140101c02503132010140f05685140d50080d00070b44101034184211f82c0a00d40c050300d100b210304012001055244c1c407140741101d0140c44880e001400201183c0302200362221100903118a24164000405d00368485400303820350702400c14a04030055064000708203017a0740704c1c0c1003054a0780c00c41180c0d0800c0101d5100755044100000d580c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 188389352 1250 188388102 188388131
    0x206190207050a080a0302101e02030c220f0b0a171510050f0706020a0908070e0604060603110a0e0a05210106060206010305070b070c0f031401060e090309090c0706 72
    0x15003030302d006480c103075603065a540445958244040d000342c0980c0080845044c038030090b802560b5104c00007803c00100910b1507080c1d070200d9004603000313a40c03881c1c08aaa04001c0c0391110605202c4022000c00c02c1006040500428002e001441005802d82e800900c10420901440c000007001b441805074107020f1800301c0090a0403800d511116120310141119000c0f07050003141903410a8455108050610340c42d0364a6400030740c050302480082c0000103a002070406010403408010304007070280c0d6001d1341080001e100c15202c2c41d80040c002d145c200105000361818010a640d011145468940303200b2220300c2c041101000d658008681003140014640000300110500100340038200000704103043d51020704070307160340f000e000060035074002600820800405502030190f5038092650302c0c40d0682d071815084000c0005903c03c07031704161791100c040700d56071081c801e12005141c00030f02d448107450304c045155200d10601c4c2500d8451800940800c009902c06c5050703e5015070301a81c1000035000c02040c4c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 188390602 1250 188389352 188389363
    0xb040312030e0105240301111c0605010c0f08030a0b0301020f09031e0a020d030509030303190510030c170c030d020a0506010b070c06110c0a09060524040b0702061902 73
    0x45404207081c0111148158014496103100d244250b1056545201440c0d007044504003c45c01c0580c1517485424641b182e21800004046c101042840303400d26001844413401610301d81da0110b810300c000ca80307550340841e04184268642603440702201e50313a5aa91070743c0c44000c2031194030468056102207104501060b044000f072442d004110100d03160409089009440807080320081303050b0fa0012100b540042c180b603118126118803e080c501d06003051038000c41d00d15042201c403075218090b24142150354419a11885400403c1e084030520028215107842042c010148103110261074240426101100280322200750703a030303008041e00d04500c0c1d041c0c0000e69403070080c0d90560302d80c0104800040c152424200310382116034044010b80009107084e0b000d80d501254201031480358051002103502c5a56103401c10005000803c00000c1d55909000030310000c0c00c0c0741242e00020108442200403c6141c200940c0c0c1100c0ea0652501c1d5628103500c08102140a8504c03110501d824451400f012203402180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 188391852 1250 188390602 188390633
    0x30207050109061a060705030a200a0f060c17060f01020a020603040606090506060a0f0c060e0f151605180102120c03030a0c051c0c02030412030e0312041d0403090b0403 74
    0x820444c0c4c50103141c01c212003803003130140080080d48204030315840b5500414522141322801303141088007500c140d140c2814009000c0b003c0302c0c0c05004060520401c14039106182203425940b414800202c421a041c2040007805030080344100a218060f40c0c4a80c0b0030440d001e20158054269038032800c003450220081c00c1a409000f03401c50403c0002140b0381000410744a00b00c640c1e41c2c8800c03102c3c6520806566a0072404401c0d1607494aa50160040c0d000c100001c040c03007000e00008080c112020700b0000c800c1000503152446100f00103130490072065124059441d4000302a00c0c940c0400041d00040c0d2410341000440c1010300c4001c50f0034200e115001c0059840b443c01d0308414865114843d4085070706204403c41b90481203454514544034040c1540a10810009401249e00e450780b9914920700c507002c01c010484c00074841c2c0f00900b95a0034144034003800701922811060400d414510b08030790101c00c0c0348207044558503180c001800c0c94458280d103001007804840c400c0d911601c0b8282042030910140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 188393102 1250 188391852 188391881
    0x30f0d020c10110304061103040302090c0703030b1507081c060f0e0105040507120b010309080c03090301110a08071206030f140d0c02030d121508250b0d090303020705010906 76
    0xa0b408201d0340c010000c2e10350f04610200030318502130501009490703000d03041c018034140d84001d00000c030041c0c0311201014050314980c40013a46a005a140c02003d5816440c0010f00070a04d41005403921a12a01070b1080c0903484045903032904403500b4074031904c09404040c501120f0504000241f00310403640c424003520304140e5908081da0f2508188019540103680c018001840443c0b00362440c102a401040d08180504d4003081134042c0341c94080e0560482c1c544008160800120000b40345002d00c2007901041105500e64208181c901010305003550040111091018001d00c084602c002644400c0c041c640c0591440d59903c04c2e402c00003d2941c2c41c90721160903200c0c0760304484407203000d601501c0900b540100140019140c04000301c0d02142c500d50403801440c1c0b100c01d8175103294a0061301501600010004014007600d261442c4142c4505404400d1080042d1409102e52181b44088038006003910303a0200702c00c0c41c00c0c98101c0080c490035201800b10351800900c0010050641c001031400702480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 188394352 1250 188393102 188393119
    0x10b0411040807090b06070f0f2a090b03030304030818070b0301030b0603031c020901051c0212070c111017040b060307090c05180402040302061602130612020f030f0d020c 75
    0x1002100122145c00c0301941e80003205100748000a0316000d66600880c0c818908500b104002c0d6465000e204804020b900e8003400034150107004c24903c01e01c540092908040030f20440140c000825101d01c00500301804000040300096086c2c2c0e0801400342c1d403407004208445a582e5201004060b54100703000c2140c41180c141c02081c424540041560030300c400c10b0389152840044400c042c0c00035400344102d6070520401303111140c0984505100042c444a21410150360b951030850034450100005140307a081c003280611220200c2d1041d4030350140608241c9500c81031340071440007920290007454001c201e03550454104820031118800203030003080c0c2942101c86090b11030703000405841d0380400740c038001082400b80d0019111070710000300c200c0d80050001482c0640300d40100e442030348810500500010100c5407002141009440e00c00a440300e50000c00900781003108006e006809150081c0c822503105003610320783d58003440548203801c0104111001c09100944c041e44403191002d5140c81101e40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 188395602 1250 188394352 188394359
    0x14010e040c0e091015090213030c0902070c0b030403020307060911010f0212180a08030f180904020a03020105070201030e070f170304031208090c150301090518060711010b0411040807 80
    0x10140c40501030403c03200500300e1451080401c1c001005070709442141c420200400003500d5400780300a0904010780c0c2c200e80d800074110700705201684a030340d011000c01841000400c000c00c411540d04003d545542c816107a8030345460508924501a1507005421a850005190104501580305080d10002071300d4181188030340000680e16400040c80c50105000204416801d040601c031600f00502c0000309034151a5072600181761540c1c0108000c01984000081c8142030010000807005403504110340b080320a103005d6022403404401444000d05200340842c990b01107a01a80003880d40e18448000c039200340340e442c1921404015076104801c40020510041031002c04088115000d80341c1080780c01e0701003203007035004403881000240040443c2c00350100c062015030380c0c591305c502101c540360840782c1c9030750400450100b111406400c0d503140304800101003030a040003007850f652002032030a0509103440807427100d90150404402d034a6101f4a060048021011540301900a8516450480304010348 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 188396852 1250 188395602 188395619
    0x30e120304020f030703050c01030c09081203011707061209060906050c03070e0d050601062003041d010918231f1103011d071101150816031a090114010e040c 69
    0xb42d46c0030281c555003000560201c0d55003c0d4212188014851410000440d52440024103100d8000c92501d501b43c0c002004018200b8890070240b0451110400b070603c080c5000400b500700c4640a071300500c9d85440e01d100c40244001c65124000c0d1540080b010302c001d143c05e450012103a8002c54904011aa45000c0800e10741040d20b00305d6456580300d4010f090396420702d03205640121103966030014112020700d0404c1002c0040c8090300040c40403528031010403482c02088111801c050b04035541103442c0104110706a0001c91401892582081a444130456913100155000d5141040c0801a01c0380e0580b0156080056803000c40030812148204038a06084008050603c000e1084002c0210001800580e05881422442c1c202c0114202070201080c40d4084a0075268a02074082400250300e000304200c00b4140305106c0d20410b0090682c410604641d540e0071220000c3d003201c4070312208000003c04000003540b042e11001c0d00784601000541e540d2140700211101190205c41e13a103100c440000b02c000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 188398102 1250 188396852 188396863
    0x703020a0f03020f090a1119090501050a02060a0c021603030e040f05190203060d120f020606010810090b0f03012c030304021815041e0e070506030610030e120304020f03 74
    0x3070f03004048549220200781001000c4c800680000c0c21142e45001000c4507040300b200600500e840040500020074800c0e00c0038041011680c003490501004000c80c980c040d03030100b4081e80c41049103000185a0b600400200d280a0104052005c0108204004003d040c0c01c1072071600b81100488092190101c03031075028084c1e417800da851031400300409e0f5550704000d0194004d141e01c52806084001d4001580d02c0303080c088080b000801c4e01040a9000e00080c40390305011865000c802030070030521604040c032814207006014032030340f1501c030383c0c6041008080c0e45800526000b510002c00a201c0f0000c03008000c01088080300c1c4213409241d80c0c043d0380c59483c0010041d244216001010460302c400c1c0710171111301d1010001c040e02c040000c0381880c074040e65110b00c220b042d501c00502081c07852400d1080007000302ca00c03002e01d0803401c0d801784400700b1842e500c1d0021242d00c110107480c1c08a021900306002e80c06040f2001c0600403900a49060b80040740d60000550302c141d0003183c441a002c01c0c44010701d40c561 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 188399352 1250 188398102 188398109
    0x1608061b070308040f200405061e0d0309031b0510090501020601050d06091a06010e041b0e0114030a050402010e061c0e10060801090302010c020f06040204050a0e0303090703020a0f 79
    0x5102484000042402402099442405420b00c2528045281e443d84511901440e0040030340214440306d450f20308081c49066031060007a030741c69010454030f040c060391244a400c1414855a02c06228104045c4650603040045600480442c4072810f000700044065019004290080d60404819526180b01e586403004980040e0040d00361039081c4000e02c00440580d03942030366219101d512600c0001c80303442d0a0071450300382e900003200b40d003060f00004000c442202440c91059041c03100010310741070b00c02584810b1100c503003045984030300c0540051b60140c4405820300102c08001c000c10110444580046129500c01d90b40c11f1200200e00b001c00845004010780c1001084405050210031912035007d03103c00e41243c400c4501108580650005944c40398102c5030323069448050000070181c0900460a03401c480d4000382c100c850151140c0c0340d0314040107101030303c12500e50700410711101d0264001007504482c0c03819241d50340f400000407a42c500161104a009409034440000c900c0d00c904a264140e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 188400602 1250 188399352 188399401
    0x708060d081909050d03030e0d0302040308040b0703020a0b1e0610020d03050a0b0d03020c0906060403030c081309091208070f1d1c0309290f0a0908160806 68
    0x4040c000010502c00414410320001441004a4041038540e518035480091030301c6580c01191401003111101d00381030702c0704001c40905005000074000186480d0589041d6904018010389556190408a25100e007402000c0c2581c240072007440041071040c40e251021641100c0169096220042409544803113101c240d00140c124030110b40c0700300d100b17400154001518903070101780003a050b80000d030101c038030480c1200540e20804d03641101c0e0800344002c03940100708507134050078145592405024101d000400420849001031904014446601c0140152500e10001c005030441807900410560a0b050381ca070102c3c03004000210080e08c10184c1d440c03c661681e90704140050306001103540321f01c40c461a268041c03c690700030070311101c0d03510b11852017034060760b1265001c2e071030700e2050340140c202a000034180c40d0070801c3c0d9101c0741018400305d45603202144c0a45540e2103100c00e084901c3c40e81500551024000c0041d4404c01e1002c0824040564201c501501c51a03101c4091055400406031984440f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 188401852 1250 188400602 188400607
    0x30206090a08160c0306050a0e0c15030f04030c060c05120901050106020729131d060d0b04050f060a0f060501090812030903040b0a02010c08090604020904021201110c060708060d08 79
    0x401004440c1c0050b1424859104d200e034007601c1360359200c02c1d500100c0d2804002c0350f841c0440c0e20b01e481c040043d4140340506a6561403508148000c1d10303602d01c030003040340207400121004a41014400d001b80184903400550410404c80d81410080903980001c1640a8615080007c124281070611826040b038a240d0003d00ca4640342c002c000c62211440202c00150080b1204a110000140307402403180d080c604500001a5003020480c2c44840ca2901e01e0301031500f080400c01c40162640442011941c3c1c00082040d6903684500e0502e161030061400c0320594000c403424000704003a1500b25485100d07000d80c041c0040307a26030004540d14003440c420782001d035005100f02c1403110005401140c000a400081d039250a890701040c090550000768118010303035448220b0030345154024040c54100e04d51a004e030002d0704054002a10b0420080c10280c4500c14001243c41061000d51001d1b1070f54122001441c2c40f103405402c8603880b100b00315401c3c0c1c0841d581c600007131068945400b00410080d4440c1c42a070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 188403102 1250 188401852 188401867
    0x9110c150613020d1b080906061c05030715050a150902030709051801030302150708071101020903010c08010810050403050a08040f0c0b070314090607060b0f090c07030206090a08 78
    0x3454040041e1986400000400d29550700750102e000902c0114092000400d13522114904000c07101d84118421081040f14800e0145e40c8201003041c1d600000111040e1408200107401c0d80358200d1000c10080c10b40c84002031850400550b640c00001400c0070030400c0000390340d90920002552180301000131200354080007402010344aa015540254091030010409620307040880c240000140c140307800341803010010410035504202c801c1d0050803c0e5046031a0b410b04c8031001d404600d002c0c001d8801c0c04880700c10f908200009506544085400a0091241460014014006000a02640c171442c0501d038000031032081f180c000c5502407a459a556450700010300c004039200440940212001c1d1010403042000c05c0d111039812000d0048080459a1902c60b440c0c00350000c0445090103851400c02c0c00701d0f40031981d80310305850360390750880808110f031503c030703400901a0f40700f0990386a840607100302404699010300c00070741400c9120350211140c0b6220803603895500c041c4003030001d044d55020481031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 188404352 1250 188403102 188403133
    0x20a120c09062c030102070f05190f02010509013014010608010501180906090c02010e0a110402180904050102070510150302040e010e0609061518070e0a090207080409110c 75
    0x50f4140070300200c00111510301100000d003643e001d117074181c034000c2c50301e0750740c40034403030b0602140103c1c141c140c2c10302c04444002d0fa00c2141441c18100081e045c02000710303031000242d001e407000d15902030241c02d80e094203000e90203855074070190101c810101d052030480899102c000d0285580d059a809403100462603103010011034184842c40320380b1061103803102000039260340d18015034014000303003080400e03440c10300343e0020f08450fa03019010710581d11128005011810641152901d0381c010358015959001400312880010840308220760010f001d14204010b020040d400f4020041c400c030182c03001e400840c0e20240503514031510603401090320110400040ca425400002a4801800081014a1201d1070181802003c9840c100319411820170410319125203043c04030850000c80b003100c40b40d044407002241d0490020510001d22582568444890b40d51203903100081c0340d0441c0a41d5102111315003540c0a400507c2844062800c2031040c444095100b000d641d00c0001e0702000b40080114940d07034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 188405602 1250 188404352 188404397
    0xf131e0510081f020703050d020c0615030105040c030201030f0207020d050d020f0610090903031815050a0608101a030601030317060103110d0c05130e041a061e060d020a120c0906 78
    0x106d091110800030810228000d0010340301c01200c05010302a03510306a031000642241e11a100342c440d0f45013008010000d030f100d49903031007075940a20f400a0130002904000d0001e116131240654000c020b1405201007180000e130445072000941d003940c0343d1203440c55045603151016180c00b180000e0a49051042c20b50f03550050361441d0103032074046500d00c0d01a25060708003031921002e640780071160092010000280c01095000310000d0300c04c00090346031500064a071880300409503540c0d9180d00e114403d400d0890400d050340c190080070b80d10656581d1801420404130302c0c1500100da00000c0c001503256010303104035256011a001000c5c80c050501e9200c40003004a68610f9040c80310502c01d0325140700601d40c003000a040b01c1c101e0707440241480d040031480354229035280c1c580e0600703001c200301460300e07026640035442e2240700401c0e550305044400156035008186010440502c04180003a810b41e02015000300c540100d4030030009001040421501c5203180d01401d00442c14041990400c01031b40c145 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 188406852 1250 188405602 188405617
    0x7230a031b0b0a03050a060b0301080a0303020304080904050702161a030612120a0309050c040b061e070204020a0302090111070b03010b0a0c020301091202060a0b0f131e0510081f02 79
    0x60741c200d59151a1140040c1d08072440200000f80d480d020484120303944d21410010b0b19007410400e00350343c500f003200e0f039613050a400024100340d0007002250800c010603054501303400c1c00820500c503c0c40e100000039a114001d0041c240d004103a41d81c0001c052007949010880c00701d03c00007403442c5035210010f01c0f8400d00c146d0310056003481907030000340303811040308080d0203000055034000c920b600050810f070b4036001c0101000c51149142559803015071390384000711903298820f00c49010f4440000078801c0000e0292001c041e4206000040036044c40360315500428658200740c071a00e41025000030710699400303c0e4050b400c11000d00b040180011140c0f40042d00c010a9079203410503600c01964042825118501d0084034056484048500301030380600500d80d1107103c0f84010407000410f04006103160b100710b00079500a01d5441f4107240e10440b241c0000c05183d40c035880700c0c0d080d4140102680000c103400c5070744640507141d880e00421200f60101d44034880402d48103090041d29015400440254003184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 188408102 1250 188406852 188406893
    0x507060819050c0706230907060201150f06030c11060a090c080d0c0201050d090807080304030e0306070903080306010c0f111509030c2e0905010e10171803040807230a03 74
    0x41e0b030040c1c0000303081c6016101f284508040c0c05c204c0d1820070301a094802c000b03014400358024038424060b90000c0e90090007114030b0307032071b002c110755040d0b907020344d412451300701d440c07800c0d014400030401180000d400c80101c403841502c074199995600e500c0306449108800000f00003514050100d00590303c5078019201d420304003980080d90b4034113507075000aa644960b404403822200441000140b6401c0f44c01c91340c42d20340c10f401038100c0e4505440010815031860200426000d004070104916922900d1132a8042d0b60006850400001c0c500f04005800a841e99884c0705d00781c06d2105008070100a402d50f524940c000c0c0c004c203048030f4264208a02c03c5404014108580c14610b60f007107221b840400300014a1045480799450a03061030001484106451b101034090700034540920903a692000385c03d04205240c40e10985280c6810600a100c8000840c9001040c4000f00340426012000b08d5035404890174054802e1a5000a0b0085982c0103112801290b10060102c002c1011408101c042c55800e081e85 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 188409352 1250 188408102 188408141
    0x301020903030d0f0507080112060c02030f030705070606050303090f0d050a0512030f01081504080903010f0e0c041401050d0f03351e0c0708070507060819050c0706 72
    0x21800319103150040e0b080700d0001a158400ca24001c04d6070f129080e009078040c6450780503981803c9041c080060403130002000596207002c01d411440c424003c0e10006001005c0440d0341c0d00300b0840c0100b003900040c1c0c2c00e0f80d4071440c1c29000a400d14001084440c0c081c00980424002e107692410401503891405050b280750088080060000350103124a00f25240840115a22820441a0380d00c0101058102c03c049074400d00500c04c16600c80c284e2940d01c181d00ca11217658030b0003542c010a015240401014041606004040d480c0310001b003602c01003001c05071020014a04240e600300e42d461000e1107510380018a901161010400c00151350070020700130b003040c099001c6a540c42e5808a408502c510450401c6000c07010108840c000c0c8032070300301b07150000304a10034440b40401c0c0c202d07200180c80c60031807880019000040013200416950ac1b203821078203584a4903034030760001d081500c0440c5c1200c4010150350b8195400c1601d0300c035079806007180004c0e0301d0402032103554400042c030102d03001ea0a4103403071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 188410602 1250 188409352 188409367
    0x60e090a0b150a1b0609050609010902090408070212070611100b1f0504031b0608010b030708150a030807060b0a0506040315050402040f0c020109060b010302070209060d140f0c01121a040b030102 85
    0x1901d0b82100001c2c420000000c81b40e00b00d05100c2d003010005401c03031750b40c0d9041000d42000740e901e40d4025030f002504020711590703d10036480040d980024550400020f0f000d00c130400103215070808015030440b40c1e160180c0310103600c0c007110501115140300b01580c0c041503400c400100340309090303c01e00c0e801a82c0d042052400307440e6142c110640b110010840303c44074a4810900c21558800c0e0464014140700c80c0c1030741541040c10300601180c3d002015a0308440381ca44085007240d940b07222001c01190040d690f103599440b5410440301610080000342e000f4040c4080006080c00c0c00800c450449411607200c1404100384c41d45070001c2e00010308181e9005072240c002e03461000782446240070f40c4070541c00001e000d01c12032510320181c0d0030103e1428189481880042c0c05a03d403140c40a9210350102c0710340d41c04800303910300072031a800b06003e03c01c01031245a26810100074001054101c4060076214013010300c1c0d400d9030100940f4108001e1042c030441d0320748031680c142041e8108030060a001800075062494 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 188411852 1250 188410602 188410637
    0xc090c07032307061a18040c0b0a030518030316050901020109120807030614060d0b040e03070308010f150905040207020d06110a111c080c070b01060e090a0b150a 71
    0x40c2064841d00d1801c0c0010150f040002c40e120b1921402c440e1880d40500504482c0050b46080310004541e292403120800a020400d12013110009041c0c04000301303440c0c09030300328002c0040c041240c07081400c94600a123105020f00010507130f4480c14000e012142e04080440c0704664507080000030605541d200c4001400044451074000c852100b1641ca14120745084280101501c0d01ca510035180c0c2e03100e68640a0145c0c88146c11101d4400c807140010444d0b801080210b0014030b42c000d20030f500c601010581e00100360740040c22904032261400d02c40546500da58150800e07090750422100450440740040250781426000740a013140020302e48a0304078660340300d1000303542c054039444500c40d81c00140c100c242c42d00034980212101014000b051903105030000b130b00d880196150b40c1c1e402d00071070b48000f4550a03000300c203c411103544154403810559441402a04042c1c090481a200c1c00702000000c030f03192658843c0300c2034804010f0185030407940070305145c2c400b5070242085400704000e580c410b080075103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 188413102 1250 188411852 188411897
    0xc090103030f03051308090d2a030201090e09030406211104090c1b030c020627040b0d0506181005130218360a03030905010b01020c090c0703 62
    0x180203031141d410b103400d0700b80000e00b01e03040185520408600f10340000082103e0500b5179640744070998030040403183e9403c0403500c0030340300200c11501076418211210310509440c20769044900c00c2e00e88091071a141e405c150a204411a02c5424507030090004102440c03007580d06072101c1c0c0c580c03280c420a0f01c901c5003115043d5004d40c112240c2101001408010151191041c0348196001707280940a6503244040b030403424044180c0a0100420030340603005554800003120780150900c0900401549800c0311382c6060440004120b1045103407c40482c5d030f80c20202c241c0038106901c00c0181026507100d80c44d10300c030a104401c0c441e640b80308181c500c865041e179901c038450107074070481c20106041c00c02e4810054a6150540b41841e00c003595800c2c000340417596205500101c2c1105c8110040000c22200e103000c4480e040c416907050310843c40c00b4018150140d10003151140140000c1c40709480f0480103907500c1410360004c4d50000501400034003483c14803406050701501c00e180007040e04c03481c0c5010f00c0d00d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 188414352 1250 188413102 188413109
    0x30432011b020a02031002030a020f040f03051b06070b07050d14040c0909050706140d06090209120105010609032003010504050f0706030605010522030506070905030708120901110c0901 81
    0x260354888040a001e81c0c96180340048204920003080140300543c0800c0c0c8605000304580c140039004404200480c81e02d40580e800c188078100404e441c2c5130f840c0c01d04d40500d102840143c545000340d011840c400c5460741e04c171090f0361328081e04403881c101c400d945000041d800200001c00b00b003414483c43d4050b101c18014400800005034ae52100da003061b06040c040300b00e080d40441005460020300c1d100080300415000100c40d00c908001818401c196101a810f100f00250174658a1030410046245000c0d60301030074844200751600403c1c11140c01986007210400e000d8580401d4500e07004100049036080041c8040c0d0f4070b8030a136400f1140440c0030a0a580d0180c07070071122900700300c01074520300c2030030856107000708114034043c8680c500c1c15001a10600c01c1a24040040410020384881010b9065056000703582c40070440c1ca0300d1030b0111008100724403d014851090044a40c0010046c40010350782148801c04107000e8030b044c03416001554101003900031007e29018190300001c1c203507911004079008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 188415602 1250 188414352 188414453
    0xa140a050913020109210210020a0218090607030b0a050f040e07030f050f0a020904080f070507060201151d01090b031912030606020d0f03051e010305010f0e070b0304 73
    0x60081c3c400501a00801e4111b16021200e00304159400400c045103c025a90103031103420780c901800344200d060510701c2d42d029410580a0040401160003c2440d0f4411030300641a0f605a0711080f0080f81654000700b10164055418902030045142c285103038005940d00800c0040c00d0aa40c42d29603080c450a5407042d00c1600c20504908280003081c081d0303403548008900038205a50742640010310740c9001400280a03d1404240400d240090300116090380f50410125400c1c01c0e55030f00c0090107408940c075805201101d5030000102076540280070a000950740c400140141e00300071140005104082c411070b45845000d204200c1c0d0403081c1180000309008054180d881400204054155000d50784140115880218031102160b4491864400401a45408516a00c50b40d00f44071148078107010780c500c81c0001200000c2045815802000d074065050400d0041c841c6800340d441d01c5102500c10f002180804200040c0060301854006800e102c055203010305d0320b04203a44580c200580840c0358680c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 188416852 1250 188415602 188415631
    0x20a0b03183007050d0f03020f0315131e0506010507140a060b09160e03010f061e060504050607121b232d012a08010b04050a140a0509 59
    0x8000e441c4244182c1d10510b441a500e20340801d568900756a42114030444040128100b0016142c5100e0b8040310401030000551917241d08080064003411911042d603d40f2540001c03000f84107504040c016890041d80051803907141c1e030940c4008901507c0000c0c286030421034108000030010700c1580213500b64100c400e00901c1e811f0041e181600c21184d8810b070a070322a000603420400034107000c3c182c101c041c0072246811005202d42601007809002e90840c03500000342400000303d0000039405a001084003c80741440130590b41d140300b0354a0f07204038061560004410889100030072880742402440c8112460300000c4030b03510700c107070120303023000c07668100c50300c61420054002a000e00c0100503148a00d80700038050a041c40b90a100c10098500703049030850f03c0038480d14413024029408440f0020300444da400241000328500031350b2503400c0d00c0b070702d011032201c00010441c2800c00b02540c01341e90b406000712004d20304048110320040c20903004147e01c015002c0011440384c80e00041c40d4000d0720510355400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 188418102 1250 188416852 188416903
    0x5090115030c050403020f0d06090816230601061107081c1d06180d0807030509092a0705010b1002280b180a0614070f020a020a0b0318 59
    0x181614203070781c0c1c54403c22100344010700144c0c0d03458244600d85413080307414100083c414504031001d08008003020303000c1103020900c985011102d05405100303903c2403c60b0303c1915240050078540301d80c440c0001c2442c0d4041c4005001d80c90042600b400610101c1b000c030f9000a9480b8a03980ca0440d805264039100c10344100c2145000f40c000c1080c84403280e0f078000109024201b00302294141c010201546004481216800041e442d2404840306e403680004d08940d0714405818054003540c40401214000c0500e440000d05802420260100c1e007541c041210b01e20300040c03540320055412502040c1c409540e242010b4903540d854600d116035072100d9401500c8400c03040301d110310440001c80d002400100c1d280e10080000303895801c0c083d610150035944480c0c4805644072091500380341000c0200705900c7e0044400b9042c00c5034000e60310a02e4107940c0c404108400c458100d889200140d002904805c0c1c0c1c1707005200c12640c510180da8045080e15449210b403c00c07415003880c02e00390030400da134136108004410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 188419352 1250 188418102 188418107
    0xc0d0905040219080a090c08060717040309120629030607110a080c12120103060c050a0804060903021207030c0605011a041203120603080d050603010c120b060405090115 74
    0x290014002180c007141049162000c81400003a00440c030360030003000c04001107250031240d020903010b50708140e9000c0040d40b2600c495036640e00c10359120002c100c1c4c250108031300040e0542041c1c402d55240c0d070303402eaa55140104442280b55a41320450b81191103120f44800301000340d10706192243c101416068100007031080c9400c00e000540944100a80502e003803c001da4001100c3c0c0301a6406010b00750350341e016440150426400340e02040e240d08000a00645021800c83d000e0306880c000c500402c11856205029034041c800d012611000c2448200040c0104207146e1094010600a0050780c3d8005089010400103030710805040700803c0d940034100003840680d03c6102d005d4040640300c0c450207204850b4491007800759115042001c0c00d05180e100c2010702c00c58092400d1624920203000c00e50b107a1a2a2060350861414030f1503091901001403070720b26050040814000194075144824200790011801621642600302d42240c4104000180c54079031400c128000e0402d117103001581c51040400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 188420602 1250 188419352 188419367
    0x9031e12020736020a020303040314030403080708190507110c09040206070206030702070e15040c0201050415021e0a0c0302070b0a090e060f03010f0b030d09080601050111120c0d 78
    0x8040c11944028420b00c408105007503002d9003150001ea403101c01c0c0110361107006400c0c480107004404a400400c09443c510307000005140100e11940b9004111391601904207600c1c0000c680240000e41d0450206095901481040c0d0300001900c81c0e0130208510a81180162030081e01c80c000015070510ba0000325800503c203101c2101c1e4202d07986112420640c0000d1054004e400020b4441e07000040420079140c003c004000040c0014501000380d8649031424070140c81d00c11212901803400c209140c028144180300d901e2045038401064013040721140c090100135009042000c1480403040030030401015581d01404030854240c3c0e0740d0b03000200c0c41ca0000d06140b465030159a90b202c043c895060625045200101550812601d15900ba510200060021581ca41e09a6055460184590b0a45019410a003040ca00a0f012108200559141100d01e100c5902c98a102504030500600c00c643c8a91441c6541d4104072040352810028020000f0b130650018000d0030716940b24094015005410111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 188421852 1250 188420602 188420633
    0x10050d09080d0e0106180b1807051c05070c03030b0301020409140402031c35090a1103072102030307021302030f060d0809092e170a050a08030709031e 66
    0xc5c402c0601c0d00400b00b4076808a03102c07804c0b603a44c483c5d02d40300003a1114114601c042c282c1c8102c1c80c0c110b00b0304140142c41d0758400d070404040d40d41110300b1001048040e01501d0b0040d00c907503075204491641601c0450007400740302c0c0b04540c0355408000019140f0118000c6108500245110540504091040600e411074100703052440ea00c000d0550090650040481c1042400306148401140080202182031101406680070000110410b00107035076000102004102d10580c544501d60941004040e503445481c8119000c0120300c1041c1c242c1c1005c080b8048180920140c126420402c15600041419400c5601480c581c1e901108100c08041070562064009405036415040c0312040d49a0f0b003450300c940d88000b400794500c140403903e08a580c0250022050f031440c0c820b498090000248101e41f0980e01c40c0c449046e903201003c003005c02000c903941846640c805d0082c030b204a07665455030b20030b42004100c50300380464080008089001240c0ba0204481a07a0300050054010f1501107201602000e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 188423102 1250 188421852 188421881
    0x1050105060301090b040b0d0302030a0e031f0f021315031a010801090b01090e0711060105060c03041502010204050301060306020705010c110c04110702040603030306050a1203050910050d09080d 85
    0x100100030584500084a040d0394201a000c1004850400498094080d42e4078658104081015203028950701002804840b0216580d40040e500c40034201366559056074440030400802440045e41c03a141b81d4800b40260600410241c20031029500203e0420000d610013821103100b0842c0720840f5601d03105518000106003141000c00d200e1100080281605009030603010b99503a8000d1713030f90b80c050b0f07280d030340200581c0210301c10503d45040020808007020085440300c0c4581c00c000b041c5494280161038518114200550915180264200800881400f50825035608000c0425551020b0003600c0155001d8480560760324081c1c50440d084580c1c1d02101030401480e1000c01409260110720404007078003c0b03d01180c1a904802d080c500303849515402540585440000010140c041e0040d404a400c100c5804542a5948003150505455900d004001070010400e6580c40d00e8451a081840901450400c0c2803200c07112207442211059402a41c2c010360120f9142c0b03040c04580141c0459003403a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 188424352 1250 188423102 188423111
    0x110d0305030f07030213060e030c151e07020f06091206010e15040e120c030f040f03050c0d05151801090506190b01080c0a14120106081003110909031b060105030f01 72
    0xf25421b0350079010600543c010882c0c40c084405060740d08001203a513540c8020448001841c0049009140da844145c3c2240c003026180102085d0305c0d0441c041c0e503031054000d402c000c0c81c2480b00082250740c0c4d000c08c85e034541c021280785460002c2c03d03003045400e010780130191034110181000700c0042185115042c0700e0b482241407c013050f0321200e01040c1c0c456181c403075044150300d5401c4031404a00303500620541004250b004180010b804400e84140380880b03000e0001d640e22214040240b0403030943c7e204001d0843c0e4002107040221401041515a000d65099040c042c03030080c40d2203035401e5030384500381914198000d40c180045604003960740c482e2104000000c0101c40007002c006030084000904c0042400000b003074401015029400052250f80102800b542e1402d080800041e189000c0c0586c030001100c880c002a1100926080e14040d0380c0c12050207028081d40c1805c00543e040c00401c2c5800a001c180040351100404050003a03100101c0e00241c19130398101405d0500d4803140e6100c00c90540e051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 188425602 1250 188424352 188424367
    0xf0705100f0f050112031206080a110a05010311120405070909050c03251809080c03030406060506131511030414010806091e0c04050306192f07110d0305030f070302 72
    0x1134178005a54035070305051074034a072582108032500900c2180d00c0510300d401208810000c015054000c08510b24040b1076240381d660701c0d04011000c5480705050000d02c50f10402c00e4480c266001c2c04065842441101142c0c291901d4a07400d40c1039406881c41294543e02c95445c282d010310782170040b4883c404c1e141d083d00d00b95a00e080c0ca1a00c1d50003d81c40303511100c021a030700000d0000d6054002c061803039008541695100c0f4001c0c11181d0f03d500c21a01910324902d041404a01840e056007146c4c0c80003c81c1e14100d00e9581001072003902c44400031000024003002640900580360107102a0008101a0050f081003943e6040050000745005003c14801c8117848100440420788465445180603091039142c1c05540721207560300ca51046410690740341c071a52040108064840d525424103100d4082e052016400c50320701c0c13150700c02003e07540500841a07075210145200c2d4030030141000d24019a4040d0022010001252684c0c10364203056001a80c0007007080495134004000c030780c0100281c5000c40c50302a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 188426852 1250 188425602 188425619
    0x50f0411010c0203010605060a090e10030c03030f0e09101d10090b0319060b0a1d0c030a020409050a02041a040317072f010e060903120f0705100f0f0501 67
    0x84240c85241404000042642551000d40c000c034007400019101d10364030020703401c0c00b802c610386500c10304c6010041c810005401812900c080030071654400031100d00181560b5040c6d8111164030040d60803c980030840315801d039280002c480c02540b942d80b04020880c03c2c0071040c4000d0b600301802d221a07088613000d100305049011174031801c13968852000a0003202020002e4141110ec40c1c01c0d00d4000002c003621010b0000c2039100415400c0c1c21210306686590f6075004440b10680b601c01018051030f1800052648035020008541c040c40d0890010324203901e5004000c00c40394251341d2015444d40c0441c0c14460002c0c140110b0400d0100b091a160401d891640c1d0002464000d190246500c240801c9550030805840d0803a20380b00c0492001d400f406088917000c1c00c0d40040c0d11817990010b87c040140c54840c1c00c0000454024200107030103403c00300780c4101c9610340c513408010009501d2ba400c100220205509004003225031011001c0407841640300a07102c415100d058201c44051803070240100700802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 188428102 1250 188426852 188426873
    0xc1f0b0406050105190201020403080d0506090708010b030f060103110a020319170103120c0206030109050405100606020c0103051504110d1505010c030f0c170d05010b0307021207050f070603050a050f04 88
    0x5000302c19904917010000c90890280c050b0707600041c9010000b00c0d00709600c8072141c00c0a44555000c0c1e980e0890355583c44800c65450345c01384118890224104046020024180d00441d8042010b041c0400c1c08140e040b00d10070943e000b202e1250058001003100c0703802410b10319040041090741d24055458100085601c0407a08041c4401811040411310900310103000e0b0007900d41c2c2c01d4000301640c0d1250303580e40030080a0070040b0b60484840c003450070111842017980c0304001c1a03902550060031010540c1d401900100320141c00c1c007008058422080d403403569a40244609008500380c0c1648a0b10290442c5054841241240c103c45c01e49403014806640e00118036280c0540600e40001500501202501c9a1424250107404d00c112000034140f50030ba200000c0c210060000b00c100300f20780c0d03180400452404140e0300e440050b0003c15500c2418644030001e0204240114284c9407081d41002c80c05191040c16401a400300351100208400d407083c81c860158862603105041c0d41e036207403a949468851 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 188429352 1250 188428102 188428117
    0x907031a091e100f0c0e03121b0f030a0e0a060215071d03060103030504081203010e06090615030114040c0f0e040f090b010e1006020706140a050c1f0b0406050105 71
    0x1980780002c9807840304208000521400c004104019101404034600007818440d55440e0200e5080455034020307003400240456200403400000e812700741c2c561844842400c1c4800841c0d5184101c402d488504030040c0000c202039002511543c001d08051418007850b401281e0282066401c0091003142000041e5401d81e0301c245503150409441c802c03e00030081403c1d00c01d03c003030340620501c8000300415422500030426908658200c2c0c1000c4042c0d100341400b44000d0081440c44020040451083d0030861240c03504034800500c400113502481d04006003d810036404080802d511600c480b02901f4a0f200b050b070004030318940a8100b159141002d881003402e401e21038001c42e80c5082e40c401020089c2d11842c6810343c005e075500d40f0755a5032006960002d10503240340e0311188218030001081800000d40e04111521504c4005803c0c9280310f10448076001103492109005040010301030854060098000007824080508021310100303002004031402844001c0c0280d140450511043c0c0e00141601d094 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 188430602 1250 188429352 188429383
    0x108070e0a020f2101030b0a09081b030906071a0f09030910030e03180415060c12091d18010e10020c0c04050103080c0f0109021309030e0303030907031a09 68
    0xd640b03084040f1011803040c02c8000072070300b07041607103403512004001455048030301624807002e850700c0740c0e0b80400885011400c014201a010010085d00c00000c0c4003580d06c0c08051415282007403448004503ca59201c0b0034126034140c0c010310072200d84036107180041e8104004d150103240a140c96040d89a41c0c1c0f14044500d41b2036206032826103620380c8250000b03008511004150b0b52100c900c014078820902d000d5100500c11800d10401c0341c0f02c244020141070858046a88024409030203072110440048201c0a207401c001c9083d00100d01e00740c02441800704140e904411144510345102d001807030080810350502d0070390405079484441e04001070900030407400108016515204203902d149000c0c00844520342107410907000005210941016207000180c05054500e85c015200c812422101c0c0510000c2d4816650440c1140842443d44181da107180300b42040b1500009200c0000d1640d00200d48601c081e611018044c4108140f000c24030004102450a404c0703141014843e032034070740d400000394000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 188431852 1250 188430602 188430607
    0xa0c060c0f0228050d020102030a0c061811030d020c0f060d06170d02100905030301030f080706050f07180b0415050f1801080c180603070504090f020706050108070e0a02 74
    0x522100710919103030340741d00402100c8150b0032480f0700d007091000b501d1042d4241450210000d11800c24241c0d04002c40d605a001e913151800b01c95099841b00c0007000183d4449070382d02107034823034008000030310092035000c2c0103200076851181c000c241c5010f440840c20b00454111258044a5450b80000000e00c1c00e17084580a8503011400d004c0e80003045e03aa803050350300d209030003c180d0381c0074000f0540c018045d09a900741e50780400d203200211b0644008960040640d44104010030100c1d00c18200c550850f4402c80c440b51500600d82c50706001d8500541c1c1ca00988910703042404000740e0440540303401000303400c02c02e40aa40c40c0006040045c0507500c50301a460a41c0c00f0321401c1c2070f101d40116041c045254040316283c4100304480b07842c00c5410034034140452807840209031119005800c2d142895105002d12008401840034000550030142030503013405018800452001042d0140c006603060201005860340c440341003881c05e42c1e0701a800b125844d000408103221a4038402c08455003ca451980941d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 188433102 1250 188431852 188431877
    0x2090a0501030c02100212070e0303040303020601090906020702060c070504150b090d030216080a06050a1e0b060d0f0b0411040e040803090c0d0b091c0f03180615030308090a0c06 78
    0x1d0400804420195505e0b10000b0120214481104054080e901750354800c135000c00792a05056a920135400f014002da400700004001c80f01c4070360808075000388a550f0260600e0216400f01c0d0144d00b002e0b18405998005d42424021070809208010342105d00354400704d8994a0b09100000900c141e0744c07440c0c01800d566132540b0606008220864502c50307403943d0340c1e101581e034448190311501801012a8801c0c1050f01041045140d401004d0703500307408500c0844191b0305018442d00510744400c02940248080c002c503030310110b00e80304844408810340b45c00b0812010713200410048482c5403854251240f420300c0144403000d59125025489035110650743d680c5d0311071201c183c1c40d000c8403c000710741c8046144d1000b4200915002a24043c03485d85003110403441c0411081c520412840d8046000210303602c040382101440783d04180c0100c0021580d58102010075100c0c84241d850581c102c0c0755900c0d180004008040d8412001903000c002c89024011180c4155545981c15005104800400c0320514411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 188434352 1250 188433102 188433107
    0x507030e0a050315220b060607031818060e040c05090411041d0c0a05100c060f050103050309120601060518041b021605030319270909021302090a0501030c 68
    0x700080c000040442d502c10159035040011074504880c21070a003542c403106540c500c3d02c0e10420341d03c0c0035400040d2080a9031900d05204081c1c20038103041e400c0125440d01c02c544100950078800191403008100040c80c0d03960300200e401e440199200d650320529420800000c1043c0c0402403040d00c40850781c0349695104ca00f002341420440912165201d443c1443c0001c00c10940140d070343c86100e032081a101100700a404000344240e081c401d443c1c2003001a00e60982c1e0324820040070500920482c0009510900107611034120f038001d800c02c0703655a000042c0c0e40e5143c5001307050040c120820b42c00821440d0b0424a000b401d41c01187c81d680c1d405000d480c4000c2c0d8a681d41c1c1c0181c1c029604500c1c0780001c0c2c13000c08000a65602140c9442d218640301d80c0000b040c2410044116684504072080041020042c59001c4550b00b500001c0000c1091300c9829108054160040b820000c0c407050401140c0c0503004e00410019241a442c41c040051041003e1403141e01da00310600b04442c0c003401d0010b01a441104203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 188435602 1250 188434352 188434369
    0x1706090907080d0216150207090203060a0e0c03040c0b03090d030b0a090c080a2003040f0309080a0803070e01030203090a2d150b01050c060a090503040b040e07031b0507030e 76
    0x2c0c0744a03000d0080032101499000810140b803054024084c0e08081c4d070380003500c041c03186c0381552400580280e0002d106004994000b0b5030005005009144030660343c549281d52410255040d1948490020501c030500c0501d00700f1201800782c02c0d4030b191540c14280300407a5102c50f414040d00c1450780b62044a403882e0740705010140109802c031800d00044403030007001059103e00725540c101081ca00f00d10290044001d5242d9692441c039001d42c0792861700d450300c601d804c0e02c105800440400010700300104d0080c0e810300c01c40070742d18420001c40c0c1c4c0340d0601000c05000c407484203146604151050041080103100041d1a0108a030000c20049800c3c2c201a002e81004280040082c2848014086c040401408010311003041c100e030380c420001035a56000441d8188600e0100d849142d10580105290300d50a03030000c0c04031480345e030449280640c1e90720301031007a4000d5440205424224401c0140c502d030540180c07903030415100450b03c440544d0503005002406981c901030b0401085855405c0c07103072100004c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 188436852 1250 188435602 188435609
    0x901060f050f04060c12051602090402060405060c0a141b010302180405010b210705091c0f0c05030c0909030406050f130f03030f0e130902061b070609061706090907 72
    0x2a40d0b290b07120351001c5d04070390a90908448200b080c5c0350300942244144140c0f5200304042c0c880c00388951341502005020f140140080e0fa1240d400c10000480c2d07621003005103054800c40000c0c000400d014104180d01c03024802149a6541041e170080601780d074841c101c1e0090705024280140c85e0840812045624007514045e07940252070000081800021040980003004a84010850b5074030401c00201021f50142c3d06040420414041d42e1101d1501c0c8070000c501d0101c0d2405e00d4403054240d01e40354141507440c5001e0300e100740003220620103810184034800c00c000090360b0302c19035410001c80090347e03841548102c01c01c00c10085602c1070005030113000c880501400107403d04c5010703242c50421070241c1c4144000c40c0410011600f0a0649009002c103c15403100100049018a0890700800180074004022070303104104000071203c04001da1855407840300c4200017003034528103046000d400f42e01150440300903c507c40d80868002010b10481075802070040e9060605500e444480d9494144183c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 188438102 1250 188436852 188436877
    0x150209060904021c140129181203030f010906050103090b0a0c0306081c0f02060103030c0201030f020702060706060609060507020901051219050f1006180911030304030302060618060901060f05 84
    0x1510500300705c0301a0700e140d040e036414181d0b02030310306a0081085080d4000c071068001800302440f00908038121505594103100d0003510015801d6224081d050a40d442118010111600033005000f00880d034030404001e02400c1c2010421781c0801e484400070240020f100080c1d581d110140121124440d800105c002d0002c0c004031507135442c910320312900502201c42c000b030000c0d4110084115940c800225141269090b0315607540401d40e03a00110003a180100c102400c4540030440350005850300d20043c021715004000018a8a0800c00020480520740d88120100712003800150056030781c201005045490460302c486100d40e401407240d04000c0b0b00040b2700360a40c1860342e00341c01d0050204442a44164000a68018105001f43c000446000740079007070b600c084c2e08044880d46125a84080e0541c0c0c0a188141e00000100001916603441a0030072001a00400c0034803846007050000c281010000e081d0040292510501090003664148110002c008020000c541120301070300864110b1900380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 188439352 1250 188438102 188438111
    0x60b041103040203240412020118030e010929030a06080102220e0709060f0903120e031219080411030316140a0503040b0a0306050a0602060103150209060904021c 71
    0x1004210308503001124180e0107809281302540300d24064000380c100100d01106890a55140c0e51140f010b90240c0a4a10056650742d10341042c0079419641e003203a0340c0c0c0c80380e030303030b443c18a06a1800101126401da00842413003010309040408132101c44015408201d85138141031b100c0e5a0805000e010340f510786d01c0092503500c001030a090407000e41340090591109980048011565440c0c5040715580031258100000e0580205101d801d101d40c10b09410039190349807d0f024984c49446c0d420380c4804180d45180400c481c090501090b060a00900301001a880107031410044100c1c5e00c0250b183c0200c0181041101010000d802c0011400c0d010114060103030440351201a101d2840032210000318090f038040403400f01c3c08020940c00140500940d91140c00355013020b1800e0900d544540102c102d8206150315240b0106140c1c80e40540b00d0010002d95000f810b09500d5410441e500300c00070000c505d6600c0c0100590303545502c645003202e5040c2c50981d401039544002600390180c100c945100c512585040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 188440602 1250 188439352 188439371
    0x60e0d0b011205210d02090d02090709080c01030513240e1608060603070e060d05061005090c130b13120620121501021f050406110301050616060b04 65
    0x322285085400c3c440c0084034404d101541d8120041c10040c145507200540402c02c008042d2401d40280110000c050401103000805038001a002502105c2210019000000422500804220101c2d4805080c00d04100504081420b451819882c0760b000d0804100002c40b000c0e0806080905641d6415000040109450650300b86884401701c001d604105101034001042222002ca0301e50b0049000600401c5594074152580e44002c0004165a42c402442e00f103080114500b03103c1c1d1031150528403030700c40249042804010700c03031354007a203c0c0b04810750130f00a400d01222002064002e940d18035204546031400135102c888651055000000c0c0b4041d000b6020007040002d0b081046070120b01400644500400c0d410141d06001d082c800c402e4900181d00464407034980303d05030f00c2d040745040c419191106500c00700003004038646d401d4405070340e03585c3c8100800d005052141e10030082002620b2469949041e0001e1b90178080c07108808104d81685a0620030041d55900911710020050b2090024041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 188441852 1250 188440602 188440619
    0x7031103040b070501200d09140a0f1b0b0a03050604090c090b010807110316050309030334081902010b270609041a040501060305060c04060f18060e0d0b01 68
    0x8007030f08407002d601382040503c8084a1015000044016110503801c00c04540c074488090040c21005940d2a60b40c840020380340135042c8190b41c000c501803c24503003c103502e8034100f9000f054910044911381c1c40c804040c03155110104c2240c070300b800e41d031901003000e07282d050004004010300d41005007850550030740018014400c2d0030140700b00500340c80f6840b459860a405442211108519041c190010030062002d1070780c90107400407203130140084030706004520010a00c0c5034070a6a041d2040ca402e0b030304500b0414511001e80007512802c400e042400d078407030f94070007090340640b14801c4c945c6d60740c5c5115525098801d500000c5580d0004181800a503003071843d6807040100d08400c5a10b002c100000074030300b414441c04140c007541d40300c5d008140c121290300d05d15000c840042c20488495403640d200102090b41046120701490359050590364440c948000541a1084800102d05100f00217030b0322200302501c9548041280c2041c10242d200d0144a00060380b052000e0400914001c01c01d03001244095 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 188443102 1250 188441852 188441857
    0x601081008150708070206060310020c19050c030f0c010801090e030d050c04050102160b0a0309020111122106010e06090105041a13061103090f0d2907110c0607031103040b 75
    0x40303e40c0c81e03100c0d03141c8400c50126201c0d8405ca451a4140e4020b01d81460303583e42d294024222005000d068548400702c0905010b56034410440603205a4003610320452585001d02440d403031900080018601d0914141c0041c0c4a8141481250714042d0f8503084281510307402c1c0220760704035018940400607881c00c80c08903501600b00d80100c500522a50034130005400f250807000d01510701d291f005904040c2c103000124080d002c41807080741000b440018031001c4050030005001c04483c040d02d10ba803590b416081016224a2072040c4189440e410000d0210710398200c10341280c0f0000c00d82e90b0994981445005031514841d643c031021a8403410030030200007118200c068000c24041203c2d81110035503d91040395616040c00000240341c20820514116107015801075070b106101402c078440d0140b280d00c5000700300a1802d40491084a1040c2030341800c0e84810030282e0144090070800b0100061000e1955140d418403841d90103410b002034902d091500a07120309050501140481c1d0740c554952a1030b0541d42c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 188444352 1250 188443102 188443111
    0x1b0909050d031b050304120c020d11040b09060d0308061c060501080c10020714030c0904060f0608030c1b040f050108070603060905010b160204111605060a0203040b060108100815 78
    0x78030700340111140e2150642110b0320f14403030380d88141c04c68890752102401c940a142002c010f124407100c008005890300341540745131502a030140c1194003003080510003a20604601c1c0b5110341a20800c01c0708942e104000325044d17076007519040301c1070741d2400b012610800c900b41141d02c0d8500d00b0034103d030800c0702179000541685d0055050311710040706c1c2c2c070522407584161724411015030040c0000f0b1100c81c00d25080038034443e0300202114410740250001c80c00078402039a050740c895840d0903145c8280c296a000794402407040a00940c0380098190640e91604000c2001c0480400041c04414180e555070300031804c41ea961140400c91565210103169480703086101e11408079040c0303040014008203d01c5150b04a4618841032442d0500e010100a5075802c0c0c603508982c031547e2121200b16036080e00001d49002c0d81403100c1c1800c40323070792030500e41e140880c0104410310140c0100200000201d0398004607402290a0030120601d4662500b2100c942030150026802d920a403e080b403070152504e504d1074001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 188445602 1250 188444352 188444357
    0x90c030605030607052d0703050a0f0e01020303071d030313052b0b0705070b0109150b07080405060f04080d1e020c0d12140f0d050105010c0b041b0909050d 68
    0x5140e031103042c9921640110fa600d008903005000c2c03080084011001002c6403900d4010f242c401078004c89141c94a030b0010780c0b043d400640007150a541075600302100e41411125800d0005c400400040005e64900c0b00400d81410005555281c0301098408100d10482d42002000e0365100c440341c5820243c02c0e1180d2091510421050095a52070024071101c0c1841c02080e500d103044818880e103620010050182064040041c20072080010070f805c17642c05c42c00703031140d0f0001007000760f0300300001c83c500301040d00811084001041420000384080084a0440d182910603640350f0f28507201e07a103011b01403580118601c0c01000420300d9003c0d408405040820400e1030712100d05031f41044102d84c4c80c1209043c040c0c2045040140c0b00c0848c0c41d0b03c2c04d100c40010a454108a203946000d803081080e04a2801080040300105108c04081d6840c043c0a0140c03a0030b1030140e00c0340306c80f525820101e0401070005040c00841d050340608900540d4802070103401034042c1130200b42080d1400942d15081900640300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 188446852 1250 188445602 188445611
    0x3010f0603080a0323071b050604030807020f010c080a0b0d0b01030807200f12030409060b0301051305060a060309020a05040204030f12050a0507021c050a0c06090b091c021801090c03 80
    0x81a07404159501d4040e19218075401d02c0d60b602c100c07d41d0b102141d180741c01c8005070707000c18540000380b00300b002034803c2c0c4c07003980c801810341044c40020f0b1404100c8085104c49074100050204900e42c400d110030f52140c3c05410100d840300c00c4030003103030038242100e402801c13490880740003105228046005000d228410781900031904801e800b184184401d00f80203661000c0c1d82c0304680e2080c64030200080e10841c092041d2441c040c0d4800c6040704458030b43e8000c468060011004011920709a02101c903400c955003010f00039031411000054841d40680903050a25030707140d00d038105541360844424081c0030084d101710f5503030307031030b41882400c1340203540341203a00742c4844162001c0b0b6441881511031b460110b445040c100708031a400c120440c00d01e18020003101c0c0700d41400001249080040702407450148159845140c2000c400501042c1d4503006109504010003444940d5142c04003954011204080c0042002c1c4240c400102c56024094040c01824880b20002c940c3d50056806101900c40300d440801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 188448102 1250 188446852 188446871
    0x70b04210207030f030f2706080f0105010c08070503040e34051c02070803160f030615120b030a06020a0201140f0a0c1202031003020a050d0b1503010f0603080a03 71
    0x2a580c0c030040c000108444c0040345041c0000b80160030140c90b20030181000c0b800c500407542c90b4504407884440180400094000c1004100c1e00000b016400900c810b0007100d0643c181000a8801100c0c144000d0005000241c2e98081c00000e04c2510701414071800501ea15080c4000841c0500c04041c6c090f9900c000500040078001040860b44002110551101070801100c0c410201c1da044184035503080340c640030000c55000540f08d0005622802940112010351120004000c041c03006003502c0c4000d0510b0100c060007548235840c22440c400c0f00034035100c245a0343c14080e803c0901581040980c15200d50764040040180c5a00500001400c5600802c803a0243c1c2565a000b03520a488096075442e000300030440e4100c191304081c40240d071505090301508803041d48030040f070703004071401203250100340424011898000c0c119001030074100ca0340040101d96440340359001c03501900302c0355560f0040303440d49890b072429000074a25480803101003012a1b5a4240004245c2c040940d103000680b414803940f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 188449352 1250 188448102 188448107
    0x8070e0a0203040b0c180406080a0b2d0a1d0a14010213050d05160609080c012c0f0a1e080706050f0c1203010801150503030c150606070b0421 62
    0x40e48074903080a400e42c4c1989840c0000c880c2035004544007155402c081c0049480358071107000c0d450050149100070150855030b03041204200300064581700d811001c455441e42c045c3c03200e003885940a0100000000c080c1c07184a007802c01010040281030003032200012403024083c011603101c80041c094404c549000d820040c20314200d11402540401c4a06600e4040c040707130034074000e51504144540b00b200c00003400b50410314503000d5198000c100150000205010103030003401042d40c1c090080c01d1115401d03090b030060b01d651100e020011010b040d45032008800701d99800d10f00b41c600d842d01518421082d03441b12884440d8060060142100c12140707400060302c0100050458102c0705180e882d20306141d440c000e465a2a0310046120f20b542c4074807251141000c0ca243c0040d80280400000041c0103000c044200d04120202e41c4000d100760030500552802d0000851100c4a60180608918003a070b41c420010301c4c680901c820107050b01c99250f080000304a150401c48404080000e4a103005e0480d00c40e04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 188450602 1250 188449352 188449357
    0x41104060c08090d0c0e0403031503120e1801060201090302011803140f0409020a030c030e07030305180103060801021602031b03031206010c02030a05010f1103040c05120a08030108070e0a02 83
    0x50000041005001102090082d805407071283c00040c004c600b0850641c8500c07840d445141c000081451442051104258140c852201c82c43c48429250307403141d00e151605030188000300247c03424002d03884500d0a40340e440b08a50003406d0f01d0308003006500e584416000703000b0f20b5002c07012800340d842c00c0c546c110207500c1c205105804962550300d05c140c0c011580003a4581e0b800c1460700c11a1101c050002181c0f039486400502006551654002035803060450001c0075500309201c081c10a401100d428400b281e400310807034034040300505510042c04641c0c00102e0040c203181d84a9912540301265001c0c111b001c2014840c0414000c41c2203450000006004101c19031422040340e82c154401c102c6403003203051004034654802c0050618409507840781d0003290034403000740710448542e5500c8041100014182c483c2908141203500207a0443c0b41550320518031840d2809103e1069a010001ca100c452081040e5010f641e80201c8681d103d5039038054065941d0414000c45825481100014941c00f030640709 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 188451852 1250 188450602 188450609
    0x2a030f02070804060c0203240a05070503193b07060f020303070f030b09090d081b0f0f130308030105040506060307021b012015060109032117070509041104 68
    0x2d071518192405a0a503152003520900f01c0c1c0600132128440380c0484248002e041c5800100f9594440b8a0007400c000100d41c002490501800350500034401001c40000c00d6401d14000305c0d4000600d034405a0246101b018400b082842d0418616030091880c58000a8403003c074006500722002d003919602c0c00d86094442211400041c2e02c1800050700c018804d4107550600607007070400142c045201d002080704205e0480c1c4000c0700d0b45c8030030164100c0030f0f44540041e9008181d0302040341c0181c402c070007600b682d1191002084040e6800b0175207c00c28280002141d090202100d8042205962460b182c030302a0030034400c5a00c40c5140500040d10740c2001c000303c0b0320440040d405407400c0000110500c1380c00000d03041c11410000780d1500304440b5201c1c071508604100a100080007111040502d40100d1900201943d041098031841000003030304624201e440940012000e07c01d51001542c02c58041e4100203101c01c02a201e0001d01080640110080401a4064909001d120030050000d01b03688510710 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 188453102 1250 188451852 188451863
    0x6060605160303050a0b0603090607090e01210c050d0f0c0801021c0f2d06050a050102030a140915040305010b0406032013020d05010e070c0c06050903012a030f0207 72
    0x7106800000d200c2c0d44a26400804040c0024071106058040b4540d030700100c1c0c0082159010724280400c0e03d4100b0200c800070500040c0c039042660501000d03d00701030210703400d000d2804a4a40c0601041601a406c4d40a090042d040c800d1481642c1408402c65010910986548240c0c103030210320b03040d040c000c60740038440d11001060343c2104601040000d044090b01251000e541c1c1d000d2403d912140c100c3c141a070b00b004181c140280040c00d00070004c030361241e440f0611988001008101c681d8020003502d0743d810041c01c241340010810341c2040c1d518401c1e04116641700304401c05002c2c01d114203001401c1628000d6000700481d003850703018801252441c1c04094850b808000b45460354101035070b001d0f1b01002014001a0f41c1da5407264050b810382c0c0008069540d465180c02c010303c1081485d00d113055014882d46021109140c1e90b4440000300302c05402114104180010f1400c501c2d03c00b50080408039202604035807035030a000644408101c2000c01d280b00190800c4590300e19008603000f0f5510254105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 188454352 1250 188453102 188453137
    0x803041203110102090a060509040b0603060f0d020a0f09020304061413060507020a0f050a06200901030504020604120516050f09010b030a06030f050c0117040302060402010c02120d03060306060605 86
    0x40e107080d00c00014103200c0640390b640800c480b00b0140c59000204004012940f601c80d03c0b013140ba01040280d628901e80c8a01808086c01003040301e50f1081f41041980343c0030381e01070801603460b0006c20360166407600009181030141d200055181e001d90b000b58440c500030b403001c2001300e464052060707060070f00b65003000c201601018400b0118030b03a98000341c6c000340b0500495040d400c4550321424014250303242640c46401020aa40c188003440c0103c0a40d00210300013011010036140d003044c1140194071a4504045d40c440c00030341191220320484000c1c0c04214005c101103085494002e507504031035201c01d10090348121000981d0b0500742041d0a401d50002c2c20444ed070307800c040030084c19400040c00c800649450744000808503031000720420300103004901404a01c03007648001b4141a01045403000341a41120402c00860b60100d101c5402550901e001120100c0500006012510b00c2400d12441c1c0185803c0341440c0360160f008400700d80c8156810310030a543e501c410f44281c001d508030141e484044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 188455602 1250 188454352 188454389
    0x40c050a080a02011116090213060327030201290f010e060a18031e050c0a050a090207031404090606080a0203150607150501060e0111070b190215040302070f080304 72
    0x6548656043d60710728111200200f13000e501e054500c1b1039920003070382246d0004821484080c94000d00c00606a01d007810b02415040c6008003500d04081c29448040400d825410401c240c401e401c40d0003a1004600c0028030750102c0041d102042007220741d094403841218001d00407075401583c4070740e4402c070010328080c241071800b081a29405a88038032460080804100400011100c20311460541c600401c02c1900158524189141c40350211000b0302c9a40201001c111644e1083c0c10582580c09014000d0381b01c240501e004c1e500090400f00403402c0003808100410040929405141120860f644059850f20781d0040b080c12403106a4200c24501c1040e1500421403d15500806250344a04040160302000140328400c40728280c0180c000900e0040b06501e40e5a0311050551400e46100041c0c05950b10f4001c08080520540c064150703091600c40c00c800d5642d00030b01c801d045e20121802e20904903d098500203442e8902e500441b40045100840403406982c00030a481c1691110310002c40a07444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 188456852 1250 188455602 188455607
    0xd02010834020109050d0e0a0311040b040614011b0203030a0c0c0f0e060405090f070e0c0903030d200705070618080102130503100212040204050406020c15040c050a080a0201 76
    0x40c12154100c501c00c1e07624460101d90411140c0c4420049250b0000030702002618106080c0408205a84104513082d8507115441d501d000b103440840e80c0c00015850803101100c0410302600f440301040d64402c0c0b5250000510317690101c9200b01c900807d90302c212121850990150140120f40000b039015031052201c0030031380f40220617045005001d9251900f5190b070701c07034603140c40c01941d0300800c1d124020b40c03090084030304290007184d421000100142c841c0803154a03a045d5114104d00c1044c80c4d881c440c1000c1820b20f10004220382110a015040c0c907a0740780b403045058040e0a50ba441e2840480700c070402401c14012040139a90140d0788007018080c1c03907203440d0b4201c0d40180c0c660381070448008100000961403000f41b004010814001c1d16030759049280c001094104050300103a003800c54010000c0200004280080b60781c4594100c400241c1a251030038030350001d004180d10482a0f1182c442010001d00e58200d031180b0031403041050807099512a0180010301506100f9802c49601490b80c0350010360 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 188458102 1250 188456852 188456881
    0x13080403151404050a061409060a050a18060218180703020913060e04050f01020a09050405040c090603080423180603010b04060b0d060f080a0210020f030f04050f0d020108 75
    0x188500e002c075954160050703a00c0705240c191000c503155404000120104616405a0501d0f003502203500422850158051501c070743c1c00030064400c0a5175800001d5000740680d101d000451b004a5081b0401c29085c03410500070b41c0030b042e0000424060b4007070540a0b103020400720000303541612a03c1800e07142c4101c281c0c06504800301e15984028109030180d03c240c21441641c0042911361080382c0c0034201418018100b1044443e01551030f401044410315094110105070200c0700240e40005442da590300b880c100c8111981c02440b4200d080c94400400e00060748003500c142c0369400036000c1c00e081002d017921824040302ca0b1094110050f07000c800c42c8600315800c7c9590100303000d00045901d110540c0018111503c80d0040a42c503040400c24401072500c5205110290450403003203a0b0f5a804c0040307031a42d9401c3c0755002442901001848022103200744110802c104601c0b048948480e0504201862a0424000c0e640100e005008541c024a400c1c4462001d07190103840304400c0d6101e0754980364104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 188459352 1250 188458102 188458133
    0xb1c0b040b280905040b040201121a19090606081f2304091b14030c0312031008010c03090212010c1d0a0503070810360c0803030a0c0813080403 63
    0xb00807480e0000341240759409070502c01c51140004141c0b40c50584005444034641c0b010b5110042e05d80b148101c50081801070f07102542c1c204031003511903181c3c41c14051052502d04e40020700c0f034a0400f000040e40c150092401d50080b8845104080c00401074003007808e044489120348052603854039142407a00d4629013400882110240010601c0240d03030b1514584410002c0100d10b0b94900f954080141c060303a00213520104104501602c4942d0940b80081d9031074900c031a001c2040d8000002084804942c20520001449540002e011504500401800800701c0d684183d00440050003003001000041c8204420342c4899210f046c18811a050003940d004032102c0100d400c074101400200d80b59030200042d8000301041e038014110440413403c00c0c4280c40b01d1207040004007502c2c08101d06c0e10400d0780301400040f440c01c1d00101d1920b145040025801007030340d00c10b0203180000000e104400b04039800c071842c840010f07154071409882e040d000c003400020031300307001e4585481880144001800d802e84400c14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 188460602 1250 188459352 188459419
    0x5032a04020f0a0816090503030315010302091804020906010f27080a08040f0906060203040308130302092508070c081803010212011d0c0d0203100b1c0b040b 69
    0x10190a03600b9018690702c012072680125030410200506080c4010344030386403401d58904154190301d44004261349000203400c40082c48414484025164840c3d03060341c803100c4c0c00400304441600c24850040c0301c00010351b0164054440c820005905502904018001d0426580c0d140900e24080c0000088202010000303c0b040b4241c680000d00c0c20b0040009004d105d01900840d41e4a9280c014000c041c02a10390210300041e0801c102005210380100640e001c0381d0300140c01c1551818400020344400f8555007000758494400001d01421842e152a04034109440d4184200e03a151040d4081d5545102105c05070001079140c0c10100000b002c40b00984221500035a0074015005a00300003400e90b0046411550340c1079555004028a0301c202e441720b078240c007035800301c4403140c10a102c0c0c0054510452115051f0b054000022442c20340e48254102c00510301a0301c0991030f403020f02070f51517101d80504411a10a410138410800b01c3c0340520504824400003414803007446055024008103089801c0070240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 188461852 1250 188460602 188460607
    0x51305010615080a0b010e010c030905130207031d0a05010c0302010e0105090607090e010e0103020405090307050706030c0f170105011119030c03030507020640080309010605032a0402 80
    0x50001d019403030240003516190249000c0b01140101801c800801c03400080c5e00b810b80303884640c0d070030082c00380311042c0031318152941c89100c4c01d00b0b40d0802e05952049420441011000740b13401c1c507039806130503d00c1c070940d601c56124540c00c00290310761540c2180180d2058000d40204072a41c040e16a00d08594440e00012035840e00e0200000d0849408840f220300a80002c010420100c1e400782d10701000c1d000203040c003000383d4100808a40403980c1408024040c540e1100880c0b0384010810940e014254000c003188e4074942c40781401000344c01749000f01c0010901040c829400a40103200c43e8a00e00390701160700701a131303181c040115190302d05c0100f04101401009080c806d1000c030091090a40c0b40651503c20f03501600d03150040490780010715903421500f084041c0700202480c15850b218807000c074084404040c40000c1c5601c2200c00189080500141c00000102045040c1c2c014501c135a840c50300800c001a903070414075407030301c60700009802d01c850044140c180e50008907032113442e2010301410060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 188463102 1250 188461852 188461891
    0x30f061528052b091a04120c1113021605010b01030510030213112503140c0303070c170d0b03060108070b03070c03090b0304060213091112041119081b0108060405 71
    0x4c17048021040320721000d0845808010a00605002c183d6071003020340b4201c054807025480343c2c07100302e48400304a032040b26001c2c034140000b181d03a011703205072010302d210342403140c42c2500d0400d008104005920340032a0070240000c01d844254441ea01c103e030b40191080386034401c984442c00080c8100212001d040c8018000719180b9440c4003032489403189960508450f101017030501070b141c1303400c4404142d4602800c10a0004103000402034903000000ca0074150303064402803400c40050501203610550420010030307181c1c0c0c000d01c80d4000140d0010300b078003900d0150b600d810415807a0b01041c0100f942c2081c041003c00c8070f4602c10324007408114041d01e005601c150712100000318580c03094805590594000c85c0c03403000e482c4100c550a00802000900b0050003409080c035051500904013100e044589400028091055501c4525001003000b4521017400f811211101c415100f1805070005078896041e10003003680195001072000c101c1610341c00301c541d40d004200801340400500c40400c2c5210042c661 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 188464352 1250 188463102 188463113
    0xc030d0c0b0c072906100c080c0a05010f0213090603020109061d0a061d010305070818010b030a050f06070c03140901121406040b01090b030f061528052b09 68
    0x10403c41002061900c03043d214008103070f444c00307488940715005d4841001040740c4c2145c04100b219512031035a6403a03041045c1d6042c18500f0b03c031806002542000c111029401c99a4018a000740b00080c060300300a40703c1428004a0780c0300d010081c0880c0c14040b0600c4440d0043c00610360f0f0122032400d021107200305502040300c005087d8000004589620046680b8584014114858200a1804000516001c4c400804da00e1014000b0107442042c9012070f04d42c20000e420900c075541c03004d4110b400704102d03443c0ca40c0e1344450180c2d0003640c03402114049604a8418802c0000050f007698924204008460450f061039000505280c10f01c80803400004640d0b0807802400903001171500c018446240600034130068a6034080e84134104511154180102812581901d400229107001c0d850744e59202c102141c410013010742e06003280c100110f801005404c00c48024201280000d90002c21449481c2081d1554000d00681951980c014040f540c400c00c42c4404080c0e00446800700030900808c143c41d80c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 188465602 1250 188464352 188464373
    0x60c09120f0c120d09060f050702090f040203071e0306020d0204050301180b06010c0b27100c030b0f0619030612060605030114190e0a0b07030b01020c030d0c0b0c07 72
    0x1641d0b0440c610034001c6140070811207036400c00850241c00000320300600104256041e01984040c440d130410091062403284040d80c400741d034085c0403a032480c00c050002c58070016044404030300c01c0c402e000001c9aa44c101d261041e0b20b007102c11250202c110b0865072201c0294100000c4a18026424000054a668240141c0071259081495aa0300c2d400c0c6050400320134000602460501088064210002d0603e10310917902000203905000c94406501150500504c2140700d90100d214101c014003100781980e2010590051645080206209603801c0c010182030280b412903100b034040c401c54030452150754091001d4652403500080243d15400c07025030501e2110415200d165907240184480c2c1000d200d24051544005071420316454a21226188040ca1007541c8501d213840782c0041d010341e141040b010031b0090b030041c018030342403600001c000c0081c0300b44004c00d401032107035440c01c2c00d49081c0840e807001c20f107401c0d540f0050103030300745e03103036260503840181c1945001402042882e0108200c07049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 188466852 1250 188465602 188465623
    0x150601050f04180c2a05101b080108150403030903090504110a031104030f02060705030c060708040b060f091f080d050403031d03030a0804050a020a081606030608060c0912 75
    0x40f0055260310b100c40c001181e210800000900000303a80c24020840705100030f50000d0b84030480300020301d4580c60300c0341c03c110481c1070000301c10707080040e089120344103031406144850f45a600c0040c1d507a41c890b6043c2c5e844103030b6206081c0401d288004a40801c0c440c2e003117010028001d0811912030f954600214045a400513030091503058042842c0c2030b102e03414000d0030f000810800e03450f0300706420740d00e9170000c1743d40c0004000c0c844c2000007041000c21205100b66004000400d00751055031410b810041c00e070318012a0212501007020300012a00e191043c00b182c1c1c68035003d840040a560303050300c2e0110340e00d02d049a00d002c2010042002641c98010401c071004403000b43e680c41d880d1851468090100001c0c03030b84030383e103200929500c4107442c0c07400026611000c2c024588028a9142ca081582c1420b14101c8080c2d000b03140000085001840010108804440b4111085071680e0340d0904504440b8140200002d80e0030034000710350705a480070050004424000e1580100f070709450049480c1c11760400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 188468102 1250 188466852 188466869
    0xa02030d0207090c03050105151309020d0911030f0a03181e0305060f0c09010f051204051b010e0d06050403090503030a0201200903060f07030f060b03090d030905150601050f04 77
    0x22003e02402c03207a0701410440d0045410148003039414100021a00380090648242800d004610f41c0f00754881200140f00501b241c0070f04550303a01c140b80003a00a80b184c2c11095070380681d0480d40c503402d0f04000804c03000b801c601e0f602612003100195012503161822503900007014035402808244403d14400c0e2000b0241903600000c0e12500c0d62801d41e09100005000700154801d44003003007440007080c4105c03491240240fa060110902108065500d40540503801d81c1140c42001004104440020404506504a00410f4220b0051001100c809201c11141c80d00900d58a0146000542c2c0e0340016400500c030303040095030320303813150003003440d6421201300180140e440e1140c180c50300c1038200c015205d00780002e00d96450481d503100802d43c0c0d040041c010b8a0305103658400202c0040c0300b540507400036030514105100c41c941e00c0108007019002541d50300b11500a1a4607084924003e104024540368801c02a201e100d65035554000351300c1001703110038140001004103c1c08c50b000355000344054000103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 188469352 1250 188468102 188468113
    0xe1b0408010c11060109060b03040b09011b02010b09060f0f0904060921080912070b0a0b03190b150d031b02130e16180905070302060703090e100f03140a02030d02 71
    0xf508980d10b0700006910001d00795207413003c1446034038001c604507a48240c01a050a61035100c0c0c00c1101d00510003480500e01c000048000d01480350b03819040550b00d100102e850040f00e4485004214146103844442c0394070440940d0b00003070900b4440e0049a0040c020200003442c1912034603a008002c040f03021140804511070b40d400364050304107038215008030b44903000b401d039070f90b41001002c514800d003071000e480d03405060000340d0548100d8016400103c80502503402601d0307081280394180314140000c403200c0d030707090300040c0e24060201c8202c5001c11000b000c1409583c03982e00c00752a0140014510b0407011900000900580c44902d00050030f0900701070005a4600e6400c0c105040211002180804900c0610208100c1d164002d07030a07090780c0001d40c0081d1241842c41c060b850411b155000030340204003c0740d10028035411100a03030445e083c1c1e881400840d0f54841c68810303250031902480c070b00c80d0303540c10b801d101007103080c00140f000f001020111122300101c0d03000a860154400040c00059100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 188470602 1250 188469352 188469377
    0x3010308190201051e13120809100203060a090e0709020f09040507031a04050c09040e010506120a03020601060f050d140106020f150610030603140a03090f0e1b0408010c 74
    0x1000341c09a00e501e940300030441030500c0783d20300c50b132054942c4c5880b034041c05400200b03030340c2d01e1042c0072403840c654010404242c1010410300a0441603088901044a0058400b0f5075414116802101d2140c80c000b40400400c9090848500040140700c280341002d20900740003048200003480107044060201c4803554a03401420700700800c2c1d80303000b407440080505080040460340e8004102d02e980c0e60341260041403a640d00c00d11800140101450b080d4002d0600f504000c0303054041d404075005800944018000c01803851700343c2c3d50303200d40550060050740080010042c1500c04c2a00c040c0c520110315151380740561000b40e1100361511210714030503400c041401003052075010491041c1210b4840060402c3d4440c4201181140c80000c00b51402101607010711665144694052405140d111207411182c4068022642d5594031a0300103e0104048403808203d014081002408a03178202c151300820781d50740103e0740c02440d5000740200f01c249d024003002c0b404480c2070003103800d8502c1c1580c03200c03481c549 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 188471852 1250 188470602 188470627
    0x20c0c060a0215070306060e0409050c030a030302030412050a020303070e04060302040609290a0506091206070804110a0e060d0203010603050609160e0708040816050d08010602010e010c0e0f0406090203010308 91
    0x1d0b10740c02c181446c0040030804030390000781004494004840001e0303000001e040083c140911030038026810300914490100300364255000e58041c0340280347c10b00c1107400d405d0040c0c072180b00b80000203005d82d100b4030014a45510614454504142c003a1010403000d41d01d901140540d0500e0700028041921422010700f031480d0002c0031100b51139100c01100c0320140d040041541c90040f0b014542c040c0a00151401813030710f40482412070000c8020480e4014508810000c0401c82c060300c00301c450f0f00106105102d41d01d004021001230312032505240895440301404c021000c60b40c20001c0b030300340d52220000002b20740c1c141300381c0b0306c240d8a0b50050010202000e400c04c0d1003030096000310102004040900003625031280c40070341c3c019032024a40703940310803041c194910401e907400002c1003827051441c0803074641d42c80711405049840903002400000c260399078250a9488a03003c605c001100030781d00c140c1e2450f101080d403540f2040079000190054039001c01c4030a036030090b0400e48009400003494170701c03d00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 188473102 1250 188471852 188471893
    0x25080f0a020d020109020604120f0c0b13080609030313140604060c1214010515070602040909110f0130020408030a020c010c0b072a03020105060a09060f09020c0c060a02 74
    0xc420f84003c001d03208082d4001201e5000f24028002c801e00d6401410040203170751041d000b4a1504140050842907680c00704135100d0740030018000054850a10000e800000020300c2c5005d19400b00c05182103035982c2100c5008180085c1080d1084100c55a40080c85030040c01814025409620045040c2d851004040c0c080da1100f8600d080d45450450190344600e550101181911412540303441c0c420220840200c0c18056031401038030661000800080d10303060b0f50302c00c103401442441400408000d10041080c5809000301141c041100c01c0c0c03801080000140104400059406800d8201c03030010300b00b03c049801507084644203a0002030906c92558040140760320b040c4091a14103a80c2c6070729542c04402c13240140c40700050118084a40740b5a440f800315810911010303a001c14014411400c000780a400f0517500e0b2401103100200110f603d900c80d009500640350000a00403a251801c1910030003540154050003484c0030b846502c400c2981c4a00040000741001d50061040c9085102c0521040c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 188474352 1250 188473102 188473123
    0x6071209080304030f1b08030a08091b0d0605041b030b19020408030f030a0207060912030b040b0f0105030a150815010801020a0c061505030106062c0625080f0a02 71
    0x10382c000d100410018070b4000320b051407503512080c89140303081c80442090140c00950486080e9001c08901c03040b4070f80d03101040d1407149006000700c68041c5e030316902010709052042132080e0820b60044c405804070b02941c2101c1c0c0c000d841010020704a95000c142c40300c540180703810840341c04052606115514400e807103801034011035503004625191501c1d13515503492040c4402481c2c8800048009001d02d034140e0b054410194106000344000040d42c6040501c88810008013400b091801040d503200382007a03c18031103603150141000e880e54001c2401940d00d5000102180c1d1500d4407101c04c0c0e5401390f21643e8240060212000a014086807038403000449036052b00400140d0b03105001d41f072600c560101c4130031103043e08850300040d164502c040c03040d81e103d02e07904210380540c01d201c0c001940e1b40e4020b0036107248081d0345410000710b0484140040c4c0c0e2401d0b04c02116440103003409400e4541d60144500540c00203181c215203924460340d44d400945402c44006020510000700720169100d40500100081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 188475602 1250 188474352 188474369
    0xc060609070503010e070c06110306270705160212060402011403041a0406090c06110d020a0c090527060708070c0f060f0f1d070f0605160804030206071209 68
    0x5240606000b811400144036126115920f007020032100c5000b59070b824104d540044061002001c041040c4030250300981d901c0d030050322588031000110382000647c0451540300700142c00b168030748034000c45482c0c1205404000e02941c004039800107941e910013a203104164075010307044a1400e0f000143c000051032500c44e41c03a240420400c000102d20383d2a40c040c951468028610545175410560014081e021000385003040c60040480c6080e0000c101540ca101c0d0901240c6d40c00c0131040d401c9840d4014594020f01e410580001441b01c1c481507000950300585c420312500b01421320746282c2c0390211110400803202e03080790301070001b542d5100c158a45d11a075181030261703100040c1e40d58482d65210400d0041d00b43d96540004450541c982d800403160f00c44015414009080d0004000b000c003032101100d1a0307144500200007405000041c2d44804980180d220a801d092074401c50302000080c140d000c0b44d603004108030200050340c5d41005015224002d000641020185030030242411600f500032010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 188476852 1250 188475602 188475619
    0x17131d010f0806040204050403170f01030507050301150504050601020a050616231b0115030c0906090e03040308071a0c090907050f070204020c0106051c0b1311040b030c0a08030c0606 80
    0x2500b2400102e03150803950569002034030781e6460070100c401c1c0c500c0108004030703449030700c0500510042380c3c64460305aa0140781555100f6603524105401c840504070b50500c0c2481d840d1040000d0300e01075102079031007001030040e2914040b9580e00c480c213180003200d55011885454500b0790300180e0103625410403c4043d81c190848802e48007400409005040e08041c1080c0060048083c80324203400c4000210780d000f10203400b8a440b4500000f00000c40d00410070170074986000045e0044090240250980e5208041e514060468a81e8501544488001e5440c21003100000303050904c00b1002f0744c4500d400b041a161242c414004000085e40064426402c014080c41190559903120040341d03190303a812140140da51a131001440d014044980c41507900600450084001c034003121152036120b80b06070078048071941c42111191202881e00005046442d07074025403a9a402c0561114210700001411203e00c540361900040342a42c00742c10090300f541020550758040c032410407040e900100112410364 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 188478102 1250 188476852 188476859
    0xc070605032a07020d1b1401030f02090a0501050c070b0d0518010c1d0a0302040504050a1505040b060409060e0a03020d02070e0c1206180a021b0303060102070317131d010f 75
    0x32054003c00b180030348075000b5115564200221241320505150560300c0c402a4240d48003d110b0b15812401034242c0400d0804076201083d900c03e00c00c6502c0c1e1440140010070940c1403200449940d00f04803401000b9200e148008541d00f540c54000d40303400030310044041014500409405442c0001c2d41c80d2161303580c1020000c1003a640c202c50075030300302086880c6940d460313842c450000300c10382925030020f50014a803a060001340031000c2961602903001c0c800c240c5c1040c0340300b4071520441e0b8085402609145404001c208645866000404c0720b41c010030001c01c025112100301400c09400d440100c025030301c4590f1144106805010703440050240b00c02400303540c030b84070020048510504103402c850034525000113a0301d60701c0300c600c295411090480f04c01c1c1c07440c0502690b4000d6008600c210700d0184101c5440c04803040002c1107078407030501a806407800500d507541d580d204490700114502640000d1045100c01c00c6003420388002003c207000d13042e0805181f500040c02158040e00106409141c911051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 188479352 1250 188478102 188478181
    0x7090501170606030703140c12010b0301060c021504080d11120a1b0201051e030105031e0a030c050c060d1a03073006020f0702130c0207030204110c07060503 69
    0x55120000303694213a0b07242c1d01c506048004122402c0c1400309940301c44103000c0703d03006a10103001941d402d4110134440d81d0301d644003602d00740001d05c220350019010103050401410440084084c107488625600c0c1429260803906050100d0050703208002035100414561031007041005140410941c0140340c80c1241c6039500400e006ca94240d600c07801c04900d80c1c20700469120300c00700c036031800480080080004409400c010356620a11505200c1e00c5441900c0c80d02c1750518250f01ca513001d05000500d1100406d55082d1080c4410a809484900980c3c46080423a280e520080400c142101000520a040b103680b50f01d00c4007880a002e4004d0b486100e083c449040181c0c3c1c41c51210801054940c1c001c0f00e04c00c280c404480d031112004001c0d60022490400c041a40d401500403507100300e5000c01840c40045800e000c55590814580069003c03103402c1001d803c0c143c1c01490705001180ba00341c0f8000d0031100702e03071402c14103a0001000800000800c1214a10301a078204081ca42e160340702d5540603442080c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 188480602 1250 188479352 188479397
    0xe0909070b09030f010c020d0201140c03060f04060b1912111c0608030d0b0f030c0604171c0f02060f060a0e0c090d0b0a15081b03030d060e07090501 65
    0x540140c844009000d41840d0f40400c00510140302d000000d001c10396203910b00940350b205980b0100301541c00c0000307049082110b828520310416544110a040d50344a400300510402c40c000300d29000f42d82c5140108044c08028000c0c0690034612546101100c0340703450050120020101072441103190a00c801a4160f0900880d8501200804d011440d00000c107460002041c0c01c3c2e10010492000140380c080c0d00280b60805602c0329011942d0510050038401490344541d612440d40d640070400b001706010b8405448400e00c8050003001c11249882507104100ea64030900c80b61500c082001408644540e9904200c0194003003402c40b0060186c2c2844808118280c1481c05880300b40d9803010700180c1d260030b5807016200c2041303004000711081c10301420400c03d0380c4c0c025070300703d5000d42c104034003200303101e0340544440c0480c0c448000502d1841c3d401d8902c004040c266440075941808108840c03162495140105c401a006240c4542c80a00382048068240d215540c0b001c1c0c1401840d2001d201c007140510310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 188481852 1250 188480602 188480609
    0x10b0904020a02160305060604060b190f18140a06020703123510060f0203090402070204020f0301080304060e0108070e0103051503071d09010902130c090302130b010e090907 76
    0x10301580782d054044040c0d01309402414081c2c50001525000014071a001502d24091003090701e0400a03a512018201e141e44990022100904a40a05205120300c03644290341110010318041c5095003503040452240c1900e03900440c81e00c003103090741840038a01440100c00410031030004080c4545182e5680c0358843c4420580c0d02404100c00d45055101a03200103940a259040c2c4c8c0c451126000803003500034040d041c0c030309141081c60500042400c50041d00f00300c40010080e0000d500700705034201003101135400300200301d800036001d1080307202c030ae41d03114095806444560055910b841c10000001e2203c42140e030b080707040182c20414880300300d40004034100a0f8000380303004a601d507100c15400300c7c3d164030030103829054480d80c980000c000c0020103c1c5032584800d00040c00d101c0d2603442c0803c5c01d032001000060b503c4120750b03030b01207001c0c0c0490380401c880603c64140394040d2566a00040c070042001601001180d413204044901503902803050808070b041101c2107030007802d2002c0c845031b07684480d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 188483102 1250 188481852 188481859
    0xf05060a06210501030807060b100c0602030a0f0c050c0f010c1e030608030a05070b100303080718030606092c031c020d0c0c0b0c120a02030604090c03050102090a0e010b09 75
    0x1030214452010b000c00340d00a0030181d41407005513501d140080c0c15520075002030b80c0c21440c3c00000c1c0d40c13520f00f110061b003005515550b8140c10000f140c81d00d80082d80042d0030300850b10350751820f00140711a54041c01c0b0100013036407103a075222040702d0642400c15286114800103070f450103403040c2c00b09402c1a4030203082c07500516040302c860fa104c40182e00506083d0051102e502c0007140c0e6080c82c650020041c150148201c1001c0303c55210907040705d00c21640c41c01300401250b80040000d8490703200c0d2049a103000c40c0480c0121000b82d40c0c2d190502203441e180c01254503291500c9007148842d540d030f0301c050700030360301c40320f00c814480001000a038503070040e0020099002c220401e1183c2804a5030150381c0c850025000030004111001c601508000c1d200000300d58110406001500003031050381600e824a00300041e1040030743e2040301c450000e500081506604c29a41d039404c03008a420b4010841c0507511920005a4a010540030410750181c964044041072110100500105145000b9a00c2c04007098 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 188484352 1250 188483102 188483117
    0x60c0522240201020702090103080921030318150702100c020609210d0e06010e09060c400806091609020306010c020d050601050117060306161e0903060f05060a06 71
    0x31070100d0282c496a00007030342c4908480004420300484038028035540904171030120b030020030511140c040c800a0034a00500360000e00000e1150503c280002104480d0141507480d202c110b0080d1200c20402540e40800591140312802c1704064a80714112091115000400c118034107800300c241d0343d0301031125601030001d99881c403c02c4078821100fa01c3e00142d1060051015540a541c4140c5d100001d00c501c40710710300c515012505990b0041072140c01407200810652502c10400820894800084080c0c414200b0760100780d6010034940b0b40c240e0682840c040548a100e19102286e171400c0d81c082c0407500c0a810074215011040074242c0484121550350380050780f241e170f0703402c0181c40c01d880742500650449010415242080000309038603050f5442601c4645480140800d40000b0500444216425502000100e80d003110951307990111007415140450181d540c10303960005d080301c014014004140001c60600410029000d19001c980c040003041040d440d0170300c0050350301c0303055210303080030322402 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 188485602 1250 188484352 188484419
    0xa030c02030c0a1103060114010c140a1707110609010525050304030309060909090b060f121b0f03030307051914040e0105180c0a1407060c0522 63
    0x910503951041610003d9074400989810240c4110000032a210301c81e000300000071030660f6848299124001341070b91902203084041d0b84041d2640c0c15203405076654071444100c40001011803034601c4403186113450154079402d071450200725030841400d09502c1000e084c040b420003a40e20070140d440b8810064018980e86243c115254502c00b0b0100019081d80070001c0c0100605800510040890b802540c0300c41070142d039002c250302101e0500c82d0080c0094441c0c00803400501d025158400551001040e0b1303c040c203800c61101c0d242c405016452000091628246009850003010711413180c141030b005180b9514060301c00510a1088000304507012401001405615104039080503841303a0b4610741d20380d41d649980d0000150328007445014071450102c240702144001802155000c0e00703c007c04542070a07000c541c02d580c44080004400203140040c400a00803e609008003c64a40d45454140c0c0d9003010041403c5040f60000e0400d0081e00e4104040280013041d400040d6080442c0300d010b07541031203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 188486852 1250 188485602 188485607
    0x13140a0b0f130c1202190302030402060919060201060506131203110a0503040f090b0904020402090114070f120c030e0607080d1401171b0603040f0c09050a050105040e030a030c 77
    0x308407030802c1d000701024400a05a0525510070243c080c0d083d100c0f08000200705000340107034403e10851100c2135141d11044003081e030203074008d1038115100800c083e00307244525003ca8040c9482c510b611010410a900402034560284180405003600b0369a841c60400c844e91035008002440c81100154032155240b481454400c400700200000703903500f40d440340b80b02800c00f41d0340c03604140180e10700189aa0000102c060700d6209a100e0300310080d0106e0f04642d140c1e001c00000f0f4110300001814482041400105503110400a000c0c16124040390315040500341800e01c0c001140e0034852052141c4a8418804241c0081c020f407014030044800554030421440c02c10298004c01c48001540c0b414544600c401c00c00400c0c07602d0603113030201d8070700f002a0340061100d50303182444a4406000c194009080705141045002941d001b070040300da800000110382d40300c40a0401c140e0208c0919036460040c07142c40303001d07800780c18010301c0201c0e014003000c2c50340310019440b8410140010b050580d1054004912030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 188488102 1250 188486852 188486869
    0x102250519050f0601050603071d040f090b0f060d08040b0a021f09052505040f09020612041502090604060e0f22050f0f13060204030f0c0513140a0b 65
    0x411040e070300003a52419150056903009090b00b40020b40c012000017003400d050200644e4499a82655407070310400200c0ca40c00c002550b0807051580050b198408640404264012154424428001c2c1c018610300400404c0c01d43d00c010748160300c50b001d905d00b1400071901000c155000d0fa000610318a98600c02c81d0810317450f100d0030503240c0b210340610b201c0c4408401e000d503005404581c002c0090300d540401c40c00449034200c3c400800b02550b01c85070300061040d414258044d41c40344499034400106502590000b82c2e043e00182440c070080100e141c00c000c100135070003c00e200031100c00700041d4204181d450000d409401a07000304410007a21031182180c40d60b031480080d522040140c4007101407880c06980f682c20b070b07803e100c40043c6030741000d010030303140e44a6448643c85034a03805050003d03500c5503006103909001ca4a000c2e41c130203800f4440070000c1900303801e05000f400e2203503a11551541c640740c1031101503004418200d070744d02e1400304140d400342c500b807848541c0b0501ea6140082c0019039080041c000c076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 188489208 1106 188488102 188488123
    0x180302061302061b10050405010c11010603020105070201030f150e0a140609040201080c0f0a1e05070b010b130b03010b0c06130f0f06021209011d01022505 68
    0x29130302000d01c0035400c55600c00e0b21250100380800c070066032800d44041d521a599400351001c11030300700c0c009000b860502c0d0b000f0302002d03180d0b0300060810b02813958042e0500d61a8480d06120000030742c000d848042c4c0070100c0d071038a25241c0507086c0020b00110b07140d02d4254504840e030340c3c2ca81c681385011403054000130404501c59541c0e40c01140c034010050042c01c10034800703200ca62100c0361000d0161402c1c0b17149a90715884032814001e5441c41c0d403031450340081400010400703240855006801281921840c1900e80d03036403040442d04841261703480d0302c2007603481404400491110100001800a001203100715040c91f03d54009080c81d04074071182c02080001034021031030006501c50140b030941400f5070401420b1410075400e0140009003151114010f9654094003101d24204492074440140814021810700c501c00c04800111200e024459103190100712503441006020070440245 = true := by decide +kernel

theorem cover : BRFrame.Cov 188309352 188489208 := by
  have h0 := BRFrame.cov_init 188309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 188309352 ≤ n) (h2 : n < 188489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
