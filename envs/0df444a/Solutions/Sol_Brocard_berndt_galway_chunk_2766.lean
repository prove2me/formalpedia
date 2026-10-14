-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2766
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:41.541817+00:00
-- url     : https://prove2.me/submissions/7e990adb-e4b3-43f1-b541-553beaa4c293

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 497302158 ≤ n < 497482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 497303408 1250 497302158 497302177
    0x122c0c09060f0d08030a0c0f030b10080c1209010207020306070513091a190302120f060a0213081b03100b060304060b150412050d2c04060f1805180a020105 68
    0x40c00010003940c2c0c8100300d1708100d80b03100000781d68001d5038000355045059412481c850b46410414004030380005810381c0e840c401c001040107030721070010b0b1120307502800725000c951800322481602d10700041c2d294040c0d48103000481c001e0140b070001c50700b0b00d0300507029201d8003800d42c41070b03030055400d1080d003d005101a400c0d29081081c10703e052030803500d0310318603038495110718078030801d04504600501040d40010ba0412401c0d40c0241390038010320801083c20754024903507140160f40c60117050740c40000c80ca565004002d41c8c0c0194600203844410720340030b0401c030b9a42036055a0100400107072130011101102d0040d5007201e02080000c001881d160710003540001d0060240f01001b044008c041059001504803080039104204545d00f401001c0103541d01400c80c071b00d030000420300c0381c008045081500c940008059420500031036126a00c81d042003000d0882408205e003d590340b212184900e441078070b0012030305842c000200304c404607a052000404420000104000d8030b0302d5004403036550194030300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 497304658 1250 497303408 497303419
    0xa1502061308040b04030f0b0f090316020d0b0106021608070302150c1e0d0207120c0515090d0c170708030a050a0327021c05120a122c0c09060f 63
    0xf00300704201134040c1003c2d5002d007510350440b000381e1800f14a0607201411018803811010100104c060000040740e06400038003148991041092011030707001c84c40f00350000c007010080750001c00d216a0000c0d501c0e001c03a0082c2c05052481d9521020a51600c096000c082c1d00031090344024004a12400c008210901e900411030745e4000b2221807510200704c015070915030580101601d20085036040000701c016003820b10401d5600f40c01c0ea500c15174440401c0c0300d6280641e00b40e0500007810154042698122040942020000324040ca01a012040f00307008060b00354005801060000e10002034040c10344000c0301c01540307050707000501921650050340d120b204240d1901400d42115860b224102a4480741c6581108151840d01c108400d20103c4844600c15010f552103d1000c03070030004520b480494103403802a0303030b40c00c4448106d0b4000b02c000e50b841c99403070600c80907003510a440c4600d80407811a8400c07580204005030f042e41c0d110f441848999510241680101c0c0d8a807400c69035034170640700b00a06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 497305908 1250 497304658 497304667
    0x60905060f19020d020c01080114090601020f060901060f0e0f0a050a1808130501080f0420121b060c030d02031e04030e1504270f06030c050a1502061308 67
    0x14058001d902c4041c03400058200303035114585550100040311402209003040c1c0800c1d03040c100d814140031140001c0c5841000c0ea840800c000b64028402c0c103410000da4402e503001403070100d803418080c260300d20030881c1c080c2420343d0024002144d400c8890081034050b424171150f4559060035805058007602c2c4600c4c0e15607070b02c01c003401c000740040402c694602c11a000b42c0c403101200d4800c00761070401d074040c5040c030040100f08418000f80942081c5d00550118195984505441124482914010800d9042800c50102c03130000c840c001078624402d5030380e01d142d825034292441444403034041d07494000d20660044c8400b0100118540165511600580e0007802040305030b5004410180d082d941540411090050300b0000e050003803144288040b80d00c8514a03007460014641c0450320215080c005402a8a00544036040290421207212861203000d00805da102d061600c10002d00d0b100781c0b8800d018207040015164070010341509020403076009442203a480015400c0c84c000705200845010b8070801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 497307158 1250 497305908 497305927
    0x6060f030c0e010803031003200a09140603010c0e010309111011070614040519350c0d0f03051c0504151104060c060b15090a0906060905060f 62
    0x161000080d40680c0c90101d40300d00d4804495020807041c0c20a442542041040164020125240204503a40100c88100c40e4590701b4814028171080d01096902801250001409645c550007004207455100c15662881e1600c00425003201c0c0d9511f030300004a501c2407080c024960180c0e001c1c410b5980511600503141d40e5280014204032003c0d640c00d004078807003003c000c8511504024507005810a0b0400c01b81e0078408003d605054040c034402d451003013403620a01e03a0b1000398007203503c00401c2a10221766642e0180d24626050428001c20303000380460072820a1181c110003c2e80010650340078200c11450f180b9512070071800000c0500603400d200c01003203413400101000720240b60b01c4031007010000d40da0806241002403002101020807081d41070580a0144840c1d04084804481003400c20420002c1d440c548080070b450507460440e40056180e8294aa030045c08006180148088409080568039810303880100d43d241d000e07640c0000c4080e0000c0c4502d0402c20b0081800401039200c440c20150f811 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 497308408 1250 497307158 497307179
    0x705010909270602120f0108030403060f0e0706030506040b060f0a03090807140616050a02060115020a060504080d05060d030e221a0102010c0f0806100c0503120405100203060303090d0606 82
    0x302c422541c090b030005909030b500b0002600e040d081075440d40c11151030b51410205958038002c0b4040500b10659510316002c1441c055400142512510000e07516007030b55401000c1d00410701101c5890007541405000784c11850140121610602c00c00c1e546801c001340804120000c00e25400200e5520b032080180c3c1c408500100e1121481081c80070003440e0034984100c20121080103105113005028080c02801101a0046503442c103580e52112842c90282c0c1480741240b41400d251005408945400709110500c5004002001014040c072010300054070380e903042c04010080144007a0000d8114110030141e480e2054015403403165807030702410701300300c0c03100741c00c2c11142c80d44000208228a55000d610303a580a005003000c0d05200d0412100d9041001c50140c9403503001404d982c0300d610341e846a040000d004060015083e50030504503a1581600d210407080310300c0030f84040c0c072030384501d41c6220001925402103911907140a00a14181130b03038a01400454900d044084031015100c003004030310341201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 497309658 1250 497308408 497308481
    0x51308030f0412051602010309020f150309010b030f0a03031a040c0f030b06130b03041719030b0607031205090a060e100f0b0306040803042a170705010909 68
    0x28101d042040c0c201850314820045041d440e907420301406105000010b40c3d12281d1590f199020308022a200b05075200160507900c1681804c3e83c0130707500b01d8421810440d8107000d14403559004000300310364518901019507501d55292030305007e5002100a00c000303440380e08074011100f110003e0141407218800094161411040d102000840300006250556498001c1c440900401e580d8689040d02c10030000c54a00050b000386180c00000002080402002f00f111485004803811156204c0c0c5120b4404e40149540d070b1020b00c0080d0405524a00d00e01d0888101c6170380c0341e855210940320980000c1c808001c3c0200a0001d4030340d004404045000c2500340c0201c00b810035668000d006d502d80b2002d50141240c1c00501e0300001d180c0b0344420103003551400035002e0741040c2c1003201140c403669140b4107511104044100520700001c4200240d02d20300c0c50a40120030390708040c0c0c0307803100001c080100c02d60301c4400e845010b002510102d02080b51440c82c0d0b1040ca0f4020b1010642c1c01c0b43c04600c2d4522454524 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 497310908 1250 497309658 497309671
    0x313231e0f1c17010e072709091703010e180307060509030301060306080a020303030a0e1014040201030606020f060705090301020c01021b0c030d0c0b07210509010b0d1505130803 78
    0x40d00c0000b40e0150700200d00c00750410600c2c0d90740381c03d50601103030584a03003000300480e0600c01c01c0c0440c0801610030490300501c003903141e103c44a07003035121032840001e0121448101e94115050500340040401721041e070741607030480300c182006507613240e001c2941c011150340c01b891207001c1009810042001402400d1085007a03100455407545007150080031503d55034014102034000302d80d103d0040c0d0300031046a420541c070b450041420590900386906154081400d00002850140c90700c07150b47e40d440f00750344164000d80b0b08000c01507a03000107070b84507134403150319500d075801a10000300180d010783d000d4020302c807024000506088008000c1422a4480743c00e50811a50f132080a0000d40020800c80344002015005008844e0194001030441c14030784500404044503500001c0419200740b10011010315820b201041c80304403651510010601030750300480c02d50a10401c0071540c00d10f81d045070000c5501c40003205411501da90175070020640035007034040c0340600c00c15102c0820806405940200c0c2c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 497312158 1250 497310908 497310943
    0x180a022e0e01020d0309020f06030c0f0703030b012606090703150f050f060c0607050c0133090c0c02060310090e15010e06011706150313231e0f 63
    0x840c10030003e4601500746410100301410400c0e1440113803640b40c03584011982c2a00c1541d100c3c0c542801506140c0075280580861203404188602490f91541011300340c4039080e200c20326101d4039544c40c2c0c41141308640300c1d50200d4922401192460030301a24641e40104c0d18540001d2001c0d007042c0c2c0c3c6103444a00c1e48098809840300c24180400e140c0b1499481c0707602d8048400a240907d101800c0391036081c0140858180315010902144901080d0001c807940c1858165844445100001e440600e04110030b1100d1200d440340c1020900717a16512840843e011661121002100503a003000352aa00c0101a414540ca6103440003031074150074090314250700d02c13000c0580707180d15110300000d06606059025601c00480801807040310703604040c500000c045e5030403059038140c1d258004203d420481d41508480c4079400010400c035006003000310444584a03003400031440d103008500000d039555002c42000daa82000390f425415183c0b0f91040a000700500007521a000320894225080001d140d40c180d0301071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 497313408 1250 497312158 497312177
    0x1403090a020a0b2505150c0304031b0503090f04060e0103050601050102060f06090a1a1509030f060f27240708130318030c09020909180a022e 62
    0x500e0b0040d554005000010545030500d01c144100c000201d803001c0740311804040515622040c000709019043c0e0b0501c500601c810141880450a03c1e1079204890035000200580001d0b002444000d071003502c4140c1081c02507051455520400c02d0610401d007107260700580e038840c0050200300c0381720928000c500490180040d5031402e00068140800104041c051890910400c111703a0755090005800170012100020503401143e07030b000307564031409034140c0d108424030142380c0c3c83c001c2c1e04000d022080c01a07080d03c0c80068210780b150354548080c2d89681c0034007039074130004403c100b0140c040b500c81d00c0f035406180150360400d520181480188500b03030007480c0d90f5003103141e2014080c0c0d20140d040490380c54400f4540c502023408107201c6d001100e00034200004c02940c252580c0d030f80d19548010396000000032071440d9540d50002c00940c001032100d402117281000081c1c0600c0c82030301e80c00602c50b01030081c0900d45525070801543c02103200e0301903103402d00d080c0104441c1a035a5529842c510a54444e041c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 497314658 1250 497313408 497313413
    0x903020d02030301080706080a020c190c060c0201050d090f240c0801030305270604061e0804020109090f061706180f030703050c07050613140108100e0402011403090a 73
    0x51841104800e4155072082004021078540020a8800c80300540b4201c0344c2901e030000480080e1242614031005071140c1c00700e901320055002c00302210503205941103090681e0381c90b004c3c0c0b034840203100c02030b010410620684d07080315103a800c58030225201c2c0d6035030700c407079001e0f0b1b0398a60328038841440b4007510074082e401940f518030180c8212240b00d00c2d5414800c0cc6503140d40e40040c070034460701e40c00c409401880003130f03d40c1c4500e119101c800c055000600c280e482e00d071160001815400e842d9100c00107880c04401105403540a0341459000e0360301a598528594240300c0350a0140085440d012841591030400040700003149102240b00801d10b0041e00007400c01d032030b401043c5400e441c610456900802d1010a9070a800001c4485190385824507d440e8002ca003141c40c10a4034682c4440c0d040100040d11000742d600b0007486109131021280708107100500240110b41000085401e64842000d0460070302100d400c100545134007910501d04401020031410800c1d0250b00300350740d0000b00c0e500001d042c408 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 497315908 1250 497314658 497314663
    0x13120302070e091605122a0405010f05010e0111280209070e1c02040b0909030c071208040b070f1520090f09091011130803120109050705041206090302 66
    0x4003c0c07035400040400b0101e558400800003424800c0c6445101201d11030032040c2000e00c180419113142c62a0030008102c0b410513000803050000380c5c00d10071860b1a00124501c800729100506642040e910120200b90307490065840b4030184141d14851b1043d11240c02c115594803006031345410f03005041240c0001a8814130890303040141021082c0070780a501003901c1d40b99281002401103c4410602402d51030f8000305000704014030850750040703940800c00200c414008010101d4001c40d00c201c896143e40d41d00c1e03002d01001c030743c48020140340d030404c82000304500740406401c000d0f00a5850f00d01e03d41d40350703640c0c0401c90b402d43c01c044111a1a40c901c021811310302840301c08407040d40b4911074640031200740000c0034441989021031140503400003080c400c000801000701c10003c100ca04202c250352016581015410584207010070680c10b61011480103404410340b08174020001542c142d43e401d1030044c0000e00001880c1d0420000e0921001500d5901032140d000240d02540c0e00080001c41810002d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 497317158 1250 497315908 497315911
    0x30a05101515021015030506040b070e03060c3a0606030e070f0909030e060a09050f010905030a0611190905040b0901050a120303180b07200d0513120302070e 69
    0x6a202818401e002ca603140c010070a600461020540002c00110340602d035404003501d5080580079201d000100020001a207603024081c0441e0780b40d40140d400030070101907a40100320b40c010450031081c0990350203a00c0300c00c100030500164124410702070310320400c6400c08107103000c004a50b054884108100346501846500e00a445c0302002c2c0c100d490504140800385c203000d00c101c459140d502d0b0805014544200c000c0218140c000b0041690740189100c014a80d034401d01440d0300c0f56919040c940000d60144042d40c0c202e0b58041d0180c4000a100e840d81d100410006050058038182003182d8000d81108684031440466151925580282080284021502940301441c0034404010051045654030741c4880211741240040d006001410b1500300d010f00740d000104461072001903d9102040350458486101d03000d10740d02c008007600d8000d80c418041240c981c012505070080d8030300c000ec0300d1051008011100d52031200051940d070305c400340e615040c600d801c10383c0107810000061114012024905 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 497318408 1250 497317158 497317169
    0xf070b091e03070605071b020f0a09090b10050a0e06060a091e0e090a0f02100903201206190b061e03011716050405070e040c08011401021605010e030a051015 69
    0x10703540e856103020301f00712944090a010b849012128409500d907900c842000c4058506080309200f09101858501c40d0001e0917240441d11520703000700031455090443c54001110592890000f040e1901014045154000001c03102045a1820045a03040c2c41e0130302e6440140d418020041040d182c0040c01c04843c001170494502c4d60030480e15000450540520075510940407074003c2c2c42d880703240340183c4107002d0701d500081490031900c00b032400002d41a000000c42840a072240500d0311612034400340c0322001240c0c1211081020082c0c02d88a210070341c8038108030540074140d0b0303292581c0001445900da0507900400d60b400c0e40000103001080f0700390202c101242c9418000c0950360500c03904a0780c110b4440c0200e82c007403907450002031103a602c260080d03040800c000e402000301c100d4941c07006004220902071440e00c12001135010f49203504c0040c91808103c4000b40307015410b030420004403400025a40c00743d40c1403013010700c20000300f001480407151a542c42080018904120304005a0706520b65012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 497319658 1250 497318408 497318417
    0x210907060c11040e1005010303050904180b01031e080c0a11120d030b061603020d0207050a030803041e0209090601180e0619020f0406091701020f070b091e0307060507 73
    0x240000e1580d00d02c500d45410807200800c01d5614550000c0c6810118000c441c00541031070000018181c1110090440420a54003031000c040d03003401c03041c0c1e407048000008003007005c0c0000400116140410b0060b00c0c81e0304c4020b032040f4000940350001035401c80c80080184d600b2459040c0104654a118400e540405844091501449200c1c0644490565070110b0a06403904145a510394a030b0342100d4401d0a00c9803803038007080090900070341d0303684080c0120026108081010a0618100140200701d980c40450b0034510f99a0f503407035514480d6040110200641500360150050399900b40e06440b5440e02e01c010f10556240501e44034109030007031443d03000c2500d01502103c0078040400d845074440780c004d484a604403134000780140240b0400c00040c0c2581404140410100c1e03204101c40100d0300c811492401c2c000700965490b080740304400354584a414100035100c0000c840040c017039804800d11080c0c44c01cbd8845140c580207401082045c00d0305a03040092907034108201445003e13003001e1245403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 497320908 1250 497319658 497319677
    0xb1b010606080112060213050a09020d050603210c070e130506070309080322020619030614030c131509090302010507080f01050d14030c010e0f0102070b071421090706 73
    0x140020407614030b13038007602d05c0d070300000c92040b0035204091110007000c1c0688901c3c080c1d652080014004d40107201c0f4069418180400725120b880d0000c0c105c40e2102011100703a80020045a035407407141c0c040180301d0f04601609000295002d003000714540305154210106420754090f2604c03504002004003c802498a08406207000c200c004064030740c40f48940e050380041052500d4211000c4503da04000e42c400800605480705e000f11a5100380c6040781610180b140300d884070ba081c01144003020b10700d505903008030560105850803072854041000d00134000034800f001e141034030080e00800d4014009050b00c0b048100e00701036091099592011a0f490019642d050064403511220710600c00c0034812010301e0255020310450035200c0e504220420126507950f01c400707039407502134803120101c100039008503458921662418021079009607070202003510b01d6611500c094034110000004403030380c07000c24000364070076544550010341c510084c1002e9907160f1508861191070010640c20410400c0300c09038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 497322158 1250 497320908 497320919
    0x60a0204062c04050901020d060b0f1207120e011a06030421032a0806030304060f031a12010501091b0503060f030a021f12021c090305040b1b0106060801 67
    0xe401c0b4050300d2080c6181d0340001a44a0a0030810035010034030f920600e031070140300c503910741540108048200c503002801070344c0d034540d0701201d14040ca034201d4204901c20408800030142000c51203601c14458100280d210250f4050982211020381d445980740c0c0d0340e0210f5200c1032240007519080c140701265003c1c550700d0184e40d150a03201d84044170844c15181d050072542d20034000d400c040c40c58205198000034070190381c140c00c004019001c4420011551141c0400d0751814084121002e45089031540b0800c1d444d41d54048008240314200d2400130807101d00140829036540c0e0004103000ca501001148a5040c20b030704a080750516281f180010209440c0c04120710341110649900600c21501e0300031440400300844c1c2002036041000394003468010440188c1c1e030500fa01c1e00150308003659602c0c8601007201c45541248500c4601c640d01503040d80001c2c805008030b40225070040d109142031030805603143e9500c046c0340c21174810b00318405034049014107c4171003482980c0040001d854038520552510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 497323408 1250 497322158 497322167
    0x5040606050d0504060209120c10030c270f06020c0103050907180f140c030106110321090109050f031c060e0f0c0403080d0f0c091410020c040504050d02060a020406 72
    0x5a40701048140c50f200090103003c900d5044c1d8405a00107400040c81c80c5131f40f9403040d168003031241c1e018030a80803007074100c0b0518444e02c920709480405455016003203100c40204000c40707240481311403204014880200b2000c400001c444000e02c0150000c00c0c80c02510340c009020380e14020101d54240c0e0054008119503034140b0120344600795888000113202e4040d4180c40003400b4117240851810324a035042c04000052403000714100c81e6656035080c24803081c4640c1a849108414000c4940c04045090440c0081e03001d024640207508000009100e0b641caa0f0b0b69402c010302e4003204240364101240b82480c0440a224101c444051564200582400e0a4003a8071400c0094000c100a1b944400020070076048403080300c3c09160007000040e140c1e904440c2c07003009402c540541801072400d003401119114000c40d00803050b130f0f90b0000c0c8d509041241d9010b0280c0c0f014404640340451203050805140c644642c800c0c0341c0143d0190000e807842211100d8041d00e400c0018040d0341d0214410031040000544c0f1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 497324658 1250 497323408 497323417
    0xd0e060f040321020409020f0c070e010806010312052701020f010608060a0c090b07121707020c04020307170c0a0207060f0f03020a09051306080115060806130e06010b03040c0504060605 81
    0x2071415601200c481d4030500e80090045d074011404c03082c030028103506220880c2d00a00507840f018811581840d48500c20344400704000e11408005621080041c03000074854904052040c40614101d828a0f541200300c01c151100d060b040c540d03d201d90007411505503410711905012000c0b2070000c0c8815884d00f00143d07528440282134040041c3d5560ba0580403a1150210400030320741d2400c403507110040e81c10440c82e070445951028001c0b8184407000071148440301e0105101d40619006030041e18400740600000e54030007081d00d01009001d6032201c0113904042142070062020708240c0ba12400180d0020740f80400d40d811010a00c00c80740e000303074401a80b1016907840d0343d003030b850050f0707e8602d802005c0d19050704a400142c1d0120411031104e044112a40c4010100d6104800074402c410b1031012280d8002068090280081c01d13110010301541040e601305480c014a900d400240302d0940040941407100a070444000f040700007040c40180000031141d04003400e81100c0400540d407801d40c018040c0d200303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 497325908 1250 497324658 497324687
    0x90307140a0806090606011b020906010e130207030c11010801380f0d1401050a0621020313030906091203030e120f0702090121020d0503040503030d0e060f0403 70
    0x20640e25050040c0c6894800a0042c4000e108071800b5003441c3c88010b03105c1c242103500300c0c0007607084078519049080041d1180f403582d8010380f5079502c9403103220044500188080d80180c220b81c2a1444810740c0b10b60788002d1a41c540240e0300c0f14412a61494a01d200c0c04170914102e040141d21070051082c0d20440c0d010401c050182e00e10340caa40300000c2c41c01a4004440d094003503100d00003207880351800920000034141241d24603000c010514000303a010b07a00f0803081c001d440c0c008900582c107000e41c0b4040d002401c1c010000c400428022298040711406070f078000c41e40d103120503240380e82c21010150002c0c81140540302c0d42c00c04262540c205600190f02c84080c11001c0c04040c0c59403000300d040d000501c82c507440180945092503441d21042c200c88000c0d0b00000003240540340b203000009102c280c050b60140e00300c1c5034140300c1411044980030003140c0e4030300b28400c1d500c0340400c02000070310383e600700b00410115508200215030314810b40200303810004000d0260400399110810400000c1c3d12034408941c008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 497327158 1250 497325908 497325929
    0x9100f05061605011a010e090c04060e03120f0a12020c1002031302181905100603021315030605130b0310051f03050313150203180f09040b01090f02090307 68
    0x508812180b05208251440a0880d519102403843c00581c4282043c80c200c44c20b8a50000e5083c242c42442010a001c030340f0100c49010500041c03295510a01a40700b04a40c01000c03a021400b656441c90400d0744100b184da49882e0b00010b26428082e005003101c00c0c0203035503000071418560a0b054042d2105402d00323813200400d074000001400c1e0fa00040c0a44100364010300f4040070402801342000e600340c0140c4070380c4040d0901d50074118055860340102c604c40c001031034120301541d00e400f1043d00650004022160f003855500d1011800d81c405055041c0049144e540c042016460034040c442503003030352290b29042c10308003820307041240c900042840c120303103220740c0000d40750b61100e01010b1816400a4492096542c1d4400081440f50000140c040349441020805003169107031110080180120001009a001808071540c00b0400420070085420090403084c01814074071b00180c04400221811900da2004d0300c01880503941d00c2c402c8440b13404000c08210311302110800040c2e5107221318492a007165 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 497328408 1250 497327158 497327167
    0x9060d0c230d020708040801021c0b0609031b03280210140a0804150c030b19050d0813050a1805070203090a1205010f050c03091501030f03050309070b040b040509100f0506 75
    0x700c007006c880062604100031034465a4000c09083c00d0310703d0320f640000d0141000b001380c5061400004940341110001c000340342e01e00c90803141d12a141d5401c41c03040e9160103038200c80c3d14035541c030155084502c020b4150b1680e01e060a0f00c1000307244884590100100840c0b4800100c40e00c8c02d010480c4c1d140081801c00b003c0c1542d403460031242c404108501c0112450610441c65216030f015000221007040864020b03400228000090b2125600c03841000c0e403010390785d031000c00800c0ea07000080c21003a860001045896864001141040e00c20340e001760456015100101c0f40d0301400c2c41400e0b0406103e1001e5403403c061500042d02c181c040d8014112103075624800d1b00e007041000d41c13148401240c0700200340309510700141420882d800c1201c58450718015451082c405c980a0491a81a642d10a03102e0040e20301a48080768543c01c0100f10f02114450090042030078450031000e04014016004ca060303544e81001e0501c260694040e10740706850140410501c040b03030070358601c1020344a0545000703484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 497329658 1250 497328408 497328413
    0xf030106080304091416090612020d0924060509180703020319050d0c0302030315120f030d0f0b03071502031e0406030b03030a0c1709060d0c230d0207 66
    0x41040e68801c195910001400050510a50704a841e0f18034a4000f100603075903400075445502501c00c1504800104928018000340d40540090250b1000070b101c01401c000140100340211035a090302500c01d100007143c09069010340c00a50011040385800078402c080ca0b01c408a846094090505440310035001c01c03080352581e040000f40021900101141d05140c4c1c41142100743d01c248200a40b440c0c01444014900c02d8094001030001303590590066103582d4425800c1d01e0700c1032210101b21390004850341081046c2000f04416205802d0104c05540c0d2140d1143c05d540071680300085401100c2d0800d002180c0940d00410310008880030030408005a10303d0500480c10b510405003140c4415802a104003c100c4031780317028105071405a10100414401602090380d01d0240303007800c100140c42510359000142c070608c0d0707440506803c80700c040c1c1080200c20006101d07030400d54000380d450740e8802c1c0000826501c442d072101513109600c82a04034000c8080c103050984a06000345010b1500041c03450f04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 497330908 1250 497329658 497329661
    0x2031b060c0627030a0c151404110a09150b0703031d0307020a09052401230c1c090e060a17031801090f0e0a0e0f07080609011401050f0301 61
    0x20141400d10648081e072804412140c0b2903c001010309400f42c483c0c030a42142d042e00002296840c1d000d03600c40242004490382c48030001201001e00c00c261603161422001c0b1130f120f08143ca40a10300c603032502d20028000c81300b881784506d015030010001d142041c920034801c28505074040260794010ba201c541c0d5104504040d801b07000c03c02a00003601c804080c80340c0180d14044050000310b8400c64643e201156220006c0040c0c44c03041d544d038001011190541103450355043d605600700c00041c14030b06000c401d0b4000c2c4200b500c2010800084803d4006058503c442c000e00c4440d0030000c88030444070004c8910000189000c0c000d004042015201101040315070380c54060300380c010050040010100d011070250b039078490704070030348a0600859003020101030350b010f01d80060a903940200c41032103151074456200710304031000d400f00300c0c04c07a41c0708032001d40342d0700500615140c0e40c155170007000780c140340448052404000900d10481a4989400421052640744a16044500c02c07030703c00480c10042c030000303070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 497332158 1250 497330908 497330917
    0x1061d031509060f0a0c050307051303050706050706060b0403050606130b1f020105250c020402070228080309060301090e0f060702010c09050301090803040204111204080403060f020702031b06 84
    0x2a141c41c0351010814a0301c0700040d040c1c8500c1d00301d40006503a8070340040e4501903903842c81401c004035034140001a40741b4403e0001c0c080303104064030309888082ea2a100d8506040d84c0b5040311000813800580c00c0180181c03809500020301c426400280381030b19644440d03456401c060300091180c245c3d102c01c5200b15003c2c0d0890425154011711032030440107038001251000036003030314200255080000168204070313600c442600108848228000b00c42e18424200c0d28240700d950304903400340e428450980507849210900071030390841e050325500215a14000f080c07201280d403010318254400c108241d5107481d02c20a8a044415446003c07541c01c0f119420a0b081c21005a0048003910440e4100031800e641500414800b12075038a0750407078a5100d4040c5403c0e290b030b000c07001d007840030b007040800c00504003580401da1003100d58000c203040440d140030050300841c7c00c0d581901c94100c081010b1080c08105d1003054020420f9070700c00c5281c5103a990100391039070400b00e080710100c4451409161640c44040403503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 497333408 1250 497332158 497332183
    0x10303110a080d0c0905030c090c0a0201110c01200406090506090621070305220b06030c0a060f120902030a0f1704030309030c06030c081b04030218040204050f01061d03 74
    0x300d80f14112404180c0c0148000354500c40001c08400000a040c14003003000003040c04040c183c014181d450b1079520b00142d215203408001c640d41c0e00c01a1181c150008054034040b0010400841c6035078540c0b8514170800001c0507000720b5040e00f00400c0011031f80284006080791801c0d03c41c076460f03804442c006182400f81d506013844030000020a11894a04401407600c100700d40d8800f0011521003800c07150355000c0400343c00f00c5502030340030000049022485020b5002200900f15080305106030045071603040c0a41c01900420742c0d000464110b2500f150310350409100b1290100015149500025556011010b015000030380d9610303800309202d07404104409882c2c4258100b6916507480c60000c2003032000384001d84030301c001c2142c00300d02d4901ca80a641042c484a954640c0d80b40c0311012800a04814811400e0304190208000030042c0c031980300391191507150340c1c00000c0c5468140144015584014a100550744044005004580d08111150b030212400d00c03d0380004003400d404245041c1e80304080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 497334658 1250 497333408 497333423
    0x260304090905340f18050604060f0806070e030606010c021212031302030705031b1509131a0307080d050f070c080109050d0e0109120f06050a020d2003010303110a 71
    0x18401c020115041e1141507000140241481e5640c0c110300340014055005d0642c507550400058103152805402ca0741d000745004000140041d941d0050501c200c0d25640100c0c2250451005c0080f0240c00105003082500305a026080c20300d0904002031440111010003841040f8540e03a41e100040308001d07501d01d45480c0b09249949080500d100c2c4031000541c44101e00c02c0c400c1100208580c200416003420081c000004098030507955401c0040c0c11902114003510342c0000e0040c0780050f560b0b6220300c007034201140070009901c424243c601801c1c9800352803843c0644e10880003084207040002d010b094404031858819103030010824181c2e4940318400d0060301d1612000404201a94103600c00e81607680b1550844031004528a0180e030314540203e01c0c1404a8884882044290484108070000d90710500c1c45807011002980c2e6a42111001e031103100c04941d01003003600b0000c00d82d00c1408a5551190100c44125002e440c07250454441400001c0c1048031654448140b17040c03c021b12406260301a14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 497335908 1250 497334658 497334703
    0x7030915050103080903010c050403110607030507050613140a0b0c0c1e030a03150e0a110912011413050709021315032301081903020c0316260304090905 67
    0x10804e91540020001e24840d5180c01e0f55044130600450481e000c0f6540841c50a130080e2260003040500d0300b24030810b5050045c200205000a5020700c03d4038412249442d0340300050782c07031342801c19102d907a03107115540e542e0020111501081400e030f05107501480c4040d08590b80d1a41c000c0c55400e1a29500703190098403d1980c0d09450300070080085c0c000110156020410a010000c0841d5400c03510b2003004c0049100201046032800c1681100144042101b0344a00d4008028003040819170034901900c43c60750741e02c903051240e0b02072040c096041260021402c0d04a03400d030315415265082c91040100d0310f85d0009440040a540038414401806443c05020303001200583c0a4041c0c51012550022103030710780c080030340034401104002d06803070304200107180c0040340040540300d00f0242e000580540c4503503e08048266401c0003012400130080c50381d00f201a10b017030646d8400c064110382d8824030205070848180095000019282220f542d1a4081110030342030404a0400200030805011602c2c01903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 497337158 1250 497335908 497335913
    0x603120a08041e0c0e0903120c0a02060106020d171f0b03010801240510030b0a0b1b0303010302030d0503041704150e03010b0609040f1b0f1b0b07030915050103 70
    0x2080c40744982c0c081c0c0030f00542e0200b03007160392034400d01e4541d000305264403441c400c0c40440c215905081d844000b031002ca0f441c084100c006041c20001c100d401803400c130400914110340c19414800280186018002080c0a9820250140c00b0b810714151065054480c075000642c130802411810301e141889030f40071b0038019100c50311055543c1c03003401201101d600f400303500e0403103008079088069000781103003200c441c0c0340c101003c01c0b0711036812919120130191104444141d603a00e001c550f40082540790190f43e0b8441000c001a10034412107240584190011700041000d40c0b800316080d14640700360314055550b40d960b0714120000d500740401c00002180c01190100f0405c2d05a0041d4402c0c0103aa280d00341414610740c05c150981d414001540d82220080c80480700c0c40c1016000300c000d240032407002181c54610385206070341e400c070000d1031500000c04800d07a04074001d400c01e03558911107104014885140115803030356400842c01400d244c00300765890191100740a41d94030001e40c4690390700d0040c049560b490 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 497338408 1250 497337158 497337167
    0xb03070513050106020607080601080c0306010e130b010306060c0f0825061a100f050903030d29190e0a1b0c0512040f150519080405010c0801050609090603120a 70
    0x90061348051301c07510003c210454052801648035860503950140b282d0345140c00c4d04210380026007042d05011021010b0317a4585d071914042006508a900c0019610343e4040c00182501c0c095480380d0103019656084a01042d034488081c120260001c20056a4507842240c40403404240768503210f20a41031a100002c101082d0410369040407000c40c0c084101d2210000c020612110109a8003c550441c0c4020f404a01400241c030101600030143ca041c0311007110f40c02c0a60300316001d0810710001600900322003a00a082034001d80c03038291400034040e0342d8002200066034603401201071000412000035072105041d0051820500038003c01d100d5100e140e14003070180d1010000440306d601614514030700003840d10050740c04881e4030034107284145241c5901c91f500d0141c8280c1e544100042004001d802c0560540185e00c1c0307004c41d641d075103a90326140c02c00c0390854854400e13038400c21092000400096554405a810078042252070a10a85440000070f144c1165140950a030500102e030f0030803001e801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 497339658 1250 497338408 497338411
    0x1b130303090501030b060a083d08070b07060203130c08031c02090d030507020406080730030c02041a03060a0f0501080a020616080c03040308090f19090b0307051305 72
    0x30307215400a20340b2000154203807000c01c001c1c10741103c42805803038451403040c0c3c02580c00000440d004901d007920012940d03540881d4452200408880103400362a1030768007010300000701414405098918189041d4451034440d00402900c403503008130206075041a80701411410355805540e40440a55802c03825449801614414a0030071100d11103004240d0742d4001c54550510041c1205002070056800303031041d4001103001e0341c00030b076a641d0210f50840b0400c6221b02504500d0b41100000f501810300b14082d002a400d450082d188861442001030f41240344548010b5044a000c20b0400d1401c90452050b969081c0f42d07941407180005100d01140f90360310800700c0c001607030828017041c0e07200c0092641c0d0320302180c0000d4120104000034092062280040e641071407103890494038080e600d044032480c40d0010f4005892400c000188449039141a41000d180c403a02075a043e6000f03803400c1e08514030002c5074402d01240907203030110400038ce0390500290b000741000900021050050b00226801020f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 497340908 1250 497339658 497339663
    0x120b0115110a0b010e18192108100b0a0f03020f070c061d040603020d0f020607120801090624030e0304080a1505094213030f030b0d0b1b1303 62
    0x12201064802480f800e00454140204000388880d400c0340d2960210301d0387c0c60009032400500d10090041c11165150107481a425555580000e070030701d08604000c0c0e0785107a2281303003010002c011803071125400050220290405050040c0c480c40d07640304803020340c881c0200003891907428220110708550013015020b410f8110282541c2d41c0304060017880100d0300d031400301a5100e9654401c00700040e00e000384034034010713102030306283c20100c007a034a00c20700b40b03949100d02c00810000c1005015440c4e00d031140d6070061038010041e003640922405145803000c01c0c80724a004154541c40710f65034205042007150010050311048030080e192030300f400220199a03030201c500c41c03410500410000c1c5000148058100f01c2d03d0300c540158210369642c40e0031401407201200c0c07070f40c0144228206406840071194807405d048182418410711516000f4420041e480c1d10b0300a15103440da1407103164442800c11041d06911441d04d03456500c4a801d034184503520111048101c803000901104c4802d141041001100d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 497342158 1250 497340908 497340929
    0x60504060608160605121503030705010608010506060a230c070909021c050d082724011409040602090306070c06141302060702040e0102160309120b0115110a0b01 71
    0x310703402a0220794003084c0c4540400a001400b002e0f0400c01c0000e0556003183c80c5040c403401c0082e42070040b0307045402000041c0c0302a50360b8a01004540800c0c000c10f90b00c120201d0b101882d2001c051002740c0b42c610300220b03020f1004031030400c0224400c903880482d07103585442004c0702c10880d540c200070340c050909140c0803802080800d150f032503141e8901c031070380320303d20740c400081c2c40d0b49020030500702d4511000401d810700701d003a55400c07010444007181e04d60020340c10840c080e00b031031590f01d45020480b00d2610700d111102109680100b0000d1005900c41342c180d02c0c01c03150001d0340d44072424038802900400e000316a144c000c000038440381e280c0090354408014403405023402a02202000407415080032200311060005418010b001440c0c0fa500400070f85200a100080d8804201401422a00022400c940e000d0070404400c092540080145005069a0020b42207003401359451100480040c0320b5031145010744403090082c4c038000c0d000042003482d03140889012104504201ea0b9505080c482e210309803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 497343408 1250 497342158 497342173
    0x32702031006141311030f25080a0e0a050607090314030a0c020409020415030c180902060d021e0a02030301030311010b0a180603021e01020106172503060504060608 72
    0x110358001c90781102c815000c0298a600e010f800e002c000d0400840f041202039440c84c3c8a010020700101840c000d902030070f802c203254907200c0016000708204000040c04034030307015101c03505140d0083e10180c0c8020120f00c04949203050750300d2646800c0c00f840004005000d000d0800180c603901c10072070b104484c011813028002000812003a0b85a2103440d8040307002030900100c4070054101074108104651000e400000c034400200c0c003103c1201c9690300102c4264100c000200102c004500e00c069541c0c0c449681008082402d9000494611034200c0080341d031a00820b80c180c00840c11184140e0f80d201030b20100d655280ca01d40020345aa2007404110085440c0d0005203001a00c14440c1101c45075010341001c1c0060300317100100020303250104218081e02d44400010005840c0d900020303c1802c0b12521080d4400008000607003580e030140c10090740c0131000c455074500098000740101d035410714050f101c1040c191605a000390101d00740c0000d0300f800d050106020402002c1e92214003210420016103d45 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 497344658 1250 497343408 497343433
    0x130c080c04030f080304150c090501030f0e0613110d0302030307021905030a03200a0207150e0d11040906110d05070905030703060b040b0a0e0910111903270203 70
    0x240c0a02e01001d806954011009000141c2c10303001150424051280c1d04014130340141e012082e40d00000b0a100081c95044081040f5601401942c1c08884c2e15403082c4030b2215020fa0140e0749020003807c41084004a01d060018400e000c01c02d2220f180010308005600e2002c3c0c00d02940d40c3e8403c1e0340401c01486804e40c6407140b05460564600311950201c0503516101410f84110007a19442e2021000c201465480706c031100300c00300040c50350007010b8003d0113050341b510709484220810411603005100540501c60216030f100720b64200303695400b18012850440c11404a801841c80a1000301190310305110381d00320a2400016100e10300c02c0d01c10501c401c2e580c0d1079084501e6883c40c851203401d580a00300c1440080c803c2e0308580c800c81d40207807000803280c52aa0015003034950703691081240010560601c42d4140003413041c90704020138404240001c141c46903440c00e180c40b50390300ca501a43d40710a18280054400e800030482c02e44010480d01d04456080c07a00e0324510360b0080c00301d10920800011151 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 497345908 1250 497344658 497344681
    0x27010503160e060a090516020f0c010203040b160b0103030903050105090c130f1e022a070501210e0c0f1e04050c0706140a06120b010311060405130c08 66
    0x4080800c800400d001d00c1c5040700708003481c0d41c0902480c0d8803107001d40020541d44032070b20400b8410013011045d80c2400240542c040d05160134018001d80c1070b082a9050300c02039800108031011a10885403030390350340303e0001c100501402c031407000a045e10004000041415071127052034080d24001c4d8001c00194940e21006640ea40403040d041d5040080380c0084840070300664050782e20b89010440c0030882005008051042c0c40c890b64101c0803450303003c900c0400c44964415881c1d0481201c1301c00ba000b03803444c01001c503980d450b94858141042035811100e15a40100c1c040000c540c00740a0060001c01e011017405600d400072044c0017130096a13150310400f414607060b4070801c14540d2a00741c00c3c40c4011840709210103400002c105450b601e00820140000801c94410103280100c898070588103400c052070807034166074081d032001014144561703032100031503011100d03181101c0d071003004440030f03c000d10003007545030280368000755001107a00c01d101881507141e0007440d5006070658603d151591010166031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 497347158 1250 497345908 497345923
    0x11030a03021c0e06180c03030f1201150207151e020109290f0907050909060603070f05100f02010605040f050109230a0e010b060a0f090608070219020f27010503 70
    0xb4690001d0301181003501020900822801c42c0d01c19106ca000b000004030b480c650219090310020303140000d0100c1c40070f20340c0c200c43c1e01620300c00081d11004181d001c13009540e0040c43c0510940c003405400c440a510b030040007217002c4104002e07807903094241c160300003078000c080f11601038070000260003043c1d0055102940190b140c000110b1038488a480b50f03a034002c400704d002405400c440c4036800c408503080e0f85001900e80f02c0d140110003000c1c2c9161074800d060501000798002486810050f50600140c0e0310740340c0350154500d440c5440c0080c0c064088080780544099407009401c01c1c41c0c50310203a120700c6141c0209041c0c0d1a880b0f014485481607094080e4111401c100d04048961540f02040e1420040d0304484480c0351142d0001c207103001120002101980500d0542c00424070040d4a00c11490304800c00100800c22814078140610381500003075210013240700c2e003003104201e58000b42d00310f540b21004940c0c0d813072004e0030b02516401004408494040035000e03000c05007150701c000003614500042c104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 497348408 1250 497347158 497347181
    0x71a250203071e090b0f030102120a0605060a0e010302070218130b0c13060c11090f01090c0c08030a0b01051309060f170c0d0201110f06190203010e0606090111030a03021c 75
    0x40f0034851410361641c00500c0844142640061101c0c007100c0745a03424009842d040da411259021642445c09804003110900d0780003034000ca005004003e1055000819130750025030030308026a81e010144005240b40b58041000c2c0da40e4401d940a00c403101c1c2d650180039505d9449489807a449450301365100d01c1c0c0b8020481640d002c0e40c3e10600c20301059101350822600c00780308200807080701480500003130f008071007141e0380080d560100b40100f021307150600442c41c160125003003494220341c007500da5100707910008001200d1980c944c0c0807019164400c50866032a500707010103d5820588a00411010701503521803d200c4103034041000c80d00c1040ca401007051032042e8001001d51351036040901c00c101564100aa05001444d15503e07001c08080c400134500c0301e1010041c00281c81d150340400c0c00c080c00142c00c03104a901c10b00051000c010440d0340c0c1908014202d812940b103040c4540101d81100001e0040809804040341c2039040e1900350300540881c1015450200400a108404004540791010740 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 497349658 1250 497348408 497348459
    0x1030c05040c051606290d080f07060905010e0f0706090e100503030d0b030607230f270310090503190207050301061e0e04020102071a25020307 63
    0x2005035261a5002d0064154941000c6040a80240301100804640340c0141e032003589511402d071403110084503154040c0d403501a0b407501c54007220301040303003010300d24002044404000b841035019040c207029110001d81c80780d410311003105140b9103180a40001501c5a82504c544210445809070200303401e0181d501c0d41c1e461404080c13a10750110b1000c480904403202c142207a410100d00780c2c50510080035110340318071010501d009031070203040c90031100602050800803c0d6600854102d001c5207803041c10a920600191105182000075290f4400c1c0d81d840c0030740c00c00800c05080f01031a55400240c070604100c09480c49100282103820580e505120024000c1c2c208000c1030324283e440c42d0903241540321501c101d032a45900d0300c011a08445079600400d07802501104a6051402c11100c5000a0103a08150002c9401c007a40041d607103000c940582c0410000f00c3c1c04003282c0307101000940e41d852640719044d0040384138a0350340d0019500504030990090241c0c078408503a07020009140802e40801100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 497350908 1250 497349658 497349683
    0x4050a0e0d0f14040323030414190f0e1602030315101e09080f0c010e0d08090a060c1202010c02190501140f10170d0509040b040c030509010e01050103 66
    0x822140b00701d0007002a014800c0b0600031110140c6030350f000d0000b6600c038000d004c000c1c1c20a101c0b200084142101c0102c00e5a10410090240c0c400c0c212024519007010740c0c00c80c11403030558204606c1c0d0b60094100c2c564000312510000303a0100380e100d005025003142c4c06408144007441800b26120322003110031542d600c1155801c6601030511b80f000840f441494905412002040403e401011080c001d5500c00105407020a010301d22080c00088010071004004103021000000040d040e41704110b40c00740f0441d00f0144480900061504864a5000c024000c0c542203444090180c91810342c2202510a180c2114111030800d00501ca80340301030307c260b002841211004000c0c5a40a052068100c07065500e0340b005403030b440081c3c64054014145458140381074130b44107aa00103500300ca0b5201c3d503c00c4000003600c401a900c0030a00e6144e01005140c496500c2c403009012402400b80d03809220703000351a00b02d90026950b0b02d42d000d0750007810020000d0140c9007180750540d003aa4002e00001d06107159864 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 497352158 1250 497350908 497350933
    0x41e1410030e100b030106080316170714010203040303050112050c04020f0d15170d090b070606120f0204060b040e01051315030c061206080309041a04020a0e04050a0e 73
    0x40000c0600c081d150109a5400140403241404900c5804000458070b40050030150300c1c0c00e004242c041c10510f0002c60034170452080c0c41206040301c03c800303415103c50070b0301034030034040e0a02280c65140d000350701c4200b081c02c1400410b00070341c000c80d800d5000903d0000086035160300c01051078062904800100141c032003540030407000f0b5001c803a568485e20000c001c90458410b05008224045102c54003001c1110325203c0c1c40300a01c400740111103d1034121400c45242107810100501c243d42103ca07a0907224081841d2003001800300d81c0102c078417506100600001c01c58140c00321141544207030b07018400c0d1640c90205124a016a0292028400c100401482181009503552031025550000441c0349a40d0b503811040ba200c2540042e55114000c46e001d0090315000b440031900741040d07031401c01105160002e4551a4040e40c0600ca00c12500c0710050914859090901c00301d0340c200070411962035010a001800000b0300310003c9004506040000b03610100a102c0c032618460383c00003603c8404100c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 497353408 1250 497352158 497352169
    0x303092a150c1101120e060a0b030c100c03140c0c040f0b030c0f06041203091d0609040b07020f030414010e040b1c0606091103090c03060c1603090e070302041e14 71
    0x10344071504201c008000011040b8076806440b1a03011046d0240009042846c0660159444038032030754001d0b4000643c2d820683ca0340100b605664000340792543d072a00c00d07450225200a9040c020743c81100307010400c1040306030081200c10989108540c1040780c031080155540640b8007503409160303d90444058003009040c108502c148100001702014035054580103c0000082d01103020740c006408000144a20842c0c084840002548810f07030451030f24221001400000c4020802080030007140041981c4c81e008214190128080105580d00d81e07458003004031000f0500b00c1c01900041e407540d0200784c54281886011240c0c08090110a180c41600d40c4c03d00d503800300500c3c208c501d183e0791140011058510300c280540025104c04c2c4594078180240c245140c0340304512411b200741c002c6402d129050440400700d8501e0b01480b600703258924650708043d640c00d81c0607400b90032450000410031001030340c158018002e03140250b8020364031a80c00325502c001c04a0502402c1052020646000107034a0071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 497354658 1250 497353408 497353433
    0xf1005030c0c12040b0304051203010b04140f101e1706010f0210050109142d0a0f1107020a06110c04020f16140d020307020f04090303092a150c 63
    0x80c002114600c1400320f088a465038003d40c44145480004002d0104100090061442042e0007400890443d4181095000244201c1c42500700c5851b100c1e80b0b24040ba101c5110800070041d008202e8603000350b45403030150001d540140c2c51101002801030390342655010725640000d810711441c3e448040d940d0076005503202400150014294420404d603100c07132003402d01a8501130424010040741500200120026500001d089008a07402d020110241d11030080096030000f05980f0f15888079444a0000308000e1245c09110b00340d041c1008100e00c442c0f51031500400c1b030300f0301c25502185040d42e211422a804008055220180e0300418054412490150003402d00d107407902d10a03514000400c00411107801c10203100b210018034020316150500c0040c06a1505a19a0b0015618101c00e03680003a50760070030031001d07078400d80c1e40b58840b506152081d403003c801c29501c0100660326100079641d0368040d0b1143d0090300303196008500082150200500a0300c60302c2c0d0540c03604240c03c10a980d8130010b8209 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 497355908 1250 497354658 497354677
    0x10303030c031533030609051e0403140f04030606170d0807080603071518080105011805090307140a11010219020d1106030a0b04050a150312030212070801050f1005030c 74
    0x1e103c1010740304e24800d1204050340f55840c0c800040321490500740e101510710080c481c1c51281c8580491000d031860710b550865000c4e5141c50301e41e00100301448400440c2c002c0f40940c54805502042c080204801c035445407080ea0114034040b0075520940c01601e40d10401c014016000440380000308152500481c503c58000300004c0a0314580c4e519203400b05507804101f1103041c0007540c081818070b43c01c07607841140f4020303180450003408150706040790a4414001064880f0505689100042034020140203a4040c541d0040c2641c800c1d0700c1c400c0400b41e5901d500030781911605088113070f02d0803541c000141010300d00520401e8200e8072229400301700ca2003001caa0300780c404210f40c107154600795031810021803180c3c1811000046480700001440201e0350020195031846140035803909407501d421282c00c2c202d980c0040c40d40303480b500c2408110083d001d025280b41e44a1889014480025001009241039034810b075003a0031070182a10421002c40300244009004c10720401c00b242c00030381d4200080c9203200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 497357158 1250 497355908 497355959
    0x3030f0b0f10030e060a2309030f0a2304030b010f180e030c011409010c110705061b03070606030614250c020d0b10080604110f0423010303030c0315 65
    0x260750902c00e00341701045401a4515030340e007100c2908060303644018107a00403e04020422440d200040c1c1da6a445158036064020708040707612105d0b10710071040c0c000c8014840702c070001000e4000501804d1900640000c80d0107071409000400c6071100e64180504542c1d514541c420b800080307180503001031000729802106400200300300181d00400340100480c0000500d00080140340203e006030840d0079082141d410040d40f078008940075540090070000b40c0d0b81c11a11a03680c1c0d000440400c7c4c5601e41292115001d000100d0124144100b551000e4101c0780107003018800140482e0300c980ac010000c4801d03110001400c243c0103146120540c2e110040006070400002c440c03c141c000456101c05141c0451f2920841c600b041607040002e1003d000404182c402020319051590f100e40c200a00c5458160184151003511011a6150380100034800c80040c1c0100140e146c1603031a0039514401d00090b8003090402d95500b502920030310402c00c42000400e42881c50500306520f080052012200b40f04010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 497358408 1250 497357158 497357171
    0x312020f031006020c0a061d012a02030123070806030304080109080918010501020a141203011d0c0f09060702040603120923060a08090a1e03030f0b0f1003 68
    0x41940d40000d50241100c4180798100c940b0b00b140c000e1400290000480c000d01207000208070040e044007403461030200c42c9079090a0810840d0048481c1c0c1855000100800e680d0003000c00e0119260404040d518001e47c024015000e44c03034419040500d0a80c844c001c06240d001c009500e1070710441c003542c0c000d103004050b00e2801b80d560380c420b429211080c40650fa47d0302d0018107d0740a190100b814201c80001c442c80c01d402d90326080010352181100c0700e0141c070f03c0c0ba4442e2800090031040c07140d4070490002c40707006a2a540c48200c0041c03450f0b5505501803540510341c011a14500080d006c0ea08201c03080140281360a18000900200390030215080342c00c5600c50201200081d40c40000d034840d51250340d20307081c1c07691400c203401b040060079540300c1c00950206441c8601a4803447c08540044a4a062a03002502c0358000c9070301c0c9c028500409440150f503180052584c3c03d080c601c0d4080c03280281d07030610003206107103904400c40d11071041840e82308117801034440182c1041500d804400e0020706001406 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 497359658 1250 497358408 497358427
    0x50103180b0a0623011b03050405030607050c010e060105130c03090501062c0114090411030d11011103091c20070e07020604030206060118050d0c06020d020316031202 73
    0x40c0c0c002e4400c41119612404148000c80580f003150808507500641c3c260011070303100020b01603604140455000c00702d00c0c0c51740b2080c14000d0085400610303000c0d0441e0b00600d01010020050b40009095400950800c00a11000c0c000018094162040140009112011012960300404850820b00305042d25024280d02090003849244014503140044c2d4010380316007551142a44040d010001d50b15036200014040100080e04103620703450143c03a4029a503c56007407134440c007156070103101c0d454070600102c1000d49500c10074803400398030280c000344018010b660125400f804101c440820301e5014070341c00d030401c0030f61400c618681074050030142e080080014001e0401c1d0043d00d014109640803081c104042e0103036100069019080d40b000e04618101540c00940324600030b080c46041101c040c01c1400100d060402c0c0d540200700082810800d0500c0b0710703001026000a10998001d409030001c480718450022084072a2044071603071a2200700e8099405507204082040740c3d0a400e5400c0c0b080105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 497360908 1250 497359658 497359673
    0x11060c01060902030c03090705010c050307200607060c1e021002130e250504060534060b120303010e011716091a01110a081e07030c1a0f0105010318 65
    0x15085c441031003950307440d2070f407150361a12400e90f006604004221403031a01017400401a80d000300d5010380d1901200b0343c118060500b4094203070f027440e07002c1c50014100042040c01e41c003c903803151030703070701d980c0303c0c01c00080b4408140c0d8448004240150b00100c0026054130340560040008030201d10148444545075200001d4210003100ca880e00900b48160468075050303128030722003801d11b440c0ba02900c1c06080010080080c000c0141d02101034030881e4241c4c0c40c020000c00072090003040704c0000010b15400d0304202c0060141c00310003034003c01003079000e040350210102c21031b4107964000540341526440c0c0000c980600403070344009001401445200074000c0001c1c1c00520003460340c08004a8a07044240d84894007140030180c07103050110a40010614841c041030380091980c00c100c51640b41d0f280c5641c9400c2c0c0b040e007150850007038003001030f0850426420038541c182c864010300040d8180c81006035410b030302503030a8820321802d0803c800100682d601c650043c004c43c0240380c1030001c00c0303104c3d41da503c807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 497362158 1250 497360908 497360911
    0x20d0603080d2004140a0312051815120a090b01030b01150309110f151b0706050909011203110604060c0e0102030f121b13150c11060c0106090203 64
    0x65407500001084007031150180142d80c0e9005400c50300c141d0300050802d00100380e2150b4881c040e480b0a2003480b001003552280809401990058491280900c01e884018429440240c94000b03100c001001c07808541089000d54000414448a182c6011030401c071003400c0d5940100403a40054032100b01e40000380f0259403560086106545141486d410310000b5800102045040350805141c072500602240780c114401500000a681900401c080c100100d15051403120001c10080b400007081448090120011160002000709803000c0c80e0b19140121035070310510725441e034014001c000620084ea9030201141c1a01d119040140e90a0540c4140c28241807003190f0940d00507550b2074600c020190800f03c40f0a45102c00d201030740c5890755090b4441d800b40070311580c800e9458852030029007164402045101c86190340c12081e0384501c000020200c9202c0603019000400b030100e0700d00c17a00c0c14026420650404da004090503032030b03c01c40c41440055040b0007010086076403102000a68506c1c1c601c01103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 497363408 1250 497362158 497362163
    0xe0a0815040209070315030209090102040902130f0501082814040302100e151512030415120605130e0102090d0605010f120c09150f090b010e0405011203080406020d0603 74
    0x21600e45001c1c0100044494020f2280b0b0174141442d040d04c3d43c4800104208064076811135040009440d62503c0b14024000d81d049601c019200207240400001d0003000101100c41e90500300441e5030300d0f040111407040007510280d41021421050803010784000b0403c050641c140f0390005640907031118800700b05401550260056080420a4400041c550003030089240411008002e4034103034038001402c0b0740e0018015040061a07010b040d80b5695a2a000c0017002c0642c02201d840d07640303440801c075000c200084807102051481c2b6030720001041500508040b5030000b401c12898401c0d03038140034098021900b08031000d550070081e912055660054400c0454010303000084c1541c10004480c90118440e00704110000c01c400104002929149504041c3c0b031701e84030081100780a2038031509010340f554110886090540320082040231043d8000347c08804240d0301c40007440280420b001c110781d000c0c020688110f46140d0201c1c0071a000c0e00c0940e4029201d64001494000c807130012504442c6540c108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 497364658 1250 497363408 497363443
    0x50f0901140a18080601140103020c0703020a0608010905010504050714031e010b090127051002070806010617150105030a0b0f03100203090d05160b06060d050c0c0f030c0d0e0a08 78
    0x7007100000c1d215010f1000740800c1c400500d001d5040c1104020b601c5034403400b440c105500010851111101403040400641d4094003440c030044e11004041c0c0065024026180c0d441d243c4800013900345824003400f80180301c02e07101c0c2d00000c1c0120600c40c00e568001815034a040c3d080d520401e481002040809009156581025407500100340004150301241c1d4508a1882520034064251018169002080700d034100c8a4a007130100140040c0d050811950102001e0b000340000040c00702e03003081800d2681c03601800f01c1c2d903d035a6134501c516030003c0700740070b070a000507420700018031402d00660000d41d0107074001f07080341041c0081000107460b201c594001c107078050360040706202c4801c00800c228040c20000b41005804c200f148024207290040813403010744051a02000301e0010b455003822070b0407005803003a042c011440c080c01c1549095001580380e144622490506141c00f00c4040190341c2c0441c801c1000c1c5c00c0600107403504039000c40e01e0007000d591004200300001185203042248004001900c0c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 497365908 1250 497364658 497364677
    0x11514091002030c1002040506090609032a01030b10020d03050705040906030c0e010e090d050901050706090b01080706050a0905041d1501050109090203090606010f110d021006060f050f0901140a 85
    0x16205e0500c0060b000d41010745006000602c169502c2000396010b622090b904152955109800a4604001200704910207004421519500c030300349007000c1e00100e0300380c03004c0c0240d03c01d82d004e102c8200700407064440143c00000d03109980030b200f44c11468002d0410b10b001c0b801c0541302c024420855000340d00c103d40d4143e0909040101c0580489000d00400f02c1d1601c0c1440c61400c00707520380c0c035030030803140b0a004c1140001d000003c2c0e038002e1040c1c403501500084200806480d80c5481103400e9428059000715100b0f04000082c0315201e00201c1d43d003d02a552182c00e918a0303c414007003d0300324a126003155041c3c40c1c850034011081041441c00841c541e50b8001c01c5545418005400c829854000c214080d00420800c003041b507001401030f80120083c40e00082c0f100401400b129008c0309003094655501680d80b54280c19680000d0919144a8418003005900d5641e40d0a0300e1054640c42064003260041c054210507070407a03006802c2e0703040181805803050100300350048141c1d01200034840403411501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 497367158 1250 497365908 497365927
    0x6010527040311101d0d02030703050c030412060f1416110a02032406010201020a050901050315060d0b330c100f0501080c031f1a060c010203090f010501151409100203 73
    0xa110b280094030305c001800d04c120040a00a4072885108405000c2c0f010000342e400a103801001100c0043c80305003081140301c840c81c6001c0e80580020404031940c0c0e814080322056000d0032585050140c154503c11111001c1c030306005440000c91000304200d64004d0500143c09601c050100c51401038214403200007140000355540c1e0300c104042d02042c11684140030b00054240c0000441c1d00d044800d0901c02d840e0b43d502202841013680700704c00240c0100c40825000c9004446401c0842c0080c81140c002d6002c1d16aa01c100f9180c401c0141005a082b1f07485078003081d4030302007400624014840c00c041d140020303c1c01c0241c4090750886440a0921945d550041041c0c144c180485848094100c018101003003101c4411480382c0c0001d2400e188140d41e94007000c0c01d80c1081044040c4200d0050f01054070b030404814501d000390402c40e038404a6000320320702d83c0c43c940c0040c41118140c50302102c0035400900824406c90308224080f803600542c2c03404100104040da25103442e1582e0084030780c0250780e101d0791b12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 497368408 1250 497367158 497367191
    0x10b150a02070b030603060a022a06150d122601031b0602030a021f0b0a03060c081e0a0f0605040e0a1202070807051e09040303020304050601052704031110 68
    0xa500180d0f280380c00303209000991b600490203e070814500d0402580300d424444045280c1c1c400044a10701419200c0441000e10340041001da00c15440041b40300110812101401020b9074a000700400c800c06034015003103028042c5e0a0341000f40b501c5400c8030194000171600c020b2550081e0400c0d80c40c0b54007801490b4100781c41c0e03480307903020b04510b1020b54100799010401a540c0c1c07160304007280181d01c030140340c03c442c000c5591001020040c000d140d14061966420a00001e1010f00d01f0032001802a500181e03114080b018210300d00480d10f4a0407400340e0300e102c1817030000c240240c1d500314000c0d2144800106a6903d004000041c81070101601660705180f4204d00480100c01c484000e5400c00741c0c003005100008240e450880d201541d03007032002010081c22041d0f0a00fa80101c640c01003140c0d05200c14540d065002d1840f07244120121201c503622402005a0b04041007251550041060300c01701c0460342100b0242d8100384a81444401c40d6202450142843d910440c03100c00e103640c5180000240032003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 497369658 1250 497368408 497368423
    0x60b070609050d110d0309241407020c06070605060d0804062118020621090d090501090e0711011b0216120b0f040311010609020d0c0305101502010b150a02 68
    0x3e07401e196842c403d03005111912018042e04440501d0b6807002004280501c5041c540c00700200c078404481e0452903240c940004011a00d514200c04031640c0000311442d000003004000f62030b00070981c0d0b040100e55036941025220080c10b0b240c0103650f0405610000311078202400180100d03450301d65124100094001100000c4d8040082d850700b0300040410701440176400a0802d40c054407100e545108221045141c0800d081d0080440c2e40e0903002c0285500b03002c03e0344100714005030340e081c05850342c901c011651114140503e00003075007960040740701c0758000e035003001703459403040c0001c21103002044008045c4280c1468190158104910a005101301c07819244050074a110b41e0f20210000c44e201c0600c9000000c004107000200040860107141c01128550f917122201d030002d005403620780419201079048080c0e14134442c1c1c1460900b0103510b000f030240511900305c5c0c22390100000e01d0a180040f40307c0480317810300c00f0b65507100f54550039500c07114540c000310182000315507a1003c19880081c5000c68 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 497370908 1250 497369658 497369683
    0xf0b0103050105090118112802030408072d03031218050c0105091201051312021b1005120a020c0705060307020606060702012a062004031401060b07060905 68
    0x1030200148180e079524290766054501014000d0381c0b6641b2101794400810704005890324080d8007041000748582d4608620444c0308500100c0607481400030300a03a5a80110700660250340c1103004203000c1d06a40003501443c40d081055000b80e600d42e860b00304208101c507504290300007001c56210801303480302401404403494402c0e82d13540c0102140d86a103500c0d040910806410010005200e44a5079540903200005091a000810480c1803424203d10a0f2102c0301c1c040304c12041c40e04515403400d0000c1006030002c100503038204440c1d543d280422100455107020b842c144803040c800c1c86e0303034110411a1188a8241140016611440c070300406150107580c4c1e100c3c0f84107010410411400070b50100b81c1c9600101c3c16101151207600d42d10050302c0310360706001c10307108282070445451031102e0070070400402540200802c001d0140c400000209600c01000c140703480b0392040004100048040629901c500da03c10b0000a42e0358030b481d001c041a5004610030740d034080e00d8104c1202804414054099100d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 497372158 1250 497370908 497370911
    0x28060905090c0108270607050a0212180f061905040302150403020a0e04231605041b110c030f1006050303040303080c07170a020102040f05090403020a1b090c030f0b0103 74
    0x10301040004c0c82402c00030701c06070800e003403140f007100240702200c601c262480249058450a03d420000180290401e061040043c0b05051400000c002c01c3c4003101d0a0045001d684c0000188c08010703c800e480075100019040b030010044061505900c100101d034124056551139640d0740345004000200740d4142d4040740710343d02000700b00011b985500401e4101e4407040d400c10802d030f9650400c0003c40740c90701200c40d0900d442e41c0d10000340002c00304100c408442d035405d00082494460017408100d40c640e01c1c07084500b00320a0042544140a248141d40001204049428100500d07010030304206110b0411503030b6a101d190044115640303401442d028003030580c02581043d141d61001411303400d02604001040400080d0030003440746419044d1a14501100c4844d5640d5030180000c1c000d6200c1c4c41400180d0005402c0800c3d1890304282e40b60103150035500405c891141c0c0d444140d0303240759100b188251495107060016000701d03103004001c20015140c034000b94a01d41c0b04590b0082c0c03401d400b211410036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 497373408 1250 497372158 497372173
    0x90608060603070e0d0303060b04030b040201030f0c020613050705030f0708120a02190602070c06050d0e071404022209290307030605090109020a030c0f0e040f06052806090509 77
    0x202d51091001c9131500048445400c2c0c03003103e003000c0e0b0051200c1d40061030744440003c2c010083c000400d032400d000e14402e80e030820000c081e403140c44044506040c100c03401601f00b80040748980e9000703141c3d1040a4000c80a030703030b60181e1300c0000910308000c1c8a15008640c111580420644906002116501d400660164685004490025110160002082c0304803401d0301c0b0301c03410302c881b0703034140d5510a51010103181c4483c0c441c10060120307001030119040b51800d281650700c00c100c02080c0041182e0a0966082c0f00600d064200700180d00700362940d440213a80401c1c1c0c1a4850700c44405a00140340c2c1e844001000448804908201028404506600c500c8170800c1b000c941c6000130702200b02c130703000940011140c07582408a130142507180300196004243d0b50000c8140702410480a048442460b86105815911002c2a8540b80c00701c070054420f900140c02d07000412501c3d00000d500c400030035084800c0e0308031340c51040d503c040b004154524080e9a4041030042c41400d1060760342010481000b070110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 497374658 1250 497373408 497373421
    0x5041406150d0f05151008070302150309010908040b19030c02030a0f0519030e0d03050c0f0d0b06120f090303010b070318052713151e0c090608060603 66
    0x1000211819500410028900c80300f0b200740c0c000b0464000d030348002940c02c0d01c0401003414003144002c1c0c406441e40041910005400c0200140141c2100c1d0702410b108200ca5943d501484240c0006110700c810355215a1600b0000e00918000e1001d081042c0c1d8417501e4106918890030110500c20b030200516260148c5400e48680020640d4241e05052a00700302c0d050140d003045075240112000b1801c80807180003440c8174140c00d0340003140050000411144c2001c209001282541c0050b00c1403000c445042000c000c1d0021640018020140061404900c0c10f116002154555226804640080000341c0c00d00c4030b000c1d0300000150700506290000c0d0b046505243c841e21052180c0c0b00014103002d1520002c2c0140c074a03002c200c80c000c040c000d18809164081200b01644681c1c84100710140c540950000b49101e65113440611203a6000f580d800d00480408940c14010f0040610381404c80003011040030f549402030044402d940c0c003d5031001e040903d000c80140011f03502030203113071040740d092040045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 497375908 1250 497374658 497374681
    0x50a0b0609040203100f060e041b0503040807030e0a14100c02011e0e0319140105040305040b160c03200102030c0a0303090f06050a0b0906030d081b09040f05041406 72
    0x8020744119801690f80e207800384036000a80700340d40030805404003003400040791034116607808405074083e1014001c03d030b201d2122107102132121942c8804140c050000c540800e05040260520790720904110a01010705c000180032108140d21030052007295207018600307410507074900c400300452404e160a00d500c0d1540042c0403081460480c0d41000040c40c030690314288510a0010b1444010b8141d41001c681c0403c2241e0503103107904141e5210b40c400c4079400c03071010705114840c41a078050361031900b41404c0040096050348184d40040860680000d8140852100c00c6c5003001903200385030607000c0304104d400308490200c501181506640040c001451220008500307400084d070705280000c1d400080d4034084030541c2c41601c000e0a082e07d0002003002d085000d601c20082d0500840c3c4102d419a906001c065a03500310240032400204060040790518030103030982d07260304c0302d0014214100318485008c10304680c0c40c44c402041d03054460040c8018040d2905881c081c0b000302a016003403070b203022046d008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 497377158 1250 497375908 497375917
    0x906060509090a02220e0109030215130b0a0f0213030c05030307080d090503040305160819021819020a0c02040606050403020306070f18080d020c040510050609030309060a08010306050a0b06 83
    0x34012850107000d0080340038145d180401c0c07a40c51007020409558502040b50080c4000e02c070480261041d0304141590120802e00207104501c81022480c8030b80d80c0c0c0ea104c0d0b20800e0301510481c0c04503164114000c43d0340d00c41c0054403c2008080d04045c2d02499414904854811075211034026001000000003103014801280c2c0d075001014004076040102c0d01c0c00510314807869002030614020504030302c0d13410110715011002c40f0034020848400c2c0c0c0f5150022505d005051000960040c165174000403598907100d6442c2d8403056803411042c18400307006114083e83e012100b606c00141401c504a01180f9061250402422240c680b460510b811030340400e688a074003924400921966103d01c10000f0311422214203940d241008803a0203030354400c11903660365400c482500144c00384d40041e0804d8180340c440c0d5813160b08691150303900c2e02d152405000d80d40d440060075a0305030004100c824066191f14000f881c1748400e40d03489000d90741c9941440c008940c0041c10a11295092070248948e03030350f8400030b58 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 497378408 1250 497377158 497377163
    0x503090a091b211d060f0f070c02180705041a2b0f0f0204080c0405060127120c0501020613030906030b12070e072a0b040305040e0a0906060509090a 65
    0x41032510340a45050215604941c01d80155003000302403c51800e8449030100c61a000340205c40c1d881c1c8510320f02070307074148003165000c040c0c280f5400041c4072a4458104406201d00141c040700d006c140c1445064400c2078100c0d0b0000104070b00085c01c01c0140701c0c3e1640d0740b00802550603507605080c280d064200d80d1014000d071350414604840e4201d8080d24165211464684400c00304006006518541601940003807091135028041e10320142114140341c0500c030310804050b540e281c03001d034000d0340700c081d60054001ca50500707401c00440407a001264128201186005001c240917562034480021b14140000b08100034802d5440e582c14002030704031003a10280c0b88a4140072981030700e01000309902c4500c100d0362003854807519400180c20300840820070b004d090304c2d543d01c1c00100c44c0220301d08105403140f0050511860310314803010114860501c43c80c0c0142c440d00d0311514180e503d922001189100f81c038400d0742d0b01d1b66040d1400402940b80b24407401800c044d60405400c1c41e000c0a10303516485040f134003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 497379658 1250 497378408 497378417
    0xb0a1205190302070f1415130b1b1510080a200f04020a0f0f030b0603040b0a02070f11030c010327140102040602060609011a0a03020c01180503090a091b 67
    0x1d04040500074091030018013600200c0035500ca690398800d0042d0540e08030000c0c060241202c03903281350710060007121041d94080c1c0503501143d14148060784158002c0304005129865502d0410401c40c050220240700d8902102071281c1d41451001030410b4102c9522001540d8803c0c01c4003000504241c071b00845508296126241ea001514082071580c1000008107920500c0001c05001e6142c02400c4007200c4030070390b44d4207103c00074940d00c00d904454000401d20351004040c0b0019000603415814541e108000c0749000d0b080030300d5556045003140c180c18040b1100c1c405a610000641810050001914000d103010312049881499581c82100a88482c0349249485100542440340c501000300512807008021513503542e03208002510b540c1d090b10054402c00701b905c00080c60408034090300c200040030f0011031385401854102030b8003c1d881004846940e540381c0a40940ba6042503210303038400f0307028001440c1c2c0d44c01403c0030000d443ca11a00440e24803403800201c107000712014500c015061089050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 497380908 1250 497379658 497379703
    0xf010608011d071b12020111090307030f050120030f090d17090f070605040810060317070f061b031b08010b0f12010b070507080a020906040203060402070507090b0a1205 74
    0x1144c840484204207054415903820000402c03130010f000046424055008000400b24100d401c0c499200d2842c040d03030300d58004203080c400300b40405020607000c0e00c103800000e48944040c103582d01801060710034403a01400802040442d041a444440d400196540034041c0d5050300e100180c80c000c06c2c0e52001c00707007004040024208440400c40c86500300b501a04940e0b115603144001071159200d4020300400d4003824003426264461401400c050b01d6001840d600d01d40782e0348a000c4002d0700404010b44e2010a02c21441000c15014411042c1d0300084000c0c080c0d00b0310f0071080c054156424122206041d0410020000e20303258403030f0a65041d203400009083e0756000000c80c42da260301840348a00c4001500500018101014400404000d0300c02d40654401c0c699514560351500034412003c0e4200c1c0c26040054183e06c1d0690003542e00000c0100010b0600707800361900c600c0c1502c1c3d40c000b101c003156101000c00c030a2911800000042010401c00101c0300c03101e68515880c0c1c0440040380d5a00455001e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 497382158 1250 497380908 497380921
    0x5060304080a170c03012c1501122a0503100504050613181e080d020702040e160905011403120d02090910030201170606030403180513050f010608011d 66
    0x1403c002c1082c22030b0454114600f865035148200d58020b104001c00e4800c40c01d400e40f9502d0b4080d41c005100d2110300c828131050769641094020071a00100003e041009801500c02031644911800580e0000c80021002c4200c1d400c0c0f209140344116801081845024020010045440f00000c4162482030300d0111303898440c04c01083c45a07441500098400d400d00d40d911074102d5040d0750b003414480c02600000014402c0c10b0203180d034010030001c003a01c400400c001c41c17805424603400a02d440d40c0702510000f148005130207014280348010240800e8940400d0081055507a14055140901305a207200000c80a14900007940c4d4402143c605400540220303544211070300948c10b031002d17004050481c501c07030311f098a51428030350002d0008902050748100e004e00480000c6124901c03881c000750089185884a4500341c034541154840b4001019980030040790320388403540380e80150144a800402c0c0c2d07003080164070344040c4050b00980704204160380100114610304100c030598a0807403140010700e0b10b403071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 497383408 1250 497382158 497382167
    0xa020c010507120f201609140f041a010816060509030307260705100c0302030105090103021c120309060b04020a091a09060403081804110901030c0302040807060207060f020705060304080a 82
    0x1000c255554103138107017200b003074010101d40700092460b20a1141c10803501c0d0070011040701d01200c85940e0100c040c10015489029110303040b07070414004c00041c140c0d442030034a4005140d609030002c0905411070201c82c510707180b0030320b44240606075509003e818140c1e20070100f613590041d002d0213480e48030350141200c11110f204809403821246019065911038050804035900c902c20b4901190031b514000161402c184030f4829031341604d070014508106a4a15020040c0d084a08564180a1100d4403505400a0301c0079070990fa0303222542c3c07000701c3c400302039003006030484480600d26802940100300c00842698000191002d482c00f0042d00001c40710340c0070040d205401544511070700000002004410300098001a023207401a0f140300d0b00d0101506000d10080d14440307200e4481080040c01059030641c040d411110009101d881d0060400fa505c400e524581b40a9900c101c2c00750b041800d051010f982d001007401c5110303541c0d000600d071691601c004140d00384801040904004004100304c040c15126 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 497384658 1250 497383408 497383427
    0xc0204020406030501080613050705040b0f0405161824020f0307050a0c0902072004020d110403050129010e010e0d0303140a11030f040204060f030501020a020c010507120f 75
    0x5801152102e8985402800410081c09090098403ea000003480c011101e50b02003091035001002e0080c0301e1030901440098009040310070b07400007082170890202d0722a845018402d114095440022070800f680140030740442001c80040030203801d40c21310500e01c81180b1140e10303412004650303100403003a420803428900360401301000d5001c00218502804070014100236001d00945019800d40e50720740c009001c1b4880e105000700307101c03040b0641180580c44410342c84801240a40094a0444d59070525421550480f40281c010940402c0a009014091040007140c1342018048007902580406082d0b21804040c1d0080c104010700c560f00815034031039800c0010040001e85440c941044601d00138003d030206c40c00c86541d9010840015494184d40d0151504c03541001120519546a280d0307800c200d100c0040040e80c0003515040001610700b05260003000640c0a1000140c0318189104000d042502003c0340d10f04000060000c403001c1024a0f0300d0010311031761800c054083c0343d5802421303030b0344090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 497385908 1250 497384658 497384663
    0x160203040302090c0c010501060c1101080c0d1812020106030209011203120e060a0c05090607060902030708060906090d0206010b040510030608120a02060f0c031635130b0c0a0c 77
    0x505201380043d40124002500c0c03888503040003031000d03030388410049960794441c0c100078055502115040c074413075018221071038001101000003481c1110204203141560115806060401243c88a02c0c080c04104c548880e40c0d000944024020646140c0025550f01d0040c050000b1202d400d603500c01c101400350110440c15600440c080c42600c1d0692140c507294807044840400990900002c92460f511540032150b40310801002d56040c201286c840314000d0641610890b00f40c0b040410100380031404105c6544118403020082c0411320740480c05a04290240301c200307017594042e8005000d111615402c1d01c0642e001a9015143c0100d9524124040c102c1503200b01c64901500e10050ba1140d6400004c01c54000c10360212811500d035030442d000219001c64080c2c214a1040c8003081001c6240c4402c0e581c128603d00d0b0010340760340d090096004200d00420711141c0f0702580880d0781418103032890303420b600441c0c0303903401800c98034541c88034003c0201c01444048220400210114158020403552004c580c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 497387158 1250 497385908 497385919
    0x4030b0a0906060f050906030f030a1b0b04122003030103060903180608010518060d12111209040f050603060402061b06010b0a081303020307020f0406091406040c0c0506160203040302 80
    0x4c0da41c11504103005118080c103401203941c680000d80c581400101c18112005650040d440d26118020403034840300d0b01203089425050b0440e070000824031221809004600805030001500b03c2d150000d00003110407036942c28140700b003051500740480048180d80c1140d400802c0426040c0c600c0c6803c6035240011000d180140c05101c4003c01d2540d40000741c40d0503903d01782e40c5100d481100d16003c1c00c40c420115215580307d031070300f601240040c4000c00304a042c0469400d002d00c1160b0f52200180c100600c02d00c501002600106010506180a010303948641c40d034030358100110300348100400e444410040010b402408006100e010515800504011040b00c0c44261509941c5498102c5030a81c0007071036960004942d0302c040f81e000361144110000059040e002545014030036030900400c11441000b036640550fa0322000240b104160044010340981921413588914160040004aa0f00c00b0003800130000440e54500004400084e081c3d00705030035130941d602e003889458080b80355202e2600000d4000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 497388408 1250 497387158 497387171
    0x503030f0103021314040809060403080d09110406080c040b03100e03030604240909060f02041401301802180106030b0d032c0a06020c090a060b04030b0a0906 69
    0x180d50041a14141d034800c030b41110a031800c0b000140195021030180c100c0000442c4042800210100021f00d0b040c0400f808070b608095803900c0d00d03003540d0014000d18540c035450b40d541c1010400442245401c1e504115400c014403424508100d58403001c588869004a50ba028191030302d070380400100c1d892075401d00c0140555441d54008545a41060b6480d500403130404481c500709080305240e008401000a45040e5854502000f84c40500415007003950815500d0011740c401e400180000c0c800f900403045d50300700c01c9407280001440440034092014060000c9401c00c0b84036503800314031142204a29601183c0c900410400700c00103810540c0095228111007015100e1441105003d03049540b16103040120300e1119080c400c0603100321400400240c100c40d41a15071f2254628200c0141601580b05062009400e010a04920311900802c000d43d10540c0d001c181850400b00762980071402440a100103440c2c000c2561143c0924080104949501000580c841065600c200c1074180c0240701030016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 497389658 1250 497388408 497388421
    0xf0d0e01060807181116060605191e08060a0902040e01090b01171209102003130506131703070605040c030201080702010b0d02041d01060b1305010f020709050a0207050303 75
    0x99035900c1c80b8802c41070b0004000c4484c1080c05120303000303058091070445450034000c0305480c84021070303150085803a5640d0381c074049001e480f404114102e02030005403901c81981000c1e04400c00242d034240e045c2d0030285c5080103100500c004100383c3d802580c0f2407008903507520b81d40300240250481c8424801d241d803a1052840a2004c001c0e0042e040f5001d022038040076100003480c0310340324407200036601da013200b040009280720b0a0644101908200915045002c00c4900c0c461400c0b9041500d086040c030703400801d013080680d1405a17202c000b008116000303403601b0140440009110424807524140541e00c200c01102c444040c030465126540c4210304100310314182ca000200315031180800d900041c3d241d0700042d00300740144a0060142070003420b02e1031b8100143c2c02c02001d05032115848590940c4810000e149880074041c03003024111503c06071f80c90f504540117402e060006a8403480c100000c0c001310703c0f10960041512070945503011030115583d924095484040d02c1004401400703440f001041102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 497390908 1250 497389658 497389663
    0xa29090304030210080403020703031211030703150501110703080c1c0c03081b181201180614060108071202070f032610060c060e0304081e070b0f0d0e010608 69
    0xe90f842100c86081501020604481440c0308803001009680000c2060010a0007882c811111000c151004201c0030700c213031144a00c1e608161240c4012940360b810995101403a001424050710013071030030519042c2040b088030759800c081d101c080d005100000d43d03504900f000382b1400c0b0903a400d6030048002d0030f022060080400120302c82c00c1d000960448081207031145504150b5440003c603603055414114080150200040d02c0d401842e4494041402c1c4100104280a050f0780c105884080030b650902c1401c10700c1c15990f4590386040310243c841e003040f809072380000c04d5a81000862502e260110600ca01c0b8100a200b0b00001401c85400d40c00c07d0403c055020f251a5000a82d5440c402c0d01c10060311100c1000c242d0684184881d48000b050500c04244605c80c0c450100f801440e02042110510000c141561b12a401003111604401a507001402a202c11203040650034001808901c2c03500c81480050300598a00069503000060b40b0b942400454208187c003080b401c000f00a055030720020b050303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 497392158 1250 497390908 497390917
    0xd020f12070210060806060105030a02090a051306031412192303010810290114030c04050a08030903101e06261c0302030709030503070f02010e0d050a290903 69
    0x180d107404c14501042000000c10b609001d1441a1107044c1152034406a00000c2e4005c040031075001500f81100003010b59420f0507050314101c0080d270015007a030035800e1140406010060380400e40c8c1c4449030607900c4003910000c0b5aa1088842c15070a46100c60600c00c4034000d0580824440700e9002c00c001074020300716500110304a428139412908030044c0c605404040e50007460000c0046d81342d00e50540380301141001d410b490002d05161000b4411783d10610407009402c03c4e690714079620404036090001c0e00b04249000302410192009504205501340040e50310b00030240320303082031603d40c038070805a450311000540c022020000180641526194841611613542110500d5280343c809005d41d030040100d0200103002807444103281081000c0c01c107402960024001004200c1d0301480000810020b2000c2c0080700d101c0d44501c4507c204070f0000401c80403007821541d00c142444c22040b00000c40010341c2c4050103600c5203c070203c8111090400004607410410001448000303001c00003c00030210082 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 497393408 1250 497392158 497392183
    0x50108180a050d11061b211008010608032b09050d020f070b0a020604060209190308031506030f040f0302010f021308060a020c0613301202030c0d020f120702 69
    0x85044e4010301c44226600e01c0203071040c04604810500700b4404030f02901c028005514143da40da150100c0010644141102c201c580300008076007500180303e48242070080c01c0040000800a41c2080c400300c2c0d2801c0c0a0b0980300d00c260102051090010000d0f01a03004989502e03040803d9801e03000c0b8080b00691145c1c0c40c60b840030014080c0c0070003c00c529240400b9140c8802e41c6500620060b540c6988800c000d52040d000389900080f800c495201000020301040007862082e2074441d1a42840c1145090080c00d50024030b200b03000a008112a03103d01d2079503168041c2e08030001418403072050030107900401501c2811820107000280c8041600c2188015000f1114183c0c00c4803440d5407900b113808124003e804040115410003004142042c000400940c00c180c00b60030002e00510701c110900d1061710301c0c002c2c0221314907a10103033100c00075007060907172115548046081d490751401e0500c1220741e1003100b180005096000c5000e9a0a05e401d100791804802180301640c40d60601d03c00107982c0d8046100c55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 497394658 1250 497393408 497393417
    0x60906010207081005100f061d01020109020f040911090c0c0c03010e0c150f1801020c18061306080703030c020910031208091014060316080601050108180a050d 70
    0x20400a5200051000c11160940061300b030894501d01120b02a14028020200807002d07013402040c189402c00c0080e0040c0740030f484540140081d600443d091082003c2c0045c1507900d80041c480150311020382d2100c0c0f500c012280041c82e80c0f181d00e486e80c3c448003116070301900a08003000308071500403040e009041c1b940c82d8000321381210403014101400d9840110440700c9580200d000c2d01502c1c145010800082c01a2100c06400c129207203000c003100c1c0d0484410a82003910f21200d4804558040c05410a00c0d1410b032941c1443c5014a8810340c0301c84c101500303003400784019035047d03440740640d0742c07201b4082c0950700c0c10380e20030035600e050051a10006171400d03849410380d1004980c00748102e180c0c0400300e03540140e40c180c0c507040c41c0d002980c283d08001c0c56050a070003035510004101903d0300c1030940002c071140303070003206080c40c0080c50325110400210407045a4013030410f101e22040090110b04460003440c208681e0743d00c480300ca0859000d40c5001c60b00c10700c01c2003003000420038045103011905207107680303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 497395908 1250 497394658 497394661
    0x120e121b0c0604140a090f0209090702160608070509180103020126010605030703022808010f1a0309150a050103031805090a050c0919030507090506130c02120d050609 73
    0x1489440d480000540c80d4800820032042103844c581a0f03c600a251000b80404840f540e1110510203581545034484850303a4009050062450100540d54100c40c030b51004046172411600000e0b80c402c03e500402050142c0c400028030100d00c034a0440f101544050054940102d100d40e01e0440401d0a02089010a00002c032032480350704044008a01e0303281c0700c201c0702c0701e5034a00202901c29a1001d0240310400d50200286241c2c0700280302c1c60452a1590602d0307060310590b40000074450041030300040d80315040413004012198808008480c621a400480c655940343d14a00340d207084804000640c03540304400410200c3c41880c1c2c0071504903030190301c030390f20525006526240e031800725024250f4011500400700e504c01c00c99034070940d072008180c01e440d4502110500060350521150051500f002040001441002810702c01900103190640044c80682042d400091804007841e842c401d40c40da6aa40041e4a070340308011001c103006402c0d410650b106201d00c8808040d0004a40840c00345c1c20820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 497397158 1250 497395908 497395957
    0x60a030f0e010213031e170d0614010c1b1214070902131203121a1503060f0d0f1b05010e030c10030902030a050d0309140601080a03120e12 61
    0x840b009100315821306005182942e40f2620040c803e2420344050b0171502031024006545500030074075400c055003200342c80b4000c144402e000d0320b80d6900320308400422004090180c1c0d80041200841940c0480250343c030081d500c8103210a0f250552000c014100001c03040807d00450342004e0340d143c10014140c03032240361100300200c140c0c8a54069038681554040b000c1058829001c3d041d01d40c24032a203001582c2c4040c14521100351050380141c41e480c2d02c1c01e480703e43d07040d20b061414082031144c003c000c2400c1d0f280000c001142e00801c148090301074810801000304000c940540149480d80c0800409071242c05409100001c00b002d01500303000c60000701d0780703c809103000079802130903050007042d506600c0e8101c2c1d42100508030b0300c5c200300d825201d02e107807074000601d041c0704c0840c0440b030030345e00013420417558209800782882000c1010419000f820062042400100b18550055054103140c00400d2800c042d0000800070f42d01c06040b180603803005a20042e10b03000050582c451004c1d0051004105c1d070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 497398408 1250 497397158 497397161
    0x70b1008060105061e0705010e010221010e1803070b090105011a13230402041d060604060c031b05060f06030607020c010c11040e03131e0e040b0411060a030f0e01 71
    0x2c0c01030644c440000d0008448080410101022407000403054a04200c05580d0303460035110314254244099401041120000795600d0440c440d01e0b05912040c4480d501d0300c4540040700f400a4840d8284501b400d441e4004664200102d404403035100140b092a0701d0003608441c000d040030302503e007100013050030044d18a0741c10360075607a0004031000d25210702d078079205100300150352941102950000b4004c040c1059640c81c80900001c2c415083c0b04400d0440ca640c00314815100142983d02c100404e10050110315400442064002d83c035041154880f04002110030406a00880083c001c2c85524104103103414081400c5029030300540072a8003684035060160f8940e0035a40203540010200d88803031021500500584040c4000a0000241030903896000c1d070030f40d400782c03a1507400202d01840411490309901090810000032013a5502034600b8151402d280ca10702800c06054120303250041000c0c000101c1841c000c00b500105456a00c098009001e07000d032800d8120611003610304900d1100701c2606 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 497399658 1250 497398408 497398411
    0x3240501060c0506060907020705180a060b0403150b0d060501030602070b250810030b09070f05030a150905120a0e0102010506030703030e091902030411190302010818030f070b100806 80
    0x48005000d581c5d40b00010b01940c070030000c003940218840c0f02c000003065200d000c03005410944d0b0002400262500c00d0b03461055891b2603009914003401040100701103000c0c401c00a040e184200703404281010200c001589403005441c0c0903091301d20f8400004200a0180c0c003c06256200350624005d43d41c500c102480c00c2c07102c44d480e4192402070b00f458600345601c682e541c0e80d0b002800d00d004103005516a180e101480004135030098955100d0328050041881000c00f00300200400c40c02002d04186d5a5143c154a402c07070b11b28003501d41d84551005003008002d01c010034125540a6000f600c54190305001081501e25109030fa026504e4507002c900350341800b050040640b40c140d180c0e4025040c1e058280002c9410082000140070442c20350b01c2413900b154002540264001d107903d11040d8a0380007004600b02c0101a01c0b481291007880c10401030340c020034074581c0310180c4001c40e40b41d09544000c0c642180720f44004611742040018521040041c2044920f0280d86a001c0104001c2c0d1507045041c1d84000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 497400908 1250 497399658 497399663
    0x603100e060703110708120702060c07050715030e0a0b06040b0f0d02090c07060510090c0e210f03030c130e07021032040605060613091503240501060c 66
    0x1081c800030b000c0c0c5000381c0040c0100c03899445001c1ca41560342c3c9580b101e6801c101c0c1c1c0840040b41c24418003940030380c1001600e4100b2a103140580c64882c050741c5095070764003940300d09a60b90051906080e070907406036201448682c0c414050700c000096610b45014100c100300c844910031840c2c00c15580c2642481c403500d520300072010302403c28800b125001c101034560000c000303080c03917901088000f001400710302900340580c1030758015000c0b2500b00380d6403205990710b0b21401030070440c010451417050b80d58003400380c41021900c1c10b40c2040c010752252413801c00d22140d003014645d00c800010b03c031080c00f402ccc0c018410410780e110b00f40c1006032683c0841000c00b40642d0302c500143d0104191a90030072055100d80307401e000840c5008450302003142e0201d508114820a105252041010041440100c1c05407540c0400102c40e01c80c40d2403000d00c81924450040e006801d036055480d00c000c000d44851a81c0320f8041c0d50044a072040180c10862600043d1903000d01c0481c001e405d01000203200d60151024611196 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 497402158 1250 497400908 497400913
    0x1107030201170411060d02030a1b170705040b0c0319050a09030b1024030b03011518020d06120620040b0306032503022b0818040c0302030603100e 64
    0x1102c4818601c414580503005680c4500001032003007003551000700a04d504242e400300940c980c9044d2400804a411940c03106000303a0550401e0100b844c2d10400e00d00c18074a0390340304891030344c0310705c0c504685a0046030071600800c03c002420b4855401d000001c0e0020203414502c100340600319038021241c50003080907107400701b9000401800060039070400c80307621040d0608030080c0e2940d40d003190121030034104c041825091b05c03403841c12078182d45409504108481580248814504c07e40050180c401718820400942401c082e15501c64040d5012500302681c10242803206549030300039071200d00324200048421901e814000b0b8907480c8130090390f94405880f010824182031903d11040e0b083d52000b0103060f458011440f0f4100d030300200c4401d03500e070081400d01c018901410f610502a84003154603644c651040807851208410001e90322a1000c540d10155460701c0e4840b51001142d008900d50f03000358004d0501184c04c8a041c5e040d8017031072180310210202d81c40700740000305010403070b01d100c030705240541c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 497403408 1250 497402158 497402177
    0x403050d0c08071712060d02130b01021903050a11060903030105061c0f0b0a050405010b0307030921030f110703020c010311130b070203010501050312180a150e011107030201 76
    0xd801500100341e00c900514849103810107540d5001c22000003002a4000898082100c0c1484407240c040a0780c03020007a910090701d680a0740004400b5038003130120030501510b400d03050240c0d0744280300300000503403080d4010035030a03060302d00600396810607078110b400140d903c103640900c44030001e00c850240f40650080e5296900703040c01c5c800d0a622503c4000300c0c0003e482103009040c9a10703c282244c905018200243c158035801c2040b03040c0c10300d9840240b140d41032030018401161404200c82d001140c908000410312200c0c50b00302050a50441c1c500c0402c03502050070101d40d03405030001c0f4802422000e0070030070180320308081003990258150242c0141e10035801c845281d4001d511180448600d003c00d1810711050309203a584140b101e0f00400303c0e03114042500c02c2103007030900910340900300803805010110603a1001d0200d50007900800340300710101440c54516a210070411b04041c008102107000c074941450b6010b8960140b203101c03640050450030101180150120b841402c0d01e60580d070741341c0c03803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 497404658 1250 497403408 497403433
    0x1022404020f012105011a1305040f06150e0a0f0605121005030d020102091807080a09031214100e06060f1b0102162d2003010f061a040305 61
    0x1820b0b085101810301030001d0300d00d0f0315403045400b4031034140c400060104c0c0340c0d0b0500e03110548195002005502c04031045c0848010b0595403000c400903103070191400558000c0c0d20344a4809080194071401c5180c0000701104102644210103c0070044259010400e5580d90001c00d40a01103d104600001c3c20034040003007415100c144540c1c0185101030b02a002c01d40364000641404419009100940c3d4006100400d0341842203800e41400702c9140301c4061440c0c41c800c05030203590014104041640e81d58032120415001d44654881489001010046c031140300c07207003000c1d042e010749000451001110000580101c5000745038400c4101030411400d210140183c0b110b1782c1c015441c03c001c01c450640c4400d00c00c0c04244041c2c030030b0395035681070751240108034100607075503607101e0000c00d243c4241d001c4036100d00022155840d010960204024020480441015000f00340981c86140e06508111010700e200300503400c24811344d003810ba18041498202c0c18410b0391803240c2d10006145810100c080d104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 497405908 1250 497404658 497404669
    0x4030f0e03070503010e150f060d080c01022b0b04060612090f0f05160b070314090607020909011b180603090f120801150516020405060a12110102240402 67
    0x50850050115401c0b036444000003800c0d2201d520506443d17074000000c00002e1075074260125040540201c1030805420144085881034000382c0b0b014042d000001032a840c030380400d60448209a8001074014000501c040300d80084249034450040705900300b550840703044c64180b28000841d0700359212114190313a0b10100c0005001450b0045e01c0c3c0c601079291000210b40c81c070a541004a1181d000380c10a2981d10ba10001e801c4925080600f40c860b003481604d0011b90081201d43d40610001205511120010000340a40c030540200070340250b1010144440f4910540080c0d1000030641400d010040015400312001c050b02e02c07413402121608141004524087d0b803140f0b6106029218007800740c0076585603501c41c21042c015072000150200c004010b0040aa40d2915143c3c00b186080340c42e22007900c410308501d44101e00c01034451603035800400c007280e441c1207165004240e080745540002c003403400e0103030340341c6610310301c56002d800307200840004c00030800045407515115084452198a49409000c2c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 497407158 1250 497405908 497405927
    0xc050f090402090a110d0203060a060903120309230f010605060a051b0c090c07020103050f0108061f120f11090105060d050c13120210080912030a1413060b0904030f 72
    0x380900c2d51409017010240c900c0005024240340c5680159807828200c0c14041c20b4020380d4006810400c2041060001a403030400c004504011171401140814507401c01a08146400c2c1007000040a601c1103140a64000315400c815800b040c1c00800c045a518002c0c82220f2240300321080000e0030400250000790035040798001c1100000d0103d914010504020641911054440d000f05107804500c0c04d04546c1d00d4000c04d50b000c80c1718021000c081d40741141096982034003808042c0c44030a00314031022040d07400e0110750020400c4a02d00c82006a442c104070408418601c81514409040201030126090000b0280e0494101519040c07505490b00c02c0d0400400c8003500890750010200143c0d810745000c1104400645051854501c490030103104008102da008502d8105200c0b010381007142403007021a1582040c40785417003995170381e9140c00005004121032103500720001190340034056000716029200e05054800d4004010f1580031a04205403c94121802800a502d201650300360f1880b425254 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 497408408 1250 497407158 497407171
    0x6071e140408060103030507050706170a0b0d12031e02030402030706050d11070b07020105070e060a0c03090909051f0603110f0f030106090506010e01050c0c09270a0c050f09040209 79
    0x904182d00c900c1d00383c0c00d0a42c283d0081d000208081220340503c001800080010301490901c5220342c840c06141403907a1000503c0d11001c0c90b0341d4443c808c42511118481c140203a404403a91351002d60f4032001400800e641005281c00d5011a41220485102803003180e01654000b80184107030f9207060422900c40d4040e040900b151078464421800c0d682b008805040c181c0d2140c181072030507280c940300c000c2c03c490004045104202d03c7c002800302c00c0c0c6454040300c00c003510500e8007080040183c1410740703141240d6030101080614007001130082c81400f0031010b10000c0706103038010241c984400e02e5016030744240400f0303051321000d4900803104e11300606060303a0900098821144a001d140c0040e0840c2c0e0140d112080158498040080c29a80b14800e00010750342424013508013601c11461315501d41c41d20f40b0080c02403418001140c0c80e00c501000b0003031044002a4000c2285104545658a900407180203c581e17040120000c103c2d031400e01c800c00780a02d40a0310218a5507035640800c8400b90380a03000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 497409658 1250 497408408 497408447
    0x90b0607021216060c0b15130b0120030711010801081b15070b01050423041101030e0d09080c060705030d0c05041715060d03020a170d1a0306071e 64
    0xb24030028110300c1030030000b0820b54803817000380b00440c01c0960011000802c45410280796a81150319903035032000000407807a00910000e548500400113980d003203128003000d2946095000d000c002510000000d081c0c480c450102858035940400064651510130b0103001c9894020780c007510408003411035002020b9034020001d00c01c540d20342d200c0f0802c0340c0c800034058406070786400c01407290b41000e00aa0039003022001043c44844414100d8028240018100400000c07102c00c1141442c0c1c030907000003c0b00c90000064901c070100c101405440ea01840c4511f6020340640c1d411101c0354035001c0d0980340d0150304480518648149400d600000700410388800d4140401400082404002000d404c10608115401003461040000001c099010000c10070780c403400002c0f44490010780e0100d00c0c0200d0503444220114050507026884c1468003d000c3c0c0510386a2a001c4282003841040300d0007106ca50080c1c0641d001a01e61000c111140411550b080b0443c604100361049103512a5100c09030019031a41c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 497410908 1250 497409658 497409673
    0x1060e0112030207050603063106080318030a03050306010f0c1b060813050309010c06060e150f010306031e020312030c09031204060f1202131806090b06070212 70
    0x400411a0000e80000d2007904103001074500b01901002624050882100c61500f14581030001034541200b000702424107150480031095840100010030286241410003400902e03100e1071710380c0d9290031020b042e403031b000030702202800281004a1074490846d055501e1134a107995910054071300c41c0f92521104200000c2010190104004800f0072034014040000c1481c840d150040c000c03c42040642a044480720350001800083c0001044070710002080c00c3c4802d019001d400c100004080a40c0061252280041007200c0605000c4a603010090101c1c0c1c03805a80c400400110111025404010310710001051001100e005c80702024405501c02002ca41e58506001c604031060f40080d910088078000101d107211091406000303103a0000d030b87c10323005400d00b031030910004c183c00b854803041d001344a030412150b00003c41c2a0129410004a0104a0b400aa41c3c880d4180003c040c180c600e5105880c1002c08242504140140c03550840000c182c23070304003d500d03020001e03081c1c00e411090509200c0c220 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 497412158 1250 497410908 497410919
    0x1d0603150906011e0803180102160608040c06030515061608120103021804050c24030f0105040e0309150d06030209010b07031e080a110c072312060c03090106 69
    0x20428428415007014007181c3d4900080d6071a018504000c030004003251300c0c2c040c80b031741e0000401c1e40c81e414007203001c62060040b5980141d0410244100c50820010b4950020078459005080395008904c1810b40c0751019640300c1c0c0071001c4a8061b206900046140d0624904524004001d40880c108a00994900300080d544100316544000040b003946001c2100400562400d2401c000e0303e600d05c42d002081c3ca2130550b481580b20301803003039214801c07241c040f40b84c53380b942c554004c2c07500d090700030f801a9940c1c10040c5100c0001070f0300b4800d0502c40c40c1024140408884c001c000d50307281c01000f821030b5075501c0011a00100c40d07040760101c100e05942c1d59400002503502c00050034000c100e5002c80d2503032845282070042c203501303402e142c1c940040205034840345d5595009909603805500c2050004140304910640d4000b440750b04040070a9100d18140420901607109646000c6805013a00b81a04010b0806005506c5500b00340c044a030741010001074100020030300150360007100712000003030254844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 497413408 1250 497412158 497412193
    0x1b1011010b060d0e070b13030b090a0209041b060e150717031e1e060105070204092102010b0d02060306060f1603111005010819080412060b0306101d0603 67
    0x207154843c1802e840d1007881180000900c200d0019148000a051910703842140c24220a401817100502e05102c1a0019160308420700c0300c00c031900d600400c0c4d04828140b40c10300507031039407518000224040f000000020706500800c0620f4119501a100d24001000180c050020b80c1040f0026110090740c1c1400c0d5141407081c01c0114410b645c6201c001c199a10b6007404002e4400c401000c1c0c3d0401d07104101c0204a07840d40d00541ca500c0002440c145980b2041480850040c01c043c0307800828a1401c00c0f07a032002910446c040d001c4200303843e03000700010802c00d070402c000b0303502d40440a5007100d010408103030380b818080002d010382451010700c24580541910042d0446100d0310050303000640d010071400c01e1810500650b85003000f0000d0074007207541000e001d540c54107021403900f040199482e030f40381c041240d00b40503140141800049c1c2c003803642e0315041200140c16501e034154405d0144e240091034a9140e401080103070349400100b048400124503006600700405071605a040c030510b18002010a43c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 497414658 1250 497413408 497413417
    0x1207030309090b12161e080c101b050d0e030601031a07050c120304060b0414190b0a0b03090d08010e040312091b150203180609010917070303021b1011010b06 69
    0xc3d281d00b010003924086c444a100810004005026520480104100d2200003224115500122000b0224516490b001d9a02043c00d81d002c00d4000030103080801400004070364580480c0b2551114031030340840000701074552a00b40401000d80c1d041c41507403000101031a5400d50f0240c00350030503a161034441d01a036403400c14501c954020201d400000c000070024540180d000040c01540e042c08a040d21411b490f208410003891503160342c0501582a02400c081e801110070548003402c04440076841c0c1030307003000035442202e28085900c03079a014240d44038855280241200e4028101c82d044d601d4543e000c65066008444034052161100540c04c00310700501d0745820004041d09545030404d1408002c8220080c50101030829500144890790010503280d158100309441141e440340d55400703020042e5071062694008000000140c41108081900081d401c81a40d0283e001c8610820901d10700103a00070500314580c0e048280c002030700c8005d500607a0140101340d58007001207901d42c090404181941c20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 497415908 1250 497414658 497414683
    0x518061218191208061908030301090c09080d0e01090b04080303090708070b0a11010e01060308071b050d0b04050c04050a140c0f0319060308030a09021207030309090b12 74
    0x15103070300d090000e20402074107000142c0d19a0207541c1640d50340380c9141509610a6007000d016401c000140c85540c0c0400d0381d810f04071040e100b2000140c480100907a242c209001f04036031145041d0002c07280c58040c00001080700c81d540b00509200c3c05204007200e245050740f0a1a0601c5070841010a00c0e0340321340051f2003d00710500042d5200c0c070b801c8103180e18000380c5a12100c51034000d801c007030101c0300182003201c44a900900300707a004202861205c5004001500c03481c1702e00d5207000780110404c210354009000d05801030304c40c0194540c0d60365100b00e054400d80314060303014003000550000600800542903010f0300541c243c0743c403400c01703074049002d9910131940400364540d540c1100c08110311091f1340c03a803ca000034204030304142d00414071101600c4094100e0428500d42c13010030100c000709801440c041c1d81d1007030445031241000c0030034901070505880c0481c8115155000c00b60711100c0005c142c4112505580d4440902c1c3c94402540c00070804009242d03001200450f121040e0001004080501e64 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 497417158 1250 497415908 497415931
    0x1603140106030b03250b07020d1a1e0c030103020d150501030b0106030c031118030f070306020327150711060c180a0b191b0f05060604090305180612 65
    0x400f9002050f0500e0503c00c2107410030280700034039880c001650700b1582c2c00d0361458200035aa8801c1800010f030641d2400c60020300308101840c014040c0b003000740c00c03640500401e8101c43d0103210950351520064000312102c1404800920041001d0b1030440741c00340c04240a4216601c01040280d40d200580310240c0003034559013075070001081780503414440d410000d00c83d860108074202078517250b400144152600c100013111210688005076906203e030101c0300b05107600702c5542590b41c1c42c0520180d082110b0701c04004050102c4076411544410001118031300c1a00601543c4808246000755100c02a00b240c1c2007003800040410202c108000180c05844844500c58403a0609408504102100003019000d211680c0040010038210303410740d2004c03114190400c240c88400303c811210950314030b01c17000d0081441c40314101407106251703103610f68074001c505803800740c1d59103400c2c04152441110000c0c00100c0401c03407190b1200540150100c00d210051080b071521406010060801c0005d403060100007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 497418408 1250 497417158 497417171
    0xf051009030f02071406092d030d0c03050a11030417030d0605010915080714031e01080c0f04180203010c0914030604020915040b04020c0d080112050303160314010603 73
    0x16401c030b9401050545144010550030b030402115540401c80c01c05600d01545010a40346c0c8076660300074800194501030400300c45240d0413124144140d00c87c01106034000d0003060f10001042d481040c2c110400f980546540d4601b819040088418406020820b03900d4042480040b52000400070040403403005e4500560700c40a40700c0f08030301103505e9503100e14140181705008001410290b50708107100e0707280382040d00c0c0569941c1402c0d51240303110100b1030001d041c00030070048900c03612000d071003418108134030420080e0380702c0750516a1084408905540600030280f02c8041e49440d0300020f1904200441000c064202a40820b0a4074920a60200414040481070010890045031811000412002065107040c02d802140741500060300300078003084242511449901c0300c0d00050032030701c40a00111b6440d1881c01210381c070340801e220004000303a1001700010720794015030101c410035030700940510302d0750711007400c01c0ba4000a0f2104110502d91070700f0310038000c101c0003004035008269684010414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 497419658 1250 497418408 497418413
    0x30304060207050a080d0f08040804031719090803160804090501060503181207020f010201090c0306020a110f030409020c12030108010f0b04050405070509090309031f061d040f0f051009 81
    0x803002e5600b1182c5c00754040305100d80c0b055400207002c0340501c500e081c000705c00c1e11a41030061b000c2c0b19940000d8000a60540f04580c280e1408000380616180340b04150340c030040c1c0c810111340724403661049502941c810300500032a40e0200d80554122441080b55a1620f640c60801e041a80c07002d85c041030106001004104054280c83e45c001102031744940900210b50080c01c0512083c06400800fa0161800d8412010164003d6101220300c5402031201c0c040c40e642c0303281c03403000380d4421606980000c02100009003014000103040d426409210050f5041504103081000290031039800c82e0a58815550640c0c0c07020256001503020b4410513001280587c51a044181075071401c01d0b040e40990720f001d0402000c94804078164083d42c00454005d04c80e5100c81c4411032841c024064071f16854002c1c240c02006400e004039603820309503034220090016a40d40c41201900000030000030702c540c0352000009000400304000b800d541d03449000e9242d09035041da10f4152030891071403401c21005559200d010103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 497420908 1250 497419658 497419669
    0xe0a05070e19030308130816021009080307060c03021c0c02010b0d1a0a0b04140103051908040605030601140c10060e090d1409060a0801061202180904020a0503030406020705 76
    0x70382860a032109501080c01d41c01095000c12144400740800408001241041034224481c50440341c00840c1a83c507040d66100e07813440901b1611040341302d4040d130803040648500800c1c000c402c640740017003c1c0d420180c0301c1d00d0705806043c180900b03508140d820090114400b04c0000030501d84130a5030350015504003401d1000e0308450aa000f050f2061040a080900090240790005036040034078003050496110200460054107800400030351260402c00c0c0c0020686103002ea06048900031812a01c46c0e060110344400105003184002d07004103002c2109101c1d00d806100259044003040c0340c981180c000319298100241c100ea000303c8190303080107a028900480074041c0401808a00341c2c0300c00c6a0030101785c4940c1d44c158184501c4c051001d14400ea42c41d6a510005580303031401c02030409075449020100080001d8000d001d080301007048106003071081c1c0707007034820344d00c0004045090350303c95143e0800304030740f410000704102ea02c2078030000b021403981c030240060030041005030010307e44107040c03004100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 497422158 1250 497420908 497420927
    0xb07050408070e061e04060b030c1c23101a0c011a0609040e010f021201051509010806040e0f10051012021311120106081b0c0a110a0e0a0507 62
    0x106031031a0f503014819182e40d40d4005104000b501d1045e101246401070201c0c004d0f048642c0205040d4802004101103680550002c1000038499a5440902c080c0410bc0c50101c400f1200d04654044003074402048030500000002e4000ba456040c96200b2581c1c1c1d9410704009481541c1a210798101140201c0104024042c880381d0282501c2c2142c11018440045403050040c0160031b4461501c6e0803014005001c01c0d0720481a246640310306548d0b5104034010080d170f040007172203610b00502c4400296070766040102c1c20745004500580d80d00d1790a4540004200244c00741c03012080b0a40101d580d82d1508180c1040b070304441c0c01a000d404110391901a620015904450340b0030f242041101d04400c006948200c80720118404007580018030103044a101403250050f600410391040c460340000c9051500242e607288a949030300c202c20780070496000700705120b008900503a00c042e4041d6403010009103070700303040c0100514064031400310f0546d41c05090507032140030348002d070b52a50b8440138006596401300812 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 497423408 1250 497422158 497422169
    0x1201050a1508210a050c0a120809060106270806090f0d1125030c0605070b010603090f03035f0708151002010f0b190501030b0d0b0705040807 62
    0x38440f42030408214880d0280e560302c030340511000040c000c882140030380c0a0350300d0610132074115030414142c0c0c82c0100744150b400c180900802c11200000303a0a050014009040e50302a41d14041c056111511181a0604490300710071482410140464048010400a841400018000c2c1012a25200d00c03608103d1080b0b454010058068aa14260348000403001041000003a00040341d25141c8030f0598188402d03000103040e0802e2210015144d44e1081c050120280071b4007203413100381d9071238000342c04071084034400a06401d070140074000400d0090b849041019481d0826218102d0001c003200c241172010184208800389100c3d0f5154003506640080302e1035600000c004c80f40c43e550001c24095044024102801c00c00c0600c00980c0d481c04107400e024a150000e8110309002400030400780c081c2808000da4286103203040c400d55010b180051900100444810450740c100e420400110082d1107260314241d006441c9a4211f000101104400c078402c014036500c041d251401c043d51107081c040c0c9135010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 497424658 1250 497423408 497423413
    0xc09090c1e09140904020a0305120c0106090615030218091602100c1b050c0613240806010c080f030103060209090c0a17280e010e0318040b1201050a1508 67
    0x244990f030b220b500050100c140498000f105543c4038030024030350107199000105107015a0711500c4880700d52002070095010300034001c1c07100300d4032154904111030091151520300c0c42001c4503d0344031806a0300400304800c80f0140814217040e0403010078001d80065580d05070644040c5c03010358220398140101d0b040342d650203c00344141e03110b264004102c402c400445000750f0b2001c401c0802008410001c1504440c0042c010945a00e2160a445101115031080b09040306c864103035140303800794203d0070001c14007064940052544a042c0110740c2c0000d1401c3c215800c58042000303110352680180650b0003944605005a56540c814040c8480c50710086d050401d240030030b100d0360400c1500480002c4a17104e000714030b803a6035545d107410080d01c4014016254110450b040020105100075000125000c031100000d20030f8205c194011a580d109014212420b0701d20b0744500401c500d45500030710800100141400034004042c036506007120700c256094107040c1d82d1600c82e21801c6c08040601801030100300c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 497425908 1250 497424658 497424677
    0x90d050f1207111210050f1021110d020a032a08070504050c070b0906070905060a0203040504090602090a06020309040615020a241e0f0203060a090c09090c1e 69
    0x1d4402c0c24500c000c045a100e218044e2041d6500d00c010050481c290401d40700920190030b004104880e541c8040e203102c0c0700700d140040e001c41c0c84003a80325084004101f948110203040402e8440c2c1c500e0b500700311001607020b800c640b000740150f587d000406024600030544801c00d05402c109610145514200c1c1c01c081951411040115110103e0b01c04200e800682d400b08150b41e840200c02550b00c100307400109103060700c0003805082000091610f10807240d9842e80d10f150313602d40c030400030140079020450b401640100701c28007060425800a41130b0502c10003001d4103100e40800014140700c5503400c240300680c800701d8881120b282c5170241e0300c024090350380306a14180f01d000d0003e407074400f00746001e041280b8000001d4640d040c0404120040441c10208104281c0341c50051070f0b0480712584180b0340d95013440c00100c110030281c800c50b805004001e02c00554503141031320080c00791020718400c0003800301c070361070006080c2801c0c010307000e0f83c0ca019601c0084814441000c20040d10b4001001c404200e10600c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 497427158 1250 497425908 497425913
    0x15181f0e1e041709060909150f0402090607140a053a1e0c15060303030e0105062211030c032403030a050c1c02030901120504020108060103020f090d050f1207 69
    0x910800385503c0c014542c0d90f102142400701e43c0f18031803900030a030010503641c01c0140c9125096900e0240c000d08030b81c0ca20100e08458104820b0f401045130050348501d007000400002800e0b0404844070040c50000d5545500c11a00c275a820321314010341a40114490074125150101c407101014060700c4410b031946003a03000c1481c0106a40c04042c10500f0001e021640c840005e4000e05002d25540d900c24490710b5000c0d00b032510340014149a120480200f400c2c09141401008103000c1c80b481650041c14500e0440107a4007600603012195200c840c1040e50790055a03400420000203501c65103035104d030355035a4140500c85280d501c4401045144011a444007880140e0300070048994042e114030f4004d4a400384640305508000c0c0100c035110082c0d1507080d031f125046801102806449400f40c94044180d421880302409455040310000d00250322100041d20541c0640e0191508200650105041c0b140800103c0c1d0700012034001a20384d5441342030919402d4a040040d07424080e40740250904000299 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 497428408 1250 497427158 497427173
    0x907060c2004110c0c0109050607030c0312020c0a03172a0d05090a02040e1207080d0615120608030c060402060c0109020303030f040203010515181f0e1e04 68
    0x4a00040001d8040d110414210040004035840d40360000c004110908510540036031641c040c030310400e8180916202003120b58058410f42d0110740001d0f180f64540070a03a54110307204c4880500441c05e10003201c1501403e050ba074070240c4105000c1000822000f80f031428041d10845042d00e8102002c080901001084106903041c084200c414800c103034044000252080414014200c0d0180d109182c1020000c0801001542542d444d0080d10b0400030780601c0d030307103a94490b0100720215102d09010007047d8001540c9900820001d4150400041e4850f01d5030071021440d078211070047d0000d00740001c070004130700322440382c1e600030a0712800441c600004952156144d01c0020030191044002192954200c00c0a401107410580d006065969070725112443d185070b00d41c203840590107903191500040d0300107282a0111038103800180250b03e14400300e40c000120401c0123065a04804400b1701142000111001c424040d0180100b48202031801c0c0c54001102410004401c0340a200c813000d020200c1c069 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 497429658 1250 497428408 497428427
    0x5190903020d030b060412061e1b0c03090302040903050d0507050405100c060f1805010b06030c030c070f02030d05180f010905061b03040303051c0c0816110111030609090706 76
    0x80c240480c9444004c1e0004041c2e006680c4440e903141c0203105103408000c0c1603480310940c540310712962201a00c2441008048032045002100c511410007800402203000b9041c83e6100c512034a000b415030358a0742c2c00328040e0344101d40100c0100e41c02054510051030386000c0e159202c1c58900d0414105031411000500c10342d80c807115a000e00c008245004240141d079040390305651071000040c06019030801840485403d07484003511790354a041070890031807034004101d0340a4401581514250b84440c140103809030701c0300804071176910b031202403400180c50034880c103540f602c403540364161507403040c0c503c0a140c8810131f10054491440c0001c60301c0b950380c00601c040c05503a000d5910035101c6584100100741c0189444c1d40b00e000d0b01c00030800004060b4810020300341c0199090340880303540070050f0501c0c01c0e58000b207429400314011000003038801c030321013400d070304010018604514a20b21040c61282103c0e0414040035551030f001080203101c0c10701c2820150402414401050190b01c0c02070018401e151 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 497430908 1250 497429658 497429683
    0x303022a0607150c17010602241305010c05090424031202031308030702100516022814040c020a0803040303150302270106020a0c18020f04090519090302 67
    0x1c0224102090003110b1041c1154003007404810000300e56621005844102030000240c0d210b5000c4d0000b10b2a2803020807840f81e1114000c0c2c00200841028a5208200340014501d15040d01070340540000b1403c240117902d03c00300d65450f000d64650061043c0800c0e19120071281c0d440e41c480840f001d10428030180c1c51412207802000d14105001c079240200d043d841901d000001501000b00049007128000c00203000c03181c42210f140540100b0243c1c1503401780180340c8141d4050340301c0394249025040480b09814489000c040c0d0a900005180c09454107403582e800c40e80d2450109100c5201500f041d20400d10421500d0004110f40035191303880d03040d14030000f00001c0400d601d400c814003401d4080302a01000c0d50740142130035840c81c0140c410705004d00900180311227200408000185403800461040c20250300030b0030201c2c1c0242050060940440d11141c0000f4880c2c2c01c0007440408617400b8050805000030f0200070a50b402c085112640f00944480b00114541c03030303c407c2e13200181c0c000030030030090350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 497432158 1250 497430908 497430919
    0x30405010c1e050a0b01050f0f011b0201030219081005090f15150d0213091b14040906031208060105090603130309030212010c0201061508010e0a0603050114010303022a 74
    0x303000c030b40442000b0b0035030b40020014031903c1981800c110000300c501d8141d643c180d4036581880340c00c400b0810f4860f040480f050210300c21180032440d03540c0380d9154240d458010304000d072501d0701c100040c01c0f0061144190400140c4500144818020082048001000e0441d441002410f0000c2c3c03064090b440504561254290380821308956101d004910441100c1c00461540302c44c2560b1000b0065404200e0121000782c03010008a295640762045169603004010070810000c1c140c40305641303d01004110b496000d41c28000010007030300710702855001d035106034600320444981d00c05c01345c0008005400b10341480803d0200f201c0382d490f80001d89901400002d183c040004140c1402da5200000d508007a4208100112000e6504d00540284119071050f60007080180e0390b0b0b9400604001610021200040d900d00c010041c40707808400c840c2d0822801c16000584950f41d40c1c0303403402c45012103c40100e110544c0c0c01002815018444003020034840110300d2542000c1c420960108080b14003424400c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 497433408 1250 497432158 497432183
    0x91516020f0307081b07080606040b040204152303090606040f0b09040c050a0f03110d0c1d0403030609020a17070306090603050f0c2211070515100602030405010c 71
    0x103208200440341d2000140580b43d45403950b00348940c107580103484446040301042500e00b40c81100142141c00c070b84210000c0c103202e4039072604000c01ba02c0a441031b0340e807141d0288008076040d241400018000052500c4120318889003441100d02423110f0602c094000d2030510400090034404a60305a12540c2103c0014640c2821017413140144400100c1c07a0704515010200700410900f52080360a07603404640300c14509541c0c1240e2076194006000023002d00501070521003083c10024041201c4510440303052010588408584200d04038556001e0094001c501c140001d0503018030800001d40750f201000c0d13151046c0f4000c05094050810462200c481268000540e214441d0344164080c1010010901422b566800d0040d52909031640c0b00c6098000c210883e900303441e007201e4141c1000201514100d9130b491f80480d00005100c1409a001103403020040c01c00003403020b00424213071580d0305500c003074942485030041d980c000c600c3d080202590310400041c08160703003212204107400e6000501c880302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 497434658 1250 497433408 497433451
    0x140102120325050c100c090803070f1403090904060203070810030b040230030403060f090b0a020304050c06070b09010c020303071d030a02042306153a140915 69
    0x4502c00c89404d40c485000c0c05448041c29a02d039040a4000300d0596901425291503450035070b00d03072103074450041c003030810f002d030072000034101d0044050000703179100c00d076414a115440492440c1800300c4045a900e5800410230586a030016500c0b9009280340f400c20781014210380c2c40d47c5d0480c5015001030710480a0381c1c5950b011800c3c0501c1124500e4141c0b1002c09104441980207079aa0010f020440d0142d0803c500c100e1034a0380c61040040158008650700710356225000d03010000c0d40050000e541500074450351011a403200d0b0001d011403407003454010030300d24000409500f11100880a80210340040041c405050342c403800740a00360362400c0590010314004000079251000c0394038000c0d006400c06500e10f40c03036199030346114000c107080c441070f801541d506400c1201540c094414910900c105000c0307046030350250a441100030100c2800824290114010741e000c915408c404001038907180c540d034071307000c1241aa925401c06080d034010300c0701c101c004209034002c0000070105030000c881060031911 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 497435908 1250 497434658 497434667
    0x20906012106060c21020309100507060204180507021203190b28060315090b030120031603050f0103020f1c0302071505090d061a0307140102120325 65
    0x44042001e44200b2410340c1e502e10103464580052010ba9540350b560301c414051a55205040c0301c110041e074080d42c07502d0450400c0101e440e20501400003001414412040024146e20041000e000d09150a0952040c008911001e07610000d00341800c5402c00d00030303040d000d0404c406580d0081401c2000310446100c080f021343c024010100820f900004200400305c000c0e40802c0c0580102203d8165682d446d81ca64600754103840f0000c0340c5142025404908015030b2640d45c1c000d841d0100000c0000c205640e07144481984480c41300102c0c802070000009200d00c00c00c289031b04101130200303401c050001d860980c50401084405110203030040400c1e2101140c40e5444c4159941c51059a107040d41c03001c1a0341c10300035540e5450b401010441040c0b843c6840044d40117105592082c44010000f6070002c41543d1072401030a42c0043c0c42020000000ba2941546c0e0b050105030f003e00050982d4803120074130200020303c0c14030841000c250321181002884004103100b440c40001d81d400016200040703502c000c00b03c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 497437158 1250 497435908 497435957
    0x801090e100515010905030d0203030406020a210b0915090103060509190305030a1d100c020c10030209041406030a08030615041707091e090f0830010302090601 70
    0x10301c4070320701820460404226111058002401e0380d0f0341c00703484c0e150b030140340e51484e411100d00d0159100b8400207002882580050200085601d0503102030b12030440281602c20781c03107580e2499580c07a03070007002c803500b40021002d0b840350b0000c1038450a144010045000d8039410700025010039121303c0080c580c04402c1100b440200c040362504036006c013050900030100d41042c1d401c0c10b46142003401c05a448800b080441400300d084c8409080b01043d039540801c0289446000e0f1419400360001c181040d80d1141c00b4038514500c9614050380d54604981088110340400920b09010b0380244180325072614000384c505e901075480b210440da1380d1651000242200d00100080b4000301c0001408a0941c222000d0711030001d01d20811680b40c15112115a0141c8800255440600a11808401070b560607034122401542c0205503628a20013903889429056010307181090040b5040041400821000034444420000c904000f025a50456000424011001d090f00f410041009100900c07441454100c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 497438408 1250 497437158 497437183
    0xa060609060507060b090f1e0c0904020306010e1504080c0a0308120c13030609060c0f08070c02010c06020d02040509010f2702090a030b0108010c03051510180b0304210801090e 77
    0x904180c0703000700040e643e00900700c17083c00080640e125485075400000c200c80d805a21205270f21824a0152020302001350802801c0c24100801c4206104c6151503c6138241140d02000280c41d90740c3d81021400c074580308000441500507466400208007045610040c4c911100496490144c07507199400a14000c0c0215210000b21074450440003007003002d540c2c0102d42c85882044c052008070441c05041e42e03c2c03610f10309100d001c0b600440020700c2951180c0c030300c1a4180c3c0705040003c1580c4170342d01e5000403030704119481803000f5400901030005142c00010700d801400c03010420b414542c01c082c05038600e02d14000100b881c80c550300e0480309143c08150192814060060030b0184e145540c1d080100c10300000b8400c0c18540c0d403900340c400c10307030174400d004580c445d8406000084800784603a080c0302aa43c0030500c4030b81003100d405132085013103002c541a00000d1814110540d1241000e017045140d031007041d2113146800c0d1400c83d00000c1075400082e41411151501c800203510020501041e08004200205 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497439658 1250 497438408 497438419
    0x6010306051e0108010207061109090a020a0923150705030a03020d06051c03080c0f0306060c0109080406020115051e01030902061606020409060803030c2b1e050a060609060507060b 79
    0x12134032a005502130040303540904028018503003081c00782c1459101c0c801500c2c1d0000d980800042c03030230000c4d0f001460903203043d02c1c1c51486a9510420781e074903001611102072101000d1400300003a8580070080c00c1010f0200c6480c10310300911540e03216a0b070700c00c0403110001d040d008100c80703c54411981c058002003002070002502c100e00f0b00e401da140410038080803404a00c440001c00d0394003650b242540c80d4188801032442c503644502d400c201054208001220a542d02e410070300780091411009040140f590340c002103800c412030800368194201d1608814003400100c100d4000c420b010b41c1040320000030a0070000f41010b414000300b68a441403030901980400001207680401c801d0394014000c0300c494403810020f440c3c81e00082a16031006a8200c0080ca03400d005440d1009240c003c0700c40d5000d40e240400c05205071031038481c0191030040242da041c6003201080c1c01d100c000d20740201761340411a0f00007003191508004000d400c1e40e42501850080000c081071500402c192507105c8588040002e10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 497440908 1250 497439658 497439661
    0x2030903180d02180703050c0307050906030604020403140601030b0105040207020a26030a021e07030201090501180f0f03050d090806070c050709020316090b030609062b0605180a020306010306051e 86
    0x30304c5560800ba0317010000245020001000c20f404c0703000342d038001c9000d5079429140001020800146800291400f60f000354200400800101d5041c01c0b812044640c0000d000c0d650b245081c980002c00f8164400c031b00a60040140b140180c0d180e500ca50161101c007510300703285040c40c1c10160540c0c410300c001c4500500c0002201180f4030f03000690100002c58500c41d03002d44640b1190752a840d05414440280403400400007446190301407204052003c00000c820040d840da250302d20714a800301079014042c04d580703c000c1403050083c140f1450b00f600b8070f682480c9141c20700d055112035491000819280070049400184010000309001340b00040c10845804c7d901c07420300c0d00000c10002c0c5003003000b03c00b2421001c000140a0820f00c20b8a00c20000100960310540c0c4100c1442103844140420303410b400748101510b1101446840c151a0442c00b4a400050a240034030040f0101c1400d55500c4020f40c0c050468440181e5001651905480c3d00c8031003c1200c2d2600201c05c4100c20444c1b1440d06680c0300c140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 497442158 1250 497440908 497440939
    0x303040309150e06070b0711060709091a030634091503050f06010806180a0e0705031204060f110307050d1812020d0201050702090103050607140f160305090604240302030903180d02 79
    0x212050551b4280ccc54200000c40000701e54224030310104a00a0f01a080300c8000760800c103035580010303082c1f07500d01c0343c000f04c0400c1510700748200640070b10a14049200d00c6401e0010341184a0403403164452400c0402c010700b440e070111803010000808803410060004002815912194141a00754000070240c20041c10000c090300d01420300000300006c148200d010001703c40c60001440f04024102886041c5401c1c246002140c185100304503000030300980110f4400d0180b01000140559402640134141c0000d0055008007881c91700c40800c3c8244c022480240030b020100400240d0043d41107444441b0703d042840103941c0350296890196010123010300000c1804800300d0041c0c85141d440e910342c4050000200608000d000e00d2911401142040c02000648002c0541020402c0d0013070078070500382100c042c0096000d6100741c11041041c42c0d8003001c148081d01c804046081852171381030550071890182292580c0b80104010303400c80c1125050164a60703250300303ca00c404540c010f0800030049000e070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 497443408 1250 497442158 497442167
    0x4050a110420120a02211005130c020106090c0e0402160b07050316020105041e0203010e0609031e040602060712090c0603050415090206190207080303040309150e06070b07110607 78
    0x40e40c0200320342c0d034000e000a0b060b100d1807003115601c00b4006c3d020b41c03940c40100e0110321140c03c001e0840520f4807245030007203520b03610042450031040300350308007041100f552a002425070f01142d016149650802d45c0d0250100d070040c0700f40740c5402041d0b40c0141c560b1198100400021180d0a000d04014480340c240940c4075442030080d8442c28601c0b00742107040175110310481c200d400403240509202144403242800c486803949502c00340d80010300128108520006d8a41005c0c000d440240c071a0f4000945510a104061100319000c0c4411310b465041c10320f0400040c6d114076000300201d0802200d0603006022510070b9100401e170741d4010050704811b85c0c1390f000c040e0090405036410341c0c5040503400a4000300c0c0300c0b23010b221074aaa024083c50305220f0400203070300310550703c6203408040d4001c500010441c844100b0145100741d00035a11000b0040c6004600b00d0810a00c02d40390f020000034128510450301c803c81258a2158800764402c007a40d50f038070b4212602000221702d0002d5000f00004d010845600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 497444658 1250 497443408 497443417
    0x603020d06090615091a04090903120f062111060304020a1d060109050f0a0303050307110609072c1303030b130e0c1e04180f120201050a0504050a110420 67
    0x5440e0792000c00d4880706480f401b0240091264150302040000b841030343c803d600440586842402c0c100140700842035514240d440144904c0b44081d6145c1d030410000d50300004120080303007441344c4403090b0181601c421101089007090b00d80a41740c000041760454450741e0004000704190701641d5003401c000c440384e4851840035141a030001e2100c2501140b94680b0042c01a00c200d070081443c03868515595003074500e500020312840900020b00f0400203840418800d080c800c410300300280c9006400c00c002d440a003a0940840c1d105101c1040c009da60240c9403603030711034009142000c402c0000f50a03140403405400546030142e003003142110000e003480203c3e0451003a000d072034816a103401d045030301400703005001140c0a408104d9074401c400402c1c1015401032a16440003001c601101c0390369155444080e801356022540d401c170301c440f078601c42c90703084c030071035801140700c0030144130710305081c0c5070b8070307651801003101803d00c2501400012103540c45502c404c00901d03000454407041c41ca814101c0074503400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 497445908 1250 497444658 497444699
    0x40e0a0f0c0e01090e19020f030708070504152603040308040603051503061303051305100c05070f05061207210603020307080309011b060902040f0504020f090705040603020d060906 79
    0x480c2d03001250300b01d4640103041800303940e40024a010507920507210039582e1401e00c241e81113801c000109419032400e210080292201500500409151900748403c5403240b19030701412003080da41c01c1c80304e0745502c1950f02540b00e032442d82c1c0b00f207100340a404a0940c450350b4001003400e07800160019016405402c054803034102c40c21204540b030480c0040c1074507840119951a0380344052201100082e004d000504840301051400c003201d640c95002140b4011b05955151022a0340c441c103600401c1070070807018028101058102c050503180802043e002d01440801d039280d03070072401c001000c4500c2640e03900c112a1220b01a0f545202c2c0784418136005129602046c0d020b030051110104d184034000040b2880c44006955045000b804002c207141006828002155001d440d6144500507a0352405040140009801c000800c1e0030607204100881041c445581d00500c900c80401007696080819241151082d00b409a500c5507020b200800a01240e004504500c1c907145011404020b28000c6482c0d242 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 497447158 1250 497445908 497445929
    0x1e0e180604210f0806130905010203041a010801090f170c01060b0a03201b0f06040b01150f0e06130e0c070311030304050706050702063601030c0e040e0a0f0c 69
    0x300c080b4089520706081403210000c18004008070303440f0b052254000240c80c079415000a1203011664406003682d1040c2c80c10340c0c1c1c40c00c614400c80030040804400500409540c0004c0003202046d56803075400301380c03003031024000d0081c0b840d0812a4a135101c040b207098082d071200801c940d45d180d90603208184c001d1041a80040e00d02030035990500056a030034800080090f010382c2c101281c09400303414580300301490305044d0044041c40c2540c072008000c600d01071445044083c4a0f90b040c950076020485588012104110b01d540c80301b04000c0e007040c48032460721410380c0c030955280c81d10514144080c3c81e0782e1112800101e405d0030050a89108006090b43ca80320340d807564144036078040c6455580c04103860282850b0441503041001500a000034020544060215803d041144000221904008007101c4070315201100081d03d41c110320404031520003090808015150b400e00c2d004040210900480703004a40e541c0f019103034500c040207445940e40d48140481e11120b51490b004000d00903038807400380d628 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 497448408 1250 497447158 497447213
    0xa0914060a0e1b060901180605031b1207200a0b0405010b0a0308031f09020706020703080912040b09280807080a02010f080a150803070c1e0e180604 65
    0x82c01c01003620038904000c07091000c940310705441040300300d5215541460501c8040c050700440d41104c101d00c4e000a00302615942e44078a4802081d04281600c2514607080d090104003000c40038815000460308070500d842c0111a903514043c140e20340f2100082c0014042c412014070900704005020440d00ca24822703170007407051500d014140a00f017000350000804498040c000250070302400120003031402007041081c0741103a507a03606a0200c1e40050010b441050300018180c080c1500040d9203900401480000c15201160340d07124030860040d03020310385104d4400600d00c2615a00c0a45c0c0c00e44c41401001c042c00c61103030940100380ca21109100b8081c40340113600d00040c28107070206802102517010313140c100300640c41e540304681055008000d40030300c44d0740c0c20301000720301070000c1e020000d00002001540c0c1c903012400d1032002c030340b0140e1010f400001110124503d4182044501c0101c4400c2e8100b10050744a40317454449030740c42c00502e0040351180c00104418004c45060f0300c104600420f90030000e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 497449658 1250 497448408 497448431
    0x905012c0303070c021509100c0201020f1605060702010519110f2802030a12030c030b040203091903090308030c04030b0a0e1b0a17030c120a021002030a0914060a 71
    0x16800125400f4000c1000c0030410b5025052040c180140300003610485031a180001c1d0002d100c02000303428160004890651590840d40c040100040b260b411000400e07840707070041c4421001c0d504d00d0280c20301480c0c1c0440c00320110390040040d40c900182a070800826400d030584024000c5a1101a078012846a001072804400000c81d420012120400c0e0380c0e2410708a145c41c0c0203500e0203000049800d03108141d08030005c0b407403603d01d002d4114607070380d404a140c604034000142561f078000d03210b03881039204201740700302c452002a4000010361400c8000c100d40f149030400380d90b000d40580c40503282c2c134000005c000c05030020600900560307109641262243c0c6608401c04c044a503d000314200c164000c080d8185001400ca02c00019458000d0601035401d0b00d4100c181050350104444540680c804250307004664402e000501c454482261803e0038441604030095442d1151a110703142c0540c00030124440101c550001d41b10250030081420702e0311124031520350345900071203201c0c20031032400c000500d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 497450908 1250 497449658 497449663
    0x10204090e0c0f10050403020904140123010801230a150605130b0f070b0c04050d0c0512160e070306030210122702010806030321070e0307270905012c 66
    0x1d0030401d507161740c01c09095600340704036402c0182c801c0d41d02072003040002d0408402400340294031310b0f090304c50106566002e0540b140d03a81060b0000c8516074181100c0b81d03203080c0e46002c0030740380c1e440c07515040000e503c83c610780b20024003910740c50ba10040c415000105000740c01c48000e28121911009910466a40d03913405a0640101c0000181e08802000280b01284c1d0a8500c0d503041482d140e07009290582d02d1000450b212990042241c5950084e602081540351803010003010304c24420261800b42c40c05503070b0422507802802041801b0070901c0102c1d403414400d80c0200d01443c2d005e1302e82e021190b4111800352610304500a101c0c0341a060803054500101884c1401d071603014240d003d2610103005500540300c1e844c000304507030f400d40300070700c8120b02400304020b001d40344104200790080307503003040040204889508a0310500a030301c10350f4100854242d8aa440036a40040300c1c1500060103513141300d401030051100c0c06001982419040c48072074080c001400040034a0301c9200100a00980a494 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 497452158 1250 497450908 497450929
    0x80406021506091816090f0b090c07030f0e030d050403110d0302030a0c021c06090203060a0203100501030b0d14030a09080708030f0306130c02010207031d150903010204090e0c0f 78
    0x240c102d08041c0204061000c44d1281071440540c4034195000c001308a24415088446540100581a203c0c0032081c00c1a406200300703041c10109440c0d4847d07500d04001c0c2091503100700f0300000c040141094404003004d1007000000b000f803030010b09958000541003402000358000e8041944d010060301d01c607403503a00d0401d4100744d085505402a50400c5881d260030b4408280303180090381c01440a07100e14440404041291400d907104a100041c400e44a0060510f801c500616109000b441001800303003401702414100100c40f4240303000300d0703500030400c04201d00752846500200640c036092f00f180303081d02000c80030345a0111a5546c1e00d140ba541d0b91000d907920082407050402c1034000708400711182420b04000e5a00802c017411940000d681840b000702201c8840e68204010f0350f011561004142c0d100c83c101d0a040352410811003109043d40018464000085101d04400c100044410035501c01b901550000c1001c00c10030070800348c80b1140c094580d4075440b88680700b11601310841d013843c900405402c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 497453408 1250 497452158 497452171
    0x6050f04030f050f0c190b06010f0915050f0304060b0130151208090f0a05090a0b010311180a0b03071d06090d121101020405010e151201030804060215 66
    0x400e00b8480d080403da41952001c107964031002d03c03c001070501c400f004c0020301c03c1c1e00c0c600c050340c1c0307582d200904081407a4040a8001410003030681023000805030b00008800c141c910f09100c9044140c030441040d14184115100101c010310048104820f02506a1055560322000e807900004001d080750000d160000e6540f14900d40c07904c0804070312031020540d210440b420020150305072116100d07240e00d41c20045103442224040d0000a295815040019240310048400c0d13403801d02c02400d1100280c048000188104100c030764070030880700d2a80c403039044a04002810795085130780780818100c5c01000c0000001843c0540d1103590006044003052088a200c0c0b00c7c00e03035400c25522024007541007540c0039a99101d510060a0190070729a03580d08881c0b5400600c070340c4c0d00e000100810200984280d00c100d0fa1000240d10512080055903009003c150b0389543c121114060003401300054060b0f030081141d10144180302ca4004020450404020028cc80081e000c98035001100414403600380400c440b003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 497454658 1250 497453408 497453417
    0x11040b06070f140312011d07051204050c0a09020901140c0d0819290109050618060d050901020408120a1b06090b0f060f0402040515031b070b0406050f0403 68
    0x5540842c009125050149110b40300010200315aa0801461a0400a07032200201d10310701c010010502080307482501041c1c41c5520151030724040300c01401a00614600c4c0c14400c0c035020018081110600c00000c00ea08024010392003240c40390040300c025000510a0303408180402d035040f207200c00712070558a181c0c0d840c500038002100320300700c200d80c44100a05000460580c0100000c0021401e01450b50702c291080056a80c0030906092140358000c284425818442ca101c82400f55803148d0088400707100c503400f4100a000000c1d00811010720880039081c000c18504020b100580c04c0640003441141c080700100c0d02c009000000c103200d10f2282d00101300104103520b2030142c6a04130300e507260290a0040e10700141540842d103856122000c225443c0880c203584000304043c80ca0038541aa01403a400e03281181070508100108a48109020401e1000f000c04000500340c1d0300724402c241804800340481c0368544007189800100c000b010f94080f96294205000108009000343d1528801c41d0036545 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 497455908 1250 497454658 497454667
    0x6090209060904021308030304050c040c1b0305030615070b071832120607020601080106080c0d0c030203191106160b09190f020901080d02100e2811040b06 68
    0x402000798000721007112001c5c00c150000034004003c0c000f46103d14001c00142c05103c003207c042204490030340351081c003031100741051400d60803d2034503282d03100c90745030401c580d480d15103000140629010828840407464000303840403c0041a450b81400780455440c1c1200640350b910300900b640100d4050003151000d103171414040b03101080035100042600c216001c80d81040c200214110521007540000d995010805000324580d04000b101d00500c8000000c200c43c50400c104d498075a040728207644d1003030310100c03505814009200e01c000011a4024120ba500b03d55040044d20002b105610035034004804580e81d01803130401a08807600c000710b044118064422668500c5004000600b4a88141c407809540790203070010b080781071210034040c00c0540d42c08802441000a13000301600122440c0d00301e0350342040b00e99000102e500640c000d40f03501045500030511190301d030040c060140024040a101d040040304d00c001c0503588e0b05801031001d11010a020020f010540f510300d450280c0103c0c0820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 497457158 1250 497455908 497455927
    0x30c0e0a06020f1605011e120501080c130b030c1905180901110901050d180501020a090e0a1a090c0f191d100c1b170601060c0c0303050a0e1e040609020906 68
    0x200460805451408c01000e6090511000c0701120800d070005d98041e0300c6000c600301c0034548600c1004c004c000403881400040d00742c00129454541540c0c68901804d000106000700d001508080005410050b120f42c0341521142c126401d414020743d8081d000354070b049182c1301010b48020071594101c4068446a1500c00f84018050040c035641d05140359190380342e001000014003c0c00207000c001410f5a803a540d080c1800d000300c0c041d840240100082d90300d8002c511086000e84448065018170840d4402e08aa4800f40856072500c1682e015910700348001966011158001e600d000c44600740da0380e00304500711040c00c100d02160040b2100790b400f9031018005508144200d181d101401d100351040a001050441c008039004030a405c86e84500302c0e084100a10b00c041000740e1801042c4510300200c0c030240d10741321400104882e000260400000041a000250007512010307114500070301a401100c02c001e0580c071080c441134520b54410750a25000155005a038025100700d21b1009103010f19180c01d04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 497458408 1250 497457158 497457197
    0xc09140a15180603050105010f0813020907050d060906260c09091509060a0e030406050301050d020f09090f060912040b09010e130509010b01030912030c0e0a06020f160501 75
    0x184000030410801c1514248100c2d90507000c00628980e1404129941030400150503960300360801d81c2084116400c0014601010300c2e81e00070140c0680d086905a114118115020720070b44004a05480c100b060008591503164041c0702121800c100c140081c0c0e001401108141c41410381480140d07001c0c800003030503850088000c60f008413040c0101c400c0d40b50504075045090a044410840640100013000014209402401071a0194102442c549810030308040c00c00d00042c05020701400d681c4081004546910301044020f40c0010010142e5113401c8054540d01c60103016000c0740b9020700000304100e24000182d0440142d00c50009600301400c2c40701c0c03014103411900c80c040c1000038103501d4481588503080d00c1e012040f034128021031230b03142c200710880c2500c03003803842c0604040c0b40030340e2480400c5554041d01100603d505e404070b4000e080380c80484404429550705584030602c070380005455600082c0d03050b0140900001d440c0700e000d0810358255501900d120702030110303149586d0340d80c500004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 497459658 1250 497458408 497458439
    0x1140403020d0815190f120305040e070905213d150e0403021912050702030709060803090102060603070b0909041b090c020f0610050409050102090607060c09140a 71
    0x20020303c810700e10f40c8500002c045808061120f0207040009a0034040b86d1402814500074001c5200f04003e010501d0750300410501c268405c0480200010000ca0185481190010000e0000174203803004084240b203180d880101000d010100e038071602144010f40d581c110000400110241064440d04c03030504206603181512605c150340f0b080d07985100850300160045040c01400851a50f07590034686450041d02e040e01400d0300000280c682e43c0f003c0c000460091200b000415640b9000b51030b02154408a0724000c1141c00011282e41001e60204074024000042c00c80b0396000d03801c07500940c440c0c00500d9169406800361000f03c850400404025040c10030440740c102d072045200d00c940031010b42c0c000c0c180164540050394210f451f2030000c1d501e44c1c0e0401810b80d02d0756283c00541003904101e8030900c82c9096038400c1074001c98072191074406011080d4191240f201010701144e6403420203140143c0141940c40c081720200307540769000304000b8403001040340460400780084030305d54285140444240c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 497460908 1250 497459658 497459671
    0x1050a050d1103030307020a0201021006031707260d1a0303030402040b0303190f09150806040f061e15110d081302030a030903050c12031611060c0f01140403020d08 72
    0x141c2c0c000148280c4040000703602c9202183c0c0075000c410024130009040c5a400d801055000b404e041080c0301040d000603030402e40e04000e410490b500d0459240c007055420030903100c244000c1440a81380e28850140c0028001960241001c105488903800b0442d070017001110030640544c81400082d0040c2000d82c080c00903080c1c0101224100450000d009a0010100c415100015014441c005040c0d0f04290060041d11480790083c4200c200d4100040c103c14004202520954441001980c9500d81d540030170060004035803400c0044441c00404804007042c0c0c85020601c000c50310708a1205032250710b001034041c0c007201c040c0c4080c40361500b00301c07003103c8042d00403031080c0c00810304840140e5003081070b02c0071280300780c4854020500e9414103500340605815030034040d5050110102c4560030200c100c505600110f458401c0d04a12410400400224000207070341200c00004d6481c410200042d44035201032904009000349010490640d107420016100207000da030080b1102c90b4013074040c0205030b85c0100c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 497462158 1250 497460908 497460923
    0xb030c040f080102070b13053c011506020f1b04060b04030302010f0c0e03030a05030901020405030303091507020d0c0803091f14100f18020c3301050a050d 68
    0x19192408016104419400080c07075a40c0024038600300540046035660040030b4040c0420020000d441d2151110b440480c168408800c21452700640001182d44540c8001010015844003004100680c000d02d1f150001c1e0f1349203400c0010002e80248001140074103210b0303507405000c040039000441c416504c60506c0c1103500648800b0b0214800d082030002e40020344c044e900209e002ca844190207011100001d168200b00b102c0c0d0044000765031000000c0315080947c4d4034056551340d541a140c0781c02030103240c0105506000002c107108800c00006000d800340342081c491032100f52158ac0050b41e0383c02070030703016030040b50100b601c050104a480b0b01640d40020303401300392110340c0d54030511400d407581005100b0104a13030710160036410300d18904109600c5624650b001c00b0350b9090001c070b0102410240b1413101c841a85c0705c010105000c860b010780340303a21184001c5802c0d01743c0c1c0d4a901000c00d10481e4200b4a000090338a5612072201c13451031504840010b08030410b00390a24041c001800d86d4104292200c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 497463408 1250 497462158 497462167
    0x60f14160c0e06150412210509190f091a04150807270902031203011d0a02070f02040b0103020906070501020405041d06070804031106041214040f0b030c 67
    0x86151265014034248035200460240342402c0000c49007010140c00daa000d941d82d0001000c011a4a01c02c1341c055984003040c0044402040ca020801800b40307254200404801100c0217080c02d4106020b411101c04c11104d0703078469548400342c104001c08034880e80000c0c01215008000c1020207900061a940b04a95003c1400d000000800d09880502d2020395240e034035400b08020340034040c8141c101030500702e00094000d02e22901407014840f500c100b0a101642d490034650701b150f50400c685c12507481515907003034032583d40381c21082444412042e20396072455076100007a0700e8a024401c41d03000d951310040321844180a80c09001c0141043d01d0707018140359082288408580c1d4520103001c07450322820001d030391541094144415030b5480a040840101071910350322101402141c026885419460004141d5075241012101c0e0100c0c5010f43e103c03402024140014018005010000184152241c0000264410803000305125a11442c00007064294080c00314420260055070410004561103003403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 497464658 1250 497463408 497463427
    0x920100926060907090e0f060a151a0a0806010819090309050a0f1d060d0f0302070302040c05070605010b031006031d19062f070204091b1707060f14 65
    0x42003000d984550743c940c00b00808200d020b00e80d0207028400d45184028142110b10b0340405070340e0f2000541410341d0140c4404210701c201d941210050024600351660000381c0742e01e1844580c1da0b034040300702a40002c14010024400e0350250920b94080c400440321072480c1010044283d004203c80740c812070800005000c0002c00b503560346a24030281804402c01404c8910b44501e1400c00300d6a080b282c000748503080301f000107580c1c0d0850f18424840d04454541c1801d00980740803401d200d40d81d00002e40c040e00c0d1451114100b81c1c0f2078060298140304040404c03c60762035540403031590008440c101c5d101e112005040c8441407292304411103c00256081d1a02e140c44480c40c1030070010008009400d00110f44e038180f0502c161030050907075811204074403441c6e00c040c03c105d8610400d0b41842c504070780782000502a0864a480d40100300307a0750401a000c0c072680c10482c000041c2003a52190a41200b40c2c0141c0e4158960702003501c00455a85444103074410a0540d0305503403900703102085403171000702401031041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 497465908 1250 497464658 497464663
    0x150402071a09070501031b0c1e0803010b0306040f0605030c120a050304030b04030216030314090105070b1f06080f0a0b01050705010c032019120b040920100926 70
    0x21401e00020f00100c82c01d240004045850350040d02c0f1908010754011484a5000403083c420603030451901c2405004c0d10040c000d4078800320030000c10742d090000c0002403035040c0c03030301441c0910011030b028080c84005032009016100f081c041c16030725402c4886000b400d031800350381c444844900c110994000000c1c6490745401c64005a1055400c0030826040008240c1d051200034141d003841c56a060050742152001444c4030400245403880c06400078003821a6805141038071421756005444059078940320007a142c400f03131140c2d41d140c0304030419030780441c10303d004040d07552140c0b5140c160b99199954a1070035202810780428a1410700004002900c0450790078010128000c2c925200414940f8450b05c288146040444040401041c14842d0855047c130440100800382001e1a0601c02e625010350300500520070140e9180c3d02030310b40810b10741000340c02c10022450000340c40d41105c0c640400c9003402010030480b512000080c58001c02803045d4503000755085412404101c031003411003280f035621403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 497467158 1250 497465908 497465911
    0x15051e270a0e060319050a030e090708010e070905030d09030203060a0b0d0609020f03030f120f06130c050c0f01090b15130f0207020d110f0402180405150301060e0703060e150402071a 80
    0x203c6c3c60700040065800c7c5504403100d00e03030b1140143c0c3e104019242a4000819a403c18040d0311242040171003c1003013039204800750005070200406684d0050908600500913620510089000380200400900d5401d542c4c0b00d14206102d001d031034900281e6241d500c010003001e4205040383d00c03001c2e03006961000c0c1c508101030034040c1c0c2820070f502d03a1170005082da4031903c4401442062020055010850103484111820b211204580d1000c01c000550304070988180c0280c1144c801035100c0e0100016011f9815000344506030f0080c603a681c4141c540914078482e84200e0841580c004403007005401074418180d1101f10009440c403001030038040306a0000e103540480010580c0d000e907040e011444e4518000391000350f8440d08460851800824031510703042d081d1561411449140e5030740c00a10fa203500040700c4800040010000c111194a603034a810842e80113549507800649051000b00b200d2003500c0c11280550391403940b0710b080c01288400c0002a46c01004203ea109042c608480540d0550700c4945 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 497468408 1250 497467158 497467163
    0xc0e0a09020c070308070c030c031401060b03130f0c0506030a061a0c0d0f0c0605010f06110a0b16020f010609021306170103020d020d020405010b030a14010f15051e270a0e060319 78
    0x101942f031607840125080d11115008210180380c03c00c10f11990078440d03000340d0f100c1a07105035481980718990038810005945a481550000b0001041196442043d403100080d00c400380c599a1089600224400345030103003082d0405141d01c401c070301e80c9000b0300032520444e0203201485c01c60b4940e4640d43d1424207070340083e800012030340c40b01c0405005503a00000044030808000008044800d01c80e11080c5004a025142d00c02d07072511030800c0711310648280108011610284000e0041950354810704000b036001d41e0b40311580c11441c1c600461814230695440441f40000395400003140d095800300800790310000301c12640103222611101c01a16180181d60080c9100b1004a440340781403260482500d0503865088030440000b401802400200f51142007070320304215100032903180345d44094415105884000065800d040c0e000313072280e501100101565040b4030002480324038005240f03078541381d510034030941c0164100c0c02804105490345016602c51001401c5680080102d06400c0c071100701024103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 497469658 1250 497468408 497468423
    0x60f0608090f07091d1b0f011215060206070801030f030302090406150c050601120b04230f070602210307030c020106050402070c0905130506010909060f0c0e0a09020c070308070c030c03 81
    0xc105c0680303141224003680510040c00b40c44801400c2e00b101c07050703800c2c1d0b06006100d40d4586102081591182d81248020071203e0020001020f1030150340d242e41c003c030710520006101e84070000318010301c15490281200e5100b909842c04101c1d0b42e4050340070b50000e040b115046507803203034001510844018841d00610160719100c84000450421f1802c0100503008401040705010719000021401d800041d805500202d42e50714804105086848040074050444070034410000e1701180418003088107402c4410036000c4403d80c002c40728119040f110b2040494038490030078800510414002c0d004078190215600c0001440394070342c4000742c200d80242d142692102908001840060f00d50301c5980c0d006100c440e13031040c442c0d50710350305c0c9640c13801c0500542c1426501c0720104000c10445410580058a045009110000c41944000c094904440e6101c0c440c3c0d41040340043c42126502c00c03124807500749c1002d844000c0c00c1d03032540c03520780d0f201450440701d0a240031000070125445002e8500514841c180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 497470908 1250 497469658 497469671
    0x6090f151d011505060705010902120f1c17061504180609020909040f03110d0c0615050307060f170f04050d02060f0415090c0b030613060f0608090f0709 67
    0x210346011004280780c00125a1501400841405184160700308951040ba8110b9440410303103032460250840c40f400a400032a1004442544c6c0d01c08504a401d1200403012036180044500b151140941d03100703410400300b00b0407628560912010038a41e6801200030b42a02515004401014203d60103a440200038103c030300c503503503170030101801410004c3c244040d0035400c0000c0743c4000740f100702001c0c01c002c00c00c800700600c0204042c001d0728200c08080c2042c042d0350f591242001d000e0b00081041104031442490000b01070084e203039083e285025a072010f001802103a0501701c09544800c1c0c00e050410900c0001550303071410141118136140f06070702c940c9001d91203081c14600649440020f80000d400d40d0403640030420100d50000b00d0560003a0031240c5601c8a1407a071100500510388508052b00e40304a0800209102c15245c0c011402a081079500e5481c1c1c202380d00d2081c0c101d502c0d6000e10410b410410760100051841101e2181e005030080f029100031007000ca26240c6400e845510001603a0780f2500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 497472158 1250 497470908 497470931
    0x60d17090a060c02030d0e0a030503040e1b070b06040b040f061502070e091009080705011b09080102040506030c0a0504080a0b041b05030d180807261906090f15 70
    0x1c203a070014009030420116850095002a858040d8454035108105100340f44500320b6a503015184000e5801901740c9580b2519010140d0b80306104844101d603100700107401d1018194148c0441e00c8054211900d07210035104c4104100107414500541c0d9072040d02c840c2e424203e22240d00c620350081c07508030051404082c85c0000070b41400c007a64484c010b00d400380300411402c8507010550b49188400200e002901401c1c81c03400c000c00f4091000d000c1c0140d0310303004031025100d1030b8415811075a115510f0f1000340e290340b201c196090784550302800740c0282c000d1010400002d040c10180041c09400d040090400742c0300c00c0b2042c50031b82201c0e2f0581d1580c03011001d01c8244240340c05000e03408601e03440d92101c00b034142004240d903945171264080030803403130030320703088a50300038031074520181c001c00f82607550040d9511030059500c0c80780303825161482c02c03101c1c3c41074800c3c40014120190803103504014600c0c5440c0d031120401411401c8094a800b00e1007a00c41000881d40141e142c0c1c0781c68581303c00148502ea04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 497473408 1250 497472158 497472169
    0x606093c30030c1205070c0905070e1e09060604120c030312050601090501050c120c01020a030f061d0919081b06010503030d150b040308210105130203060d1709 70
    0x102a0703910070000d40000380d0100b03501500404a030380d0084401210b02042d2181195144a210390151044107005804101c040d1313281c025038000c0c00e1569508800c02880000c00051090710403031082c2c500f1301a001140e840c1070079a201613208a005210710700f06581c5c1d1900026010761010b080b00c1004019005004140d00400c5144031b49201000410461401d2000a080000e450040c20306000000c1020800004c1c1007003ea2841d5440840480d210207601c015107010350000725824011905110701d5001403030441c03141c9401c6403520100d4850242c024828031000e148040c00c962111300402d100001e4148c0c00e0b65484001611034241c055852407010140507000e075141c0c03640d03207090b005000108055076002007600c0c040c00d000007001034090245401c0d03660340d07203886e0f01081900001060000070b00031007401611258506815088104130002189a2112030902400750310000344112522140c1043c0c2c051981b0650180000d80d441642c1e44550680104041d8410340301c4100198504050401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 497474658 1250 497473408 497473469
    0xa0f02070b03090a020d020409120e28060f140705160b190302030a1d0a06061502030d0c1724030307110607050c060307030603060606093c 61
    0x1038101c1030440c1043c40c001030b120070030b00d0b101900c5500745134042410755440340e202c00c007078541c031141002803482500009011030042c2138400307202e036126000040b410076140030311001408860403d0114903041c01c13010343c0d000740300c814800c0c02c20603007100340c11809011000030110326010314010000700072040540d0640081c181c0064149010502155403000e17450b0b0900320248065003009a180c0c0d4804a403c40101312280c14482580703161002c400e155500440e2000300540955824080d07681c071a51130711000488010f05d4001607004000701030342c00758140c0c0700351100c0342c85241c030a08100f140c01c6841c2405000b582c840032072400b071800b541101100c003803030200244410f070302650602c55152580640480c0c03c0c0300550007000002441d804220b818800034001c504020320036500ca0506000082c01410a030000b12901458031740003203141d50058035450112000b019494030300c0e60b07120a91000e11900e1002c040340c41c043d582c0940b40d214290f4012a4003070304580a030000e40707080400000044540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 497475908 1250 497474658 497474669
    0x10f030302100b01110111030613020a08040f15020c0c120f102319150e0a1a040606020a02011803080f0c030702040f061e0503030a1d060a0f0207 64
    0x45010100002500424103000b040005180040c014040f1801030300e0540260111200a5182c84041d0002c03040040c003940c0141c009540602900c924450410f00700c1c0b14424031500410f0050300003a0000c3d2480d4044d1081c40d204d51180b00d81e6111900e2404203070380009441c03803c2c0340c1010500c0b8100e4107202180f40840764242004049410808212a8031034540c1040300070540e40301e17030400c2805d90b40c04881e00180c0c52180d405a66070701d0108035010300002151405884079082c85a01700c0301241080d418070036118000810481c0e9200c400e640c2c0c004010040d68100c03070160380550068903070f80e0b911a90700200200e8000d0310343c00e101c40c400104104541c20502c10f0090b1045801e0020a154005896803240148119662181c0550b40c0d41d01d58010414001d40c0b140c00c0451030650038010b0341140b0121a00014201e502251140f492207400e02c2a010351a019403007400551030051107400c3c2005003905400c80030ba04000b422011030503950241703400d41c02203540a505248003d030b0400c000030080c003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 497477158 1250 497475908 497475929
    0x1403010609141008071b050f0607141c05090f01110a0207091b0c15061202040c020f120d0b1827100f2307232508030702011401 56
    0x80140e0401340074000050502400c00810035500c104894000c800045400d070414212103c2103032020015540788021103007240041c0090804001d0324842c482945c0c418145016490072420050006000030840100901c80510403c0c1c0d1070090242d0a01c215075001002904c41642c07042040b9001c1d1800d049680003d0034207140000310041208040040302c4560000d192000d54298581000000000000c0011480c10701d084400514003050b0f03402411010304c00c1c7e9041c0f01c2d801c40c06030144e85501030201c04c00900e03000751703003040d41550421004044094a180d400107215030101d010492aa90142e00008071803100400d05c000006a04c2a01c0c2070900c4210a00c0102061000c1160303e507030403010a400c011b07480e004460b1500445400014141c21640440f01c40901c00343c51030894003500303952000116440841004281c044021000c400d03e00f01c2c10366a18201d03c03200c44250300070058102d0b000c0b003c500108640080c103490300550007421550700104102002e900d4a01c0d0b4464103a01c8001e504 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 497478408 1250 497477158 497477179
    0xf060c01090b09071a07030203070b0f0103051b060307230a17060a120b0c0405041b090b210603010e0610170303070909020d06080106170111180907140301060914 71
    0x4030050b91003242c03201248217464884c02c8900d0260728500840314010a03518280040100d514000540c0c0c0381203a01030021a04515184501e256890079035000d1650810410000514801d00640b903196245100000da00080d8010060300c405581106e9806000a00d2400f00350304155844400303150840c00844802c5611403404200103402844841e000308180e40d942c2c005021440600c094800401c4050002e01c4074040b80c41c205500304001600c488040b904c2e00da808260802400306407180100440d03039445604440280704080c03454014130a0354159250841140001d07405c4c881240520701018806140382c1c01d00d040d900604403145112105a441032040041031540309042d0b81c01c44640d1440182c0c0e50b250324840c00060441900101155800c0203030004031403911040d80d9103920100c2e0000c0100300240e10b505d40302c51040d280b071a0806101d9161041491410022207508413405090028803100402521803598109034003c8010070348405080110254002004000c0780007100d44034200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 497479658 1250 497478408 497478419
    0xf060e0105030f032a070e06090a0c081302060f07061407030b010e0603090a05060f150406180c090906140a051f180f03080409060503070806040201030b0f060c01090b0907 75
    0x8a00501d4171a5030440410b9101c4101e030885400b0348100400075000f40c1d8613003034881c00e03c4a010179054070018010204000041c070500710500c03e001d005440c5a44800094607522682d5075059009141680c1c400c00c02c110b003c442c541d80354001e155080c071030780e004a0003200c042c20820100a00030618401d15040501c2c5414603030303000300500840300c1c00701c5034280c40b9160561198031701100000c0013401e034410101070190849844070064820f0350f5041c035118041c0c590f18240b02c03c4d211240300b103c03142d9601800310030850407140c1010f0101a0b003480c01e03031040303076880c044442070b00e181d680b1000d415036608020f1a600c1c1000e10414020302415507070281c3e608c090038000d40c00418181400e000f0040030000c95198944070100e0140100f504507c12a0703040d0716418001010b1303210b072241d040d8451500d42d001840c1c7c203000c1004422545268042c2c14650341320380041d006404101107455000740b50841c00d01c0266251006000700e0909036000003814061031801852412002c0d004c00805c0e80700c06001c025 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 497480908 1250 497479658 497479663
    0x2010c080907030224070b04110a03050a080703051312030206060904020d020904170d0204050906190303050a020a0c0b03060906060408031b0a0803010e09060c0f030a0e100f060e0105030f 82
    0x1200d90540d03040c21030a061405d02e81840100d080c11045076040054003c051003d1040340724012401903017240f09000c0d2910030003040d04014440144540c2002d002c0001061200c40600311080c00790400c503107022001c2c1041550100b40342c100d9801120030b400004240b40e4108046540601c05031540c030030718141030300001d2208280010091046101c0000181000301c2194160103440d6005031441d11220300760140c4002c1c1d04280101801003050f1800682c0390303c3e000004039400d0002000c2900743d5419500c044a00768002101d40d0300790b124940100000030030704a82e00c0300410100700e6481d280d040070000c01c410510044d0681d84541c60a12041c407104601004403a04a60034904c0900003040d101c0101e0308295100b80c01070143c0c80040000510300c10f213000040d01c00c2800b0004d0303a0055640e40c0c10642d1f28003030250f41008554081c00082c2142c10b440d0700190a0302480f00880708004003409450003600c0350410301d040308940b00e0b0020499400601c1e4680d0151204401a00b0039441c104401503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 497482014 1106 497480908 497480923
    0x30e0418210e01050a0e0907030c0e04050c09120a020402181305040f1218080c03010c030204081002090109031202010617060708070e03030c1b0102010c0809 69
    0x1401d500001c403082005841c0c40e21645162140380300111400c1d04001c8285003805040100c4600b10303603551440500c500401d540100d0680002c4034010103140714040b14500650602061100c007072000e40c15111440c1085e55007002c45020b0721211460044002c4019400520005800c80104110300b030780c003495030003910941d985d60b0071a48400708a820441c0c2c0901100c41c004907440005901a0204800c04114a05440ca40394101001003003400550300900076507008500f65440340c2000c0c000c0e808503420340e00b0118189480c100d0802c1c2ca4154446007028056400500300c1d40701d0b03006030350304405190401c0d030003c118400a03902900803d110300404c0c0160001144102030014000b079110710440d201e5440c04160703211500182c45070303064120710b290302d030100b807010b0350304950200020003040324800740c6a41080880000682103603440340040c800c000c0306404010120500090701e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 497302158 497482014 := by
  have h0 := BRFrame.cov_init 497302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 497302158 ≤ n) (h2 : n < 497482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
