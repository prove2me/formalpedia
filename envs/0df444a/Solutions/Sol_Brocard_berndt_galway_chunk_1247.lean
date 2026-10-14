-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1247
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:58:10.535483+00:00
-- url     : https://prove2.me/submissions/7b67ec56-999a-4693-a2b3-712be0e221bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 224100719 ≤ n < 224280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 224101969 1250 224100719 224100769
    0x10903050102030a2c0c010f050c0609030a1107140f130c030b12030408071205070521010c3204090207030903061407050d0e030921010c0f0c0b06 64
    0x104c50b482e0082d0f540481e900c9035000c0f0300314603488907800c1c144070b4259481040d84150f550700e8183d400760b1400403401c00d02d0f00300682082c4403000a2843c05c04121500c149942021503080e40a1790018940e206140200010b4a030550a207100c180008040300500c920031400c2c48042c20b41d6440350f034810803a00c42e0490080c01120130b4810003a0144c141101e080d401100c010b20a41c180f10004000d48095858120141c50784500d00182890381e40f016000940f070381c1c090240c0005450703560345c2c180301801480100d1030881e050850315040c212240480313003400f4001c2c590102c1c1c000c40c00060300807240030040107a90b6100a103c1602c0c202c0f43c0078a8101320051440040e1060a240c0c201110a080f240309080500104411255250340d0030015074402020a4090141c064101041e8000c00708a421220440382011f00c079138002544075142c0c9100164419148030980e0584100707006403040c455250404c60070604003000002c1c040648104007a03c08014000420700c1030ba01e20042942c2c10075130031440008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 224103219 1250 224101969 224101981
    0xa030f05091f0c050a0c0503090405040b071407120503070207091e06080706140a030b04062c040209060d03021606020610060e1302070f0215030612280201090305010203 74
    0x1079000c1d0307403400c2c0e01c50400d100c0b0242844036060103924031907481d903035520342031805044064a07030030f00c1d0305002c036400d000500201c0201d840c1e51080c00d10660241c2445040b07410b00c03000241907042050804d95640000700119004a2010050903800038058589607550741d868940c120300b008100d070000f100c05814240d01c0c02d030801c11500180c010b001680d40402c0901d80d00c00001c4d030707200124812400442c01e0010f03004032010626011b041161240d05022442201d400c000404031020380e04030120005101d1814900341d0030342c0707142c0d244000006055004d60f0409400017445810020401c500c1500640c01a00c100b6109201c200700d0302280c041d80981e0742d601d5031406520341004031010141c40301c44501c0014003034440c0d2905602190040c090701501c0f6101403003003000c0c1d407200d402941c0b01d0844400480060305c40e000c0e40082200c00081d00d985a003402d03002c112002d43c0c06400a015984110703c00b002201c3e02c10305045c01034804030058a0090035910043c1d5595943d0b40c0041c7c86940302208001d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 224104469 1250 224103219 224103223
    0xa05060706150b0c330403020f060c0703090e0f0402130b031009020319030c030c08041214010b0103020a0516050109080c03040911070b16110703030306210203030703050a030f0509 79
    0x10070100020740300b9a006101c03240b054110309800c00040701722103000d01580d0510800e91142c2003402441541c1200421158180c94600c0940e203118020034001419014168001104000341220182c0d4100a0a0074040368921a10182005c2c2c46100042140e2800700f0543d4003118441001800795a030750008040614001d01882074180d0082c0101d40b9503000b80d82c0e40c50141420681d00d41c8540d28190b00030744003201e403030316816002c8030110810003010440300c044528440340d080c80345466071610000100640d0039504c1c8400c0e0326041c10700500002e9000e64009081c0e840040c071346401080900814103006003d805c09460241140300001441040b6403004001401581c03400c0400344085001032103c070101e8400d0860241c84608500046240041500f0054101555529040b01111416400306080041c558070450109039500e60401c40c4040240003291101040404602c0301240c0d500420340741d01c25140000d0401070009845080d05000c0c0e0b012819501011604004501d458058a9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 224105719 1250 224104469 224104477
    0x110f0f100506040509071a04051f020706020c0a120f12051905030118051803030106120b060c0703082b0509100e0304210803070801050a140a05060706150b 68
    0x1141007800c1c500000c0150406009240c001d06000c002000d03501d14040450340f03000d10001c40a0081c0c417080100103059078454203103070998009101d08941c1985c1c2d04401a01d0403002d54480d4040d500402205481c1e9650b40c01140100c030200302517070000f40214500400d1122a01c1030050120428030030312100e003a4424080d01481c604e48401c0c80040003d07400c2030319140001d00c2200122070500c1d001c06a248490342002c1c1d00040700c43c9542c0e00c1c0004900c6900d007160001d03000280021202520b00030160098020300c07070142010b4401c0c03480c0401c4858050307200c10301804042c110003400174142240e00d100405140c1c002d8408405241d1b030460f40c40c4008040c003000d031080c1c0d203507100740324a1121040c41840349100c000e030000001c40c5800d00e071211b400380d100c1e1049100e0380701200c20300c2d0034404a03140400451050109a0703031040c5030760416040001031203058000e9006a22990600c5070b040e1101060310b400d03102c00700d8070262105950324040340684441c1c1000600d105104200041c00c03d4440702034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 224106969 1250 224105719 224105743
    0xa050709060831050604060b0f040b03072d03110405092a030a080d0f1113031b03050d0c020a0b092b02100807020606010c050d110f0f 59
    0x20800a50710102100e0200c02541d500358100e820040750342d8004210596000c4a405204207410b0f08105030b1941820030f4003c0f00c1c2510016100d20080d17041d0728040034800400d030801c0310100031494000000c00e903602981d0040506040c481d01080c00d42c0d800003d805860320745c0d060407407110207440c1c2c9000080c8d10701184c1e0641c065807c1038003044c07020300e020480702806245440c408040103c8001c20f01829001c04228a805009864080380440c1c200401130804035002e40e000710342004040c407480b00f107401000340000d040b80180925041801c40c1d07940541202c3d0400c101c0e034039054089003201011300309940002c0c41481544550844140c111616a5000e8005c440410201d9501c2c2c1c001007803032140c00c03849607010343c4001c0c0c20b000710141ca24607801c084680051981442c4c0d400c4e401700c0c1d6510754a006c1c640c0070805000810664031307030401040d40e21000070b1030f003071a58040c15940c20b691090b015411000f0302251858030340030031004020b149500303200c90003154000480c402e1042e4640401500e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 224108219 1250 224106969 224106977
    0x3080904060b04060516030e04022106030a030804030305041b0602010c02010f0209060405011b0602070f060c0219020d211101050a06030b01060810030204050a060905060d02100f020a06050a0507 85
    0x30000e202c0e90304109840441e801c50301c0396803130b181d1208030a400700b9801010450900c10f81a58503492521b4500c080c14003100f032521040c0c0d08528603650100c800c03000070141c510981c003801c172650001e0ba00c541c0c03140d04982d150502040d113071203914000c81c46190072010314000940010303000410310741c1500282c54220141e0000c00c9400c059140c0d5505078407495020701d801c13440802c0b040106510880d40024480072080c07d42103072a8203070b910001641d00500d402d46400d480004103001344410740c440d60300d24008900060080203441d4081c003410000c5000007a2040b100a4411403d0249a030b801d0412a40301141d00c0c444c1400400c80980080c0d00c00054540d650310304800158030304014030403441500d401000c0040141c3c078221b81160b580d04020603842c02c03020030090006c0181c07180d0050701c1c05103088400210344035003086004411641c1c0103141768454120078500e800542ca41058585007400c0520304503040407100034040c6d03e4055244001040c1d14988000c1041d02c0403940d21044c018181695 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 224109469 1250 224108219 224108231
    0x1e1603050306011205010303021c0921020108010608040209150f120f0f123901060501080f040b040b061207090903020f030f0a20190605010801020a05090d05070e0103080904 76
    0x4071310011a0824040100960f000000141170f1454510520400b02440e14240244c0354a070300c3c007498041c0205400790f90003074048001c0021581c00134290b501400300751500c12250300d01350f000105921009050b00c100c1848080c8000da940e00e44100e038018251000d0240c0400c0d540c0401c0e519905c400c0b82d01100c500f030140302440c102d60714011440c00394490440c1c40560505012903000c1410700303042907403001d40c0f140710a0340290303032030713644840d040404500c1000094036490003001609400005041812032450711041000060700281000d42090308415240440d40e40d500200321403c103c0320008007140b090682c0054400f020750002103038288298260707041c02e010700310171641d82c1c02010341c0c4500702d4109022010100748503640f10116060840c0c40d001c0c00c0004200c0301802d02d40c004032801c8250352405000302c01e10009025081c01407000c0707c000c40c601000140014a50300514541e03d20840141e407059041c80800c0060901501241e668059a941e40b46030100784d580c8007411450085003082 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 224110719 1250 224109469 224109497
    0x1f150801180903120b120a0501050106020c120d0c032007030507050d05071e05090934121403030f041b050d020607020a030c060504291e160305030601 66
    0x3018010465900d52101070802d08001e04c40030250a00300d80c1d00c2d40010344c041c1c0260b001300c2e0800440c90703a540204000117903541040c40007401c0c009140d58103400b84040c10040d00300c5110005044141003003900c0d100080a80520702221980585100311800d080104020b002001c0041040811a0f100c0c03000c9481c842d83d6a001e00c4402e8800c0ca0015015402540c0100070500401c450b2881c104010303880c0d01d070b80680f15000244130300b905444445042d4007000701d008240300c500711503100040026003900e00340c1800c80041000e1100310701601c550304240c88840340030804050300b664855050305017038070389a01e089408000c0840c0304403425a014904090102e100311044501071048c0c0f0300c09010f2010b108419024440d15034800801281c000d010f003600040440c0c2010b02d04009032400350383e030300d94070f91810b42040c40b01108109686031160100c0d5009645202ca4021070355020b0000c40040e0070030b1143d003403a198070301503402009641d010b0a86100c00b0507510800441c81200300342c13541e0382c5442003a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 224111969 1250 224110719 224110721
    0x3100e0f0a0b010509040512070804030209060904080d0b01020c1c02010f0c020f04090302031b011a03060f0a0c0c05010e030a030e0607020a02120a170c0d020f03031f15080118 77
    0x829805400200342c0300061046060509a280d4803031b0003141200c003168161142806260b204642c1510184000306081c4114034240040540280080781c203d1002d041c29281c0407134610070740c04480e205541e1200450085d900034007002400a030010a24480009a801401c54506a900040740000c00703a00c0d00760301c83c1e4002c02683c1c400c243c010703100c1010180000305001c001c0400e1070741501988820301c0040304a440b2903d00f40540d040743d1002041128250082105010b00440c00d01d00c6500103204005400c02e1140030568452500d45000c03406000b5003070295004420041c010b0565402e0107001c0f15035580000061400406541e0100440b801200006490301020340c1c0890040e0414440c020141c603050682c40541c91290058031003102140e036560141d801c3d480c0403041074001c007151402c1565005d02a407120319840d0700241c01004121210281c80748001006403080f5084d94802c04d042e115043d03040b40251a41071118260404a020f020305000c0c0248244000d00d00001c2c84801e0404407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 224113219 1250 224111969 224111983
    0xb0d020a090b070c0b0304110405040c050906100c0f170705060115030209100c080c03120109181a07022a030709021305010c0503190f081506030a150503100e0f 70
    0xd02c02600f001e0170030b110a1615403002e40306650348542d1400f8081075545034410103016911429809d036a4038a0401032050205004104a1060f00b0100a04c1c00003a0040101c0054603800382812844020078a01014000e0040070729003111040403d0542c01c04c00005445410f8881c18402c07500d5901c2428801c070180c1c0304052150340c00060045c0341008160082d82c00d108110312801881d1b06104d0780b1013041c5d1030742c0c011100d03862030011518010441c1e54068400d20303840c4070b410b00e1440c024007203503100c020307007441c2c070200401040305640b0014100a20a009010489401a1012021f6961138107004030704e0031854159072180c040c0c100300240e07030f1205100302d6500d0b40c0690454162540b41600644a518400c1070a0314140010428401e0448060800340030106c0179440b006034001030800024907052b40100713822070740341900d11b500c20030f44d0755001501c0d0302c10640140483c00880481e80c00310003400580c085601440781d000045400d21a540002e440441c48604031200100154280b0ba51481c0e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 224114469 1250 224113219 224113223
    0x40512030705040b03060d2f0a0b03010510051c09050d02010507091203140a020102120a020412020d060f15061205061e120a060b0a14030c06030703060b0d020a090b07 73
    0x1400c00c81000413401d400099035100b40010961452115192910b20070344c1c9607448000200020719030308110040c220140c1d19800001174482c49440741c101107000c411844107000340e0b8800c0c0300710781250002034404e200f141c090031452640e1050180136200e5110140c0701a0904481c640100035400410600c1446401d00c1040340d030359000c8210740f43c0141c00c0c0801d14440320503010000710310000c0311089814030040c1fa03ea0703500d030300043e40d40d54060040c02100d0b0b0054070100191340100000c01401341a0180c0d05050358040b140b042e40d1002600d4103600408000b21160095420105103207401207503841c0e0300302120031a81b10039240c40e5003a040b5804540080f5181c039401600e0055000b0003881c5052010b00711403000c1c02c211103503800303e20940c2c900003015000701da4483e2642c0040c0894204148104020700d550609110948840030000f9210500290381c10b01034003000c00090076451107034014000400c000caa80c0350f03032641405e180e174019503c5140150045075038a0400200242440120781c9090303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 224115719 1250 224114469 224114477
    0x30706151805090d0e0f0303180406061e03020f040e040b06030c01020f15100f090504030f0905090a0b0f0d0f0501151203080910020d020913060b1e19080405120307 72
    0x107021144140d8217049024081500301d0035404204525442c10001000c441c1403100c0e0502605080741c0811040d40c00d150081010498082e00503202c0004a00090700c05400b00d040150301e030303840340080020320f0060f5032148010781e80036400e00c024802c03d0310038540075203403d4080d40d40042c4400c4c0166680c2c002d542c0e03000b18070784c0241c1c49144d00b05030582c012034101502200c0c0503401c036a1003448076402c503129000340030144e5403a000c1c4402c250b002902d504290b8054241658001d01d090000303644104000c10080c001510f0382070140d040e6075002c4002080031401000070030400b42d103040c4001d0414502c5411a5207610b404800d80c2c1305103800d0b189404940d0903502c8010400441d81d01114401006400310784144600c60410481c44110300192015003a8404010b80780d204c4c02c1d0400018124403d50220a54940750b41400001170f004116001d090142d000c00c03147c0010100718111074030600381d15000c5002c403032054801003603001001d6401b40d4018422942460002d200d6544584015990302000c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 224116969 1250 224115719 224115733
    0x4020102010f0b030a020f0402160b01061e050406050d0902031c080903041412070e0112020103051b0405010f02031905070b09010b011b031130130e040503070615180509 74
    0x47c500300942c8003c1c0000500094100174a0110301c040c490420391084410088102c01405847d078000d10707160100078007100c410004001c040300900984280d000e048204040000c0c11200c000e0240c206a5070154058200e851103481e295886104440d0200d1402c005502c0d80c0100d280341c0000420346040c1c030310101c2000030880741d120400072022402144095240200080010b00a0b04c0d8498940200b042c02e91144c42c00b00b40384001012950018003081d60b082031050220b40101c003440035a01690b00a00f4003080880c0310010580c5180a54a820702c00500c03006254074215600901078944c1307601c1415041d22544604000b035080c2c84000c095140083c4d04018242401b10030300c034405c04114082c0c282100030340110408142070101518850541d14a0510f40440140c4480c0c41e8030030440c021500c060a0517034580c00005555001d106180003101040007103010300c41c082c0101e51040358006c0040020411056141e140617821b48500c9802741c0418030a5958081a0f0103114465410b0034054108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 224118219 1250 224116969 224116973
    0x18050703151805032b0e0a060c050a08010501050903010f020c0d02120a0e090613051503060112020603010b0a02030f0d060905070503190e0c1005250201021e0a0f030804020102010f0b030a 82
    0x1a504c103821010341480d40d191104010070705da4420071281c1107064000d00380d5030049082a105a405034049901005820880303a00200c0d40002c0107819602c091a0591b5100411320000740981000e40b060440d66100003480d20440100148203d03020741940c00b40c414092062525140d00d015601c011808181c0c101e01c1c1c481d00780341241d405648014000e14092045030401c070f01c0b034100c403000c80d03500c00d600312103080503006032404101c00c2d030051000400114420042e940891000c0c0418801c03121100008103201240303500078010344034120403040c00c02c2c0c3c86001c007004040180c0458450301101e18581004982503a104004492041d85240004909000701100000052008001030180d030b0040a1800f841a51400c2036021411580c1d40d625031036484030b00501c0000f030f11001005c40030850001c01040180d03004180f005182c00603190302c2c03403200b1840400e103050103031412000301255604140c250400d40c1142045004a0007a0700030082112605000e070708031000021b6841d0301d54001040c00b40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 224119469 1250 224118219 224118247
    0x17010b0f0f07081201031506080115030b0406091b06080a0b0916030b04150812070f2603040c030506090606150a03090204050103050703031b0f061805070315180503 72
    0x110340c0300743c1509142c034108402155454200f17030002c44520101d650650010010303805600e0250580c1d0000f0041e0540411810001c05018440140003800305000502800344503800038107181e800c042620f060030194101d01030b14404234014070002c50081130218440350071b60300c6010000d1a000d84030200940341c1b1444603810941c00403410003007503110345c240e003030f281c48038001c05048102e402840319040327082c0380000342041d02000c0650300c0c00c2030502510010885521540d91203980103c41c1e4800301d1010090302c0c44080074080591500200082444200400ca01b039050031070b0300402c103071400c0ea01c40b040016180e080a42d011365001d010001000030f280c209400400041e4890b080000d5402c1e1580c0c0410242c1d00c09a02c02d44054002640c100705040d0052804c002110720500c1c00c5182e42200c2d0381c0c082c424844518040c1c4016900c0020f22001c800741c107140d4903901d400c5401c89204076a0381c5801d1401178009180e940d542c60803c3e0b50729003841240880c610a05070310601a50070b142c1102c0120b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 224120719 1250 224119469 224119477
    0x30614070f08040f140f0d090603150302040b0a0b0304050c011b030215100806130507061b1214030a051006020309210102070219081207020612090c030d17010b0f0f 72
    0x59032a0300f40c42412032501600300401c0c07444406c070002426903010721440c0507008105e00d911072010f2500f040011209650640f4030700098a83c1140c00141951101c000300c0c0c51001e441d040842d5403070000061200b4040300154400c0f400c00300340d1300c01d48150146581400920000c00b0f0080150b03002410444100200c4455103030312000c136480700c80c040c3e079454400f9494904245c0300c1082c0c01c07404031620070900030103000400140042d41407000b131400216103403402c0f41d200c6080190408141c9116080c0b010320511241440c09501900c1c0c50b124200007809400a210039107042d6004281800001480c80c004800c0c1d4441502c014205071040c102e810a90b01d2001c81503c0d00300e25558204071303440050b40c071800940e020030204103108074040e08000110b40303032060544000c100e41005116080c0141e441c00100c4035036618042a6980d42d032600c040340ca241424a07410b1a0303043c0079490078240390039031002207150700030300c0c00184000c2a40d035204842d4061141520200d141704040040200c03508981d4014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 224121969 1250 224120719 224120723
    0x1106090607023a06050a05090303070e060d050c0d0b0301051e09010b060423030106050a050111070f0b07030e040c0906080910060e01051f080112020a0b04030614070f08040f 76
    0x9040c1142d40e072218040038401c3e08920000c01e141d020540c01440928490a54020b4100404104508100c259203507203010051559007001508020000d094a407042603410b11028981c00780070b203040ca0001c5242c00c0d004204240b01c01841c01c00340c812140f905004050207240324007000b00c540c104000158841c1400109035a06a6407030703010012254807850300900c0241904880b00140706031185400700da030841c0c815042e21aa06048050015656108109045800909001d80d0080c29020340302d0510400380e03c0060403d01406001031840250390040c10950300c203940d41c03500342054400f00800c90707148079a2140056028503043c0302c034600a02c500c0c0d0304080c00f04d003141c011400070044071042d1011600401e46880001004100d076003072180c000781c02c50209616101ca605280940240407050520803032075002c5424001c482552500700500d4054038415002d10b03a0b982c0c603420454040d02183c8251000442d0540c001031031240305400124450860740d0340c142ca20380f119107034004140d00381d0400b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 224123219 1250 224121969 224122009
    0x40b1c02060903030c0d020609060118020304240c09060206010f030b100806090a020406080a150c0c0503180315040f02010e061c090b1008100203040f02060408060103110609060702 79
    0x242c0c20190303820406084094840c1d0300500c08aa16240000e040c40d034081d01c004080d0380104d0041c0808503100c117038811a04101d10300161a0f41c0d450500050f5035413104029030b440145246182c00d580655004210341c0340d81601e0319086113a035074000700c0c0e8441003442030780c2008180d00e00c00d100180c180c90226801140410800c80300a840300c81080c1044019101d04071164401d5203c00214181801894010300882001d031060704040d0300c0d903240040900182c54242c83d03648030392105d018050010703202e00d1500f080840e5205c48501d0109a2020058540315210b4400c00040e007a81c04941d9815600c12075010100c40d86005583e4011b507407100030501182c4d4442c5042c401d14058801445642c031654411030404901c0d9081800c14001402006e44141e40610791450705108140d0001b034120070311081d0560041c1c2d40d0b540c2d410403c50103802508025404440094005020b40c40002c240303058078000c3c51610407443e4000d0070800d5a2154601581d0020350500a51001d45841e2014081420441d04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 224124469 1250 224123219 224123227
    0x603041e0c0b120a0204210309081515190b0703030b0d050604110324040c0803040612050c070209041101180b0d0b060c19050109080d1a040b1c0206 65
    0x20381c840034098a50025464400007042c1c18003456054001250080710a1408528050401345034010750b040100b0b011a0032080d070f40b08841010310440842c0007d00d4040103591400b040d460948174a1582640c8100300565540c48a41e080e04e04141101d8040d13200d082e042c00251700e081d0807141141c000c200c1c1030f424156a03100a80850725118260342c882481103002d040d1500c0c00b07241942c10000c4080d1030754003c2e8052461281125008a00d103006a0700600311420f01d0f81d10b80c41d00038140d00b03440c2c1280840d4000410002403058101100c60401c29803428140041daa40003801c0b91a8002c0f944065401a4141c0108021800300c0b03401040502c03040c0b42c150a40c1280d40c0903d2500d1496901440213154001800a100584e44c410325100786400c03104186003d180f844901d07035035580d60700200011020103103040d042103425406620101d0780304103950740700c8000b803e038503005046c14000ca02c1d203104800090102ca00d840e00ca0020842ea000300302810070354910380205800c0148a5040343c200100300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 224125719 1250 224124469 224124473
    0x5090112230d2006060f0d14011a010206012103030b0102030706090b012c0f091c09050a09020c060a020d02040b0414010908060906040b0402010e04090b010f0f050603041e 75
    0x11050202c00c101d035849604401e841c0d030540c003a10b0169620560354940140c0107100d690750740ca0281c29800c80c8219200c0761400c20303604104850340c028078400056503203849034403d1f240c4030003022454800c0e026020f07152141e91303822012005610368820710310504100c5400b000040d0180c1d00002080c038043c8112420103c00d507a4090031900948029203103001030500410481c000928540408900d441c080701e5000f0708000d080e0505807014040d50580681e2400144142c01c003044003811246e6013580c1070074080c0070808013801c0320759035006d0349004ea8225000400d00c180f20f402285c80000b650001005183d480160400081d00302444840940e42c0070440064001080c0c00500040c00b0008803c02e030b0201000c001411036425580040b1058004004003d5203800106c0d401760b11035000700d4503540a43d100e1004031a800a40f8441c40d90152400507400d00780040c44840c80c0c1604c00c00700302016019260fa5045000c0703080c1e07209240d40450200b00140c0001c1400d240000034018422680c00c041542d9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 224126969 1250 224125719 224125723
    0x3020d0b06120901060602012c1f0204050406090203061e030c0402040303030b0906030d1b030912060e0c03030310140607170304030216060c060525030b0306010509011223 75
    0x114905582d2184001c06101d5a2402803140070010061b50008000b0015051159105100c03c21448440c4008007840c070605007000780014010350440b03609800200340741c012031000a4120b80039450040303142080200c0d00c42942d02c2103030301404006180c00b4548490310380002c000e409040d21541c140c05000054921500c031400500b0141d4070948011888808510900c04002e2009001c2c0e0300c02e90002070030841d0b0300d420802d00801c204d01100c5500310400f80e07040a8070101d182e640220a40e640060001c418081035034403030307000381c0206003d40750510141410141d507800142c42580c0703080044401040070032040a5800310024002e880f5a0500696448100c6050384901d418030850034000208020941c3c18800c00300140303001400d180c9001d04064000300381102034040244040e03a1800444c1d0358504450301c0141031108101e040c0e2041c440c40100802802c2040380c3d842c0207100350f80c00400c0c2c43c40c0012043d4183d80e0070b0a080a507a038400d4603248180310780c0021140355045014400c42255070300f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 224128219 1250 224126969 224126977
    0x5010f0507050c120a05120703020c0a140d0e10120b0301020415300f02070c060302130803041518150216091a01050d0b18040614130303020d0b06 64
    0x142d856843c1c8440810750114140601c0f41d41c1d2511003241080301d03110b00d94103c0144d03012811002c944550660b2612400e40c000e11450500003118415150900104045000a0350b0280d41001c141c0d0090500f441d001c0d65002da0112845034000398000111100340c0c4901040007504140310f6003c2644503065020908a0b40590090300c0700c482c0c44025102100d401072688008003401c04500f000d85030b00707a5030700320750101c0c0c022221240c41c0c0c03a2382039419002540d80646d900250485e945001e029a00d000140017944291115801d44148000c00194103c1c00f00c2a2011180c19008001002c0703241a412100c00c00e03c0040d10004a00310340c03010619131035806626040307903041d400500000b045040e4030783d004042c650014101c035040480350151100041700d0380c2c020003000e00700395899005d0840300303a015203001c4a41c1c03174101f44025500c0f03c1e42180341c60b01c01e020314014482009561050709215209034412100218615501e1846c5000244a0360051850400c40800001d50707070011000035031903900c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 224129469 1250 224128219 224128231
    0x9050a0308090111030c0d0f050d050f07110d081b0412032304230a090f0506040e010c08011415030103030216140d06022d18030a021c05010f05 63
    0x1502203000851560030458a0301135001c140c0045040419000040f0ba68480c8040f1b0304040240402403054014080c200391a55502d030340f8010702081c071b0f14001800e0070313a004552410000360300ba100191040c03070218500030400c546a0f6003620590341d48440310a0b0911120154080031020480080c52246608860030914440c3c2d80c0d4052114a03a1100074241d04040c4001040c00390400c82003105900e03000b05010200e4000c45440c2000e091304001518551040e488001c0c83c50a000750004000529446503100d00c0080781d0400c0180041d44034a0300300c03420054070790080f4502ea00148a028114403901610703140042005200c40112142040c05810a80c801c9016a0120140c0c0c0d0170b0940465003103014043c003960180c00448080c00007111195110009410b840c1e0000da0041c01c030751640c3c0c140154805041d11103191642421300d00b6143d521180640355443d46c0c501750a4010310b000300d11030340c40540040c0000c03000d03141864070000c00024a4012107440d941e0f54081002508a4000d00340300f28 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 224130719 1250 224129469 224129483
    0x5060f030f0705030c0405120109060501300308130501060b0f030a0b031c03020d02090406030c0303020d050903030414030a0b0a0506040b06090915030f06040f11030c0a090c09050a03 80
    0x810019454407414001410000c00d11009104010b240e80060054034120f4030100d84003244005501d4a5500424038208003500240c2808004a1200301c810317400a000f19000000244c590080008041c5d41d0748100e8000b40011080c8020a0700010306145254000d40510300006005a07141d2005040c2c0c2d00601a401c0003510110421034003050b02e100d88489050b0a078040c0052743c0480885421a84882840d00145036000c03a800045010b0795042d942c044001401c104040e58607414045a0700e500341c130027100144210403008410314071907015100c1902c40907004605040c200230346680429080505103805104203244c40c0003007407000b030b20140a840d0b04240007486092030024001595010300e1f0f42da005140400240140307032070b0044000e40c4440c0d203c21100010703840d440000d0600181e50b44002c52352181c131061001740400301d101200011b210341c40e4543d00b9562441810748a80384451035940c44200f00400301304131500c81d044000700400070b1401400b880e0b198000a000040c49030400c0d6502 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 224131969 1250 224130719 224130721
    0xd050a0b01110109030e1e0d05030712050703020d08191b1e0c08030a060305030a1e03140402130609020a1218170c0109060905060714040602151005060f03 68
    0xd58004641140b2101480c0081c804900251005042c520164606900803041d0203101840480d480f540c020b0082c00003407582001c0d030720300c0c00c01550f42d4010301d1090b81d141501b203242440f110301480407200c2c12541900584200f20142c6808d50349994000c0c0041981051401d20740010740541c421924a14038555a4000c01c1c0500c0c800100135007007001601034000406011022144e80104070308800d503030b00902c0a540d940d40c03004000b0262515500c02000e9120109000e0107141e04003202038403280006490b08411008040301b101a05e4014070040c0e0a040000081005410800e40071401c968cd181d40100305680c1d40e00d030600c101c0e40030045071703c0000e590f0291005104070a00506c200ca040d03450840e10105070355183c0303c5101c0b001c00300032164a580000d404544403029003200d000c00d0381201d01009104118106151640012920400015201a044841c4149510075038040d2400e2754002c14125200c03590001c14154058030083c1c40e0302d14240002902e6480e4401009181d8450a0450326 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 224133219 1250 224131969 224131991
    0x4020403060e07060908150c0c12032203080403030903020120092713030e030307030c0204051003050d0e0a08062e03050309040f02310915030204110d050a 68
    0x2070034a0f03034102c001088403203101000340480000d0024000c15803041c0140d000c0e1210001d550083c07180130441001809810706040e4070340050380185215807001c1d00351203140d0070200400c1c003480b10b506100502044010002c200420300c00d6110106180c4280000500d408015100960300020700c06c1000c809440020103504a0a01d070b0024941500e000c244076003405107098007a64044002800d84403a640003c140b002414425925400c0303401d000340507039580b400745040c01401c20011150a034002d9040c1808582e0314020080c1540c02c580e0804054500d01007442d50456022080c28100c6d0351041e098000030a4408090250f180039400c400302e251039104113000a41070f007090b905c4103041503070105041080418404802c0f103241c01021200001d051902e0096000203001d40005050303402c2c03000050a4070084c540020014044803004101e03900c070b41e034980c583c055844030640e01d0380200c81c0490410040c02c042d001003c140c1e00d0f002c0c19070f05240880c8100d0303044402c11140c500d807241d00d031441003403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 224134469 1250 224133219 224133223
    0x80706030c0806030d0c0804030819140306030706050c030d060801020307020c0102060c0406030f110c010f050606040302060913021204030504030c0b04050303030f09030903030705011401060503100e0406020904020403060e 97
    0xe2841c8581000c1c0342c9840c00340002511800c0703400c44442440407141604082101100845d0041c652100d441516444914907103140c0310f03140400c0c1e002240003000101da032a039440007924401d00c2d0050080001c1818404110b6058100c2980c0c4480c510007444841d03400d9502d402440c0140280f20001030700d03460b00c480300034034003201584d240d41550010030074440b1840d080c0c1c085805890745402c0200e080d941d911941801000c0f039075881040110086400e044001701034000f8008824805e0080c06140c44101c100301082c41203200003035001c501006450300500f81011005845c580748100141403201c042c80001012100f00c504800013200001d09104100903102d909020701040401c0030f00b05410103000c2607581c44050182d0032503a43c07007000a40400c0c002c200f210030100000d0141d94079400380c3c7c64800e02034480000100c070708180140000c541c81e845001035a2041409002007201c4034601110000303589005001030f241d9640806c0705168a8440340000c00c010761294a0004101440400c0d8034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 224135719 1250 224134469 224134481
    0x171305072d0b090306040b0712060305060708071103070201180f0b070501150308070807050a0203100f050108010504120c110603010e0402010215151c050d0206090d030905030f0d0b03060108070603 86
    0x38074410b00a026648550301c0001d00030380e01690142d00e044050702d91100503241000005410004103081810110410170302094050060425460341445030311000001e4420b50b0800c18030300c6c41d607807007401203801542c41429154601c105440d0400656511560700d807001e05e425420944610000151440800000348641c14008014084c40200d082c203590b070701a41403050690207003e40d440400c0a5007400001d0010541e05a80101161040d040308000038000d0004101c01c2c04180b0324180c000601d1035018000c0390b200710340c002c0320550b000803c1601900e03e4070000a06440c00e10f190b0f40c40c15400e40300c0360000c0d4060f01204400d102d11303240c01e00c002450807061112300d2151401032800d00565024968912940503811508840340d54046211004c81c0700321410f0280c510311a0741d401c001c1c02500400d40900500405003034800c0d002c1243c801b0340c25034100080041c81039100300019a801c9004038003400440641640104d170782c20740000020320b030a900b03801403103590300030000800c0510f8240c802c0e2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 224136969 1250 224135719 224135729
    0x130512070b04020f3015100b031015020304051c021503060f03030706050403080105060a0815010e0d0614011a070204020c0c09010f0312171305072d 65
    0x209241110541c0c1c0c1d4108540040c0000380030310081c561200b042d640b1400c81c460003030413020160005e811018002c00a034003007040c0384c0020b0f01440328002455009010014400c003042c1001c60501d9260102c0c10b13076036a20040444280c0382900801103112803080d400c0e040d004400394011070726181480c4c00c10448a5441080c00d43d02071030284000300584810f01e6800d50618540701441e00c0b503980c1008244102c103010303216941400000741d43d0082108e158441c60041c0d0080e9102d007076982e02c03401801050b00c2003d0404010541100002d401180400320040d0902d00c107141c0018060650400b003071a014a0b035608032a810340381c201d181d0f8624601e882581c01032801002106c107442507506c610b8160300c1080b4000c1e005540000d002100e000c030420101c050f00c1c801a104214540e55140003400040c040c0c00112040110040300d00788052050800300c450142889a426558540c08460007454205440440d05802600300002e814002c102e91032050703070340201030300003089403910900c03403611425000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 224138219 1250 224136969 224137003
    0x21504151d01030c23040f0602071a0313021305150103020901050409090602041d09010509060705030f1005130b01021002120118181218290c061305 65
    0x9500070044403070320700144a060a0900150140250604442c3c1c49801d640c150102400b4071644d10340480c280c80144105e40501c0e03040d030300090300e400e422070300d078400b44c0b007445095440042c2c0c5524090425000b590081002402303016a40c03c142d000c5a40c0314a100074503144550b403441002304440c2e602c0d0080080502c02d103404c41c038041c2c9010000c0c10500440c01201c0600c1d07541c0f500078041280650440f0040e2880c02d80490120144408108100e14112070b001029420080807414016000030194024150b076203c03542140d581104010701010014084064407079200400541034682c82e500c41004c8036024004601001140006840c2444120000261714410010050507080c42842d43d41520440342d8001c441d80c3c0304820702e40c05030100ca640301382c0381c1c2c10301c5a2070350400040c01c900e08101c640d9038a0b9810880d01182e40e00b10f50a41c640b0410324404903040b180204503108420600d020341d83d580c051410112000021454010121104402d40e0b60b54034120051010130401200310300140302c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 224139469 1250 224138219 224138237
    0x110901030c090f060e09030c071a0403062d0c09050a05031510180615180b03060d0b18060907080c010e01120507030504021507030203090609040902150415 68
    0x354140000250b0300c82d034030800fa65580700481030700c80b98100c24002e1074035422545003410408030b015201d074000c82030046c0d940700c0c0072400a20003810180391015040c96001060410b403440d00e80d203010b002070001c0c078039518407005450400801803505c40c40c95801440d400140302840d07090040c21107012500b241d4850005401c040000e80c0c4c002a254208c030410740f0000c1010f842d80150405500c196030041c0581448c8695103110b070030815480030046808100c2c910b44980501c000544417400c605044078100e1001d9202032003491803643c0110b0f040100581704003080c200701e880c1d42c0c882c84420380340c0300f404200c08540488070900030030045030405c01440c0540603881c9081c0f0500d0b0b85540d4005c4480c140030101c0230301490307680280b070000600104000d00348254606800d000780148001c80e001c034821081ca015132181c0000d42d209071100194180c00035480c10105000300407003604010391055000307840f69080001601c0c1d0140c160715041c0400c02242d02c0d1410300c4d4131030101c40004401e400130459507074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 224140719 1250 224139469 224139473
    0xe0901141302071a040b040c12030e1009050d080403021003020a02100b03210a031b0c061a0d030203040303110a11060309120a11010f050c09091306050f0411090103 72
    0x5035041500d96010360380140d49904500d0051040101c200306031310340007107090800c030a12105c1500c591060784522103c040785505d50341001400794602d6000f600140301e460140049003030500715900c0b416201e0402c07280301683c41c0001100c00d818207070200e400600c041000c10450601d001d0301900103036981819820200f05c140020b559011840c040502039441e40c80b0303462542c60500482c03082140640d04051032500d2400781c040700f0313800391000200003850003006060b0322450440d2500c0c0a840359590904241c072980f1a02d0103003810f160183c4c1054498508a0602d6444c8142c64007640e210741c01460b125490f5080142c041031a10b504400c0c1900310f20110800500300c0020709070084011910329480c0c0e11002e40c040d28050503280000c458910005a181034181c00c00d09104c0031500d41c500034410190400350308001e03180e0a54100000c00703020b00c03d072119072508400b81540040d404102d41c170003c40c80e85500e010f980040e1a0a010003018000340000e000e8038580210040a01341c46c4043c96501d19 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 224141969 1250 224140719 224140729
    0x5090f04020a0813060906020d0209100809061b0d020406020601230f12100e060613060e011202010c12200c130b060c0105040803090f1b0d0606090203070e090114 71
    0x4081c031481104d00514070b81040650b070300850019800c5682151540d4044240ca002540505050352060b03203151b948044081c45103074168030440300c0304068402034840c4c2d490f89002d2540e07201041094841401802d43c50b4903a4400b0b0030013840164010b0085502d81242e009050310400705000c94070759920302001c8242c4404114525014083e55014820500c02502c54107081100d401e040c100350406983c24000e1000003130b01800f64208030344060300c844004028100700e451501c901501481d02c40010003042c450010403491040c01810f205605241c00e5582e503021400d42c60212010503455000310911132000e24140710805591801007002041e1400000c0b80c03a014601a41d84d0103807641c08100007a26035000340c0c1c00c0000c0c000000c4c8210b0a0030b145c1180c15800482c1c900302c080c4103c07a50f50022220019500c8408c0d20003103101c0344805043c3d401c2c014441c0348448162500d4dd150700c80005c0d4441c4030702c011403048000b0b9135180c28911070b107420803000040c180e210f610541400f400c807035541e03a16 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 224143219 1250 224141969 224141971
    0x2102070c060203030112171c09021002010c0206040209040c0e0705030a1503081c02130f03110a030c0e1b1204110f0f120a0209010806090607080f0606070302160605090f04020a08 78
    0x1040401c01020511034003a040d61180305034031a0901ca04235410741c140f1102d038004049491080741c1d0065807d01e2203070224222100f14201070010781c008008200075040101a0681040c000c01800310310f21344503510080c003107401340c07507290000d90000108400212940300350140d0740c1c1e0307580ca241012403640d250f424150183c00c00030940c113200c00d009901c4403805903044444a0920201d085205a81d609036020442d14502c8180e80e50540020200703680d1500045880a4a62050040d14403d0038070200c601d40c245e000b400c6855079810405400c040241400c080d02a50030a16000d00191605140c0465a5240e0b00425809081100c1c0c42111903540d0244640b0041c4040c1c500e1402c078084c010b421403400e0b0750000701940114030780d800030a4564000c13906511445510086504030b8440141c2183c01c15000c48001d1540e04074a40030480502d4000300811095010344122100d0a0301b0f0246511030840903445000402c20025401045080c01c2185034220f500c112011400c1044a01c801380c00400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 224144469 1250 224143219 224143223
    0x5070c0803030c04090b01020129010801050406050306310f031e09050f0301020d0f0c14040302060406030b0402090405010b090301060b121303020f01050a06090501090b010f0503072102070c060203030112 89
    0x511920819207e034401d6014004000c0302c0710224003904806494914040740c046503150000e81c000002040908080c0100c90072500090000e02182c1c0d01c030600c99240309286801007540c07501a0915550b0307a45082c0c1d1882d5042d005045407040343d0914a0080d10f01c4080f600c2c600b80e0a106200612105508002c00108403030042d03502c3d10308c29528000281c024400c41c031a800d0458981a40404401c4540d84070b441d81c1980380d05c502010280302e40c1500c4850185110080d802002088203010131446a0401c0c000c411004d800503090595400c0010142c44003600102650040400d1244003851309010b00350040600c440105d18188000d18602c6400800402042c510241100d87d04109842008018111210741c00200086c0c01c003081c144c00075101c01e11070440341600308000407800850503c201700034070034140c440c4541218005800e0340c4c5500028210003d00001c03c840500d01a0003038a070300c2c0705181c1041c0040e83c400304d0380740819140321241c10403421580184014003042600100e81c000f125 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 224145719 1250 224144469 224144471
    0x30c030e07030b070207031a1506040f1215090b061905280806010e0406060603020901020607030b060f04030503070c1403032b0f0213050108060a0302090a09080a05070c0803030c0409 80
    0x5510600284e02d00569540b00900c0102e9020140000d891108d1450f0300400d072114800e02c10f828030104000d4140194040c10042200b07000d02003200c25034003002e80340c589104400031070803901c0241c425002c6031413101050724040e08202c10042d5519045011018030350440e181d10920500b800c001c10300d40e29901118042c1d0030810030700d28545013009051607008040c81d500b182c1e01356840d0300c103441500e581950b0890341103052420100d40280039000790b0320140c0c01a40240b1007070b6100740c4120301401c3d64007001c135003040c403c02c4010034094103030008101941c0280001d41d603c200ea4506007021140b558050300b42540ca20030140400d550200482d04020801020100305468804103007804042e1058036203e03c62a10407a4903407894203401034841c81d00c45c0311503644850341c4c135001500c0b401c02c200c0d200c81c0d000900d078400344010714000c816150040112840080d200e42d2940c1c9060301e9901030030b01c01c40803a03030114045040100030150f00e005401c034000958110b0500301a082e51034025401115031071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 224146969 1250 224145719 224145721
    0x60709050a15030e0c1c2913021305090c09061002150901060e0414060a060b0a140d0c05071e020105070201080604090209040b010906060305090a030305270d030c030e07030b 76
    0x3102040174020041d0000d103400024102c07600140841400c0040c121843c09030308100040c505000650450142c48a60981c0550765039860300440202100c1c070100d1380140190f601d541c50581a00c24903200311042c100401690102c60b00f040303210b0500070410382c82815002c0f41c82c5946603010a042c010b4010105082d4001d0716240304490250003103130005417501c0301035400c0206018580a000ca040c5101c001520042e031541c0c2c003a04140c5409004404064104200c0e1101c800e100c0c00d00c0a41480200c086a424400c6000c0c2c0d001c01d40d1120a0312a0020300086042028080061282c110407200d901e03100c081d130b01d0640e00203004c41c022414081e06020a10001450580783c0f0317040440b62680c001c05120162421b89440c100902c1c0c280641c840883c50b0140201d003842c003a1203840d004605500082c004a001381c0d5046000d410014404061031003020b0b10201c41340407107481d20529005590140c007291842060023070840c1c4040001307000b0036007440c0002441341d2000c501d001c00d40c1c1c0c00507140201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 224148219 1250 224146969 224146991
    0x9080f100b0a080d030207031101090c0302060f04030615050f1008070e061b0a110d020d230a0807150501060507120e0d060b09010b030103020a0b1806040602060709050a1503 76
    0xb4200c40e54840702c0310303000b240d240c01d2101d54154014003880744240c50358034075003215464042c203c8483c1c0900400c903002144051025250460140002880108240b1300e0180c42340d50703e20a075041c60140c001200d4000c4000e10481c178003008505078070700c020b40d2680c025440300c8400610186000e02020240b142c41c2c1040b06194885108681e05594426180c511a01d02441c0306551140d20450568030781c40d4005e801101490038110204107541c000308503000180c1182c541e165480c09805428240ca201c18420041110701848150761103800f443c41c0130b8441c0c075a4140709216007581440e0800003480c0c42c005201050f004001c0d1003006400204804140154400a807298146c01c94840d0380200d02c0000c600800015400241040d80d0076a5060b4403070342d907804200c0c070501003804002d40c04802c6140611100d0081009441c0881c0d610f151100c40d40c00d520082406a0701079013000005800c60001c1119403600086040002e04c402d681c003240c0c80d0704e01624440460442d640d0001015203520001070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 224149469 1250 224148219 224148229
    0xe0102040504020a050a030e0303091b0316060f090f0e0c070c0308030a0e010608030405060313050c100519021f0b010e270a0908090d0311100c09080f100b 68
    0x241c01d01400c21542c541c0300441c060850b4000d034104000003820060540d0461401000350b2b030042603044010104e0907006000b09104101c01e40c1c1c2a6010b2285083c0303000d01c0352460b80948024074440d1218110b2140c18200101044625081901075007844d80c001c21001301c9407500b00c1e502c214180c0c200c0d91075001a01e05a409200d1682c03025102407404401d110700350340c0a500c06101050f200b8020000e190340d842199880b80610710801d40e22440a00000c1d4100d80007803440d82409101d201a40c41c1400c040c00001c0d103649990b01181d00094010615841c2d034a041d100340c980c2da616a000908450700b1038030b50780e030000000c0c2800440603902d1354907131240d5074003404602e241000000d00c0901d43c0e50007404403203034500a1103440759003441d4080109900c52198402c090300300781c00c60f120518012910050214056100078110100200c0307440d040707410f00302070150b07410042d42c0c58008103031340708a1b050080851643c0d800a0721240c000c1c0140601c140000152500000340c008004214080c600000503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 224150719 1250 224149469 224149477
    0x4080d1b150608010e0a110411040305010f050403030b1804140309040504060c0201150303050d0203040f0209041416120b0a0e0a050a05150405060f09010f150509070c0b01090e0102 79
    0x415060800714070021a4040750440b20a80300e03150000c011820060b1440c695400115030054a4120400309058203801d10342c0140c2401401440c03900d20740f40d502c0e940c20342110003d81248074002c0c0e0b10014401056494000ca01c0344050449100810f94180c13407071001961001340c00244024000b03001012000c03c14000e1b07801503507000303100304503030314103404c005001d80f0710100c40c100154070b021106410078484003415000c0c1e0780c056894a08011503040a14020361000d00242d90312071901c000b00c2c0059035082049403107184030b000306854140040c2c85241c074050342c015a03010b0484800c24140700072031201c10034425143c1c00440060158841902400040032001c140300418014080004184840082c440500503c80d07411100104100003601710011404d072402032442c1c010700e020915511010740c002e604600d0300f400006605a8500c885011242648211000c2100c0308034100040d2034544e07105c2d81c2c00720150134440ba8020807070340d0380d4121a005000e4026000d90340d40c010310b00c5c14002d60541d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 224151969 1250 224150719 224150723
    0x4110120010e0f0607050406020307030c06090609030c0c08011b0c0f0b04050304031a0c0a050c1608010c0306082b02160b0904150b0910030b09071e0504080d1b 70
    0x1c01000c0300580a107070300c0d44508071181d41944130f00c40210702203d200d40e048070110781859010310b040c2625a40e0803121480d1301c20090700c52075250b0b0440001300e1982d10074591054840d13198800d554200e4509030501c0c0003140e000121300d91610070010030000a40310707142d4034182c444c0380107401550540703800103900012100c09440c40600318200700c01c2100000c010020340b80039411000c070082030f2504490951108440e101c48404050107554901405030003d408031091560170759540341e03094085d10400118603444008136039121003000d0032041e010312400d00030300341940c09482c07160040900f000c1054004551001b000c40140320894480d4130901c0800b41c880201c03002c01e03803010b981d100114110781100344180e200b14a040e100c0104644043c11000c12030f1a403450950620300704508001064607060240b10034907441c0c011400c495540c00114505c140d01e00d4886620001c0403220342a1341c2c2282920703000a07c00c4c100b00a00103040d00050f040450110f0b450012070401c03140740a210304007111640 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 224153219 1250 224151969 224151971
    0x5010f0e180a0209091501140c210901110114060607050709050c1e0309060c0901050f07082203050705090c0909091f0c080f060120030307090902030411012001 70
    0x10300101c1000b5400801540d03000715118451600c80303600e404401710412402c5804500034401c0000c0e0080d0f0304019150080d904003e0b10800c1610002c540c68950940d400040810070000325041c10b0744e00320b4180030700c281040008020000714250b203d00f01c03000280c2403910400300030038002c0030004204115000341690000502c80e078100440c1c00e0f495500302d01e61201c02400e0075405403115505a4055034405c001d600024006925400c200d16880d600440c0c203035041007002c21001e071000b00507000600416104840643c3d0f039480030740a411105081c42501c0030860f22a84003040400d0000500f0816039004640404180e150740404840c184651043c0d03680240980c810001c002d80c02150300c115803864003000111260b002c541c2c03c02100d407090940c102044100c00803803095500560b60a5203c003040c10030202c140300c0c40c00117049502c40354410074134075403001041188d6541d00034002001041c0b46d03501907055050a99035080d00b0b04c00f1075027180c1006480450710409000400041c002a040c03940 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 224154469 1250 224153219 224153221
    0xf030c1306050315160c110a0f0915120b0606040909121e09030f110409082203020d020112140106110f0a0b190e0714100905010f0e18 59
    0x96100041c041d14440d1078400d0145403101003540501d5448588201d00144011440c45020a026100c51021013015542d0300c0450b284500355880308081e034000341161450b01c054292604c00c4a1080d12084c1ca85007102c03416502c82002106101d840804103130b98000c142c01d466035201c40203e003c602407507100007544e0382412004010b00c81128010329000c2c031503940f0b840703040d070b00e50700c0c1c1803000316070440c0600003d46981400c101040074a40d00c1a02c0a201c1c0007003810076800707140083c0a60744c101d60305070b03800c5800080200c07519860710f020ba42204244421320308054555000100e06071096200641802102540c0e2022501c0f29400301115071402c0001a0295841d01c078010151400c03c15a1080f520a0502d220050400080c82d0b020240d0302c8203500c6100c0c1d0700d012a5000c10000029102c3c0099181c50743c24402180030700c900006040c0503201d10b021030581c01d0070041441640d007690303814010070743c80c02d021990b404800104045440d0810740c11030305c0703040e001c02e0342c10f06d030002072406a0700220 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 224155719 1250 224154469 224154499
    0xb04020d021c140129030a0225080a0f300c0503040803010b21160f030e0d030e0a0206130501030617030403030807050d140901050912090f030c 63
    0x80d0141280c61004442641021031904880d0122041c0101c0e500c00d00d41d090740100301c0b40101014002e112082c1c3e25050b1120710f42e50300d8078030090304203448512055801050620241c035401d0381c1d142715400c0c2d0f40c1104040c0590b6407034018152084480000800400840402166019110003241a4901007080324000544040f01c8d03551f6010100c0c040c002c42c00d02c40040d50207480b54003903901454001401c01d01c0d692900d4288022039101d8582049421b882d0101c0e42603c80190946c54800d10140e1801400e00d01d400300000c04208030b840e59001854030b040541d111078040000d0f904020001c0d42000242d84000e044064030741a40010000d51041c1c002600c19070b482c51f4003400104a0b0340a0301e00f400720340d885070408580700d196603c10442c1ea600a02040010070301c1110000d8028602c0d0402c00d282c9400d07e80050b060b1802405406042d078005414000503031001d1046030380c844c00c0c2c200039000d0211103420110305880382054052282482c040b5500d215901440b146525000c001d041301d01504c00c031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 224156969 1250 224155719 224155721
    0x21130308070c080c030a15090525050a05060a020d0c08040504021b06090d0503070c061d010218060a17040c080613030f21090f0209090f1009081c0b04020d 68
    0xa406030030018001d42e1307441201c07410000303181b03401070354450000c84150314041c0c0754800620039980300f5200c4e1711448503080c051a208030a4602c8040203500003114260800080c4107608800d03500041c0214410400021704580c0402c14101c440c03070070710b00810492a941841c03071190249420a41d4410701c000fa03482c4c44205415581a03030f01c01d215081d00c3d404d80e03075610559220000c2c2040b98012900400001d42c10f184904030a202d0584112400100e001240380c81d107040a07040b0003549420380d80000c00301c01c0010344070903c061541c01120001d00d820301001d13000b07010700540040a25060000b102180030000075904c0304000c1d00007403003110783d50326000c004080740c141c8140c81a0007150340840a4100e491040703004416480c0c0c0e1401c1c0300d01d03083d0141d03007610003803400c02000d4a030300648a844e44010381d5402179241c00303901c0d104010f040c044101c6503d41d0420b811a000307200d000d46401100b40c0018807401c240c9140c1c43e1521074807003420071081c5209002c0c0150010a5600c1880015004054003075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 224158219 1250 224156969 224156993
    0x11010c050102030c12160f110f030409061e05030c0f04110307020c090c03100510030e010608030912010204030c050409030203130608012402100f0209130e010e2113030807 75
    0x32401442500d4a2003039800c50b01b01000c101000031f82c981140c0705545d0003000d00b40c101e0451a0104c4048840c4c6d2803846045400c10342190b961140c40381e50400654034032407202070502542c03000c0e52008a180900007039403403070a40d0241d409245040950344856803264040d038031101132038444650340d16002c0307002515011075180c2070b440340980b5404140c0a1b4151001e4a1181d008100c52002850400e0104102143c2c540c800381d04040e11040b6044e10300d0003e00460300107180c55002140ca13507040340200891940700e81074a0340300382e10600042012035020151601151010b070f4000914450b2400d0407400e5124011800003039040301c0fa000280301c1e0344281c071581220016090b40300480301210903049250b040354010b00c0103030300244030314884602039481100c0c04c2d841004014500450000444e0844aa8840304420310b035a4040ca500740d014280502e464610304d0304040e01d0110450606005060703c00c5030005807103440460510600d0180c04080d4001e541c01ca144a0703200c3c0c20314982020741140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 224159469 1250 224158219 224158237
    0xa020109080d0203090d080715140601140f09010c020a060807030b120c010e0604170a150203100308070606030f050a020a060e0105040303122d050c070f11010c050102030c 75
    0x4a00030015000710041084220355107158051807620030442c00304143d13140100070644090900704440c2c00000c045907010b04007a03501070310108030000410058904800300814950610212a0908103240c80760011141c00b500f1900f21662100d0328000100c1d10214085002500600f401601051060304a50030030700c1414143d40c20700a02c034410040c0014800e42c1a00b2101d0b961008922031000c2d8050305218642d00320107800c981c1060b42e039041d2042610b040410540c2260411a200e9091041ca4000704481c448081009d40c03039410520b158880170043c03072101502403200802e001d000c02c55580c224000458015698209403c110b0910075102d0200103800c91080c242c15000140c1240158900e94908405031203e038101842c54070b0036150680314040c00100e00380c0d1074103001446404000002031000102d2405021900c600c0111000c40d14060f240440800c0306005100c0092010216140102c0d84900380181c50010309005071004024800011310550000c010482c8100078100034000100c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 224160719 1250 224159469 224159477
    0xa03031d0103110315040e010f09150e060606070804031a010e06120615010309170c0d0201060e0601050c15071d0418020607141207060b090610080a020906030103050a0201 75
    0xd118001035044454400d042014a8420300005020a84c1d012250040a9019001140f134241030031095086070040460902115a101002000d021941345401c290310310844040116500b032a042e140c0d1564005c091034412480090900b04102065017a00e00442d800011040550a00760191a00c0b034024010301e028040540c0019080385803000c4590f000c43c1c0e4100c0900350540711170185080840f0fa504000e4181512600d44c00c0006c1d2900720340d072500340e14100c051520385507094500d5003000c521562200031681005028004804804c0c00c258000c1c1090801640e45d040820b078490418030840d025184803c1180300708064990000c0003040284602e6180161440d441820001140c503070342070b4644080688407a03d00141082c1005003c0315019203101c9100c003003642e00704d502e40130300a0045284208080740410802c549805a0b5241d01811116918103180000c0030400e640b480f08404800c0001c4400441d94031040e9a040319202c400c0a0150f507074030b40c1c403130501a5603070614110803030003d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 224161969 1250 224160719 224160767
    0x1501170f06041a0901090c110a1401050c0717070c080613020a1502060103061d030c0d0813030816030b1512070804080f0a020718050403020105090607091707050a0303 73
    0x543c1181c079460300380700200711128990070072000c00010034400c01d581040c000584a0f012040d41c04118030b4229901c500403c0001480100010342520000790002c8141041881201d000a0840c00004004100b4841c086d48600903400c020882c885d10340d21603083d50040805000e03400103011400b2021500940c1c60300240e694411040c1000803410f0001e4005130045401803001441d95045280e004c0002601c809151103050403450850f0300085101c405030340f0600c00d01c0c0d1625040780115512012942d240c0094856640b000b401e60300c0002d00d0708841443c8002841011402688641a5010041c2009050358540b05030000395074410300350301e0310003074541c80062101071003842080d1141c0d621000c018200415194480c039503410200d0060158001d07043c0c0411074003045048a00c07000241c101c0800d40e410705c0d04019003142c0c0058035600542d040b550030030200381c2c0c00008603400c80311050080000c2c40450342446090000303c0c0c10859001429040002c203065200584420000c0411002c000c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 224163219 1250 224161969 224161991
    0x203030d0c0c0210030e0f1c031a0a0e15030a02010507030c06090c080304030c0b03070207050d03050903010f021b010c0f0e0f1c0b0c07150903030f0608011505030609061501170f0604 80
    0x2840803600c843c0c10034588e03800a41e8052601c25044004121008072010061042010006049410640007c0d6110304004200405945032100d11a1205800e801074106c140310b603000200140701d0414081d0910800f4031520003086100d60001044a4111103188030294448101ea40c0301e5001d4030050322201c2850b40c02050242202d001c483c0500703280d80083c1403503840d00080c000300ea41c00010a5090000900040b0341c540c17400e005641c00f000381c914005039100c001d403000c01d1900f10f20b02450101c0b0f80c9448007413040681c020021001c42811030074140398580d164000155281140b000c0e06410414020980c9018044204100d9406200c0c0b581d407140e035030b0340941804075400f81c2c802c0580381681c41c80103880000540c1c1c0c0041d410034042d243c046440f00841c1e1148040d680c1d02d500c0480309a645070841c10800c29641005006001d00701c4c080d00c42403c3ca454203580d07a0b10068250010003503940c20920050380200e401582c0000c0c18103688540d0b245c91941c0c1011000100c60315805981010b0410750 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 224164469 1250 224163219 224163223
    0xe1906030c08060d0b0c070803090a0201031d0d080c04092a0215040f060e030a020a021e090406020d020c0f010608011505010f0e01030b0d0b041101030501030203030d0c0c0210030e0f 80
    0x441024090000d001d258500e0320f41031090174003d0910800c1e540100100070105015030300031882600240024001c11450f440010100c0b00a440d04e0b0f1815041c01207142520500032540702a0a40b051800440c1511035031581151440b0f154004d2800c140741281d1602014070041c0c0d151000e015000815804070070700301702642c0f1003c103505075610260904c00003a00040c912a11010018042d1800007604440309204514550080070340d0780c0581e2001c1030300821840e0400400362940004154501803025110118220000150000f40280e030007080340c1c102140690f0683d41d00c800024203c07400564015032041c02000c5600415156509150380a00301d44400310800c4200e40e01a560b01100c103140c1c042c11110340c0740c0f00d080b41b41010303254413440b003040d5078a40301c5489050054518809504251400107080a2000d080505240c140f4004001582d030101c10b0700d41e980360344800032942c911b40d08011200040f00c800025481544003809403009903045d4452905035207448210351080c02c2c040b10480d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 224165719 1250 224164469 224164471
    0x512210f01120f030306030b07021507050a090302060706020d0903050c150402150705120406030c030b240a021014090f2a010509030a0b07020706050705060f070e1906030c08 76
    0x3803415800158140000f01c0c1c00c4028070810703000380b4000985945950382e07107410180940341c1400507070010b080e0325049c032540c0d40c00940043c172030b0070070b149070402c0d0b074802a10010741c1e1b11010384a0b034008182e01c005d010711a0100c41c00402c100c002000603c0c1e142c0740c054225001200d900049200340a106164000340208960242c3e4004081d07a1600f5600b400c204e8403a4402c080c00c4a0a0180460300c4407411707044030160001c0c0007240c8001c128011030410050403601c0381c41c081c0b842090696826013101d0b10b81c03400d402c1820507200b156507691100b810281e240c08490005054128030f4104581b0841603086251400f96480c3c00075076842880c0400354660360700b008060300203144002030030380e003542e500810019500302c01810020b090104403400681042c0c05008140c448506c80760400c044c5039418060b4901405c5036091140c10080340e621a6640c424004100b4900c00c402d0306c001c10039050090142030401e0b80d00070f10740071403d521500c0813010703042135200d040c001c0303410881840b0031980245401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 224166969 1250 224165719 224165729
    0x901021c060602060a020306041b08070201150f0b070c1a04170109021e0a032001030b0102061003110d06020c010c03110903100902150d0b13110d090512210f01 70
    0x8188644909617030074025071000d0711007a4800d0f510800106210740c500000c1040301e140e515004614174080030041d0958078004a240101c0031229014094031041c102010f058820980000b521441d0a00d000c4078001443c0d0404c2c0c540c07007401804218600c00d032000070801d40704280741c038210800c140066542603c014010084d80141c660141c0c000269589258400c0f03014010071041c0309a0760303038460319a001a408003800c24011103582c481665600f50040404824080c030040130303203142880c3e54414030415804024000305c10320189100c60303035071071745519011a0010303011551420dc42031094020582d58000c1c3d00464102022085400103072000d407103602c00c014014100720380101c003038000205402c500884c0e000d1991403d000407564000050030200ca08003000141a10307003103040145410810001c902c00301d09046000310180c2d0044252141003400050111300c001c254a0854204030301c0c02e8800f0003101e80443c0e0000c1c2c1c1f603900f20300d01301c4044856030307071071881c1c1c44410340d80d24252002d00070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 224168219 1250 224166969 224166973
    0x3050729120610050d091a0606030105010503040605060409080406081609050307210f120909090c050d02150d1401050f01080f04110a09062c18070306050901021c060602 74
    0x1900a0505100b6070704001000d18213a868800380742e4912044031151007091301c4810041202e003100d0044801440d410023000c5a0741d6040d90702d0f0900090182c40020001008151038a003c18825103c541000700041ea10100c0c4948403511503000030f0071506d040741c01078881319124524808090062104d14150303400078024058107818001d0b69444040070454000c80380d403c9200181c0411200c810346a11288070701002030000612050050a5060035001216203e143c4800c03070001a5400a941007114420340d010825007203a0300000d9424810000c0c6200c45090004003e1200d66a65003d80c290345d2030f0248554207a62a401409a07109417030080e240400c10210214400ca50220800c50b4410310a8004107210609200410004466580a80030040e01e8a900780050750b00c1e81700c41c8580ca1591404500300d9051818001420000502845c0c24a02c2245000004280038020003004e180c01036010300650600a4a1a000303602009905900301010005600c0c410304500600301258040c2d80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 224169469 1250 224168219 224168221
    0x6010305040b062809060f06020c0a1202040e0d08010602010608160608190603060203060a0e190b12070e04050d110d0806060d05100e13020d12090305072912 69
    0xf0034002c03421500b01d90050b58000b072003050310480d0480c0b03003ca409400329040104001c2c1c83c4c40c441d803a102c1c04a80101c4295041040013014903200d200c07101003142c09244100181000f00c0c00458014110b00384480c0301806680c80300c0e2201900040501e040b0399a0b07500800540b0341d20f0031140d495101c20102d188082c1d100440410000c0e100700c2c1026007205019a820704041000100380c030840350f03240d02c1242d5844c0c0205c00c018491a0504141d0002c050030b40c0d0805251038030001d458514204200321011040d42e901040000d51071b201490b0321000610300448400a0303c980c0e0134450310002301d40844451043d102d013441140d100d980407a5414580c000280301001c0845400e07a44190000c2c01590000d1081c08041c90704611402020300844060b42407080582c20000f05420140e0b0051455402c0d1201c00031600060703c0b203800311b55145400034000f4481c01f035040c008944600c41c680c00a4060321403a900800c0818444428a0071804207101c007030b04506111845076207030701070300a8440300d07014224 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 224170719 1250 224169469 224169481
    0x309080f030601170a0f0f09080d1e1a040e0102091f12022a030414040b04020903030f0a0f0306060e060c2d150402060702190b18030606010305040b 65
    0x18041d5420640505000c1c5810809422150403143d0072103401401030340382e8000004e02c5c20342e403140440030707401c2000602034414140c031020344a00c81c3c00c5152030380a668410b100c0700760074641800c0c1128108600300380005100e00c860800302003502103400d445a850300810075404041407003141c0c2e180c00080d01001c14595110356015030858000114001d0002d007000c00303601a001c510080c0340516003e41d4208010b00b07602e04c1c80041d49050810315441d07038010003040c85004404601c0340340801084a0201e1240c600ca8046400fa0203642c800030f801d88070204411140000c1c1d1030180194100a13564440d0303100c0d900c0400c07002c1e500e032441650085281c0640d14045410010002d220241c2c1d20780840d408243c0d04480525030240c40d410051140701000801c0104020907c0000d4002164040483e0142456000200c044c8101e210003482880403080e0703042841aa90f600c40c00801d44e0121a60325089501429040909100307501d078882c1c02403000054156009100d43c5015a401011520340c2c2d90b140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 224171969 1250 224170719 224170747
    0x50606071a0405010902060a0c11011103031f05030f0102090114070b01090e15040c051002011a100c05030f040e01091b030b01120509030405030610060e15270907030908 74
    0x94003c0d01d49549810f504005602c6080003801061003a9503508515a4503040c81052010000c460a04100002c0740c5480d40c040000207503508000550070000321038100c01801003070003405a00854041c02104c2813a01c0c0b01b08194003a051488081e254030015140300441c01400f8407401d000100384028020040c040030b07903035900900d480d2111404550151404051820340280d00300c0d411601690b0250f0184100d0505c6281c1d855040014002444064070200c00051800d0341e2000b00b0740540030310036007904004d01c142c02e48040c05821a0a03290781c0c40c10040d06003066441401840c0310403a040c0000681e01070306215218250409983d41102c000000314200c010300314500c1100c3c100044410109411001d07482180c1c013511001e801155114502410b141c10b0040080230040e000c00807a00410440b03822094512940e08111085401c0d180003292400141c05800312005002204201d000c0550181e40c0002c00700c5c10301101c10660315905c507c4118250303000010000d04940091050700f00c54030310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 224173219 1250 224171969 224171971
    0x10602060919031211121b090307030b060a030c0b0d1a0105190509030f01050a0e010507020a1b09050f0718181e0203240a050f01080405011508010902010201050606071a 74
    0x909000b0441ca081716007404800d03008200400d0104402c0d90a009450382400b17511a10000340030100342c00d0880c447d0010703466070501c1c070005c1c00030f251010010f8829605d07400002c019690028058090710b886040b42d800d0f640008000c510300e02c1c82c0c09410300498502d8000c112000341c059584520b41490140c800c0d0403011100d0a010138404148503007400c5035024040300c40814a944000205443d01c2500362040c0d0707210b0318081c5c0702070345400c090105455000c542c40155a4106075210700124031400d04164042c82c5910a9003801d10b0b08060000e00c01f040013405018213206c5e41c92160b46d034079401c0d10610300034031031191456545084070340e001045000c1c0c00100b50400914160881188811009000ea0b0b00440b000d41b5040744100a143d402038058142c6854800f0996000c0c00c070f14140390104d5031807448201c050341488489400101005400d400a0252031058103045202c1603940c0c01c0a17020b4855a0005c9004d5401c2c1400500c860500c8000d0328619038001c604200903450501c820213140390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 224174469 1250 224173219 224173247
    0x503010f060509130e010f1d0604030c110a0905090c09010b2a03030a0204050109090c0203040b0711030109050619050c0d020703020f1501090e0318060901210501060206091903 77
    0x13a02410f80d8507629a92050a280740c040000100b56000300252030b4084441d0414003001d40003265000e059103120024400383e0155142c1010400d41216041c01c9024100c20001e99602901080c030100d5010069001035026140d038a007111700451016081040c800c40034000c0154a0506002ea10920b00c02000009070b1540030284050440300b860a0540c11944100c032020344154000800304200d580c00004203000300844502040620a42d0b080252070740300741e20480a40080201d0345400b03102e08140003101e2541c0c02402040b10b060186042a2100000c5800003000c1c0c150100c4000d1041c0c241c02520b10800c07010004510f081c60103541500250041582034045100d2400c640f060000308002c3d80c103015182044c00c4c0c030551b14060a10f07003603880038041e45d42e0b2038000380000200d59952084000e806101117484580f03035810540101c0d180b2000d00007034035014201c3d86801c0c1000e03107103030300080c10380d40a0b80c25200680d071366020841c6c1d01d01d034950705600c169256541e071201180c400c0030380b03c01030b42d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 224175719 1250 224174469 224174479
    0x90b091327050312010b0a0f030b06090301020d05010e091506120a14070918110409050c100804050106080a08031b0d05010803090f031b060304061b0c0c060503010f060509 75
    0x86a007280c006070a880e41c041155564400280340e80312856405501d0300411020041c03500d13140c02c035013005004000351600c0109143d281da460083d0743d9640003e4440b81c042c080c0086407070703010095038640038203420700c60350b4000e0000c2c40200700100703404160000c00c080d1680c09841d01e074884000344244440c05600b014003502030b292009001940f024804650303a8142001045010300b40003a010444a48004100614262060050008541d40101c102e298800c42e00080c0c0d4443c00e080031410f200c08001c000b540001e408180d8103000d6000307140c0e180501d0040b03000300b10b00358568150f155641c0000b00046c05040c0309000040d0890b442c41060803124041c1c40186041243c0403503000187d038020303001451075400c00705100740c4a05200252070301f0030508a000f850701d2245041585505156803000341c2c02141d0010001e02880442d4200c08100303102c01c040080703076404c0e0310401003c0110f1030303208484440d000140044e02c0e52203403055a060341c511840c217110b07140c40e1000a540d15809010646d400c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 224176969 1250 224175719 224175761
    0x501050a1412061003110402030403080a0b21010f0b0405060904080d02070203010606050910020c01140c0a020306150a0b0903030a110c0d060e0f030f04050402030603030f0c0d090b0913 81
    0x80b092110314081d41105145003032050551800001260121143c90b0049105101300004203500200c41d98000075648000118001080003244a20f59618100c10f4002e5076008442807003141580034810310440001c003001110342403001c01c401c4d614191400c0d607000e0404800704011902c07800051000c080d542d200140f8102180d40130030700303661041e4082d8010030340120300080d0904101880802d900c0f441d201801c2014050030018002200741001b0f0140c003c00840d2000e030400c2d0804c14002c0340f5030000c04440d071902d030400d070100d1540310700c29000b800742d6444c0800251130b08400302039903200000140a58100310403804207c90025856040060500c00c000c5e41484688640704c1005405001d4107000c5040044039540e1840d102007134421844990003081030401e041700d0402684c003601c2080b500981e40703072030305c40020380346003d0103152005502d40014011840c01c0d00180055906145859608034999a200d0013a040d00442c03403c15004000f90f01c1411728850785074400110814403810071940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 224178219 1250 224176969 224176999
    0xc040f0909110105070c030b0a06080709050a0c0807050313060902060c2a06040e040c080303070e010e010804080d0c051b0606040516120b04090f060209040501090501050a14 76
    0x80200e921500350140e0781c07407520040c04031000c9107201207402030038880c3c6048060780d10301c82007604921000c7d00400c0440b011030802c90700781c0c11401c01031204008945640341c272020610010304054030280e1400f442c2a4a110724107004050503071042d41e01ea00c451b4210b584020048800301215042212103d5903010903200503690000076000407080c07000189100019400c5407503c0107026400c1030b2084280c41440942903882400b00e50907144e2080c658221601d640c80c0c407000ea40c8081d00059102c1c0004400c00090980c080c00031085000266580415035048070010b403070b220002e8802504c005003c1015020494864008402100a0345411413078803000c1c40300b401e08090031000078800c3e43c0000091000c9490180078443c0c103c244030111241d210242c6402504408504035031800058503130140c013540303917201e620440d00e668000307403509900c0050f4079000c0001d61003415018451458240007182e06080c61080505940d0050400e010407030270821001404040580e80036030201c01c6224441e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 224179469 1250 224178219 224178239
    0xf051219090b18281a1603060b090a030305280302221409100e100602060f0408040605070206040b070813150909050601020f0607021e011509050c04 65
    0x50a40a1660a05103050440c01e81c1c80082c811664030040d58003049840c080d00c04c0503085070f60032004c02d00003810203a24500d4003c0c00f46501ca003210050241d02000c000b60002846526140001241d400304101a102c40c0d0740005401461105a00300007070701010310009004400914140040306030645000d800c019000c0c150106200c0a0f01c0083d40104090540524100603c03602a41050001c00c00c5400d0402d54207112406501c42c40c41380c40c81e240450b955124600c0303008090100c1e40364030031507440c0021700c0416000351445450010303c5958005500700c00032003002c0b409142e11100b03145c9420700d44a0102d07114ec02526042c3d0707200404000001f0741e6500c4000400382c40384501e0005446000300756840a80207800d600c280032841444002c0401250302440401c280e441d044000511a220000100d15141210500d0301c5144500028021501c3d000104500707040308000814810f0240c42810a0903103580e0344050044240f106810304c1507404640006510901111200c1d0600d135035007084103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 224180719 1250 224179469 224179481
    0x190509030312090c010e0301050c070f080c010c080708090c01020604030f03020c01020c0106050f030307081213060504150501050303120f090322081002071211030d0603060b09070f051219 82
    0xf035099801410310f241c00356000f5181044064048008110619005018508038824024000c04c45019800c000d402c00c0f10007410364040301c801c00020803500c2e8000a02400c5004141c4a0700f011580320400100f0340c400c0010b20102c1c011040c3c0c0940013a4a07590780551b20003100c80100010b164091002c0c0a52010920240c1175850920700081405440d000038080342c541065405070182c1c10400440c0089040d8108858071000c00d04200b6289685201181610000b403480041402c1e04120030300003807101400e08084031508172a070401c82c0d83d82e13840406030340c2c1c458144e817264101c1c1072000045102c500d09000300d600800d5039007913a1030a056161b46004400c1244138404e0000030170441440f410030708221080300307009009001c44c98004203031503a40e40039244400e00001c0101c00c10044404101c180199001c0200300003051081c140c072490280060000d00c46494000d42c1e45d000040c149a100300003103081440140c80d0145400104215a590144010803984151101c05105c405261691081d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 224181969 1250 224180719 224180731
    0x7120b012315090112020307080411010305090a08070f2301050705071e0303060317091512061e030a0602091c08160c0e01080604020114190509030312 66
    0x6804a606000050600e0500010701948141e040680c1000d203441c0c0c1c98503440d03400841e0314215110981e11004071004034840c0c1c520146180040284442c1c183c11010300d0340164402c40d00030b16100c07030100044003142d008440b1148207520203012800403032208001840810300600d124048141d041e01c0d02030f03200d80d411100302284004024500300d000e0081c400d01e60011000e00e8064548009030300c401418025000a40d51664200c1d0b180307004141c080d90006000b59440f41280d0900000545842102d070001e4900901889240b50024160340000044805400820b640005944c40b4181440035000b060b2000035501c2403d8602c0c600d40d95000c1100d028558424400943d64403422001c1c0f000d50602202c4558000340c00784075642c001540d4105403882040660401a211480b6003031440e60381c0800d6102c0850710400d1000811852804207049201d04d00030780380c0610710005002041c8080c030802d807240901d080d054002c801c0c5544241e0080441c100010212410b00280b00900000304c0c9050710300c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 224183219 1250 224181969 224181983
    0x1419080414010603020a060518030f0705100c020d0809031002070b0709080a03170901060506040902030402090f04050307171209010605100306030b010e09120403030c0308010f05010c1101020712 85
    0x200800c0004080184003412070041c000d101c0c00d840c44e40400c10300e2009028000620002094170004806114008103803080e009040351200b9020089491b181e00080c02014060b1781920540b041190007402207021141e030280100b0140e00694032007030840d80203640d910b5414024002c1c804004c2c2c0003400901000d501805031590760f814800310103400c031042135111130444d412080380740021035004105000324000c900b112040c243e41b04489140180626001150300034000b050200b50881e180c1c0c0a144103600c00d648080c001d80360300000303c4262500300c40040c0103034810070401e00000d01c40305190000c4507a16000c18100b941510005441d100100da0340c0355a80e54818013002186820000e50300d030b108050400300009825506c414004000500a00a144401da004159003010410020350980c50301d0800944540d201d01d0020300c1c050f0258020f81c0051001c00007c01c40c0a4907070241b2044440503100c01d1004691075440304002c200043c181411b41c00360080004c0c04044001c1648911441a40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 224184469 1250 224183219 224183221
    0x905210d05031e06030c0f0f120322050a0603090206090418050c1e010c0f0807050313060516111302030a09051b030601170307053705060106141908 65
    0xca0505904000b02d00f042d0007820b44090200f142c42c0882e00c1c814950050f5840c01007405000085030b07606180b001c0b00d541040b90152600e083c454084058a002440c01c8881c2c0300b000d0710214007141d001000d01615901c403070030440410080d8003990150a402d031015105609151007140010220340c11502c107030f403105019005100400c10184407202c107035032003151003002d21020304d0100c2e18641d80c419002418802050044c0040c0600c10408001490f13100c080381b5070365080d500e001516038120141202282d034111002007042c0307015109591858511030a801c070700d0300c00382e00d450712043d5807400001d8102a02c06a25014001940000c43c0b24501d04000072960300c800d4540103140100d6005548882c194040720000555004105141100c2407400000b01c01c030340001d901d0341144140d0000500c1481342010080701030302c080c241e51051296804101100321440541c0614171001c4a50007001c2d504180300500089010700e5000d018211300026503400c0c02d800c10302c0c52003100c9001d8a504040f5040760 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 224185719 1250 224184469 224184481
    0x21f11030a0b0f010903030914061e04171915020705010603080c070b03090c0607150f150603200a0e0411071e0c03121205040b0709080d0905210d0503 66
    0x7400c502100e003860030464407859501c00a00c08d50890040300765028405a101c0c40c02d58805050301c00c0b05e0000d1100158040d403c0020707034040c2d4004d02c6140ca0042c1c03450340b191040280801c2904800c8024102c20440d40c10302c0c0d880b404418000349204200705d90a100140100b80240f007024051482a0074080c0d48000780200c2c1b034a480520f40c4214000d11041080040d600c8000c503060794400020748601e80c41e0349a52421151200101007001d000030b00c0c00c4950408003c607900000000748a040428003541e0700c61508605803001c14014445d085144200b0920082c03c5600810000103140781003400c0c41c02d1100050162081c07104041d4020701c0209419080c42010346c00720f4901044203a010300b01074040d0f03803150290240380c44081c0640c01203941081c0e400c3d01503030245440d142c10b180308014030302c0d0501e0320122400080c0c518a001603400b250100d1066000641300440145075240d09140b586800c00b00b18030380310718500a40350100c00c00e0760042114010440306500c1d0445498540c2c891a0013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 224186969 1250 224185719 224185729
    0xc051606080a09020102031b01020906220515070b0916031505010501020f10020a18030f0605151c0f0c080601080c0603041e0c03021e040e010b01021f11030a0b 70
    0x20b810101440d25004030000142e800208807000b015800d05152469005005e03000d0080c0244413a103030f000200002c8001c00200c21426001d045041c0b0070311290555240c1003444000c1041c900c10421940007082020041070104003d6544215510122488640054000000b03202564030031124880c40600d030065102650084902519081c40107000ca0f15510403816500d00802c680c01040326030000b003e4440611450070060b601c1c1c0d01e0038904822594a1401180002d0b0314030059800e00c1c81d29020504100464800c00844480140704403070918141000b40c1c5d11440d40142142c030464221410f000288103040c80ca402003030f024010708819071401d540345080540c06840f440c41030208000700000140900c5071000000b510100341ca00c841c045185ca41c443d8055900003940c05000e0301441c4c10881e01c118142c110780e0b81c00380c0d4203010b40b01c010400103090b682ca01e0b00f414050782150013400380c20414451038101e480c0b200311012641d91041d18403d01113a20903038100012136110341c0007000c42c1c28a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 224188219 1250 224186969 224186971
    0xf27031b0b1603090203070b0d1401150e0102010b040609060e010602122a07091a03070f090b13050708060a080f0a060c020109020a1403070b0f070807030c05160608 72
    0x10003022006000399a65400c045200c00602000c0518881c00700c20100c94880e521554106a01904890300c281e117603004400280c200007122a1400e04002c1e013588a20314410a480c102c030100c4400b001c49518240d4140c03001d0320142c90143c1150f50301c90001056545070b00a032030041c6108200000c60702c2c2804903000044005030441402d552240c00c0e6601c221100c203040314212000780082206010041c00c54500d1302c002000c0040e03131489980c401080342c1400350310161400402000c02002004a10f00381520781c946481400e144a1b92000204224510b640280d035105400900c51000482d180d1841401c4802c15111480020a2441009002d09003c44010050440c1e0402070900ca140b401215644036820b850003002551a4424140700034000d401141815500400e000d610300e840308000031413a100380c50550f200e40304603840012400140e1040b120b020200c44000d524185003500c80da1138550114034102d04000408142202081d0144118403101c1c20080c010840f151405034001d0030030750 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 224189469 1250 224188219 224188247
    0x50f01050307020c04090c050d1103010b040c090e0c04030812040203100504020904032d051309020a1d06040b03010902030603062202011d040203090319030209010801090f2703 77
    0xc04106000005400188000e000784084501241c8080c0505d0a101032445030742c0aa81c00011400c2e94804000d90703502486000b450550080010300300440810081c0e03428100c0f0240814210301040c03000e00c0b00d0203059030380308800c144614035040e0341c0d80d40c01c11581c0c41000c00c100c50725030030b509210071841c0a0012080c0c401c800b44091040342060340019420a50190000b4180b10700c03c0201c00000140350801407481c0e0f8203a0105805110030031028205030700c1503100c445030304008038011442308081c0c400d441182520341c0d43c40e40c5001032030480b2a4136201a43e1030a9001000b03001c001072261000300114003078150350a0250712400c1c1801854642800030300049c0070001c2032203081c02454034800596005540910704a54a40d00700584a032070203000c403402d1900603000004008200800000a010200f108403400858241c4010b08808034020341c00300600140307a00c0010131646009420103035500da503101c0c0010741c1225003900c0100b19010082d4680310701c4a8041440c05250304030000309a840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 224190719 1250 224189469 224189477
    0x60a2307030f03050604051e0711030a0903210905010516020303041d1602101d0d020f0601080d020601120503190e0a08060c2a030a090f06180b0c190b01050f01 70
    0x2090040300310b4101700d91001c004680300440350000f90274920400d83c0c00b40079000c1805517075440750107840042041005000c04c1c4c5003d10b10b80e00c111580c0340014424088824540d55640c801c0c0c0c142001154282d01c00c2c0c10369003807601003499104c003590b4240300500050400880b80407480b6003143c0c128140700001000004ea0304603101071001c1003600440d50b0300308001c0d804000030358800c02d0754603111b1b150103005481800d44200c00c5080300031500080c0c01c1030003854080884010340c0ea1014401e50340d4100c0000480140c0101004010709000741503040b40c401e00c140141ca04000c4454030080f00a0151007400d0001159203203a034100b42482d000e0900588450006855103282c00301e9204c040b4408c145034150003151042103c07101e44a0704200030007045000050f25a05e0602510090070303d54140a1101c8940f000c80002401c10301940300090425506c521008046203041c00b101150b8000c1c000761540c42c01102071400d040c0303182040c1a800e01e07201d000c0e01310455051205002c050102c081486041c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 224191969 1250 224190719 224190721
    0x10606020c100810080f0d0905010c0c0e0612030d05010303140315090a06170a0303060501020a051e030903060405010f05060108070f030f06081f050a020909011505040b0f0306040e0c060a2307030f0305060405 91
    0xc204332407281703002d0321009002c0c5015a25445e02042c43c0d002080d10325151760101080291810108d0f03003003241224065070f201151481c184027000800d00c801cac0c0d00d03a888500c00707152040043c1072814060781e02200f4501d0001e0751903520482020500b142018a01c42034010070000c10415425120705000380070700f03100403c00e94480355286a510500c91005030100416480f482103c031a04200f1140503c1026086e1101ca0400340340c080c0c06800040c0c0044600307400c01000800c2d95100d040d03228032900d00360b500d840d000b8a00a0040d0001d10303644001c140582d480f10740c08100030000b002500c6d0501c3c071001000301d403694610700407422280302401d42c5413614010060a80342d0743e2440022410f4030420500b000800706c624009487d144500e0b8465055190301082c0d85042e00e4601d00614800c28059400780001404d015034285c8440c0075044c010b0340041d00b480aa00c81a2188860403040054145a038951542041c000c070200d41044004800040d160031121014640c5406202e4021005540034012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 224193219 1250 224191969 224191973
    0xe07051b0105090d1112090d060c080106030b060913091109010803130f0f06121803030b1002060c0d02070201180806040c1205120702040f1508010606020c100810080f0d0905010c 78
    0x111b0003980c40d200340c0907402048126142d40c514105690156201d14104195000c0c0d2402a10390300d0244504c20100380342243c28090ba040410844000040c020000026400c0d01c14100c1e0040409035810381c0c0018503020840c2c015200c03841c145010380a100011601d41d407410300d509056511582205040d441c0c8518100300701459441035405840e41410084501d09554441c10000c015068000400d21804c43d0114185074159022a040200558900c1d100303044805003a039036200250f504003144182004101c0100c1c2042d80601606441490510003201e410014451019540d40000840b9004403041c00300700721310258400018078001e9040300c0c55070401e0300d407248c5408658900a15034a40014640c045580340c0d4090500069680070800103002c1102020003c0800c6020701006513180800c0484c2c4c9030300004034a2000e18000b003201e1115850654111035022000e480b00c60010584880860350318400c5c00f0000d214241d9000604565203d04002400019244c1c080e41c14482d14903c1180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 224194469 1250 224193219 224193223
    0x120a0b041d071401050d1503020f090610030b0a03150e0d1404090903030e060a06060905041e090201030612140606010c2001020f07030302060603071a03010e07051b0105090d11 77
    0x403c5807900d2100c500300701e028030010707103213407080c046e85080c40e610b00f5921800114184550100342d0b4000c0d0f0ba40c0011000003001e020405505441241d4008441070000413018481d0700502510303440500700111913940c07981c400d40550701c1c19054640075611915640c0402c20100b084a44240e030301d2618451000c034040401a05210700d0065072444c5448802d1201854020342041c041425904200c0c0c1e25442c041119000400e1580030307503c00126003100014041c80c05014003c0f200f80c40400d41385031405101a41c00052072000c204038141500c40740d000030558207080c111203203980941d0410300c050044100460600704010100c50600111006820120b56400c03101d444000100c54500300306000070300181c1c0360040c0380c07090080610a0304404410980d001c00c00130701a039804e504aa002c1390f216502d4854400307040400e0303503040401f40010411050341101d01c0342c1184403402c11914081e000e489400d50038000045414242e9164803d01c44110300030450b10b00b0000042c030f404c0c5960324889400a03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 224195719 1250 224194469 224194483
    0x7060203030118140f2211010807021f1a060a050301030c0509190c0e100f090506091008191b1b02060d0b1801090c08010812030402090705120a0b041d 66
    0x210742d001c01703400001c1320400c0ba0132501c42100d010815a0551501d145080004100c00085440c005040e4401140e1450b00000d24a00e220544040426150000d0803d500080000c0076140c8010310600f240140f20340ca580004011032f01c0c1950301d85a60b0742c15424180c64880da66031000f40101036050401061211150105000d071001c40408521301d0400081120b0102c2000b40081d88034081c0b2070070155017608219090040d8619848101d034959440d8100102409101e0455070802c20081c280541c581c406d005456110101c41004205612548010300403a511010141d034001503a070070091005400404299a0341007114400742d800040d5400310301d039030041d4030100b01d038240c4400304004140c0d0341e00303030340e00342099600c0804580350ba40d0b810b83c00180c450700c542280403c05610010410390000b20310603074104410014145107465581c00d02c031507014001c0c00130303041280500c850884c141e0761440c800c0c020220108041238032607254003007000300c171002003002c111501c0e64bc41c2c04080c000c001c03404c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 224196969 1250 224195719 224195731
    0x30f0a0215070f0210050a030b0a080309040c09080a0303020409050906060d0204020f0403060504060207031404031205090a2c10080705090705090a0305011e02030403170907080706020303011814 85
    0xc0368480029143c00d0400d14001c2400a500201039154803d00e5a485806050005c0d0316580900050820b0018400c00c201c21340108011038004201180031420142c20124440c21240b40c10000c03660344030f600d18241030000500700d0019400180802030340c1c00f0360040d41d070004102005440c00e420000700140c4200c0261400230b02540d00480d840c0c10b03000300c445c20740d80210741040c0c00344518079151401c000254881181140402c40014918400d802c030202aa810350b035014008410501c40c005c010ba0b65030b00220440c562000600901150b001000b280b40c508502800c2d80c1007200746c1c2010394061244000406a403030740758410300d01b00700b003031030008a41041302d0090f1560740064440c044129154031903844291740200d003d00001041060541c0001c101c0c2c5507862a1540d0b80c1810704d215000e030303c001e55000e40000c65941d031071140407480428051b04051101c0440380545c0d62460303410b0420341103030f01c20b01c05a00b01000400c10789601400c05d8041b401c0070001081002403a14804808035805004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 224198219 1250 224196969 224197009
    0x607090602061306021614160b18030a081b0d0f02120c240106080f0408040501030e0708070b041403010e0a0f080d0219021c230706020d020405030f0a02 67
    0x1040c00c0c4001035044510349550044411b180f0b07451030070f00604802c220200c1da2180d108480c040c400c4a607a5142482c182d55000900f2441d010b101c180320f080200307110380348a9160241e6200030700018040001003400800040040212042910609007440c0e00c51107003000340016540c00011003580410f03407003440041d0110840d2110354940c12145000c100b05403000c10b0480440301300d102d00d01c150380301d241280c065a031059195a00c100c241452100305070b0740184040b400340420310166010380c000d410a24802000c40c0d07405035565021600d86030070f039030211211040005081c49000000b50f0701d074003248d005030024003000f45146032003031303562207a410054014075884000b1000c1100c10811520040800c0400355141c241c01c000c12040315036440c4c003000c094465510740004013086a41c0d00a011821511195980ca1594051062400050704044664542003001c44009500c80c4042e04c070300310b145d590050716282800149032030316481035203505455018443c810300580da0440ca540040c0100d140d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 224199469 1250 224198219 224198251
    0x501180b1915050c01020703020102130f120212010b090c030907050603092d0106320906011407021f1b11010e040b090405060604060b0a02070308130806090708060709060206 76
    0x9402c56540c062515801138075400003440341e040c581e05402401d454581320452410660703481d44004100f40403486046c07400c551000c00f41001d850000c1c0360104949580c40045a55000c01c0002800690100c80034000200c000c018081401030410003000600416501c0c1c03441e60500126030b0380e071406001d003460708400c21507003045154407581d48130000800e0320700d0007449416103995020000c000c0424040303003100710306444d0f403000700d42d03030b100034180100c0151460989885401c011240c0e040c1c880c0f02d028801744100080310060300c0301400c0c200c075203080300d0358160b00d0060329400a00d207511500048420003403409480010030f103201141c0401740c03c04d00382100200030203004540038240d20742d4115032044002003080244000455203611400d0b0848041081940369512026240600c41507000180c1c8480c405200007200b14004050170440b00040b6101682d913580d0961600004540001160b00700c05410403c01d03d0400810f40c01010038207014080c1070404034002c2d5101c00c002c1540315400e501c44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 224200719 1250 224199469 224199509
    0xc030613030e060c01090b06040c3216021215010603090f14060718150503060a0e0c0a030513030c0210140d0603050708070803071407090501180b19 65
    0x31a0b900c01024190984980401801c61300a0810341800d070381003031341c0900007901440c151141c040300101c0b9480c0e20000141004880f40c040c0d440444011b2018510b000e00c0e002104004042e1480e0303000c0d00c2034600200c0807071040c032220000040c03410051341e01900f40c21104120303414507103055500c0c1d0300c3e0001c2c1612003420070040909007890f0240110200c44c14a190035000840e99900c40e10a0b82c03a030341a61055403c000d000c01c00940719800000000f80c0c0010030311842580290307001280100a51402900c8101131205114199001c40c61070f1000074640481d41d0305805965441002c17030810004d801c43c80c1e24003600800b0b802038001c6c8105818003030320040e01e01403004580303501c58820f12192a030104507041c10003801e00340019a8640701d80e0380300090b0f042e80045c414055a8018024509110b0603035503100c150030480c12400c400f40140c00000c1051003083c81014000c0114501c07060117810001c0040c0b0440b14100301982c024507601c604100034000d00c0401c00c2c100e6014000441502c0106 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 224201969 1250 224200719 224200727
    0x30601050412050a021801030318151d030d0512370207140d0e0307180203090a1b18020705211312050105011e060e010905030604030908010605030c03061303 69
    0x100b80029031085091ba20911501c00401e2058161f0f07100c4e403140340004044c405030b06e200d01d05a10809403004d28416047d170030948030700c484444038107208103500128089480064100385080400000051300401c03841c1c0c1d07244c5481c1150780c1004079941070604c02401e04840d400301c03012160414490300c1c2c43c09001c002002255045a009075003002c4081000001101d042d0303100d40c092540c6100080d02200c1621952130041440c8048a00500000c074000366540c400c80040d4000030100045405040d42c410b010035220010315600301014858130203c00c0c2400c410400504106004072135040c4144540c00015100003074800181c000302010112100c011041c001081c4203603020b035540c4048612000a100b0020810b80802034072a000a2100b0380e22800c16403820711207070301006c51804620701d040200600a500c00f802c034000600d0149040e07501c402c00300f0320380b0784159001c80004035030301c0c810001640f0030311035180609130850160440b109a0710001c4e5488901920400702d003200e00303603504205801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 224203219 1250 224201969 224201983
    0x403080f041d09060c130306091a100501030c0c11130f020408010b030d1b150f021605211b0102070203070e0a140106051c060503060108070306060b03060105041205 72
    0x80104104400765103040e01d18840142500ea0076004c0c41071401040e200c42280e82603074108028030741907149070751460725118082e04140c41b05075a4141c1e028102050042c4456245201c1c01030b40c440008040d2402c4001021214804080703004c00c0301d100e0351400054002e0410220104045804120312829042d00d8401400b003040c040c40c8461000500007480d14041d0880c1c5840c54040381034401c0c4030000202920000412481c44080a044051103030020720070908050301e10003c60b40002e070100b404c0f04110100ea02c200100c055155001c80480100f150800c0020389410510b254040b00417030300142a4050b01071032010b032000f4090003180b08200350003541a142425001411941c0c01a40e52890652a05068404125160030725020b00340c040c101c5c03401c26040312150381c0c0d480d02d40340603004402c40781510501c2c11007000d84c4414000410740c0c2c0400106001c0c103401703030250120030319501e4448111030039076201d4410b0440500411400745e8010050f1002c40d00e614040c1c0c101d401c55031a085040507a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 224204469 1250 224203219 224203229
    0xf040e0703060f060e0103050c0310030311033622241214010c090605070318030c06020f011401060c05071a090406092d0e03030901050f1b0403080f04 66
    0x9840c01c00260386540103d100c0017888080e2800c11490b11509d07016403c42c0700407150240080707440641000000d20a84001c081c00d02e46000703136070404400003c580e07140b480203560388100d400140301402c041c401c21000703030b402e41500b1156030304540c1c1410315a58201109104000101d940c58842c000c5110150100c140003107135140001903143d49407140c50200380181030041d0b88401083d008007020820500c80c00009062648403040114540442280e440d4412002203081000400c0061307002c4d8000c0d608080039501c0380c1d4140d0a070904210000380b4207401d440b041650340e07042c480100400003004403164150b509518200801a4003800c00b81c1c68201e455102019540203c54054000e4140301d000d4030a10204032010310000f950b401400c02900c8280e00b0842c0042b0301800c4031889129082521007504170b81c03c20200d101052021254255041210580c0070f0b80d441d00e003002002e615a03075080ba03001000610403864550030402c0c1403610300403800014040d110015814204003401c5050f103000300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 224205719 1250 224204469 224204489
    0x2030a06060f05040305060103060914010513062301150507080a0201050105010e010903020f0d140a0809040b010f05030403050f1303060c02150c0f130803030c040303080105060f040e070306 83
    0x81001449800240158070540c40040e5060b0100590240700d18221000c03039400400405103039085407515002040003c800300e8034080405803c080c504030070300925201c0c8540440540001070a81060700549000251904003003c40400c5114000c0680c48494190b81032400300c1c840a80307414100360b40c98882c0036409003031200003150008003e41d0540085046e10000e90314084294007050054a43c0441400001d40c000070140040ca000d080c40304d800d10866004464500c10b00d000803046909040401c00d041c1d0b0446400616402181018019282031880078078060103801c00308400100640800340c00103080110000319075061a1b40e40e0141c90003404400c101e2000705a0328906040203203070a010303640242c0100000c42c0358550024501a101e20600e1608610f4003d001018900075030040910480900b5400300104000b54204090b5105281e2a10507da43c4e0b0f0a60501034510001644501c1c03180700f00300040f5034420f40c2d40040d102141d010404c0e4aa45403a0300d2001d601034003154000e11514 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 224206969 1250 224205719 224205721
    0xc121b0f06010807050d031707090e0703061d0c0306011103130608090d090515090307030c17150103050a0605182506020c0307060c051006140109080f060402040513060203 75
    0x103480108030141228000380440344020740c2d410501c00b10030308a14018022418259455a2481811721701c01d9101e030301c61503d81e900a413142d40c002001c8a083d03803841c1c000f03544d0f41c00501903000c1811104081012440d4901814a4402c91000c50352000402d5541000510a0002c000744003c0098403440c0400c1855540b00c2911807400510000003102c0003181d901c103416507c020540101d0840090b110003074803d00b00e80d110503442d00c030315922072002190540700e50100000840d1000f41c450001c0c203003201e184002043c04a100c2482c1180300e9104802140c868801000082c000203a004100d82e40718078041003a540792814491000010041601c450161000c505005644008400ca4040728082402c00d03598880700100d80c0d40d030555400b181c165005450500410740281d0350301c1d80d0980701310300b101c94180c01100300109485056000391080301c4104035040c2c1d15070704218220050809140101564802c6011056844c1d1001d44040d000710345d00d0700802d00d541042c402d01e0076115000b04c015943d0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 224208219 1250 224206969 224206993
    0x90c05041a090f01030e07050105030c0c07080a1b0e0114130c030504050f01200714030708040501030606210903120c0509090601050a0f0305150a030312060b0c121b 72
    0x95001100583c480c0d01c0000c5060b2456000c6c2c4500c40c0744111000080115a003008010360701c40e4030150880c40180024403004008100801c0600050400c901c054a04058985070220341d405d1719081c0607140c02c158820901000402e500f425044500c484900f600e16040b0300082902201c8801891110a05003d000560550182c000c540107902c103030111210880c3c2440d9550803100005650b00a0000d03280512489160001c098035440d4090000028900107280541d403035070340b0042c81111903c002241c10805581c042c0b040d08010201418014142407034440d800864102100d8800c103890398458070300013814070070403005541010b442c1c81000300c944a403501406c02d03000343d41c0b2144100010b400007821540f0800a070355030a021900e03040c1e03440300c4400c03083c2c0c06001d00902001a090220100345459550a46107100650003074580d11007090174180309009551007034100f12008001080302c0c0c00041c000081d455540d60301c16120315103030b09041c60000d100e038a03a09580d01d02482085080780d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 224209469 1250 224208219 224208269
    0x2030403120212040308060f060702090901020912070905090d0804031107031e14030c060412022d1515010c031403090d080f060307060309140609060613090507090c0504 74
    0x405640130303840d07a1b65030b65100c0c42040341d0180045150354110009000030001400e019081070b030410f06010002d414042400c1c0802c41214040c480c42a45074029481000f000d14144206500500040013801741e24040e548054002100030b00000e0800c000300d08180440700084c0503100c080c5134414091119001c415001746c081105004080e03403107071030080ca2018803013000001c4460444900019081c0b81d81d035500d81403c00c1e041c2185103010f40c0a08440c0014403110014150100c144414101c00b200400b40c0c1040c0c0f0b4590440c070520182c100d02410720020813070a05540480d12400d10700840e0300c1c200742c54200c3e41a1050340301d403d450080072040c40321404000c04c5002d01c2c2d0032280e5480c0256514a4442c2c0d0b5600010b603403142d05608a02c4040c4000c6100e0b8006107680f034041e440c01550500c421003c98501103040b82e000115800890a020300d510307114030b01c0526040c500806014800c00c0761601515004070b4400e143c820f590311050540c955014005480c01010054414502494140c21981d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 224210719 1250 224209469 224209471
    0xe2205010b090a08010207120e03150103030521060d0602030a11070c03050114040312051305060a1d0a0302070b2503030b01020c120a02040c1209210c0b0a02030403120212 75
    0x10344643c22200000c542c052051096810f95600560ba8418068100c002990f910014551250301400b800d4003c000100000c0301c00c42c0294800d580791079590480462000c0700c256121007002c4451020400c1c400c81d540ca9548070344040750408001a030b60703150380d10700d0b400170281d4480c004032402c404910207081c0000c0d40c40100480c3e00400007440003515400e0031480110041318010045100c48140c0e010240142d0301c0290300140c803025240c103480d00754076518035245c002c550102c4600c0c0c8444404010756170b010a6880720b4210040140341c040225a00603480340305074000c40c8002c510100c3d1580850b22046200701d5a8240412401c0b850312441c00c004014000b018401070151180405186481c11700705c6640d18a610f42e10041c00d075216050742001b002d0f00f8401006010021541503005009105104041c00d180c85108000a40000c0d00c1c143e620011040102c074040c0b20b40402104042090a80c01c164088104030005949903620b260a47c0c0f100d0454802814552000c00d4200410f0041c03d070b41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 224211969 1250 224210719 224210737
    0x1203020a0b0c030f01060c05152d0106020309040b0f060403080717190305090c0a080a020f090606090904051c030b040b0a0b0a0c030905040c020a140c010e2205010b 72
    0x20301103554030205076102c1c80c4010390700181d030301c05242c004000031441882c01071b50540c41001501c1421500d0380740e4850031902900c41c800d00d030303900d4401444600c0c40d03400d0003041120f20404001e050340c540840a0349a005540045004d10780b02d0700c000c100d5640f5103104c0c603007007075000380000d480340c1d16414a032034250400ca9084440e0070707400750b2082060100400b60740000c850001210003880b9070103000c5014005c0500306008920070010450410303618191101d0180c05190300a1250300f14074010804440c4080d08524081c50104062007140d40380c6004984022000313507100c01d003e84a0740792941c41d15202c07221455811201d0f0901c52451130385030b00600d176000c0040b00c0511661039180e0401011b000b60344100c684640d0b0030056034132414092900305000d98000e080500c55581d4500118003a1081d816030640107030000c414032401c02000a00064280000300000c004460100c8006460611480b0015200b090301d001c41858441145c40303e2159108448001d00c003950b501e070420f0505801440b0a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 224213219 1250 224211969 224211983
    0x406090507090915060f180303050a0e0a0b030a0207020102120d0b040b0315072106080a0506070810093305090109090b01050405040c2315040506030a050901061203020a 74
    0x4002048038007406080760f00c02c41104e42c07841a40c540241943c4020100d80c0031002e20117002d0042903c0d019000c105401140030b80c9940361364581050004094080b090b00d064414840d408080c441c04403c0b50030703a41d00c14a854001071740e503191400180c2c5480d1001c40c48028001c00001e074000001c4180e080080038110075103081c07206804a008264491001c18010315481d4641000540380c01c5c46000307042c1c0703684625018400c210141b02c0300541a40da01d50020400e69022500081c100a4101f1a06501110034500a9450b0508104010b00f0b01210311454091584507901820801c2044070382c02e01c90341a852100f000d1260340000c0350bc185410b480303030324480c40d459000003803118483d02a041106a0018403507102c0c0c1c1c00c0208001c01481c01030016034803028680c4000c2a009180122040d151070121011200c031001c05040191215881d41124540c0001344010002900c80d43c080e85d800c07030450305000ca91641c441d40c00720300412407a4000000301000b40c180030141178002c03500011160103400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 224214469 1250 224213219 224213237
    0xa0c05090a06030201210b0a0306050f060105190809100203010e10060e030309090c070c0b0c070914060d020d0605190f0507090e07090801020a0e1305010513020708090406090507 78
    0xa240700071074405200182c0800c518500107524006092003414940c0d001150001d001d00040c0003080c04250250800c84180c3d80e9a814170503c034050348200c070b50005003445c00c40c2c074200e1510000004190405140300c01c1c0106840420120740c0144480659000400421501c0e5a55100c0415500390140c80100c0014200e5170040350640c4180b061840602d000f90086141584007414803080110060010003c04003e0180800182040e09480000c0120455554558181108003403c0044550095001900d408407204141c1804088164004021100e5003541c0e06540040303501900707a44801000300b8a00780400212a41e090f0f001040c1445074041040441502448101114001c4d01c51a010520b1148108160043c0410b2264407889510304070755039903035031030350300c0d0a80e007000c03005d5008188000800c4103541400403542015440d05a801e0080394941400700300c1c0440207584420700550001500c00034000e0490458040e218081c00030004243d940002c100105800e65003080002ea0300c0b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 224215719 1250 224214469 224214481
    0x306031110094101021c0207030605090f101a01080405120a050f0d090b0c031005090703090b10090b090f0735070210020c03160507080a0c0509 63
    0x844407481440944403426040e00305407410310200907004001d002c035094001c1e424486074552036000040f0f00a03210380c1d80000300340400a41006030613031641824901605004010f80d80c00500d90701220f8011302e000486803603217501542000400212040e80c1d00c0b40c88808160340300d007948009038003071005202c5280104800c004480d0000103490152a035030004c4011000000c40340010a184100c40c20881c4c940110b075a0340078115000039040d29407040c2e82c0d4141000340811070781d00c568440282020300703107107203000745017005105200c2c05058050002500001d03e8030f8003030350060018a0704840c20080c140f4101c0401c64260000c0d015140e030a506080400b805402e02e0b0034410700070340180510056947d980d41003211030724400103045408100c61520099000380090070b0f01071451075080908030a10b8400c4000e03143c0070901541c1c4001d04d20401181c0c480d03410110035520003003c401521b10000307102d410194542580345d000b044c054002c40c1201810040030704c4140d41141d030b0503a402036150350740c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 224216969 1250 224215719 224215729
    0x30c110307030201270e0405060402011202120703090c1a0c1e0a0807060906050412030c09051e150417070b070b1504140c071b031205030c040b070303060311 69
    0x2d200003400b25112030308034000d5600441c40c80e2960304a051668094a81d01c5800b143c0150741514290340a41040c01800150f5134841d10501c0803203042c401c00e520b010301d400da5080700030f14000d01c3c3d8001c0503900c0244108206200c140d4000400381e5403100360b4105810000301016074000900d000d040d00c42d40351580001510070091803039001241010b08070200c400c1d183c41c81c041c1d100000440b003032982d803107000000803c944900c9020b9070162100394040c5805c002c0103000c4443d5041a2024044c104070104030b03d41e15420310380c02d100708680b0030050102e45500450750003003884880c0341e15941d0101c1e021507069400c0d4a03007084400000c1c1150070035540c502c40c46a0074490340f04083c00417000e4000062607c0510321080d903015801500005d41d15040044000b420718007600c161100207000551a01401305840d5480c0f030302806944400325461866541e15005019810b400d002d1043c08030024045550305815200208004000d45a450714035240040081c403003408100e4201c91280c104070b0041c00c00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 224218219 1250 224216969 224216983
    0x30d02010608190b010b030709090c030606031401030c140409060504030e01020d0f0e0f180a020405180f01050d150c0203040504060e06010e130f02041707060206090c060307030e0a030c1103 83
    0x141481e450b420100039146c1584010b25880c28480c140ea800980d031440b0384900c546000003036800061803414000000d09403205d03204c01d40c080c41c02000060000c01c808894000c100c0700341c5641440c41d8501c0c0008070740500080000509010700c0c1108110a01d074100c458803400160136400d40e011010460015110750303825850181c0054044820041c43d410861f0340c01c522000000c082e00071044c1340400e90024903004036022070301d11f600400c04101505000e41c90400500914124141510f0204180f03240c3c0141407160301e200d04403001a14050101820f0b1510700d58001072000c2c040703050f6588000c3d55036801440340b90f01031454004002038003480300703d03100d00400059407100020b00042e0104808550020030503002e540c0d0300c1075401d19420180c801040202031802106583c810513039016402d081560f8082c2c0300355084041000388648d40801d04500a94045801c640c880c2c69044048004ac00818031310842c4d4401e0303000c102c06042e00440744080180c4624005079251074160207141e01c0d00e00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 224219469 1250 224218219 224218223
    0x30c010c080316120c0f0311040602150c04050d0b1b090d02010c05030408100e011b050a0c1a010305060f071d0603040501180c170705010c0809040b030d0201060819 72
    0x41880458061106500702000740382c003600d1302d510400e030700050480803104104583ca02150b1010710f90300c010368040c05500d40300460700c41d00c141081d2400101a403101144850034a1000c10704000400e01245001070380c02411019040d8410300405181a01300f0f03804c00d03074602004201ca2042070034078244490454140358009803062460400a90040d94101000b0b01300322010b00040c0004903401d03808012840d5070050940d001b145803072011030b605003150f4000c2d1141e40e0403d005001c148986420100f110741603100e914204060240034101620b140314003400070240340e514032000006001c0c0004403180980b295006134215a00c49070010b8540321a5180b0001c101940700600c0c14007032412101465119000e03c00100340b40d1405110210074840c440021100078070802c070240000581c0e02e100640401d44800241611401e28001a0580200c8100104003910001f400c003c55111307500408441031029086403011651500064082c16450295880520640c07400e002c039196441d09007281701e0303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 224220719 1250 224219469 224219483
    0xa050a1208131e0203150a090b09160b0d02070c2705010602070501050f040f03050303090708010c12020702030a0c0b031503012703020a05070608040c0e10050909210405030c010c 78
    0x42c549001011500314031000a0340e040c003031103021141200e4000c4006c0c2c41030003080310005a03441240340100403040d026103480455130000c444010040d03403e00c00142914480004a41c46044504e41d000c068441c0c604014071481080400250007501c0d07441c4815840700040081c03840800c2c43c100034040359824411080140e004c07d00800031940514000d068409904281618007602c4d100581c4045403036901c100c841da4400410440c020f10148402c201414803c0024008000c0000009145401d050100d05005031300044420071544c0c200085822503030f2100d084c031096560b980c400c503e250000c0720124901030414040d0b41c082d01d41840761008035441c02c42d00c081d009090144801c403d41141c2c41c12030951284407020004201304202402c0108070036a80c60401e4905031070300130150380c4207038420f81480240c9814401107461103680c00f025100280d41481265031790311102c030301d40558004000081e141541c54810b00c0070301c42d4010000daa10903001c17a29421211001110200c0302200d019140d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 224221969 1250 224220719 224220743
    0x2030a081f03150e01021209011508070e130501180201020c0406060504030b040204062402070501090602060a1e09061505100903060e01060e07080901050601140a110a050a120813 78
    0x20b0501940800c91071943d503070006000450031506400c903800800e101c400303c10410700b040700102c0309014072050900b2291314503038640d10300703200c290703569a090107002c1c1a0540000000c80f90300303000500d103c28940100c024041010701300759016404018503030603401402034101d450494203150142c102250746a035111351410740342d52034074445a000508126800b680f2800f000403c1c9071114400f641c4800300005540b04003040b05406071a08081d640f28506200c01451304100e026000300b0566401030b08540003103145030043c1c4580740e503644c40310020074030716282c114441d00f0301001351301c003003459032003905036030500c41d00e880c100b11514104220000000715062070030300003c0e1a42d0401c2e031000d42440300104240362214200e42d244902100c00c0f400040c0380c40d0801035107580034010250080340a080501130032010099152840c0700c1c1c01c07107401c103001c180c4046118070b00d400c204170f50240750040e0a5410b01451442d0031809020342001210020340c9440c0480c00d0443c081c00a00540e075801502e16002d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 224223219 1250 224221969 224221973
    0x3010b04090504050106030b0c1209060402060d0506011e050a0207092d02090a090b04050a090b0606070f0b04081b060c27040e060105040c081501110a0c0602030a081f03 74
    0x282c00b004004660075525000300100088a03050402d00801d03e0080480d100d1070109155404c0d54402041c0100b10307448881880f001d41c4540d41156840b09000c00045001d17030702e18005880340b160b4901022503c10014401040940d4031034003800607203009509841c09181da541081c0e0503034113580c10701d880c0e00c00322101030100c0c5111130380c40140300c41d0703220005410501240e000854010040c0c3c030504d011501c0d50489040c919040c8681e0703074040c6400008201d04001900c500d2407140b07000346001e028a05c00131b6804144200280754501c3c0d5544a480000c8601e445c0c0b400c049540c1040c800c0d00032550912115940c010004289907106203c0100b003623080c2400300b00609002c400d04002248041480f412a80468489010307501c060010440145400e516003001d220441d40c0c0c003a85502041420030500c01d03a114034955041c6801024a4084c1035842040703101414a000340600500c005c0c0128070001e103080e0040003030280d00c2d0540d00d4550346a0b6071018240c049250305c1030200b00c16180034a080c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 224224469 1250 224223219 224223221
    0xc0b01060c150e07180c17100302030a050a020a0501170a0203360d020c0f0d030207050904051b06040b0d050901060b04080714040209030d03090317011e0b03010b0409 73
    0x4a024002c0c60140d0341c01c4201e6094208640b00e12044146a4000300c03414010002d0302e007403080403220f411208001d61001e400300107000018402e1a9112481c00c540030540701c3c00b5260408000c0c0d60000d0586041000614140e90740700c2000d04128040c0e0041c000004c1c96601622040c145401185012a219643c0c4c51071180258001802c2840c106030030144600081010b14030241e60b0208400340107440d0040c0202c041c40c020102e513014003194010a000c42d40e9894408074501508010b0390107103c22a028503099050145a82207150050000000c1105010300007404000c003240303510302c808460b0b007803d0900045200d98001c040358044100403074005000d041e0302040d0302881c0c4c20300005680b030300c42044c0c1c0425032050307200305d60380d921400c000c0c41121080c4400c180d80110444045250481c004046515888004503440c113044d0384862800501d4010300c441d40d82d40062120f0085a50b03101c40358002080091115205006400704c0e0200301044081c007164142d0790840b440e41e08283c80d10200c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 224225719 1250 224224469 224224487
    0x3071205061f02060708010e1005191a03040b010902040b071103071a0a0806030303060f060304051011030403020105090a0302100b0112230a0605010807030c11060109020301080d0c0b0106 82
    0x182c1100002d50201ca451201030814040115981e01a000f9800c0414000f42809010303000b012800c0c0140060100111907040d05d4000c540007a540582b4524800c43e400c1b0f504042d95000403403850303101e081c41b07181100c0c100080d4803c40c4601a545040d980310200c17102240524090404408020041d40d800300314000d100e0b203410180101250425601c0300b80c1d00101c0b80501680d102c200e10041a0b500a1030342000d030455000324158001e43c11403504000180d0a072480290490241e0030000c003140610205003c22084405a681d05029251103d032483e0525481100c00381c0040d460305001c0f494407100842c00d11007007501640246003080c60703d480c0b030000f0b00064100030305020100c0b5480050200034060380d0403c0400f1480d020075000e000c02010b1a032840240200b0310340b46030407410301c0705a03042000d040d0488000c0c44c0c0002c980384249000d6414560f201b4444850b03104000000495400710f8005506980d00d010542d03103402280402643e102008200050100540a0042c001184108540703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 224226969 1250 224225719 224225731
    0x3100806160e0f030f0f010b0306060607030c0503250204141b0f04051c110102030f0403030e040603140606010e0411030c09030c0d120f2c03010605030d0504170303071205 75
    0x8480902c001000092405c81d100c0c84507511608000100c001c1004207124501882030300764040c08a034608036001404034825240002c0c284100b5000030000e20508009a896540c503550348507049040120365016800348004040388203a00700701c58040d00c0707007200622a000380701d010410400e101002c0d01a60054004250303401700402d05020004440c0d981c142007c0c1a81d038041850403060000d13050a00c1103880720302e042c134103550007088403480034a010411070381100e42620348062122003442c00031b40901041d62028243c00046080341c0c103030a2010800706d01541090300c2c0e0b12074400343c040030f0006031000d40c8681040901c0a0002416580040d8001c3c60741c140004d00ba0b07100c2e4445000000c01074004640282c0e0b40f04c40c5c20f1805c904650b084810313500d40388140c2c203044c6001319894048144803641e00030401199041401440c0395130b14250000405458001c0c1662094000c0134070042031a00f00c0d200d03240c8800100c2c0851002c400002c8200c0e07003d6100e6540c2d000e0209019500b0001030300001d099 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 224228219 1250 224226969 224226979
    0x18061902090a0b0301090609060b16060b09070503070314070905010c05101113080c06090f0a080601090b130204080601120312020301030308040b0f0f0610032003100806160e 76
    0x244201e40d5070030002ca00644400ca8816480c2d50400d007000e402c81f0602d41052044601c0c040f42030000400342c60603180c0140c104d504480300d00307c492500d000903140b102a650742044160301030010041d04900910b102e051030390303800c1086a09010281c4000041565040c003c900e11040504c81d5511a1214602c10341c0140300300c51100d000d141400702158130b401002062410041a0030404842407452100202076090050101c60640c00009003d481242c41c4103215024804000070f480d1200e100c89401455580150340b01c96950b0340b09400a000344500c06845107405001c210340c80100d51082d1015202c940004025036824a18009084812007809a0502c00c0032040d01e200e81120340010b502a61103540e81030810b06051a16020b0004054400b02e40f0400440400c41f4441d400989154040c604503840c03100d01002000940c01800a070746400c6840405c904c080d44803100000c000c500070f101d007003020441d0540e034081150711074100756461000c2c00d19040c0c2d6a8071952041c0b0420b4040400248 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 224229469 1250 224228219 224228227
    0x50405060c01020c0703030e10020c09060909010b0d08030603070f0e010311150415031103130303050c090915090c0304120c021c03080406110c0a060f0912110618061902 74
    0x484c51a101c1c0310390048001544c2a82031040909141181c0100203810340024511603004400051075000024822801000480c000903030300d84003500a140010300141a00595044604000900780d104444843c0684104440020408648541d180407140c0040c4107103600d90a40c0d039019142050032008035403140c0c030103034480107c08891000b00001c2035080b0145003c64103a45e000307070550700c420510040c070f09014400c201200608401c0c9112850789494001860395410340c802e020740c05032148407a0005218001c0080c00b20951681080300c9200f11400c44c03150b0764214900d4150320080300d00905c0c10940100d4244031a0080031541c021a10040401d000c04410004a44d6130784400300d0150000b803960810303c01404403e200320a041e05108001c0751500d02c40e046401d0340c0d203407030200040540c2d9490030101458821903102441d0290b2103011502081200c9074006c00d60513100b840c0010343d0007040b01080c3c40880c0000c41c103600c0840782014003601d035a45d0a070381d02c2d000c041d08100704103207400308 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 224230719 1250 224229469 224229487
    0x19060c02090a11031303030f020a020d0c05030409060b040305010b090c04140d080a020607030b010504080d0e0a080f150603061605071703090a05100203100302120703060f050601020606010906050405060c0102 91
    0x20f144540140320310011700d20510300f00113040c0c61202c04080280da104200341c10866601003241007a44959040581070305810746419881c510441d40040001072400d040030404c00b480d08001c0085900440003031007100d40ca10b0800042d030034191054030400d48100010003400802882140080038010302d205e00ea018952541d0403980c4c002180a00141c100d82c0400c2880c50300b51150081142d02031814a00705810540d10b150b07034481c00e01105084c8141902103c111360344040d4608050820b5a00380c0b0510032402c000706030341d017a460311004112200ca400007809401c0c00034031203221341070314849140c5209100c4415035080d0300c80300054640c840c0314007801c0c108428400003907004500703620041c06600c1c5142007190902004210680c40b590041060160f800304c0210810296901100d000c80c0f04005408100e19180050348020700d944e0804d132440e08110350551003140318038020317001d480d400c3d5900e00c011038450321140903c01c00f04000b0310003400300d41422006000001c81e04000189040b03508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 224231969 1250 224230719 224230751
    0x2090916030216030e1e1e0604050607080712030509060c0c15010f08160806010611100905010b040b090f040b0c0909040c0501090f08030d1806051519060c02090a 71
    0x480f009a000c68802c5409a1450030040c0083c0e5501d0503125200255002d0b0200050700ca003100c04040c081000810b5031201d0b00c2d541c04049a0003428010419981d5020600e031115650700202400c0d00c100700d0f01c2d2802540d180c024040c0c43d201d000031001034002d55482c1c50300301802d1303045030051426070b00c07484120300920500c4600c0035028000d0150812034a03807500e1909450180d40c409a500384e4036103200100700010000801d0340c15140d441c1000443c03404001c60b12468440d2040c400002e103401c011000c4103205040d40040c0d02c1c100192414030100e4803400038807203035000a580c00800c6001101c0000e0100d80c82c010000c1d0004030844810f032030f11034408006070744038100b6102501d410701e038120208941d41c1c0007030329040100000c421131800245000c4c412900c9020b0b6130986442e4607101c0150794a0201114403162585602c018104128200304c03041515029511032018050850b07103a1f100028144141410215189030b07543c06180201030303091180400d4090950390489072201418030000c506 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 224233219 1250 224231969 224232007
    0x702090705070818030f0c011205090c03030a090503060606070f06050c0c070b0306040e0606100c03051e0310210305090a0f06050304210e0d050709020d060e010801020909160302 78
    0x344c034614043c42000f000806051840c54440d040071980420f0315602e00d66007105511021461000001a4035a6400401c5003000410700c0f000d60705010006024041e143c1003440740c01925400e90445240d90303908801d100c100e100c1c0700d0020301280421081003000801035000036a001400d854940d0805017a40400d43c90b01301c03a5004925004404020003016003014410141e04018010040806090900114200000c282c4001d8204140c030746150003414041c804590b51420380002450201074461074800d80c5170410794020000888407080010b420201ca0038050246610001d80c4002400c48d43d01a201503000b01080c90304114048400621080b080d00000002e003201d8442560b02d1405140c54084000801c6584c0f5031201c848202194486c3d101e0007032840b1607016201a4006521418610f10701100c42e44000c070072500001300e02901e031a0603007244007220140841d09480c0c1c3d807100c8010b801d07802141d01c4150070007040400255816010140040c00071803504006103040c2d419001c1d0703144085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 224234469 1250 224233219 224233237
    0x90507060e040f0b0d02011b15050103030e0d080a0513050307060314010e0405060609090109050f0d0f021504020d150515090705120a020c240103060c0c0807020907050708 75
    0x4409101007a00e0419010740c95140340c60210401901c0341c1c00c80042c1401d48840d030003074100000c0f40c06000e4880c1c00c0010021003650003015441c52680d6036001d1001501090000301d00140030040c12094074100034900fa03c3c040d40c07100c58070741040d200e2882103800380c004080311132181c41800000147c64401380942030203080156030100300c3d0351003608070300f1114034181d01241c40c001c018401c01001c2400410711940002c1c08481c41d40c1c044e111095010f01600f003440c00540755004812648120000000c5c0c001d0540c03110307848514041041a00503600c6041c452070b480008820100005c0041c0f83c2103080d0007404d4414000c00c60b000903008071340c0c412100204c0d001c4034a02c25040d00000c0610740f242c03051f980110740703181c03240c5002c03010000450500d42c0030f0b1000d10707a15008680c40025000c148006080c0b1001e0071448060500c5540c00018001400e01c4250b601600e0f0500500e4803510031008500c1d05034000d0599480c0510f80e509211714040e00038009030400509100c6080094030920080a000c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 224235719 1250 224234469 224234477
    0x10201020711120c2106010807030f06021b06090114060102010902030a1203090b0f1b09010c020d0c1208030a050f04020603010b1c0e1b0301050730020c03030103062f0a020109050706 80
    0x645000215181c05011b8008c034409600c0700000f0400908000742200140342e1115001d40c4a0142c0310360401340900407224003525015100801801d0312056001031030b650b10f15929001291a01d90059080300c51150010b5090b422070280803011450300c0109508225041c500001c0100d940e032183c1c00100d005656040172013601000b403040b0010026040340d86000c030f064801d4601654072001a00380703400d8150081c00341e407008031000e06000a6010340c000422001c05841c0d069601803404480742d900845030f2021b402e10300070215159211404040307208560242a00e480c44c3d0903c000640c06802828075400818854a0454900e0909014001ea00c0c0b800000425600c40d000015251444160800074026072505003008030030b40e4404410203141001614050381c601990344129101c2da1010f4100d003c80c0d00005c0c0c0b40a100c40c000000318122402040100110180c00e2100700365030300c00e00c100751f03245601400005c1c1c144209000412100146000000b041909075861604000003030384020081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 224236969 1250 224235719 224235769
    0x182004030f0b010504050709120201020705060d060504050a050721020c070b0301031a19020f090a03140609030304020117060301201306051c020901050d1811010201020711120c 77
    0x706140076818090001101c5c1801035142c016001081456184200b80b43c134480c039082c0701c0c00d5900902c00e8901410000e07100e03944d88d007480003161300034241c0c9206060050780b40200260164505200301401180c550380c42180420024030324580403144800c0039004144d08000f280c901c4142008010b00409410031820340f02d41c5503040038811707100c400d40035400903018a0f003001242c2070317000180758990310810350040e2103408500000c00c0d0703405610a15a040f608600010060011000302c1c0d00c0d04c0d520301c0c0d0881c0d0740c69403004480c070748030301094400a0106940d401b800010b140d07880c000c5540031002600004400342c08810040c0d19495031011041c00410006041d004002860010400b420007403e0840c030b003000c002100a20440c101b0f040d618a1a800f140c8080184c2c490011144140c036445c105000034208058034100e1400c03203071800c4410b104001000e049650040c000c0d07500c02a005402000a403420b0020321104803c0d003001109940903029204030561f98140c000103250f44041145920 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 224238219 1250 224236969 224236973
    0x70506130b0705071403030909062103040803070c1203020607031e05040f0303060f0b030a020705010b090a14160512100b0f040306050f010e0c1c02070302010e010b010504182004030f 80
    0x1d0100c6240140240c102300b1001c0c115444840c05c45402030010b860600b501c03140c00990240c2c160840b030100c0081d020009000514400010140031414080c04031f41c02030a070340e12030a41411a0414000b009a004200040c412901a03440001c4040a26205808c04108590301000b19003045030100d0341c1340030440d2084145503161003680050041010040703c0c0b00e00381100368410303000080902c510305800007240710404c0000e4000c034810314800f030000801401c1002811014000f1041c000c0c180030005400918995290700e5141880c401580b0b41503e07181090509a1080c84028403a000200d030340c1c00009841d0040030010083d110380c2007082a02d880c1580303443c1064400c0584000d40c035075407000050108080445600703800189024240341d030340040201c00313901c0c0101181c2505d80b03148040b2b4400c05064040d00302d665501c14400080209076071060054456006500880710b03445580402d141d0743c1400c680c0288440004803400650025020321604015440b50b0011140509400b041c241 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 224239469 1250 224238219 224238239
    0x3150f0c1c0501090f0f0c020703060f240e09010b01120e07150c050c040603051905010e060f0103051501150c080403020a0801020a090602030c0a02010c020d020a09052205070506130b070507 83
    0x106d2401084184200100c1e114020368403d80c030702024042d540d45003828580b0780c006a1126644030a2060100b6850300c100340f030b04440000341e00c2800801c480c800002481408184034400d2060307416115000f2290a000c003140c001c00c85a096001b10f8400c840c004103400c0c2510b02c10a807501c03225521481103042a241c141e0800c00e070f4502c490b00850070000103000003440400e840c0601c0400300700d128503441603401c1c46405000f440c0341000d002d02400081c0020400c0089840d41668000c0d000c0300c4588540c8803008503038280074400d0050000692007901c01c102d1140b000514518060500c1c1400c282d141d400080e0500c001c3c3c1c2c040c5200703030350009020340c00780d4110382d240c00180a58005182400882401c098456040a03002410044400091800c40d51040c801c9900181c02030414001c490311000d40000900c8180c0310101c800701e081d0b07244100965600601211940d000c0042c000552030107082c4145900f150444100300043c0783c4004c184020988040d1800e5402500200501803a10350211 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 224240719 1250 224239469 224239481
    0xc07030c14010b15040b03010308210a09031b02150a050f030c0d050c040308160602040801050f0103020306100602150702010219030906050a090f0b060111030406020c03150f0c1c0501090f 82
    0x10004c006000412040c4004426681102d40040312996142c1070900301e41c41900118150310a401810320500101c10f180e54400d25010f80710b80c0f43c44100310181109203a4900780b081000354807003401115207100402c150b024003550310781c900f040f6050401c0810f501a40d07410444d04044040300100e880c40050070355000d042e030001c40030000c0919140c159243c0d82c0c05403190003007000c42c40e0140c21418040000c0307a4103c030000c0202000030885801c008861000e461400e02c42684a0700c566404149043c146907000e4040b950650010003440d044505403241000004003d80305556007400401d00510585450282d14101c0e540c00286007000380c074006045400143c80500e802e8584001e0100081d890122f4200181d08491250f03042ea0710000102d4100f0004c0c09881858080410006030040d000034850032078020450a886d05d800203030308400141c040458004604d00390b03d0000c84d80d642d81c0100144030584070600d88401001806c00300b103003030350000c2c0e2102da0786d2a542c24400c600229103225031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 224241969 1250 224240719 224240749
    0x3051207050408030f130906060e0406170c0103050411060703020715080103030e04050a151d0c03040309031b08120c1009200a1d2202090c07030c14010b 67
    0x12a04180c14403000e44e40d00d0082041e030f600700c08400595803081724550001140240b042020601c030407034554078002d0418100e141c113940a1030074030030b01042d11609030211010810329031004240c0c814031000110045d10015009032412664a1110f4600c4c1e00d8803030041c038000340079070000e011081c40e001e10580964100d02c280c2c0b0410402000620019501c42d1062404400803100070440e5150341140304001c00071400d01c6404888444030000f0075a1107010024007403e00e02441c1e41450b641e00720656914402241d004001607201035050001829109840201ca44003e10205641c2d8030303015400c0c40d1508000b1244007414000c50321208209041020000c1d810041909000303850140d612001c1c200c1d40214a42448041c014402c0416203991400f41d0080c440c800d50b0000c8080265190203410006036084440903200c102d5a030190408455480b4000b640a068003141c1c0e600c3d0961230450b40c1069000f107007000004074240000c10840c41c030401da03c080140c00010404c04080400403651001808 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 224243219 1250 224241969 224241977
    0x9050115090504030c12020f070303030b12011e0213031703040b090a1a06011b06090c0f03052806141609030512090406050a03030806091e0402130f0903051207 70
    0x104400641d109814402c0d61b17134401608519020104000c0c0e040460007607500e04180310361040003041c540c0c59080080ea00406417843e0080980c8914500d00f62100e040d6098284048500013810480541e401082d61010100c0c488030103544135a5906241c8251626a2030b05a40201c01d120030b111030254241d40090602000302780c010015910720b80815814000060f503450b410300003610907405458208042c0d080c600030301303540c46101d10b0040001d082c0794006803801018000c2c041502c80c100c090080030350b90468010304004594441480045402d001c2040c0b14005041019000036494050440401700050390b801d52458002007445c03080040500c04410810000030170404120b0100d842054007c50011050762a0709502c04100548102d501960304000c0220001081c594041d56407400382904840c10101c645608840d40010100880d01703645513041c0b140810014500401d44806331484403501141039040811078004492a0000980c0414800202441201485640c0940c03142203410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 224244469 1250 224243219 224243221
    0x7060b010503060f010e011b03020a0507150c170405270703150509060307030506070503070201060f03120c020f09010f03051e0d3b040b031209130f090501150905 71
    0x1411301840c0e44240c0b414002a800b040e0311603442801e00c1c28100746110b0300601d171181240790003503449040810540b4940619113010900800e81c6904945d02c1040380e503036210058140d01c3d19804080c04685a828101e8200301c002440d031140d4001144078a406030004e02e08100755020000030441c0109040e00b014a0720f00c01c0c4100c2035203514410282c520594021085564100110346010801d0300003412070700c582d104200981740e01c400214442c1e01c007a802405800d917110495820102c0038000140b0107402c00103da201d6034814071400456500050020000741142d40106220400a8001d44a042c074150b5080c02401402c100d010b20000390b210b0041130030400c0000c26600d52884c0c2c042034003040700c94641400074640607045108108035a00091600407071546000a01c03c4403e51480c3c000c0307040c65024806881c010850100a184107501c0e20325080c185c1f0300300050003407140c0c01420b000d80c4c0c3c0c88081041c40070714482c4180d00e512500c0009080c41100c1c0305072110100c0d65102048050500e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 224245719 1250 224244469 224244481
    0x60219020106061b0c05042a08060915042903010c0e03061602031909052d0609030304031506030b061504030818120a211d041407030207060b010503 65
    0x4994030050241c1c0c10f1300580f166a01e2504090681c0560311240e401400d000a81640102e800c0b0300014a6400c2030400c0050b24002806980c00c038012141c1907484500240040c0502000b002c2c5c450400d10001c00015800200b0304140301040000e02c40c242410340e0101e0080001c2c2401d20400380d500384d00c1c0c1800e00f480c102031000250b844400622449032615400b09504002d4000c000f69016030070b04070001c9080d10188000100481c08921500340303d4060030091522921084964203265440c030198002c0e01c0c24544148a80c3d80d00241c00240c061008000020210f554401500211030b40303050003048203851424022982c401c060301252046200040150420f1541801c0320204d030f50141c0c00c1600c80312404c41c02010002c81d000c2054000c2a0341414405002001ca0304400c0980710340c01c84401a004c00b0b0708582070080f40c00500340801c030700844503031403a5100c00000c1c0e04404001d00100341c07001007041c100740e4110b0039541c2c9008030343c0104410041195600071a20501001c0c40c0071403c0d49072503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 224246969 1250 224245719 224245727
    0x6101406041523190309050309010c02030309130e0105060102030f04030f0606030b011701050c1e0c0321180d0503010b03060a08011d0106050f0604060503090709060306021902010606 80
    0x252142820140c5281525003205016501540c00180c42c2c03c000868240290142c21072a4040141800390003040500707034802c00d019114040071346801c0381c000c41c01d00511100540b4403a110510507641448140301d0780074581c0e01d0000ea034001f00a558804120001e01e40340541c02d41e24050640c90543d0410301000e9088402401941d00b103a4004020340124540d134103141c5d00030a941e802c040c0a00d41481e0002c52505941000d8110a0004000800040ea901d403052000c500031540e07104441c81800003c1a01d10a00c4009086100068010f0301c2ca030040d0000c10b45103a080c080e01034030002c2c440c0d104100380307803c0101503032841c0080c810151411460040d401072840c0300500407604040800b0000c246c05407102056000503084a0307008201000c10041c40d518410200742680300e2541c00c100e80801c440c00c10449800c090800a00312604142c1001c1059449801c010400070701407046000c000b4408545000e50401907008042c01642c405600010950301c42c4d55451002c00d681c1130038410070000360303c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 224248219 1250 224246969 224246977
    0x20303070312090203010906020702030c012c1f0e0a080102030705030109050a09050f0c0a09020909060f060c070f030201030f050907050f0f09011815060c0b040614070206101406 78
    0x894a007100400c0e80c1da2a02200402d0f2042020f5007561908181d9400c20071285d0040c51442d000310200d400c0c4c0c00611004481c0401e87d01c8140700180c01083c40404100d12010842d002184001c00000e42d0014244040040328181c00c45031001581d074410150850402c01c40000c080c1c060301000394554506040b001d0140d21040c4103070103c050b5030f040081c0e07080030720398030520a860380102901e007600d2810502c1c5580f0340725030841a03c90403440c40002449509842165005000a021038219a491808210701142d010b43e034190007240800c4620300140007030141a029111007601c0c0d030f20b03950840c0001001c07694542d180c142807901c3c120a02c25030020016116048070750860720004111015000302d8035800c00340707000d142c00021070000810f030a0300038110760155103101c8104009560840407071103003040031803080201042c41c050b40280401d411112143e4454091400400c050240d00c2d40040c1100b000c803080d000580100c000d003c03a00c1c1500c1800c0c40104202148070f040f116070314001480d40d00c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 224249469 1250 224248219 224248223
    0x9180305031612090b1014030703020d140a03081e070c02090c130f090c140f030c091507050601081222050d0516050d0807081803030a0906081302030307 67
    0x14040e0041c032a2144150215100d07a02c20801c103000103000c03417030b1104254034103880004c501c8241100210b14020072510404542200030014400e180c655024041c40a010b070b00305075041200d222590300d034104104138000d01c2c070f0b100c2c2d954505103180003090360880c1004d00c105185101b0002c8148066a41d1003882c031035001d40c04440b0202a6111008441810310a0034100003400c12090000503107031442d00310140880c2c0c801141402440102c1204469000c2c80005d6000c18034404d102c0e6643c068801c85c0615070111000010310314142c0600001082032101300d01e84000701c0f000090f800108070301401a45e006001c4480103005101203003d10341c3c1d46000d50310400034100501101548454242c3c950131b002010702500170b0f2032161030360410b82d84400c1d100e10000028001900000b80701d0a000241042a9030000031050601c1882e503281112030340060309010a15034050803801255809000400198441d80c070b0310300e1000e01e0070b5805881c3c0308004000901207514400764801503140403080355031040d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 224250719 1250 224249469 224249491
    0x80717150105031e090703021305010f06080a0e1009021c050304060f0203071211061006020607050d02070c06110c1206040201080717040302010207230c0603060312030a0203010918030503 82
    0x1580c0da50105a07100c4d00e0411103503001890600703001c000315003c907455050b82e009541000b01c8242c902d0f43c100544800388103403807084841250030000d241c410a181c0d90000500c1c0e00c046002401d9450207440c11043c0840400d10300c2c0e0706c40d448811440c0c01200d01c0c00700f02802c0c0c6084c20201003912015124010f501c614414400c0c1d081d28079007114401e00072266640d03880301218410002c050801001609403405040d06440b5100200314640340343c00d1851704070740e105e07401080180e0302d02c0b100711250380110002103c0c086e002c1c0116400951006400005800195510013a15802e90700017803500603820101409140310710070340c180d240404070b84103510540a0030308a40f281c60300802121804a1085d0304400a001201803008240d03041d0000c00380c0070700424070044405c08901550055138900c020103c42540480e8041c819800d19801447d0f000714000c003500c0c207070324411031000340540c4103e07210f290080c0e0000051049148034031511403082c2c0d0710a8607201d03a5059550140044c400900006941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 224251969 1250 224250719 224250721
    0x403050c0405071106070e012a03030e060112110a08030a0e0a06140409020708040807080f01201204030201150311090906070504030618080d050603010b090603030a0302090a08030a08071715010503 86
    0x1070340940120000502c01c1182c620f401d412714280100758400032002100020306208001150000004100307058441d0384004d403d40300420303504c5580039a207080b2010b412407542c032000164028240060100c0366a030380c88203c0d1503042c8008002e0702005030307000007040c406004866a41ea403804425542595030300300c401650361600c3e04020350740b070280c2d5000c1c204a118011005c16885804503586030314255043c02070044040c010f2402d03184800d501403402c428181403084040821803d0b06041d0404e0080c00000f4041f082c640484402190603003050f1344100c004011101e03107080c440d2180703600c841c00354080d089600b000e00005059101d00d04c0040c2c8038544900804200d103040300034245003036521a00443e50381480d540d091024120450b1800d01ca035107401c010102a04009114030f1085070000c01840c5040414a01600250800c4203c1900308202a2011440610420081101e01d609894100f51407030519401000440d51000c00c003100c00d0500188141d0341c141c001010303602142420000c2d26 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 224253219 1250 224251969 224251997
    0x2030903070203030703050d060b0403030e010c30120203070207060c0c050a0909050606150f071b0f0f0614040b0307180e010f0905150103090302070b0403050c040507110607 76
    0x145001d02840a580f5000c0005c0035020160031200400165121010901c142559a00c400d070242c004c5e4400035011a52010445a00d984144c08442c0c0f114454010840302c03403408141401c003590591b1900c0324a480452a00c048180c02c00b2020a4500c9a00b0303040d865407404c110000c0d1141000e204041c18000b101c554002007000306041d15020700740c040c0000300d0450f507031a030300006440303d031304c080c0c6150040402141c05400c00d080c19101103904020384a03c0c100360134029002d6540960000d036180c2c0000840c0703100008801080c40010114204c04490320b41c20800d0030040341d84203034051000d114665045018020303000040d203013145d0404020b6612540c4188098882c24820741710340d41c2500c43c82030701140190300180b03407a051f1141c8000c1c000741651614104022283c0035101d070318003140a0110140b1542c402c0d0030010000c0c1c881c0c419640b4a950303e10440041383c0013a081101d2641100d149a1440c3c00c1911038203901c010f440c031380682c03002c03528044582c0b2000060503a008000030a403031010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 224254469 1250 224253219 224253223
    0x20d12080108103b101a010203031302011b060203010306050a0e0607090504050c0405061306020c2205040f020d030e010e0604050d0308270703060f230714030f040507051909020309 79
    0x100740d04002c055071000c007099114070004201b043d254429072800d003501604c0b19440042564860008000780d03440281050300107542e460700341124014007050a440a000062050010714021440340307101148900f0000308600035141c1c0116803100c030782e000c8010041c03400d030f001c030311802240d00603200000c81e0344901e04415514491a00440c3c2c001000180308699006a105013030104c030b119900b501ca81d500402d0070801c0d0750148140358655101500310001850b159640280e411501c208400032002d000f9601103100d60b4460741d0144c010400003211849156040014803409040c1100d51600e090300303200000b460172107084005010002c42400284031340221038041c25a026491800d1002d5a1401d02c2d0103503102400d00003150102c0c140f5103c2100c014180c001d1038000641c0e0700d00605441480025800707103c0000b000502040000b5040d1040303100344030000e600400c542c51000e861440d050500c9450014164422406007841d10b11041d02160002010f10659035400c9000d41c0d02d440b1107049034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 224255719 1250 224254469 224254571
    0x3031e060420031e07050a1b0b0c0c0606030c09070305070221270f090c04120f02010f080606030a09020f090f180d080a0207020d1208010810 62
    0x1000c0d61064031086292481e000070318070138005503031044c80d902d500a407801c11000b42540c50790003040081c070005a42034003407000c4241640c10a012260700d80c030940c0340d2490700041550700380e05010000600407501c040074440750340c2c040815030041000350a92008590764500c0186a1000c00d942c1e01c010901e064801c4c0042c241495402c0001041e07408080301a0081d680300c2040c094140c0c0c606000d110bd2030000401d00c48a107140200061000d08a1000b030016180c4014103500090804010204605a02e60040c2401c01d01414100480d039605100241104452109420900c40c01c8410001d0668071802100d5000009440119070481e207803000c00e1b40f8034010b2000742c0e40401882d007004411230303040960610403140c00b8802040200c0c410100394503040c064111000244001e0b000480c4030000e90018980e041c400340903844440040d1310341c176001c4c51900c030010001660203801000a46c2080210703095400e16107004100718115012640c0754549000751607e440e102415000042d6030f00b01d000e0b5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 224256969 1250 224255719 224255741
    0x2071802030a1b0305100e0c12100e040507031a060a0510020705130b030706050c03030c09011101140a27020d230c130c050d0504110a06021b0303031e0604 68
    0x2001c243c042050003501600040316014034104000e900001c2801000035041d00a46070300c1d52242c54030117044040903014100505003c0c08e906811800a2001c1c8a10780c40c510a902a0300130b0444e2a055280003000c00c03400710102e00501e00c0e180c0900c1602d03981d0104910440d50119071a45500e01c0694043e401c2529990003143d06c510108501807842189402542c81c44070b0407400d540b486c40d22444c0569003030103143c4121751954024000508040000c0380144058881410204083c4096403541820750710703d028210216001e103400d000c45c1d81b98a001d00b41c003805203c20000f00b10f503611086003c66a1490700081c0c0f1035180e0a01c0c040a101c7c005890f81c0405044440f20450751248034415583d4540c1d100c0300301c0c013074031070240c1034030181c1e0a600c01c0c41040c07040f40d0340e440e10700f490358560100580f0024006481c1e000d07803102198120b03550f2102600040000c0d4018258220800700347d0341c9940111082a070284c0c00030010081030454003014000300292400a84429803190004203000780710500344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 224258219 1250 224256969 224257001
    0x9050406060c050c040e03070f02040612050d110c010f03050c0d1d070510051909090e010e1c1b0807050a0f0209090d14072109080d02071802030a 64
    0x3080880e8000750b00901c081c0154103d03507032042500300740421101022490300e5142c2050211800084d200d0030306139040e80c00200040b4619440307044014010308107050850700c030303400445140ba00540142e1031140503c071610113070280d0014840040c050a40100c0b02c10201903803a40094007078034104003a5900541c440c03004001d061001000ca001400840c3c0300301078a40f03d00c8000168034070303190100300194645a5610b60074405002c2c10300101000e00303401030051100c1860081007849c1c6d644030301da0084008000126421740303450066401c3c9101030880c0700000d21800c04606031290403652002041d410641113a0219030142880749160195440c000c016020388500380d81809050b40f10031441c1802100c2d61071715602c401000e2946d07040c41e803140401184903110980300c140c2c000c1b409080440d000701085c3c0728919201c5000072140304044000380200b00344031001c2c0040a000c000080600316a80010044141000d030240034440708007008000c0581c0000c00140d032445640c201224000702010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 224259469 1250 224258219 224258231
    0x10c140a030905090c030112141e0c0411070221030c030f0a0e010c0c03060506030a02090906160212031b04030206030702010603020111070f0e041109090604300f090504 74
    0x7500510541251107028840c04a050200b5042400c690032a4101c1d00c4c01440d00342c00100c00d6403605a4070b040b8135940301d0035000e0701180c4030440201c0c04114216640ba6000b401004c1000b00c00c00c0229024416851682c0348188010001038851603400701007680602d0620b400904001146461841040a40c2006002c040341c18924103000c0c4018286018007030f00d41c0001c1c003203c5801110150046100504a41d11150b002c1000c01c5d0310354070264100c100901554460032554000c11080c04041d65088110f50018080102e6191040082c100394075161015020110b070458001e8498000640303404512120304540c13400f072641e0517084400a5502034130484d240e107031041c8060b00030710851000364003250207560044980100402c03c50142c0745040d4090450b2403d003500754541e210001c00c01c0b030340c028080c0c05a0345140c1e03589648a1044010200409031b9240c1860b081c0690340c025800a82d500a40d6402100000514130780458801810b10704203a50b12441c0e0f0b400c903041030183d030110703030483d141c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 224260719 1250 224259469 224259473
    0x3121b040305070e0105040b06180301200408060114010225030c030506060405012106020904090206031611072301170a020a020f06040209041e05060f07020d090305060105010c140a 79
    0x101c0c0c03e5089407007010042d200c50ba41d84060200752480f0b00d10305a40503008029660460000d030b000c046805901a00018504613005014444d841840010030500032003c602045002d10402070940900562860910b48048480020395914000344020811040c01c108a0070f9542c484200d410046800c0b490101d03e0304d54904103d80c4030003040e107000d8062130404002250030300106100414401020002c443d519a42d600c9610080d00120321456000307480c0d5600340090f9507054007446c020844407511140070340c44440c3c05032010641d2444242217400000302001074507505e9001e5614205103602c01400200d95100495000140e040302c4c140880702c1600b03100504289a01810089200d81c00315460346400000d003070750380e0b03804881c001c2d402003032040020002010844c003035142c501508000ea05500c0746580301402e040c4201e45804c11a00804204241c85038100141201c212060a1000782030f801c0d40c8407103403118014020390307050096084141e02040400412003040a1008007502d408031458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 224261969 1250 224260719 224260723
    0x7090b04200d0902130e0c010c0804060509040605102c1507050c03160f0609030507050409031704030807080f040b010311031e0303010501020607021b100509031b0319020303121b040305 81
    0xa01d806e020a210b025101c400719400750401c00d00b11034000032503031709040c6003050441c2c845c0d000d803800c2e582081c1c94207400111a250030021110200c81ca459041001803500702c1e0842010300c8000311110840340c40064181e984036421044402100961003940c1d503141c81c100b072854040344480b41509445400c0001103441004c809000594807141003844156554440c102d4251034036000150464104c100100070903d000d03030044440340d12900748120071340056006007441c0c00c1e0032079094020076000020490016030201120758400c3e0a0380e84220f803070610b83c03142d42d001385050200402c80302e040303481a03401e40c0d0204001001c0c2d00f04c0c05001040c048468030350f00e4070b80e0028801c407400741c461540820206800030908030000140507160038000308887c001c0200342079484034646c090000c104200c59154500b840b0042ca0200003001c0c1400b01c441c0c1d0018103181c140c1c1c280c00309190700c000201c0340c401070340d001c002c960410071100381c4000c054458034a0280e034100c0c00803122540d6000060000200b001c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 224263219 1250 224261969 224261981
    0x3020f0d02120d030e010b0105030604180b070f12020f090112021c0b090709060f050702060706050108011d010216021504150c050706210c0e030d0207090b04200d090213 74
    0x40344e4090181440705d40c5074909036139000c200c03580420001d00c0010541e040c198000405c60401c41002c10f25080e10341ca4114083c00141c40080016683c880c6100c2c40c1c64020031a0502158400821403401d100f00c070380407484d801040713812410031020700c4d03000072044050b405596101c1c02c0c81c84424105040d002c01c100c01854039441c1c0c2800340c0300c0c400010f41294040d841c2081200d400342c0716200603403103400f41101d084e400054100e038050002c1c40317110040f42261160301d019003944000022a801c179180d407500007280c600854a46c50b070040150144044c3e003c48401c0d11298195103c18895500300241c3c6080e000303070740016810708a50f1412405c83c503480101400128003610a840d59903444403070840b01d5144403e00841c00c003c1c000411a1810381b1540007d4011140d0718007420b0480c5200e00180c200346041d5100001a8401c40042c400e04c10207200c2c4041c584400c640401240c1141460300f001c0324080d0300c400c204d0360343c0400c1020b010f0003a500b100394000e034010140f80720480c1030310403403001300fa0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 224264469 1250 224263219 224263243
    0x40c0507050105060f10050d1b210e030a0509120627010c09060c0203030d09080c0d0e3003041d07032c120403063303020f0d0212 57
    0xf003030401151450030094a0a5084100a402c0f0b10942d50080c00698260b844604c0c42500d81e913661202da54001900000b00701e103211550b845181d0300c0075025450300c0100b15210880303078103072806180000d842800011030b02c1c200c4071400c00e82d44030848400060200000020f0240c00c03801034404002c8030306c124040c90382d40f004101070f003151605031000c107150807a084c802da00c02c080303107450006220141c002c0c0c212584051009084925010b4101c1d01d100a4990380c0401f110000008a0841c50004d42806040300d10140c030300d4000d041c0c0051000144945000441c1101200030b0000300c40300c95800b03211210324507081c507000c40b07a58903070b01c0c42c00c001a2800161a44040380300100440d44e014840e01407450301081c041c4408001121350340c05c9002c070601245503480e10b40b28040500c0302480089024000031402040000b801020103000340324600c1c620340c0b020030000d4100200c8206000700c035103c8402d507601070b03c2c5601d5003022100802c25221440401960007003075004800740e0f00000203603044001c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 224265719 1250 224264469 224264471
    0x9050f0106080d08150d02060c06070210021204080f0705060709090c0516021e0301112505120a050f030126010b060f030903091503040b090601180e0705040c05070501 73
    0x7955410038240c0759850f5000400002d441c02c1c0100d000d51203a0b08035040c2800d0000d040c3c0c101ca40c85940024101d07070003810340c2c1c1c29617007188040001140e014003111002552000b0298507058041e6500a8034580c0200002c10300c031800700b003840041e01481c041c0c0d07508070343c00801c41e246c0342407181c4040c000341038074400d1403000f604042030040107910a100361030440d0b6241b0804105544070703074204020007045822110707041d80d04022282d400d0798240038100440c108280856510300100c3c610340c04042c40c0031709803582803a0380301c16000020f100140000740100f20082c10f075150300c0c5070042203032588108201c100c2080004000420040c1255064a0a1003450b583c03040702c1c0c1c0034120300c1030b007030b114414443c603030041d0280080caa05081c040015980152040c00b84c926184410307001860b500c480310442d18443c0c401008000420918650303181c0c000c800b440040c1115031400c10b00640682d40e012a0707171202a03d6440741103413010104903a40140c000103009020200020348001e100e500074441c151125 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 224266969 1250 224265719 224265731
    0x130e060f040c0b1e0d09020418020103061a090118030f03080106180608060609030115030602190309150c170a0f0b010503040206040e062103040e09160303030c0e0409050f01 76
    0x1a0004000c4800030050181480074000d40c81d44c030281143c000e11034403800c03613440d00e020000683d16031140015a10140d03404e140e00183e180001011141e4640140844841c401441400340900400b541c54542c404d28050740020390540c000c0741410321a178002055001444180d008058218003818180c556036a05d6402142101c521448041010312a0f41c01003203040001c144141421802085894000380021a18945403400e844008050f0b07803082e2445035010030204850040c00303110000342c805500d030603c1118041e07102c0800d1041c20703910b1091550303030300c901110300349001e500c14a655101000038075041d40790004209000d8001c1d0790720b00034001d20b4000030000b29030044003942e00a0350060030090074941410584060680c2c007803c496400088900b900140c2c1100a0620403904902001b07152a10b02d00951800034103409003411840c0d81181110f64080440c1440503012a50075203408600c403210350078107495820755420000d8101d801e007105007050090004001100d884040700810030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 224268219 1250 224266969 224266979
    0x90e0d1202070b010509130507090501060e0a080c090a14040b0609010503070e160203041701022206050d0906021605071a0f03161b1101170108030702130e060f040c 72
    0x720302c2091402081140c0c5030f8018801030905840ea5540109034246000c1c4100782e42c0c9405143c501c4660201c40c0780c50710360006000080d48400110081d020540740c040105007031001d865213a900d03103d9002d000e001106c00040b20840c040c1c01c4400d8640007030b04056540c2c01d0034245215254003c551150180c000306000203010300300010745004650384d1200258250300c0b205034800000c0807100c079003400c5110a00c03003c5140301003640030250030001c0b02e00060341c8145001c0c0c0440022500d45011070800b081003800c105094004048a01444400100085120007032074104000d0281c6c0b1050204189500d0307612007040300001d588416190750060403558000d80710200300d507521072140c400c1e14640040c00424540d10300040384038140b030400d040410140b001290203091500b80d070b51041e20041e45056031000f45507000a048403800700c030280c1d06012981000c00300c9640f4402d41d00024001c0300c07c585070100404596108940080c003c0c2c081d116103003441c08c05801c00c41c40036281980c074001c00b00300001d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 224269469 1250 224268219 224268221
    0x203012007020108150a05120f060c070b0906190e0106030503131d040f0803150d0b0a050609040203031801021509010b0901080c031c05120c0406120207020d0b0709090e0d12 76
    0x1768907900240002d40442c00c0030240540c413000c0018520291085030747e2109001410b1141031310446015150540724041030a1168003520701070034a46650b0404018064a9907510800072441103041c80c02080c041003120ba010b004107160342c000b6203d400045824a200c007104200d104c1210181107403a4109285124243c483c5502500d000340104014030036074002484c507502650380240301d81540b500c0b01903507201056440d01d684a081742c1e1060381c041041754030f0060342303d10758000d03c003a5002c0b14149070544c003190340e80c07140341408520b80400d9074a1030400d078401c002340804010a5003180e50b40342019443c1c540640098529540710b03450a00003c201c407680082c404000c40d4000b0001c080ea54080015000403860110320b9800b004000c00c4a4200716400c0e11103203010344104100d00f50380724a0403100074000c1c0c941c02d41d205030846c01084400702582c2c602031201e4002ea04546078a0003512490400d588070350069119a1f14141440b03031400321600d0204116100302d5680e120002280c1004540d80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 224270719 1250 224269469 224269501
    0x1f050316020f06060d0c09020d14071704170f07050a0204060506071a0c04080f06010302010f020a0f06020c0c0d06050106030501050a0506160212070e011a21040203012007020108 78
    0x300c6154843c00000310b03a0f290a080c55000a030180030350240c01e0f03450700390100c180d03030100b80000748241d114034105580e1a0008c00041d440141031078114001c00c4903070260040b600000d880030b030005104041c0c0085404c062012100940281e0b041917650f044140741c400e4035691085c4c8264442c45c0741090004403030030408100c4d840740380e028015042c6514200041000c1040141150003d104180004640c0040030090400e0540480004082c07940c03540c4001012101100040030440d0813a0700150700003924400000801c6510900150b22900c031511058078101c8200c003116441170010b006d910922100b988800d041e1007039036074284616a01d440030303c00309944512804d034001104008048007408014407000ea6144010803035a0b00e034100c0c03d100751401c601da400c82ca116240c04401002440000c411400e40d0040e0401c2c4941066407001c0144580c1114114104800500750001000c41d0b5003913000003505e010f00050307001d0795100110500d40941141c0400ca001c641100d000c203000801444280d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 224271969 1250 224270719 224270743
    0xf06100f09092d0507050102010216030305060d0b0403050417010605100305060d1401060609170d0f110607051c0b031c0309021008091203010806040f021f05031602 72
    0x1503102a103451180380041100038402e540d078484815045606281510804502503401c031800d000d031264500f001400d01d02550311113415a0720401c418181c511052a42c0320f801901030a0015503565550017092200021040081c108040c80c0c04010805801c0301c09801a12403018103001c1c0369029042880c22500c96003e85540a103580000c1005070384250046030340540050901d202c0f188090b51001c0c6500341084000010340d4440e00d0911003941d03c05054001003440c41014040003aa01c110f01d41c039850760101500800461604174002d1a0040c0c18065544001c203088800038544080300a025400041091100c1c140078150080000c020380644022850024003401416210f031900f141b8205100c01d0f64420315490b500702d00c000d40d442940501b5100111740707500c8071a00d4904000741c2001800c114072034040c0380c10b00040c448400b00166040c5e110750300180d81002c0085900000e901800e15072a1060881080d100c4031030354503401800b0318010181c0e40c5140c19078808403103007640c58820000351 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 224273219 1250 224271969 224271989
    0x6100609080a020409061803030b15040513051003052b0503090d0509190e06010e2b060e0a061b030c050d0f1b08041a01121101030b030f0f0610 63
    0x290310b01514090303000801e0303140718920004e01c100c02200503942890b150f14080d40420b17030b0b50f46aa490b41c103000c811103039a0340a00d420149083e007840009801796240c000021120796071240002c3e49048a0400f00c0e010b5070b000700480351041c0c1d4000100490710114401500d0b008030000401ca241405641030300d024030041000340c0031541c0d072010102d550360049130600740d0107250902e03142544412712804c04041c1c0710558101060b481c1071400036080f408007040c030710300a030844440c002289441c200a0820300c40030048902550f01c0a0520b038020700201d5142c0315250150340ea039607042205550001150321040d0291061541c110032051b0121082c0030b0801c0c01181c1d080064150701c1d021a0301c5000c00078511440014103c440b507000042c01c03100c0710180070218220805100c203100c680d540c2c0951404a0070400d4050703604003161402100491003006001e0074000d0314111540e0f029800c400c1d40c012010701100d00e90000e142c81c807941d620100036422914041c200115808403080c4103198161031903a1a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 224274469 1250 224273219 224273233
    0x602090a090c0f1d060c060f070c02010c0308103302010203060f04180f05100e030702131503050f03040603110a08040b0a0e060a1a010305040b0601030f14090610060908 74
    0x10f060342c40b0900c01e40820340c5110b001c040c03c0003d980e85005800d01d12030342d00c010002890000003201400001030601000c0c0082070078290010313030780041c50b82003142d418074100d0015242e0600c4000b0100c095000050000440c50040780252400601c60313142c1042c0c10102007105403000026805c078481500d05c1c5400443e585075007400c070300b0643c2140300741803000b400103602003441d5120b102000c0c1d05604100c075582c01c85240200030201030f01803c03003110700c8280035520b8181e140e40020b111102c003c105e8501991584004856180380c841d510005541000c04d643c942404401c1068480d40b02303000e1200401c1c9410303100e80e180b654001c01c6c3c601c1050142c9540c3c05540715901c6115a20000030b00074800207456a07020301040401707010060007100a9407020482c003030200c20034031030b4841038800c03581010b19250070440031810010f803a50b0001020708002806034600f0308094060701412003284d166442e00028041003c1001400340d21030f11048104031601600c8260854498401c0c1c4240b074580c0e40028 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 224275719 1250 224274469 224274497
    0x10f0905040207050307150b150a091a22060f03051501030b03030c0d080411010804030e06030a0b060f0a1412070516140604021002010b1315030804030602090a090c 72
    0x80d000f84251402501120b050480c3c6503200c2c1910505074045442a60f201c0448008505101c2000002400310458050502c04003640040080c0f65900c50040c0038058a1407815500e0b090000720b50010300c0d02c903d1070845c07104072400003121201c20b106420001d4504280140c071144603101d0903014240f25104290b581010b0380044015001600303403a17902d03010030401c440c00c813001000031407207030021a152a441407800d801c2c00070b103420f10b69842e0303810b00140c3c0c1e04020009610203a5490546403c0f00e0041d203940b20b07080c041008110040d001900014002010300002d6907010140100c021b19a407843d076003416040303065100303016200d918020411010b0111381514050300181240d903084522802c00030310700d511411180ca00d003842135480d9070030000a020940c200800a120900c01c50300080c4110308200001c518060741c00500c0002d42640c40c8201d00000d55120802802580c1041080d0b071101d0300d90410000a621040711148110f00e629000242441940100c0500342c0d01c5880b00101e000d650 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 224276969 1250 224275719 224275721
    0x307020f0d0201170a060906062d0e0d081b030403080307030f0f060605090405150a030b040f05070e0106120b010504170a0b010b070c05030a020609150408100e0606010f090504 77
    0x840d002ca05002861a6000c84003003080d0311030348650041c2101291241c6401c00c2102118510b4208204004400750b0402c001c0b0030710f8003241d0b8403a0f007403c1c1480c0b005884c0384049500100742c886d100c0d880b04c070352000c002c1400f81c0000035054640c85c0702504800c440c07003465002d40c0e0780301e68807004107014414000110350234000e83c000d04000920003808500e10031040304c041c0444840381c1040c80400c0000c100c08910381464458168440e813003089c1440507000d000d000a85401b4944402044618418001000c120714413003601038041d03002040320b030001d465103000e0408a100b4006c043c00110300d030980c41c500f08040d0003103d0304d018040e11458505420004055000c8070001c0a407081c1d03105407480140001c1e00a1404c1c0e00030140764510544031034842c5040c5641c00000d612042c030a034000c1d4003400140c0e40703034021101700c00d1040381d50032100048031500c1a468011940040450300030442c007109980300c1500034243c40b0600360103443c042c1e541c0c800150303180346080d601c0d600000c0d0080014000c905003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 224278219 1250 224276969 224276989
    0x90a170307020a1e200a05060903010219030522081204020f0312090103060e1905040f050a03080601090e190c05070803040804140d03020a06090c0503030c0d110307020f 74
    0xe1841620700490850300c0c0e1840c504410000c404d08220403079800710500c003103a0010b05403c04085901e0003a1810400000c0c1110724a0150511801000880801ca07035800d42c11a03c0034510021000e00c64900040042c3c004c110440798003544450a488280e400039844c69203829450740019820b042c2041c402c88003004a000520032604000e00311041c070b40c20b03902041400c082000499044d0390701d600410005081c0c0e122a40180203050ac005d0030300a9803d000008920492840702c0c0010322640d0701d0410134201425144060650302496401d442495407003500c1c00d105003001e880392441c45541d038403034011902d421250601403580410740154070328000e4200c1c90780c98207180303481400d02441b5160182c1a40c41980c00b241c10620004040160805024484078803440841c0d8034440d440d00e07501d01940f1101c3c1040300a180300d80c4c4001102c100000b40d00707154050540070307040302d8807080c1c640782c500c0d078441d4003014201c041800b200800c020708600000701d138006a0301500c015000d015201c20f0140b4180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 224279469 1250 224278219 224278231
    0x1903050a080402280f08070f09110f040905010e0c0415080406020c07060e040e0601030c12150609021b060c0f0c010204090e0307060e010603080f0a14030a020c06090a1703 75
    0xc0010b00c0040f401030444c54054504c0b80c801d031041100c62601030307a460500c0886e40b100010360001401003140c20b03001c84042040f118860804110325402d07030804c118030301c2000c8500721551004140812003100551042d41690018102404151113903035030703290280118860564240381c0d204e00c04100c1841042c203036030803520a420150414030881c0b001400d1001d190441c4001801540289904d13280c1030096644161410025120950640e04d0300d00c503040f01406140341401c04000c1c0603013000020544031401d1398001c10b0401070151580b0b1a6006948400c5404100300b0503140301030410b80000c03a555010740c403030015042c6801c040f407040703501a401c00c00015000b5542404009a40c1400f0700583d49c10b44214009991340380c0c00c626010088400940411103d81e1400308144001980c0d00c0c100d0b40e0102e42d1002950300c0d905000310485542402c00c900800c0090040180001d00f880c580180c10040524010340da019135074001001e60f0303009002c0001d4101d000e00e0140c40b000c140820011034010b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 224280575 1106 224279469 224279479
    0x2d0f031020040e13080c01051612050606030a0c03090501140405060c0405060a12150308040906061e0509011716080702030a1d0303040306050f04051903050a080402 72
    0x100400705050800e0409141d0188091744c4240d40000c051310b0001d000074908000c0c1e012180088102c00c2020030082c54084045801d280101c0384a01401b608103804d50791801d1100015194000301c0b5410b06a440441c4404502c080c050307100d2090051074002c50908192809901d02a401003803429098000d00c401d22107541c03402e0850341e61060320314200716440181d80c4980010300c010101c2c10700d003017040350b400007c005690303001c0c1044944a403802c10400c1e0765240140d8403001c014000001420091044450403800344028048001c41850500c01e00c01c40b002c4e038403103905401e44400541a021310042e81c212540600920703842401031000d9420054108805018101c80c5000c00c980e0310074030120b80d81281c50400654000790342042081c00582000004040c007084169016141c0d406031000102c04504054490200c00350f16541c0c0340d107000503038441214002e41c0a40308a0b841 = true := by decide +kernel

theorem cover : BRFrame.Cov 224100719 224280575 := by
  have h0 := BRFrame.cov_init 224100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 224100719 ≤ n) (h2 : n < 224280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
