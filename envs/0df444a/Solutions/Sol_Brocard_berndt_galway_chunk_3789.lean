-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3789
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:40:48.30968+00:00
-- url     : https://prove2.me/submissions/9da9bf33-db25-4e56-8f1e-1ae125b0fd92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 681294964 ≤ n < 681474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 681296214 1250 681294964 681294997
    0x506120111041221030b040f151a21040302060703050601050403110d0c0617060406060c03050a110d080f0a05100b07050a02130504020a0b0307050403020d02030c0907081803 76
    0x3107140c1554048000090141c04419040300e88198030150340700c0c25091300b40020303481e04040180da141501c640910030091280400801451aa010f2010051881412042454600c4d09034040102000712046080d20b200100450708448141e50140350055074194010b00c07603040000c024a00a2040b5801070310142c44190034249955034401088011480c0340383c10480f804103074000103c0211048014184640707440701c0403010348010f4411080d0050606201c0c500341201080f815401c80d140342a0031b50940b504075592020307094162a2211255075116907441250340d01000c4070b900c08242400b4a0142c5260002c2e0749030345100707000f50f6605449040003603803804d04c00c100301722900005041c0d20b44900300ba00e4002c09243c000a2000000e2214a40340507100c1c0c01700403c51802502a4001d0484902944d0450500721001015401140070080c081c41e82c40c0d0f600000d65a04006a910900d00140303090b0311850f06110041401006031100041e8403002c2c81400715240010059481e6004265101e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 681297464 1250 681296214 681296219
    0xc061110090209011202042a0315030807020d02190303030228091503241d070504051309080d06052419050c0321100e1801020c0102040603050612011104 67
    0x141748018128080341d01030303070741c0f1491200400c4080d05491070006404512000f041107200240a64860103c11002008800310034400600e110081d42d1440d901a18209144403c80c8046811140010103120301d541c9205000410580d05030000c0c6442000140c0c2c182d928020250114850802e00d04032030080384001d18140038200304032500a01c600d5042c43e010034441c803000c00741400b00389501050003541c456808180030f420b02885104006101c1810405101e02c2c1c1808010018004d50150b948101e409960444440b041c03030f0010000c480d0041d207600e5851032007400000041c0101d100d9a4002c0045030500200e5103c01741d4402c41d030315220b03d042171070320203e035a00d1a10f60702ca4086003c148032081c003180501d00800c00182c80194000305d000c09088480d4003181d0094400103043c1034101040f0305080c056419a06100e5402207504100c514074103024480b940d02900482000003003030762010800180b019410f811040c0601c1c010780e9116401124a0007050980b69908a41440400e042004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 681298714 1250 681297464 681297479
    0x10b180f071d150d0c0504050a0b1809150a050108011a07140a050303100b0a0f03020d060509091005060d0218150406030602090906010c0b070c08070c06111009020901 73
    0x662101c2103844100440190109000440382c803543d036018200d6280100d003d4084a000348107039007003000181009400c00b8070346400102840f4050266800103000410b000601c1e0540c0c0c40003e05441300108101000e1401d44203d00506141d040c15038480c0c000550005295402040214143c1340d2034903c1c404a1004505d08446903070050404941d040c40c940203000d40c030705080c00600e186500c240d01450307490400040c480c5030500c0d1034209241028003007000380c91183d00a4803040741c0d46070798200540c41e24600e84410004003503c0c0c0c0314a400641c1d0340c04104010402180740c045c4403481c2801000240c40310414000c00c030049001c02900040441c0110001c440185d100a0f03001401850346072080f12860040780a80d10241e01c12641250042229207640c80c00705070f0560b00050078a03000b030415125881e40c1c66540d1024021400f40314080041c10144214a001c5810140e0007141403c289035071140020103581d61442c1d40442d50184400e05d68a0700d886010b50404a074000381514441d0342004107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 681299964 1250 681298714 681298727
    0x411101409060f040303020f100501060e0405041104090311100911090408040320100f0210020f0405060403150554072103050d051e0108010b180f07 65
    0x3107594021000e010210f002d040c080014806180f11b030780540004109242c2e183d10f041564404200d03054200001880390646c00421005030000407900880c1c6601c0d181001e904180e00802c01c183c009060808000515812040f82c54445000340c04451411a07103441610846102d101c00030000d1104000c130b003e8529180d0645500315000300c1c5040d1400340d46c2e9a40840c40e410161001102080c82c0314410300d0b038030f0704c100b403440900c0306420420451344048100075142d80400b05c003c900c6542c04038980c50001d000c0400c0e54082e24020b05465940c545034140050001d10542c1e08131011418500000e0701094020008452440380451403841301054414007400b0310100b01c20a054200c02c4095a410404e88803c0c04034041b044102a05690b803e20320030352401101c402e52400c01007140115000000d0784607080301e080c0066214001042d855911090b1958540c420480c40e01d824401c001003000141035201412881e0b0483d1049040140b8220b524041c6804a072424042c074202c070300149110f800f030fa0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 681301214 1250 681299964 681299977
    0xd0f031a040f32061f080702070506070b10050301230702010f1b02062206051012051005090a020607030507060f02042319060c0510050a0504111014 65
    0x35003c5500e00c00403c11003000710480d6110f01403118031203450440a42940103142e084201036401400e8035a0092580740191000c0c2c058108000d1102c00240007644203000480c09000700030308442d81c1d6003281c00c1025200c04103954401d541c00c22500700091602c3e0500c40c42001210131351181e608521481811101440014098400d554803510301c10090051441132940700d84d440201c8860729840604024503014004000078003071401e4000e91003caa05000c290194158004000b18442d514030034080281411640034030b11198500e0103a80c108400410481c4c2d030100b500c0e004101994501c000b0a54072240c640f00603400c0702081002c0008644554010110300b401040c011444070308100d05e11080740d100d940b1282d410b03000100924284424824090b6001c8821248242d001d48039001100c000c121034800d52050000440b000c0f03007088010722002c52004c080503001c01036480e1400600c0f010380021182210301c101d00400e031800c0c0b0700d002c1c004c1c0e049114103a41c4907800e0241c540142c0e142688081c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 681302464 1250 681301214 681301241
    0x14310519080c0d031a09060a09020d02160809090708010317160c0303050c0d05030405060f18010f0501050a0e0f01062a05030909101a03060a030209090d0f031a04 71
    0x200040301081c1000c1040f142a0400b95500050040f4003e004101c03030300c02c41d4215481604c495040c000181e40306240082502c8090100513610404080c24000138490b042445030740e03443c00302c00182842800c8029100e02482690b116017960383e904021030b1550001d0200501c0e19100b1ba0000791070010302000741200c01c0101020303070b020b030409446c1c00c16034261903441200014000104008400421300014200c0d408a0034514107506080c0c3c4c031580c07148002041c3c01681c40d46480000c600710b890007004d01d40701d680c0400800c840a001031800c0c001c0c0c2001d019a0380119a400b400140d000102680c062140c2054008034409034240b09003103d00c1c0188002d15030407010000020b9000364500400081c08c98842d0008503540c031501401d0205180d401400c24400e580e103c80100a0310a024034003800c10103140d06681d0780c82c2d903840005a0880f6240d0000b940040b04a0100704640e1030008505c1d11112040c0c44240c208064a80200d0648102c1c1d0140d110405000403010103070f0078140c00154a5a0b0324 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 681303714 1250 681302464 681302467
    0x1170d0906170a23090705030a150b1c0b040204110a0c0f02030309041a0415030807062406020c010201050a0b0a03080306180c0304170901170a1431051908 68
    0x4403a60844c10044060301c09078400d264030074810b180d00308000000c01400150060428682e59171902c80748001840b100d10101d0b51204003c0d241981c0700c0419400c1d19401007080d0a84035494204514041c2d0125030480c01070b07150001c103145248401040d21300888440d5105101800c03560350f5201120a180c108036018407041c0040045540c030341c007940080413080c0075000d0208a05008000681d4894038288a00d20a01310040c40400c410500b00e684141d00004013140d81c0c000301c2e1f40c2400b40045210110040b03e0510704c04a00a43c0c042a03100894100342d000f40220744640e003806080383c2e002001e499101d143c2210406c0024101c0028682c09034000340001410440d80c050017025000486010020f010000200002c011021800784010310710800000d00f0a208400040c1174425902c8000500d00e440c40c00291000c0c070203400410504004a0b075205840c201083c2030b61a100c4062205400d078030100c503510348002c860070500b103c01900b1030000c15502020340080311040b44a1318007541c02040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 681304964 1250 681303714 681303731
    0x80901051b0c010b28140105040b0a020c0a15080a060f06120b061204030f090f05090402040f0f02040f050303030f0403050313050a1b090513060f1401170d0906170a 72
    0x4032011000034404100e0700800139400605d610040d840300c0d6401502c01e88105c04402c02d92a6806026075003075442280c0341540c0c03241542c200342d10340318104290329800202d0b850086800740100002112000141d1504602c546800c5842c0701518940e005a04801080d9202000b8142c0301d40700307444846d05007210015498003890040342d040c2d84a41500038a00c2d1403501404101a400500c41d4401c1c002443c10040316818941410819036852007454840d0410b10302103800e5503101e52010f880d0000c01c0d07004000c00d000303900a002c041d400500c611020075006040c00561400d000c01283d2181803200690f4070251b0752a0742c19200e43c1c1000d000851003003041e058a20028104000c00b030445805009050390350719804070008a05001604002d0100d0b00300406e01c82c2c1c4440e0540c1e55802540d210b03001048031190462104000d00403d2040c0200810481c00004d0f54118210030406003010329080e6030020442c003000380c4081034584904000110103211008043c14002c021700c0d00b004040c0004200e400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 681306214 1250 681304964 681304969
    0x10f090e0c0a02150403020c04110c06180c040e0307120c0b0406140a0b010c15270c0801050402090f06040902060301080309120c010e040510170a03080901051b0c010b 73
    0x2401c94140c0c0507600300107503244000750100314030200c0b0524103054400c41d15050303600039154214039000600030707501e40031899010103807081502c02d400844401c5541502e4034856040340840407450010403800394902d00d464038100b5000745511007550724021803074485c095444407030818802a101c000c1000305c15407400020661801240581d00905d4003050700c0c294840d03a5144a800070b00b02c141010b2400c000f8541d10b076040708002400982180300f0300d220130620fa02e800701510480841c4182c1c50740c94000307404507210080600710564010302081180c591983c00d09400c075070080c0c030043e5200007450002484d12003a21031203580550050400320b04c9000c203a02045103500280c200301d0040c1c00114284100d4200018080720b901000130041c10340030040e0700044e000341c83d110034441c029521840040c00c9a0821007004004183c1d0740f04011802985d080c5090b00d400c2d40036800c03000105018042400c400050060500035048414a11241c0242c000562401c3e03014100d072030420354840118100f0781d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 681307464 1250 681306214 681306239
    0x301020703050a0e0402041503021b1603050618060c180a09060905060f0907050a0e1503040309090e0c1c0203070924030b180a1e15020711010f09 64
    0x4900c20b03141c090703c900340300703a001c1d02c0e0782801c03245103000d68810301c41040304a4010b03103c40c1c6400420f082c0160b9034194441004520000381202001030b2180c020500f0712100741000c140100c07030091003580d0950701c6410184100145040341c46060f036000e074020078a204003900c020b01c200c081805084828994203c0400c81d140b1540e80700480007542d5032800c01c007005c018040c043d400305044841c0340c50003c078280010b503025809081e07101007200100d0455100d500030710144407600c0004240d5800701104010780515036000701d404500050080e6400140b1407181d0150440c1d01c40060040d00c1d41c4140300341030111140f0304448503641401148119000f603107090084101401d00980041502c3c80144087c020411402001c034400004848081010842030040d035608248078000c0e4030940c64031800c0b142c0c40c00c0c902800241c0060f0000002c8014403e0400c600c01810f44180032000d01103101c1c0368103008034000c1d03140145c044051350301070515030340c880c4007194016078607030604e0701d802a1a050b454140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 681308714 1250 681307464 681307477
    0x80109031707020319030507052b11070b04170d020d09052802120a1a0f0a141306110c071406040605160c0302120c011709150a0605030102 61
    0x10480641c0d68604a0500e548425480380c01400103510340921008881506803100c0c24035010183c0d00c41c041400b1903c14030071910440c1150681c0d01102d040001004900e2421200071114075140c9000381400107612400e80d510240c03c183c900c255075445071501c513a205001c10303502c48a00c10030490043c0d01261803000d020345200d6400001004080b6262180c5030540c102c41340710104107200b0750206501c010810100045606070350004403110040c085a1a0818501c802030424070701e4000007002400d0310b14428802c81202002048580310369070200c0840b184c0074554070500107003070000380030f01e041042120200c2d0312842001540344000440a03800f03400c1100404440d8015002c100710114041003041041c400c100ca010340742610f40301019006204030112980c1d480181c40103030080c45541050103000307640207020600b03e1489841d281d61101079010185001c030740090344c944d15060000704414410440c00000f03100701000800300300103080005103500844c1da120000451183c4082c0040c01c00c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 681309964 1250 681308714 681308717
    0x180a09080712200313061412130b0f0415020c0f1b031b09010618090501180c02010509030906070606030c0303180614040302100c0209180c150a03051008010903 70
    0x80030b41008078901e0b07010fa020520f0b1800e51090202900b407118884c400d50444007141442c40d00c100c42000c44505a028035100c61594603c003c0404c29103c0302005c0d28809244145900c2c44075598003091084900402e440250907442101e24a900e40811b66001301741410598080314285000c0c100040e2400342c418200880404407440c2040307a508042102a0080f203910f80c048840b0b4168001140800c03505124900801c00300c1042050740300d200318004006002402d0090240b580c460700c071000200644058110442c0c9000050030b64144103105944c041c862881c055481c04660404006c03880e08210707010784a5951300c0100100150650741d41034001e61280e1291018154000040511414194812020710501c090031005e00d0303030482c017210140d81d41100e01c0c0096500140c002c07940c607440540000d40141c034a00038020b54402944103461841c11480840703003881c40300024040d410103106ca000030400b000344262220640039802660380030056050041415545074400c509440352600243c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 681311214 1250 681309964 681309977
    0x30c031f080f120c0c0d1a0a020301050112052a0c010f05041211070605071104051005031207080313060b1c0b0c040b030a1d010606031a180a09080712 66
    0x2d0341c02c0e00034410300c110900d200b40c0260920403000c5500d52104c00f00d0401c0d44c8a050f001aa01d03040040c04003001c00746880302411198586410b0780300754004d520a01890780450324088105104c1129170250f04d00c07a42c2d041d20114450110641c407000d280d064214103001c12013042c40490400242403040c40300c3c40e04058804100c40c1803c4c1058400070802c58840020011440403c051105d4001960390031215a072030f081e0343d10040b5040004c4480d449041c038a03442420314060058120180c1c142c2e070180c900840c281c2d003003040d41d105a114248160788000b0400701d01400098a16065014024500c80c0611404a4481141c40000301080320b088612001580003180c0d0301d0074800000d00c1c160740100c188695a01d01414001080260b0000a0800e80416180c03004a04421030540c030b0340900341041c200a010050303c0c0c1d000036018004031b0001e4001b0780000030103a8618504080c0400300128914042030294030b641c04204040c01c08480151200101007242a00107141c003030065150807000d54410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 681312464 1250 681311214 681311233
    0x302010603061104062003071205070201030c05040501120e0a050a08040e0c03151228030219030c0240050a0506090703090302120304060c1211030c031f08 68
    0x41c21258541c0c0f881000c0c66081c4428000d442d00588075031840000d20420100e401c5e1101005d40c6584190f841c0100b44540c0102d4900407250044080c1100e503100b40c8040c01104882c0c4002c5407203004511071140000d0304080c44140c01c1505a0140812032808019240f540499842d942d00c1c00201c0c00c403c80e1034002c009000c1000300c42c4071b6460358015030b0035440d1619506101c001002440c4003545100e104200f5604510030742c01042014510b040d03c008001000300c07140c0444454481c04c500b0040e00035004041d000c0284254400c10816069455141d030460006243c09000d00103003200328a0405491075200000c0e0180801801c50705010f10031614890006d568542a0a6402c00740c1201c0e54607041c00305004903030383d07620b003500d0740843c00d0319002420540ca810308a2900310540415858558004284402d1048941120300c0d07a005603200c0200c402c42ca415204200d445184068098150500104441101c51001140c229048041e5185000b010245840040c646a03000e002a03034802240d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 681313714 1250 681312464 681312473
    0x31e0918070207050108090a0b0a0c0e04060f0b03091018110f0d140102040b0f04090b0d0b04031817061b07170a0c0c090c020c040606021b060c0a0302010603 69
    0x95680c1290080400e0014100114069694882030058505200840001525101d03007005444c2d00c0c03940100019419040942008004103800800c400000d6a400000282d60405001c3d1904503585e0300c3c6101600d80c90080e18401c2c0c2e13000905050b03042e0154401344500190365020780020350719000100a102e0500c0d2a2041c82200c4088a40303002c0c0b40d482c2c1d030a005a9490403c544089a000084110281c070958409402441983c10107021000301050f41c00404422030701a0064460b100c6040207920b040c003080041c8440744160060a507502d12001800091191a10304040381411208861860721a04036100d84c0c8019a004c00c060740c0f10604100b0389510140c501c0e442c106010260500e000e2298a07442c0c0c00c42100d01500d000d074038001400f900194072803503001c0326050300b28500385840c945138500d401c080c2000c0030f0043c005104108290303103145801d03c500000ca45079a0010320082c02001810080c1d0012120762982c010401c0c486840c0004050000340d19051207940000303403050840c47c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 681314964 1250 681313714 681313729
    0x30714030105070f0206131106041d0c120403030c2102070c050111211218240402580305041a04091b031d071205031e09 53
    0x41d40081044c0c3c00006a8660380105215801130015040001140ea541c00e0003d181490518115041500018006100c1032000e0100740d400b1002c6484001c1c07915a403074803800758000c22452006040e0701401180003c1e009a010b681031500b9400c1900483d050442ca81d44042130196403000c03995000500d074410450302d01c0d0300b4ac0207000c007420910241040e601c0c100ba0b6610b03484030206007000188040d401c201000030b080d2030000c031003108101c0780c1c1d142125140e84041c0904480c8015845801c43c44000c901c207403481c6040300c041d81c0501015690f41c9408014071aa40c0040c02501001c4071000000070a0401d96451864020304d406ca009280070500700303088644404451030076800c00c1c031000e103001980c40301c00c0380c0490356844000d00702c9404e031880c001c10710311507540500c0d02c052034481031030613501d1a521071002000c0241c5041000802812149400e90314090854070703150030441d010700646003070449030000303203001d41d0499040c0901c044440d00d85044c810b180f5043e400020905004500c2c0112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 681316214 1250 681314964 681314971
    0x11040c08011410030f0e0109051002090906042304050303100e040b0a320109050a020c0c1e0603010f0f0b0408070e0601050f0a09090506060705070302060702040b030714030105 77
    0x180c091115850101c00c0100948032004071440381403690350b500c99040c426001044c41d143c465100700700c8001c0030b61805009180b02c503011206030051044035080d0003d40d10984a25800160500580d680c0d040c0811005100b52a403407600074004a06801c4c489090403159449107100e50021a43c0c0e040060441029100300d0780b284c40394506280070800010040000b05400c034560000204114020f503807013100100d4010780d00c50350100200b50114000703600c400a54100d4001080800441d1070760b01c080010303440381c059141c50a07800310032014010308204101c10008104c2c2c0310b6175000320201c1c0002910079072081e80460315011411a040c0920220484600010b0140800c43c07072405140c0740c481a10b4001610840c05030604410001e001e0b640528121820074068100c0e04c0d0383c074100450040e20143d01c0340980346400b440d03c80003501764142102200c84594122004154061950382084007992150754100e07001a114180aa00d94404000c0d52000c1c00c101048518120010b00c10305007120ba004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 681317464 1250 681316214 681316217
    0x90304091b0f0c1403181507050c0609120f031c0902011b0206040f09060e0601020102070c03030e0a030c0e0907050102161809080c1c170c0a031b26041113060b0711040c 74
    0x10407021000403c00110701648140503150141c8440340d13540003e1201000e803452040c14050241849100100072004010e044c030f01c00a00140d40e003201c00780004840c40200000d0105617010035800c4000c40e030b6404595034610003415640303405c0e1200d1203000e803419079074041d02c1c0791a2201c000b031110031180c80071941d0200c2d00388002c50400c120b80d00d92900c1c0701481d102c00707800c1c0505e2403801c0166480782040000030b1604011100c500c1c07961640101d500034001c4960814500810f5804501c941c40802c0321f101c00c00d640e5052850345800d104e0320701c4894454220310041269103d0080c000200180003400b00340004401500303803410a042d40c01d02c0741c4051144942003250410b40c50821018400321190041d215080107900c036059080b00742d00600c11100d40b0151031800303280c030308449a17020a402c2c8118442aa00d500c0803001d05c40c00b04d1026030181c0c2c006025a0b081003080c070890401c5105001e440e40b2002011032032035910f026603141071307001180a40b203070301045160070000d042a005044901c0c00ba1b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 681318714 1250 681317464 681317467
    0x15020d09092c0102070b100501021c2a0c0311011403060604031203140115140c0d21020309030d2405040e01020909090304091b0f0c14031815 62
    0x1e62202c0d001080e10000355109502c40102814a155001d5050b182000da0141c545156814007140c842d803e401c147c0325007030040c803c407000900c115520507008092030750750b500e070518441807040d85003488001aa0302488580003024801002c10340a0005800031805241202c40c1110100d000504400c009440c1c0c40d10841c0410500c0100e40b620822102100d810840710344c0c04043c05c020403406099208407040b510360f800000800c10b507044422059520005888819070b114150b40c14500c0d600811469280c0e070340104016202075805101081840500d211342000d42c03048134403e00003280c00a481c480100e074000b02d40a40310b44903d20860400010302c00030455080442c07429413604030424001ca0b03010300d80b6400d691011841c250143c0340b155400a00d080668500f040c01a03940b03820520a2612450401440d900baa2040020b0b07100d66407030503920242c240399254000d0300d08044103001100e459000703001c003001c9100c00b0700250401143e01e40340405160031550801002c00304480000b07510d400e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 681319964 1250 681318714 681318731
    0x160f1203050c031b030a09080712030b030d080a0b01050c1b10030b03060a090c0b1b150402091303020a0804080604110405010807180609020406080403170f061915020d0909 75
    0x40704800c603a180407007204c21a9503a0741e2142603001400a41000424094011030b52004012494101c031002800c00e9030200500d034645810565a03210030340b000c00c0801e808102141d080c40441d04442095101030520320b10b46444000040e10340346009044400c2302515071010380711480d04202000d00d54040c0d103001c0c440341c80c294002075100c0801500c0d1148807503890f800141004441a071a4004011003003409483c0c0200d6603040e84032914504900300213004407886424040300e01d07078a80d03014a4000d40070b00e513690340c1c0c1000345403180900300c0d042d0190b00c02c1501c2e00000848140043c000307464420080c244508052500c40b480303060081541c4e114a0518005000108000401c0011a1440101100940c503e108a0001810075421140c6090300001d40840c081d81c000942c14001c51081e680c0d89200380a200d111051340703205490581c1903c21603000728040d89418100b61884840c819000104141c3d2081031045035072211b100d11025802001e40b104245030044084001000050400e001d03140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 681321214 1250 681319964 681319981
    0x51030608060106360902090a0509090a0f050a0b13020310060810330e0c04060504060806181f06081005040207030903060f1506051204020105160f1203050c03 69
    0x500514139440d006000c0012030800040c0b04181d583c44e07034070480f02c01c1c154030703180c0c0c0700c09010790300c48405203000380c11007080003a96007400080d1901c00c00d404000740400040075070741e5042c40f543c24042600d403032007a0b6038044081201c52210a028050081c1244010101441807609101035400c583c018030749003c80c10098007802040c110004034000c0700000320001d0380c0c0408903042c1c2c40540b08040d0302d06440081c004020f072102d126000c0d80c4e0312200b10305003030b0390311101e4081c00d1082d4021800003030418401049040d010f000519001b03140100141d001440e1103c05203070712841211505010b0600d0144200446204802038000d032000c3e1420841915011450f41d00701811032160b2401164005410420302d80301c1e41c200d002071030b8403142c2440701183c10100d0304060b00c4000c3d401c03000c0802c0918000b0f82d03e80654100c490041341c400d031640b0182c2d6a80c006640c00d800c20403502c8011001482e200c000111128441d8140c5885034032075100e4018014401003c84100134001480c00504105018490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 681322464 1250 681321214 681321227
    0x30a05070e0102010e150603100e03030a181115070b1006080603191103070810060315020913410a09030203070b0903041205010b0102150151030608060106 68
    0x500c4e17171b040c2040c4c4465021a141c5540300080f840410f1800310701c8801c00d00c0c00b02c02980150f12100c8284075002543c7e4920080064920300244050f01848500400d0300b441d811000c000c400c2e505103a4100b00390340d1610740c80340a040307408541103a40c0800c140301060f00030001e1600808181d0041c1149800d45402c102d0922026801405040070209032940e65501000780d480640a04030aa40202007141000300c0500340307502048940c4843c0c0180b0901c81c051030b00c01d81c1c3d02464018580c144407482020081c0040004500d0100b8604c0076103a86040d40340d418051a0302c040c0300d42e49900301c200c0c4c003000c42d218550700074001c00340a03420000f1100120382e000094502982d004100035500b5128640704030f242d445564420300300e030f01e440036164080c0407040d400740300000e40a0f02980e0140c9000c030010071418100f4001e280c030441c40a0b0903200b000000c400318003a0301c04400700789020342c1c0d031568440c403280c030244c440c0070340360150003400503e01d43e4503001f07180c000e0446400130800c9504140380030784030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 681323714 1250 681322464 681322483
    0x6060906120f1707051c081b030a060b040b070b010801090b0c0f0d320606030703020d02040b030c0c1b0306060d02040924060f080d050a02030f030a05070e0102010e 72
    0x2441e5001d0b6001d0b00340080348006107003403079990403100c1e0742e014289071240d1103040c41741207488880c29003c0102c0301c1d030740a4604a44942300c170782c070b54000b10400c240c03944025030005002c40049550707610340864280e2101c002403018100f2119100d84132011071034051140070050700083c46a90424400c000040c0d0784c81596031304143c0071214640c070755400b500b8684060040c0322110380c02d1410b100c80f618409520701480181e46000000703640d01910101c0940c0d128541c10384070a50800e90810009103800d03c42d40c007511155404000140c03406503035142113000c581007600c1d0381040d1700001410000740c61042000107000702c018503101000799a5000065203c0300000c28a6003d8042051807404540d1a039000d111620b62184480b920001c4101c0032044400c0c402d01c0c5941110b140c16808240e41c8000d001c43c84c122482e60008040384105200c0031100c075040700308080250302c0248600140102036001031442010840c0d8005103d01d0805802000f80f01560041da06591500d50403a0601c1d4005c98000384 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 681324964 1250 681323714 681323723
    0x6070b070c020d0c0902030402120307032f1005060f01090b040302010e0604090c03141807121b0b0d061a03270d02010204140901080304030b0601020a0c060206040606090612 76
    0x80640320703001160f494502900010040070040f035000c01d400c803082d0702541c040e80c000e40c0c0101c00c40764510401c5640384519900640825001c1c101600004810f440b864600c03120b200c845065800864200c614100c000c06100d2250368580b070802c01941800c0d0b4100d1503c4100340b070001203152510304441524070a501020b810030108540e500210b44501c0d0445004100b000003c0003941c1142e800100240400c1500160b040200c80c00315445148000c41241150621030251411924140308e91850410300070003150b00a40c500c000f030484c40541d9003240700908038006590b690700c403080202000c980094008003c500007041a094414140c1c0d0156580310040d400500902030a41054030890810300740850702071701c00d003800751000503419005032086500c0c0e041390405042e0000100000d0b900240585840b55100b408104082080f261255821000c10f0044e9140d0714501d448500c1003494031b4100d030015a10507004c4c4010803004d44580001030041c0720b8100800c90803c0031007000744c1c40d040c00251 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 681326214 1250 681324964 681324977
    0x30106120b0103060e0c0304140d1b0204180309060f0305010b0301211b0f09050108030a18030c060807020d11030a050f091c05070801420f08070506070b07 68
    0x501c82d034025484240948000310f24080b180c035110114040b00c1e40304440c2200c1880041c5d000c2480d140d03001070104611501a19402c0c0c2c02c940d94627052611004940041e644252589020082e103140a080404038902039648e11020a0800f40d0103000001d100429604040c43d14004000400405003540d040d18078000f004040c2c030081d40303a500c3d5038020800010304549070448001d480c4500300c49848085410340f50b0b04418655031030043c44100c5a00b4030450403250000c0017400b0b0090300c17400c107000381008000180320001c2e440c9c0d01c40001d0346445070003040c0442c0220041c0f0400503010480809030349040e10301140514040036030303151203004845402052010104a40407403202c0d0a095580c0d10f01c01a01d1081040c41429001a4005080200707071614080c85801040310712060150f0070404a885102c0c0c2d250360400c5140c04060303065a041c6200000d01441455400e294030002785004040080141c4c4800d814002802e04080c03e0743e002e1803240804100031000110040911035200083d800c014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 681327464 1250 681326214 681326231
    0x7081303020d0c030c05070605090406060e0315041a010311041a0a0b0d0b0306130b130b0f060607211d012a2f0d080318031b1c02010203010612 63
    0x80d41c000c500d604c0b0046c407501410034003160803035006014007500001100c007407102543e00d10040c0c41e807800c2004074541640212500304c082c0f600d00c11809811034426942011544210011401c45402c05c1c5c1080341d01c1108052040303200c1c6014007503403008080e8040c130640c0c00c41d9041d00003032905140c0c1c802c468820070042807202100042d64841000c504000e4241e0700180f92140e4000380304401c0003000c070340d0409540046004041402c00c2010100d41c0040340028545403100e00600d840c8000f010117034494010800740000481c03500d417031100d580c03868003c0020941882c101410301841003a0f18010f4a000300240c0744584c0e4807400c10340c80514030404840403242080900b0440c0402e000024000c42040d07a910b49007038048902d01420380c00c0b60719000000084001c100080742c807000360b001d00a040280041002022046040140c417482001164031b02400030148200380701030708644405540100c40d91420903c210b6807100d410002c148000c518660404601070441380418047c3c480160350f99055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 681328714 1250 681327464 681327467
    0x308041a011206050c0d090308041205130603181a180c0d081e120403020f030f040509102402150c030f101221020c091609150807081303020d0c03 64
    0x222046c140a003e01808015030740c0c20058080704060794210b44090702e011410341c04c584200150b07200754010308803481c1d05c1803901d0b40480284c890140302c0700c203809079468564002202c51112142d1050080740300a094078201112800107070032280c50414607007240c010361040f607548000e04031080368031610f0f80d9140d85c5401c030003c545006107000700508a0000946180c080680600c0a204a1003542154000603900c0302072501ca004400c200340440c80240818007d518003035002c2da6000000150040c400317652908005c110081d80b4110b120410241c055810080c6c0d410700c030841c7c00c215400202c12050134100c0d1462101d110007415070850203180c5012500e00e030b020a0b0840001c0004480405040c081800d04031507000e01080240e002d07407000c0f8078000c0c1e03041c004244240d22500080c440461680c070024075004405204c80320004005510320045102c400c1e00411940f82c07010340da41d90145284c0701c038002d0b20190014000449014401d448800000e6000910f00e04850061a0510200c009407a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 681329964 1250 681328714 681328717
    0x61504020c0a02030a061b02010605030c103c14030624030c0310120c090509010b13020c0d11030a0c030e130e0c0d031710030c030308041a011206050c 66
    0x400944c1802803010b242c0a02159810908048280320940749100681460607822230b0b01c140316803a015005040c0e40891480c05030307d03070b00c0d00824600b810455075200240554142d403500981480c4001c03509544095019907800c0a03450142c141021400280b0301c05444e07200703010040c030b441d2040340448500d141d00030a00e0b42000860307042d0390040343c480c20002c0c24a642c03070700102c07190314500341100d800081d0030880b06040421540c012450a15007802c1141142c042c180040c00251650f4842c600f440040c0c40b814101242c00d00c20440c0142ca8020801e000e03401e00d81013281d0780c402c214980803100c1403020088201d03041d02c942828020700c0070b01540350699280b1000800340c0e50041d10041c00c600d414140b504102d000030745110545003902c045404215003150045000f40c0000d1940e00c80100100d903149025402c03a5032030300142d4030640d503a40d5007803a410598200310300050007441840f08102e0480326101954074482902c20710356040c201c00720036451415201a014903220700101d0511040c400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 681331214 1250 681329964 681329983
    0x3040503031902120409060e0a05060108061201331502030d05040c0504060806071e05071407080102040312030b0402040b030606091206010602011e06050a05060703020106090c09080d02061504020c 86
    0x10244d9450b240e40ea0620801820103100e41d0410102e03020025000912502c65540b052030140c442c801d181c0c56990601000094584800c00036650305d10030a145010008005040b00c21040c0560000b509048408510705545901c28004040c401c543c003100140c012054440000071044009020742e268102a542004540e00254200d03240c81400f003400c00700805d180d40b240020362101e01d00340102c42035003600d09041c21005400218140300e0940020a1403112403040c5004c0000c88400d0742d1145002c0f030891303100d503000300e602084203000003904582500804032050002c44d0214105858a0001001c51000514040c45a60001050f19141d5070f0300e0003110300b500960301140d00729a1035a10183c0240049c0800b200200408034240103028014002c4206541c006007000c0030140c5081e050080036000810101c065548904010621607014443d40b000c007203a6598881d1a02d20701014141004039501c0f0550464010740100100503545040810f40c2c0803082e1001680c910301100d83e02e08100189 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 681332464 1250 681331214 681331243
    0x3120f0c010609051303030b010801050f04020702120f010902011805011409012303101202060904090302030d180c09052a0405031005070809030408070515040306150807060203040503031902 83
    0x4c14001c28050842000c0601c500c00d0b10108a505110f00c019a8166800d118155000098818050540c189600601410703440580040c540071900f03034a450610010018801c400d03950380a4190542d03903c06c0812420001040d078070110035041c40002002144029815000d01c0000502d4142d02d074820032031144003001d11000344000307221724694503582d03600642c2c4501c60081d090101056010540c0103080d54244e0090409180164201c180009443c12902c140e05600007403100c4000040240204600c62001008200380ca2540f4908000310b41d20030f4000e0418180741c4010031609020041107030180320710003480c1480070510051110003a220341d8106c0e075014040d00e00c030401da00550741c00180c012100354a8800c3c05588041c02a0303940c1c000da1052140c41d6000c64002c22540c148400075001240207001210710b0315442e91140400d03181d4001d6801402001154101702071103090020001800d407038409507141600d000d00081d66406500150034001d00e61448410042d802003140074030f0000107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 681333714 1250 681332464 681332471
    0x80a0f0e03061006030b01260406020f04080a03080c0f070335180c1c0602040504050705090405090303130b0603030403120521010f090b12030d0c02010b03120f0c010609 74
    0x3c100712003001030300c030f1080101190070543c10107880d40c001c5031850903100c600e130700070302011101e0810034a44c10809002540c040343d003006a0610000c83e40300400160030076000820308451107245c0104003440080c240b0a4040003400f071441482c070b2400c1103420321a01032a0004003c8903030410040c0b03c0281c0300b4400201c0c1203000d100d1140f402c0c050070080c81518a2410045140442c2d441561900010550164400035580d1480c81001c034015684901e1401150014200fa88441c00300e8100c940035150203001c04c001207410411031038140030340c40e40050a04040e6003142001c0640150407185030074003c145c01118000200a0b0b2410000e540055130090380e00d60300000008006170065010384030030b41c4090341c0b00811140c2880c114030b1040c129099089038681c0c007440c00100f800140f4040c02d00c16071080b0105200a021001080a4803650f4000c40001800d070644d40d0020342154141103240d0b000b50400f0803450819200003054452007407001401d5a600c0c140300802900510280d00710000207442c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 681334964 1250 681333714 681333721
    0xb120c01090b0702011e2109120311041413020315090a06080c040c020309030f060711010501152714090702031309021312140712080a0f0e0306 63
    0x904106580007a01d4030510399485142c0e01c0068864054042d0100b070070781520288030f80c40d210751001e641c40c0603c2c14081d2180f140180300114148074004141064035600c046082c802a04100d919805d07181c01c0c1000020210840b5540500540c0b15064540c0d8080342c00c0500d41c3c4031181c240313008000c4550300f1541c030318000c0003d80c940010018a18083d480c1040040c00f84c40c103a21a04c0d00303656202e0000e10b20003001354200005003003c0340344501140000d200e1580c198504011024161540401408551410700b1000307103034218401603a080daa040c10010011108100b400c40440701e60b5251070841d2403503118a86c002e601096001d098010540708000540d41c40c800f0b0f00380160304085980d01243d49038818206e9881c01085500000d2041f680000c05c505000340c2c0c010404241082400c564841da0380a180e100c45464020503200a0100c0001048010081c02010060301ca10010655803a40540390841c190046c40c208600340800100400401c5016000509680c0001411a0311528 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 681336214 1250 681334964 681334999
    0x307170304033206240a051f02010c09032a0e04030207090b121509010f0e100605100906030209060f040b0d0f050c22080105010b041409040b0a0e010b 66
    0xd0b90100c21043c41808036490084040000c40c5050181d10000f503401414450541c1e1001c84108800b040c681c000100240001d02da1581076a5140e48800c80382c000b40c04c0c8901460207030940741314200e8a000c2000d40a0180001964004103050001c14400c0060340814842d84946000c0c140da0440e1100c464084100001c141d8000f41e070030240d0714082c200340040c10300703c0300b4056001e41c40d41e146580d40d00320508080004001c900d1156009030404004960300ca00c1140d51012103400703001002c556003000c0342040c0d484c2c440b40150070042c070003038074100c2204400b01c1c40109250703030070b005580030503800095580da40c1e9144020340318000d908203641741d17545940b40034817845980100712404030141006410260102035108107071050051402c0d051808550061540c0d202420554010a40b00300c400c02240d010b0342407150501906e4094210390340c50382852840e21400c0750003c0800c0c403c40342c0000f0000000c0405006c00c5e0042c641660105078400c84030035440c05445c0452101e50072100748040c0c00c240740c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 681337464 1250 681336214 681336263
    0x60506041a0d09081611060702060d09032c0117010e0c130e0a0c0e0d051903020f010c0818060709061b021e0f010e0306060f010221070b060906030717030403 69
    0x8038803800444445102c6c000600c0391034000c0d0380001e944800c0c01e03c034140d6403003410340100790614864507001c040a807130f1145542e0840c4000c03071a1004d100b4000c00c1a030300355820041a0314030700030940e5035201c907624250f10700203182da004102400c00c480c04208009032501c0748070100054850700c1140300d828600060b00500806003011700740300150311b10340000b07060304042c6910b601c01b81d0400b01400301000c8807103101040c1141108124114811050860500102817050405441c295a11182d003420280040c00445107006517480f825007240050041a0b07401c2104081240d8040c20300c04c4680480404010642e490401c0282d0040e003283c410506500d509030821110310421078031a40002e00c0d80c0011140307569007154441d0940d200b4070100d070f0103250140400c501984148110380854132040d407506480140610001005100814001e041208080006a1202c001c8e60b25070f245160820000340d4609891044030750f501240d0700b5100c0b62400c284100c0b80610b400070b941c00c44a905110f0240ea01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 681338714 1250 681337464 681337507
    0x2318151903112701140604120f140715140c012c070b030f100b0a1106060f0108070c060f090c080d080717090114040312060506041a0d0908 61
    0x51421143d00e104a00e1582c90b4208031401e40c040301038466030801440f07030004c10900d582d940c1d00c2103051000007981c04260918010300c501c135101c0b207080e03640e151400d641140f0020100b29080d0300000e034140b04000c40e4400650040220307103401c980e000101000c0312024450900480040c1d405c00c501d20301c03940900034010543c001ca556000700d42d0345d80c1c5001c00d600c40f0784a000361207000d00c04102154041400d84140c1e27400101004aa601c41070352100614816031000300840007081d810040c80c0302c028000c0c010309902100660301011040b061200091003030710002d003034800344890445190280950fa41c046007950700200c2c000c01c83c43d261810b000742d0521142c456031f03050344100701144100300d10800d003890003468103807a1014028404030b045050b41c100180410b41079960b0300702e01c4500c1d000c1c0303101035405540a925000120f03016111030b20300340c521a801090103910100810049541042074040040036444910794584507007221420141100d0140540304404c003003501d141c807007403000d840f400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 681339964 1250 681338714 681338719
    0x6090308010b0f0d09140706120b1801050904030e190513061212030b0603010b0d141b09010c050d020102030906090109030906030b010e0406231815190311 68
    0x3803681e6550700741c406501c9251035111002c102400590b071030b0b0410760405003045100c2e00b400440b00c1181000c82c0d20f030a00c141d10200004004840c0700c0700c55011441540c01a003800d07141c0600e480d0403a8040c0c0d2500b0818404e540c02444004000b40525124241000701c119004000030500d035141c50089540102c1c030f02840f48110080450703062451000e00c155800c980343d55044c02c480c841191503580c410119000f41000307140d210314041c000c0d540c40000450290401c204581c0d10b442090441000720390760480d400288034020030038428203111803c5020000780502141654075440200103c1d18a04000c0004029204000300501c0700341d01034010314450350040c0c0031a0050b40e20a031030f2500303030340c81040050046540d4040a004040c420f8118001c4102c0c1814210110410030b00490200c032442e40c445061400c0d07000140a070401812440956100f0440c2c02d0006c1965600d0003a00f208405801285030b89a088481440c546030641c01c00501c3340550b04010202c0e50341e040c10080580da0030541403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 681341214 1250 681339964 681339977
    0x20a180b01020f06040b04020a1707150302070c05150c1509060708010311090a0b0904061d0318060d060806130308100305030a1d0409050a0203161a0304030c0f060903 73
    0x895100080f001000c0e1842e500400694070b03540c0310700241001c040c2c81681c0010401c980804c0d00645c0b183c00304c03944960100206442c0d464941450050482c209656080600405c440804180a10403140c01d9600c112405c01221203400c88038040e41c03203071a040742083d0155058200d0000c1c00e0900180c8104039210941d9501e42d5041c4084502c10000d0000400b6469605600199030400320406a480550f440000800c03004240001c1c1c10001c04440803142d05e921401031484500c7c02140c01d41d60281e0501c0250304004241d04480f10a45030250341501548021070849034428064100000800203103082e9040360400f581c0d28000401c0c058000d6001ca81001d011401c013481e440915803c13260030030042e5003005030000088814112107000c080303804e41070000203401583c0e01d204030903500c0d202e14028554013456206060829400000e40c208003050f02a08004006819101d001d4580380e00e91560356960310b919003501d0401c0c40d60005007201d0558150401005a1a4000d48409000e40c5814 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 681342464 1250 681341214 681341231
    0x52119051b03220f060f0e150a0f020105010b1806070b250c03050703030e01093305010503070302150f03010909150c02031b030f0310050a0819020d030c020a18 70
    0xb109032000f5115440803030f14480c100300722251140070782e050f1001a43c80c250701c0c10007015000600342000c4220728013080b400080c03e043c1d80c98200408010441d4140020b00c5503601d080d001607410b00903080702400c21183e80b0081c4407690f86105c03c481f0640e40c04401040c0038144000c14400700c5090400c4842d140000c9100024498040d10381c0c00310690349a52164684030556504070b0161141d0b200d90680e564072007004000003500c1805845a00d0043c0c0007505458241803080c6129450388503191202918000050190303440100e100c1007500e40580c0c0c003203010808005a00c29134400c920001c0c811100c04000850706c041d0a81001032054060352a65002111007242c1c407003218140b41c2100c000d0303072041180040011030480e0f030f054a0081175094071f051982010b94510586c0c001c403000d4000c044007410500151a241c00681c01829040009003d40d007001007a40721480440c00c4007134400c0912248a20826218400e00c4070015805061181640d554030004026520159841e66043d400c2031100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 681343714 1250 681342464 681342517
    0xe01020706050324060d0c020d030b0a050a030b04080c060114010f0509090a0506180c09040e030f1c060b0a02010903030c05070203070b03040f0b01030b04052119051b03 74
    0xa513401803041141d0b00102400381030145201c0e164980c80702e43c02c198240840301480510b8440d440f00b2240d25000790102031400c841c01400ca0707100300005c0c3e1151090740010f01090311100866002e595000b1416101a22203081031035090045080e0034809210b84400441c0e40c0c25064270800b0444401c0e00c13404402144a0420b4413680158601160080f03040383c0040e880c1501070304256008007018108141603041c19030380030360b104030032540803c2c02c4500040b0800729060601c501d51a41e001d28015500306486004c00d1079480c862050400341c5288980310006142501c1d074040001016030780031140c0e640f000d0354030290103821030140940c00f103481c2c40d40b80c55902d80038a045951040e401005441230a041242500042e0800f6005554030503072900354600155696030140d001c1d5001f1100441c20303103040d2410f28034000107010b400604594a031440304071038003c1c0055411000b510404071071020b40c1c42c2c800b103d60780600c1450120f2070550440c2a10505004401130043c0401004015204070074a680c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 681344964 1250 681343714 681343717
    0x1b080d030501060f0c11042406021207060f0b0a08010f0b040209010e0d080714070e160c03081b0d0f0b030106060504120f020301021201081501050901062d0e0102070605 74
    0x90036011032004000c41101503c145d000c90b40742403040280c81403000000000c203040b18591402c1020900b4940c00d0328109003e41a00d0000a280074070040682c2003800f1039101d1107003c0c628005155517242e10b0f141400a966810155140a01034840100c4a40e01c82c0f00e81d001c2c02d80c103070f0500380503841c0001e8080d65080c9030084541d03189040c0c4030b003c00701c01103c0610500b0200001c3c00d84090318140160000280a41c0d403c041031008034000708015030801c244404540b2000c1c10480c0e1400c10300240034455508240f28a42c0c4075054100150156540748000342000664691620000300c0000c004a102d81198007558200901c90010412480c03503105143c01c8480900070040440c9007840308104400c614040b0090b640c1c07158201c1d59581117580d0120703003aa003008030303000306019000006001030307881084000505141042c8440107540742c00040380d80594103004100c1001141d0705002c1108038aa01c400e140302d21842c2050700201003e00004200b20b01a440e03990042c040c2420020342548074a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 681346214 1250 681344964 681344969
    0x100c08181507110c0d0501061d01030b0a110d0509010e0d1728060f03020f04140103080d0e0604061508070308030a020a0e120a1112190602071b080d030501 68
    0x700708035a8880041c241d60005095000032074a1040c00804c40c11602c031000300d812050701c10000800c80c00d0078800b820000e02450301c141540041c030b5038010004600d11407407654006210309800140d414600724088980c0c400c5a6030101458142828442c84030415489100740c40920320554401c0407600c9403c40d1b03007240307406680004558440100788ca50081829210319954052401c24a6158916214003940c2480e402000c46082c20300c010405c3d82000380c00320603070060481e0200109440c101030b1219869041c000030340807000200c2c10a01c089441c0e4403030f41c465944d1100700c4080703140a181150152070300070140350074000c01d44800200c8130380008584003070329400310100d420f56860611100080d0440c0c405901045416540b12a40d80c440c0000003203005012405051100e000f814003500b880c10f5842898055450710030b440200402c0407460191101c080603000341090380703504206010340100b00c030140000c44010000140e011180803a001120354a40a071001c44e4500c130301c00d6088680c00d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 681347464 1250 681346214 681346243
    0xa02030c040c03091502070c0f0302100e01090b040b040320011211120109150b0c030901031503120c050d020102071e170c01090516030507050909100c0818 68
    0xe03003000c111450150000c0101c071001d0301d000100049142c5800000c4081024141081907000a004d018441080c018074045e00c032722a5098131003481c550100da111490316180508000107208040f484d60f00c81d904d500000d1068103070694450b500d4201c2e00c10301e036015100840d140c01503140c2d400341ea11090081c0180d0007005850b450701d100c24001144015042403a480c4050000c20402d024100510866407400781c28844000142c039001d80d654034000005603042910078000c03d02074200d46182c000101c4003421402c0c41c006c26102c512024482ca10794243d080140f48204288801c046141c2c00000000403902030340445050000b40307003041c5e01701d11034000094824196014068914071440380310b4005c462241c0600d00300d04011a40c08006034010700c00c440c4d841e9444504000910200b002400100520500b901c0182895607954681c0d4014a200380c5000d41d000c0800501400020b014091040900c0d04090140b0003400100800c03031001202d401e001100e4002650010600010700101039810b40c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 681348714 1250 681347464 681347473
    0x406051e101202210702120307050c0f01182d080f070609030f0e01090b0318150f0604060b0313030e03030c070f05040e150105040c0903060c08090c030a0203 69
    0x1800c14000780416004104092049000e24000000354920040c18a00c2d1001d102440d110040c3c041c40c040710314003400c56005c40d031005c0c0c0c02144104c561400c40703400072075500f0402d80d0341103040c205506040100c0c00c1c9680c59480d024185451a40700b208010002c0c0c494075003001c2d0039580c440100fa10480640c00c600030043c0d59958940000c113820700408040082d20b5942c0c0c02e045180e6513090a4598184040b00000e02c14441c69841c15042035001c0c20780e6034242002030805d0b0600c1c4a10343c00b800300502448190388a1150915440d00502400e00590315480c0c0c4400d05140012401601d240c00780d40041c0560714055000821410381c5069a000c0d54540d41000c014030100d03102101e070030540d16400340c1d01d03020030080501c044004001107230003000001030154100c0c0c501000c00085807494400381c48a80c02200500c50213500c1161201d0565204035070004400140150031100c0e4401a00000e2840d03241030100480c40b5005005c40c0c0c441d5841c002226000c24007002810b44540704410000e400d60b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 681349964 1250 681348714 681348769
    0x70309050d0c2913030c090b01082e03031e1d010305100f0305010e100e07060c0501140c0306040c02010b030a030e150a080906130f020d0c0e07050405040605 69
    0x4207110f903002c0c00d84112807100038804034021900682e408400541400d50014104000700044030540200425501a0411a15180c040080d01d505401094111240360184030040d4a68a210300c01003045030074410219000c2e02d13450040c082039148228854208000020032140a100e4010041d1042070305109400e050507000054024220181130440b2030b0048040c041040f004003510000214054000801d100344e00c03004407824140b02c9034038200760909204211350008030025400044071310500e040c030b00c111400e0510038014120b540303140611200d0b003010312042207140d10245010702d0084604100c0c8540000e0203074203ca880040481d0583c100700c66850110b40600316200e10b001028103240117180368001201d0b0341d5801100724101080902052294055040002544c00a4030500c000420b1403e0384500390103642c4020300901c514a01c1d01601c041181c0e40388104010009003c091203a401c100070094859045401918000c03032400c1c0b070008140c40e04910300c52079410500003a40d42c205 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 681351214 1250 681349964 681349979
    0x9060509100b0a11030a210605060a11030d05040309031e200d02030a050106031403090306040f03050918191b0302090102031e0318061b03100b030a02070309050d0c 72
    0x3c020500a00500c00094a4101c41401c02d1005205000c0c06940e8020170401601051400219060481d48040c1c54401e0501040c3c46580440d0500081e9041204c06145900d00b290b03d1841382c00c8584041a0901060104150304803140e10181d92060100354242d0200c0203242031000e441504c090a602c00645989a00502d070091000f0310060152000d5600c2800d41c0102e89054007070141101c8a84d0b440c3c208000784803400f54617141600c0d411026510b402d550070002541e5240c064005003490710041c807400101805042114000d40b4081d240362846203801604030385130b48040b030303d404421070b404e412421244124400d98442400b40059428132581141c0114025000790888505600c1b0130400003e0034074880301014501d062141b01b0f0395a80c9040c848100851003070244400d900d034001c3d42070045042021401203083e20800400c03a449542d03085294044410740c2d4000700031242c00006000d000d0746150000c12074203002e51a204001c0340d0b0344042c030201c071910312000303080a20070800510052 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 681352464 1250 681351214 681351217
    0xa050d0f020c0604080625050d0203071106270d0c08030405070e15130c0c0b19060303021b0307030203030f030702010b101d09130204020904060803031009060509100b 73
    0x10306948111001a2860303008103440398844d4020042a500c06020040c0d1050269640a504000b480d40c40502002103200a40303680556903c04100c1c0c0d17008000112220721450201d0817a40ba0703d07088402c24100400642d4210340701c1766070003c1f64010085100d07201c250000c2d0001210740c040da261500c046d90782e00c8ad160142c20180c802c0b03405006203680050341c07502130301046000d001626104520040030200f04454190a070201e03014076420400300251054014a0030303110141c001c07000e00501c1d0b440b950010756140c02c0017200411603180c404c0c0881856400141d034045103c80d01c000205031300d050b20406603074503094480250705510820030b01c800c5290200c05141c00c008603000100d25003804100240f49219041000b40004401d220100c10420314481c50f00e404660a44483d20316080139400c02125460000000c0d018075000280c0c44002c0d1139582c0070030000c003800e04c00c0c0c98907401c04080138400780c90144a125412400d0800206040c5080510349000e211045013602c4441e1401e84011090b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 681353714 1250 681352464 681352487
    0x1508030d050c19081005091b0c0c090c0d0e0a021012090c0b0d0c08012108041509080d0503090a031b0b0a060f08030c0a080c031c0605120a050d 63
    0x82c0d01d802d1054085000c418240301003080306035207580d50503103400039400500e02c00780d41c01079125610703100c1406010f03010002c02410170179180000e11b03aa5846815010b1510150091180d080001e4408020082c020301d0040c00440c56400001d1058a0b03240402a43c6c0761700c0700c80060745c40786002d140c812620740076a2080e5501300050401165401d065214a40c6da00c660b5808508451400102d049034034080380b059103090403041c2400440ea506249500707200015841e4200100d04e8680080020302070300c08150340003007600d100034080d000f8106000034642c00351032044000340e216030030881841c60302074000e6a12a01c6800000d040c0841070340c0702210180100341d0b51a900c262206002d0b00401c9581c031708540f0805c2c620102041d420725114039081d034400b0b140c0c0110140c0d0024003822aa8404c007080d0203a4964002d05201d44652003c0c4c030039403c0d8400e5414035440403058144106140703040e500f00c941151001c5440c1a03002c0d05070040c2c9070712611100c3c0020a1038000b050300d55034041c0114605e090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 681354964 1250 681353714 681353731
    0x5030307030c1205101716150302071e060c02030c06060103050604090206190f0c0503040b070c17010902100e011205040302010615030623180a090f060b03011508030d05 74
    0x19152000550b440482c0c1d0251204017015004d0341052048000751046042c8032400a0002d01055010005503d44507007180507224604030782c0d9819150641c444d4041d1740200380c115a81d00c04400720410341901c02091084121205030a1801022215002100392216012000050030341ca0703581000450040c00d00601556201e540c6624000c00742e1501c0000d4180d260704e0b5418000b402c2100140a44510b052048480c100210b403201d42c00060008003e03102102d8260301400c0d2a0200c80c644201c0c51500b46d0403000c0030864120340101810015000100614002d40c0c0c1402480c4058004654000d20b01003210301150341040c035201c080000b940055440780c003d100000380d2548545104a02d2898126018006a1111000d001305c0c1d410038128112201502820352400081002013030300000c1c8048103442c0c44440c10005089418241c2000e1a1154410100000c420203481c1c008010040e000030640030350319003010790300d01600043c420429119447d0007182021400c000040203458001d24800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 681356214 1250 681354964 681354977
    0x6090603050603150405010209180606070b060d05060f010f0608060d023304090f2007110604030803091603051b0103110d020316020d052a070b041a040305030307030c 73
    0x12813a032081100b20300840c0b140001598910302581040781d01c0860b600307860040d8000100788201562500200d41e031965100e80c5036400341c1d41e8000020150b011401019225008000c1003008059406000c24140c40310b5402d181c06141d290181141c0c0c1c1c1704110b42c10340d00020500004000340c5006c03038503031080400c42e5142c150789102010300c2c20b0711562a401d0100d01d0744001300b42800441a5030059400208403c030080041300e82d4000080401d0711515087d0710181c0300041d40000307005400c1e43d00b181500001e48510340d030b66600c5c608806c4951048410748003030300614801c98480c01c48005c40b0411241c02030000c0c82409006030340e50303400e00440030b542ca040c184d07110302c9944d51006140c09040c1c40c03142031600580760310303041318400c064011403c3c0c200c0441d000311500003202030700141590302810030200007500c06581101120001005980552400d204005000805000240040c02602c1a07448046d041e0343d6240982800d502441c00f004007140c0003400020b4006100354030807500e880c2c1510300f08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 681357464 1250 681356214 681356233
    0x41101080c1c02031b03100302090912040602031201080c01140a1205040c051206010605030f0a0608011d0c010903050304030b061f0e030118050a030e061b15010f06090603050603 78
    0x402c6812120041198050b4000c8204002a486000c03042480085080202c0c51071808080e41a4170840c5800003d1158005602140c1a10400c011202c4c03144d1041940c0c070340d11074071203602030b60340e421009044460424035400452081804220451580c06c181c40f5500d000004546108032500701c40c01000030030010034980d00d041000e80c000d85000d14010551014014100414840c54000031004d8022a500c280300410850390b0100440740c0c051241007100280751074007243c00024000c0c55008034250f60034400c011180c0041c044d0070480c040c01103003c480d0302d040c0041c015101c0d1045840003070940d82042c0010404504c0c60048942d01c0b0000030710b5038021000054420210402c00c148500c001481002c0d000381508003449808125020a03600072910003582e039900d5a00c0800c900d0040c2004503102c11150207883c0d0744161211111080c00400ba61109560110340d1800c000b0303031110144071814000a04000c444211906581c02541c482c03146908144081c3c016010282c4429014031500130302 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 681358714 1250 681357464 681357487
    0x528080a0c05090a0612050106030e06040f020d0204060929280314060405060a06150c060b060c01020a4d120a080601031b0e0f0d03081b03041101080c 66
    0x20001401546d21000060081010300b001261b20580015007418682720f80900d8041000841981c800d510105006614106101049205124000094005081c441d022403034001d039800c5650008044030003e0160b0142511a540c00c4800d054010f800440c40d091003480d078444904500c5084084800742e0034249e5803580c030080a0581148801d0b503c2d00000f00380800c00405120709904100c061006005007800c041a05105e00201501ca100344800c0307400c0481040307455002000c580c40000c045545030301005040501179401001c10f2400a4108501c05150030402c1907040c805680d00b0745021660b80800e01c140046403400d035400c0300310b1949124601c00387d0741c2c100402c200050500c00960f40385d000c00d02018000d0380e805445141418105500707000c0207102d00403101e01e651214601008011a0718001c11610542410f00d01e420042001036401490780159150b409442c05800700c5045881070311429850740000d9500418001c42c80e4074203582584200f0356a80c001401444c2c507864880302055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 681359964 1250 681358714 681358729
    0x1e1f0515220905280302070f08031c200c0d0212030a0209030709020d140114090a020a0c020301060f050910150e1f080403020c03070b0415110601060528080a0c0509 72
    0x102040072034040c0c00344c2c204060341800104000c001403048003104038202510a9207038000d043c0c884180506041c202000e0341c00580180c80c818014803038600c1461042a20b075030041d4419140410f5a1280b151f020320f92920000d4500000c0060303400c003506546503141d0000c041d40c40240c00a80c1340c402c0c84400301d42d65501d84000c0c9031540c6002000650003401d50381d0300d142120140e00c0700450001850340358216440350460345038490380840e40141c0d20f19001400340c0340c16803220400b81d015031030704030041090340d030101c207004c20355008130b8840082d9034824030b0001842c0c9550090b2050b00860365220f0f19040d0150710b11038040c44005185010450380054401ea68011003111390001401d840c0920060580601040d255140c06030050706129061030303801500c510603441000c00f00c407100c1101d055150b01c21700c91014407031060002e8030002d50307468000414035007040d4100c0044984c0c400c000b4040ca00440c3c2c060701d0300c0500e034407404200c1c1c2d21040e80d04010302c0405000000d00c102041140c5581d0340704038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 681361214 1250 681359964 681360013
    0xf07080316060b12100605180c03060d052404060f0c0504031212020f0d1a010c170c030c151f0302010f03060801020c031b0706021e1f0515220905 64
    0x78241d40780070204100f15480400d44013608d400c480c1444062403905003200d6002d03000340c4402400364500e140262030084480044100d404990000900c052280c008450146020b0701c002d00c04110000112400c0314056102580410000c000030000200c2c1c4c00103c1208080f142083c400540c1200c04081c180d0b48034581841e400e2070300180c0b00c000800188998804406114003268102c400d6a00103045115500c001a107001d000c8004455000e05040031a408000060b0549032640e8550200b41d540721095110b2880380c1c0038000c00549035501401d0001406160340c0006070886196400560f00340e03010fa0f015204050700c4420114000d1001d000900c0345815950007503549840c000d40c12506140c1e1400d4146040d00f1507003040010030341c00074045c0010160030540d400d4498080380c040d45030400303411144440d11605c02c2011004c210f95401103105000c40d68040c24408207060801a6040421110313207500e00d50200c0f00300d801c20303041d8018501e491198084480c43d84aa848042102d035000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 681362464 1250 681361214 681361243
    0x513030804050102010e1203060409050118050303090d02060c07030e0d0501060807051c0507051c14010c0f020f10110c060c0702040b0603090706181203020f07080316060b12 76
    0xa0402c003070b5909101d400c100301000d0000d000700f45182100314000d4880500800e101d6625070f000c15003484000c2d070004280303440882000ba1130640c80c5c988035840360400c80e02810700d40520b40c40110100c1c00807508900c2a500030035141e161203070b65541a103082542c00d8140381c01007800c100c2c000004400b40315030805071440c00002d0000515010420440d44030040d4a100c5000a40c07402200040001a485080c1c0380101c13001008444042c5064880c0220080e02400700465403409190000040d401119038040f03c2d500c140744810b0303448082e603441b2000300d18464160b00c070f581030342c11080642e8440c0b44c4165610b1089880e00140c1013030149062010f540103046000000750f00400c40c0b0f03051080c2e01d40c003c4156146401d45c031b0032038050794492102d03108100a0140000c01001103914901800015091034540c03074030004540d007002507a500303508034200390078401d0140104410000105480d92458004a031209605281e900e0f80c0262041003801600410758090980305d010081c4040c0d10400640b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 681363714 1250 681362464 681362467
    0x3030f1b0b0405070314120412083106170402100504150306050f0d0312050c090a1211060c0d050c0106080601081c050702060a2601080a1a090304120305130308 70
    0x40d411700381b16540c00814000e0b01d40d404800c034040c88480500c10780b800c550003503044400d12181420000064800c0f035010522100c01c0300c90080d004090000e549812207545295149060f4481c076003951a01100210510540800d5001400524ac440c0c42c00c03074480501d00e005403c0a03030381c00c19041030800d0115000007003a1511170500c9030741405042810074400c11620150320300b205031005490740c00e003401c2081c401d41d2a078000900415680c011100e10503030103807002054565400031011a281d01590465400d0b00184030b00b0418600842075840c8460601c1c05007003801380500069a550344001c2c40000107540720100018450310910103a8000c100240282c002544031000d64102e1a041c3e80604041c071078188410f00141c2c80d11800d0700c210118030708001d01c481c01103030054005010040c0c00070000c00c0e00700001080a200200b00c1c0e0701518850920000d4000c0d03036208400f90440b04407400100ca40c4144410002c2c180740b021440b41081c080e082003850702070100d503019a11007542d0000c2d10003500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 681364964 1250 681363714 681363719
    0xc030705150c0f0f04050d0c090b010305280f02031602100c050904050601030b03460201030908120f19150306020a02010605061201030507060903030f1b0b040507 71
    0x8040c01245100700c140c80201c04075207800203105020b0f0251800020480f00d001c540018452400812900a090010900b141503030340f03850701d03240c003010b140540c0503410b081a207408141d5000e80100c6001d414480c405d0079218000b240b40010050901130301003501911007034240e00c10060740c0700450051101240342081d6000c2c0300c070064900079011a061400900d005000c1c0340c065030003410f981d10040111400b045545807440100d01410901e622554140100002010403c03078120301100c907107829100300791581003034500580100c00008a10321081100740c1c1c6010040d84030360b1103503500310300c101d0b1b01034101101d564038212046000c45035046501d030b03910140300314010900400c0f2004000b0160038441c00c1d0000008002460303031031200505a0f9008240c24400d18000c1d0813080203003501500c03040c0c0721004621503d44220084c030013560340303025070a000304009100b6088141940c0c1c02d602c070100c14000c180310449006140542c8080640311030400352000400c2c03040c025004078050b0004000660 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 681366214 1250 681364964 681364973
    0x30306041410050f180a0c0f030902180a02070f0c1d07020a12030e0f0303160906270b0c0a060c08060f1509150c06010e1314010b04020c0307 62
    0x111045484103104001d88100002031107502c41440c2034a1042e180c1d03003000741022001c510600400b0694950000396042007007104140c60f8003002a4003503d544510551015400c1503084585048011b9000002200c8031140c217481c51014541048920070018a881032507203c02001002c030b0a0100c0304a45d10410821519142e091030441069039140b81c00640d0a01c140069a5180c54100c0104204491104c4482030b81c0240c0c03209001d251480280c030b4141034a44403403500d0750300460b40d000c5804504507601c1501e5100311000e0041d96402d8076400101c0151070a1721074140e17241410360041e0140381c4030110b030000c1c0000141500c10b0b1600010619a006c5c0d01e040d00c1920019000350342040310304403c0040c284d031092820b507544141958241e8810442d5103203052540724541203076401c04c0030100708101502056000788409003140081d43c40c2c0740d0302c0d802c0103001d40000381e035403180102e1a410034002280160400401e100801400003400d001e02c0e40c003040598100c0711844500740c202140510500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 681367464 1250 681366214 681366221
    0xb120606040306021c0c030612060b010e040f0b0310050106020601060c08090d0818030109080f0d0e15070206011401140a0c020d080c100605031504300306060f021c020a0c0803030604 80
    0x1154242800080e0070030300402440c0648003030140ac42500d45086100b240d0207031078882c004a001410a00ca02c0e01090201006801e01c444024064401e61640e198028101d00c41c6d0b03810f8494a0b0b024000e182d18240c402c03035041c015540e060301c00b840d0422251050b5610004040010f5200314101602c0b641c0c1c1c000364000c440041c0f01490302a9040203d0b140004100b1001c90301e000d04410b803c0c40e2100c0310f400ba040000d00c2403030b03520709440c407805406c140d800006804562090646a00301c40040e82c0f2501070070065100440781c140403840e020301c114003e0349480040e02038213199141c410152481600010f003502da000300c05503150800090740c02040c02081c03002e880c214410140500c2581e1034240802d80c0e0b007800728800c00070182d01d03202060410000c222824a0850a00030005640082043d2000e4811054800502192912000040c2e03140a904521400e180307540150010100c4c10010311303424010118032400318003e0310003c00000b04a528030501078803a040045890340340010a002c00c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 681368714 1250 681367464 681367481
    0x30b09130510020d060e04052d1b060705100501150203071a15030d1823010807030f0c020304081621080f0703050304020f0a0b120606040306021c 64
    0x41095400003001044000402e00200c4501d144016918030030101d040740203010035007000403081c1102c0140418130600040500790224011841648218000341000820b60410030b070a41170340208945c120003a94025034408100c1000c6c111515110b0140c0d03405050030b5220045000340b40d9604014088030000803040d403012011400150315220b2503031149101c10040805000c083d407201000540e442100400b200749030f5002908072070307420220040c0501504417207906110510402c2800107250500d80c1c6844060918112101c00c5071100304004440060f070050400b0181511802180307036001282c415001060b89550140d900c40d410a804a800e02000d04c10072040c1e940e9181d0203215440701100318038a072415044035002107554518121303440d8040d80d0f910045101010070aa018507400c5002188918400c951030860341040c1c404000c00020107000300d00c541c80040c0721042c04680296009034103d1401000c413414984e580e600e120907039100c0100f0084c40d0040010203a10f0014500801e9032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 681369964 1250 681368714 681368731
    0x6090a11090622080f07050d061103070c03080c03040c21020a12150c0206010b0d0b150909091506042004120b09010b0d0f060b1807020c030105040c141c03030b09 71
    0x85c8038000c0c04400c2d5210a0743c00303003510038103181011504000250780400c0803c4184044103440c0e103440b41000e445403000000a03008191184c001601c0410900100c80c426940042c8000b07001c1d05100810900105450300302c0c0c0c1d40000c003003001002d645c864442c0b00080c520440c911807604024540884145865028100818100b1031400300c55500070030400c0c1036405502d03070a52244e500400c684050115100081e030000c20810b540443c00d1000c0c4018000700304161480152038892241a42c0e0300c2c640c0c10742a0341e0b001d201d40c01149080c40d10303030000c0e690b0003084030700d58020220184a2030416480b50707000320b40014080c130002040000c1d210341c0942c0301c3c0c0090002c10510380d824000c111011842030000b4800ba0810014004001d05a80b0078640c603d0003600010031340b80d492888102500043c2c2c1c1d01d00143c45503403140354161805000d00d0348204e601a800c10f82941c5000300c03080c001c03030f54800e2499000e480c0c800700729024005002e407524803c0c000e40d008192001070bc0242301180001810266 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 681371214 1250 681369964 681369973
    0x1e0606081b0d0b0702030d020d0c0e030a030807030e030904064523070306030c080106050d08091513032603160909060806040b0105060306090a1109062208 68
    0xa0880d9036000118030b145821a40380c140e00d0342c0e442012800c0d8421010100c119030300c08207504503601c20300ea00801d00c4880c0380c1c41e1002002c810404256071030059040007400100901c00107140d813403081d00010364100810341200e0404860500081c1900d542d17420002c42c0b841c115030100d91140d00c000c5d48150083c400e0324041c000501981c5001c112a03080040390100d20703103a41c22050b51003040e01c85c17000110900d03120804182003400004000d85002d00c015544050205c0d40814200d02c1032140790f0403204010400d00c4039075000c0d81c560903681c00580c4410382c001c50014040d00b40b190064020500d64020040491046d81546440c0520313800a5400303200c16034021003048440787e041d00482ea08481501d07517036011103400300d0707049403401031641007121114180100020000070010b919406148645440c02541c3e0700e5006011460004550711a8070076100350128005010f50ba0109450442240c0d800e4a4086c030300c004618650f0218016154146c2030420040c025115003848002401c8a40003a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 681372464 1250 681371214 681371263
    0x6120506040e03040306050402031c0513060203040807030f020d0b0709171c1209050f0109030206160c021201140f0402090f04150b060d14071e0c06091e060608 70
    0x7541c3e400350340001021150313214080380075987e0401c4207848006008803079101c0000c0000008009400c540e64241c1d00c0c00c034110b0040740f00b6002005035426540d42a00078408140344d521041e0185408802c1660800c5e90403038000045510403103514841c1c0790755104c0707248040c1343c0350980c1c0c01120707420245000c0e5049a40e048105c050180044a034240c0185062640c09800f019060000c010018000300306110740007811540f120b043d004050503a01a8090314010740d582e01d217540041c00c400070300500041040c40342100500d02a4009084144560700010f6007030214004c00f080560140c40c0503044a0b000000c1204501e814060207912130650080301001d07013407561700c0e8054444034290001425850703041981003a2542c100f07442c0700d8111014207100c0703402c41400200c4111410781d03000f000074042c80e10344503c03000e00c854050841c0800d540d801452590a0300e58200401414800b100d1a440403030307200c11003019030001d6107580e5002c2c01d40001d250b40341011040ca40300c009440c2c06600070030500078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 681373714 1250 681372464 681372491
    0x51c03050a2703031808012318060a090c0501020c0a0902030c0f030f090d0c031e03020f071202010c1b0b0606090612061801081b06040504060612050604 67
    0x50703a80e10030103810401081d4144129000b5400301c041542201045046000818168441c80c0008588155808a9540c54517141d10509a455402500c44504c3d280345025410385901603055074846070149541d10456040112103040007400c1d42c14595540d1500200030500040500880c001c1100740014100c441007200410b00d070300494424650400d5001c000101420040740c200c81c003403800041c0d03071540c0c1d14080c00d00040111060756151018401c041030b000c0100d01071683c0007112038064503000d074560344030140b08900c50300c20b8107900704040e0244002d138207600201001d4001144103041401240190001c002e084808800c0004104260200301c2240b41c0030301d458080f190ba070400d0344a40169282c0e40803826605c01c0410007900142c0c005490300f601481c40003854003640c1d0031151030ba808180503c100303902910a001c0c1d00e00710f80241401407103170145003000040b0540050320340390800750b44200103002c59010740d02140202c1c0b50301c1c2c07a90300e0100c00382c030490741e200100b01c0c0c0800182060515 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 681374964 1250 681373714 681373717
    0x80c0405030a02010e1504180f0902221107051005160903030e0f150a030e0c0609040510031202280f02130603060903090612052e150207051c0305 64
    0x4000e41801711075081c5410a03220b0940d0058017040c6110000e94443c1d072101035030303001c801c01e26841ea0614641098048007a51a00680c803e440e001016017849000d519042050000482c00706808240d0316200ca0005680940140241038061f0001d02804614500c0ca402a0759008284130070512020440d81006600014410f040e2901071070110003100900e0045000d801a07004410b90200031840e03810388080c02c0000502d525011543c041c001da942c141c521507030b0758000c807003816030040003889040031504059100544c0040d4402030681c80f00e680c0c3d00c2d0490040c650503014030050b0000c561200135542c0002c812040c4451541c14803502209945070744010050340303203000b8812280c100c9011070903501d0360481700c06990840c90402001d86540b90150810009104502c040340d030810a20720a15003620509105d4512205110000192003407844400300280f0311018000b06030001c041a100b490b18802286a80e880d00104450340c10202000340f5015006001405050f034450f400c5c000961280 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 681376214 1250 681374964 681374983
    0x2d1306240b0c030903030d02071712010510020a0b040501020904180b0c03060d060c020726120a14040e220309050d0201030f09110f061e0f090d03050703080c040503 72
    0x2200c450b140c0300140802400d51003180545030b450f01c808201c5a140d07a03016402010b07428400e03861b0b0340140000b812411907a001d50f000d544001200c50004220318140510700309020541d070310640d005081d29684000003210f041c0c8003500d0907075001c00c41041c0b90409119000d6445103505502700c0703000d9180d450444c0e1480040a580700382c01d011011440c551507004002c040c0075841441071000032105400250749040c030f80b03d2519080e400c0d1401168003580c0c00084261158230700094a0b46403150011013202d9804455501700b0046a90358030b203d45580d04000c1c0c03015003030032a003404807030a003d0400c50f00d007400d00c10100c016406403c1c5840010740c0020300c4a00f200e00a9509648411107400160f000300800c00c410b58400b81003103822002c2100c0c0b900c0d03012202008450701c4400c80d00440920074030b405023841d112a000b01e0068030504440401c0042c0406500411965103460079030000310750040d5003075008030040f030008104c12040641003002c4540c4407011407803649c10b2a25050002c1ea80da0078030f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 681377464 1250 681376214 681376229
    0x30c06090e180a020604170105010504022d1b0f1005072012180102060c0a0e1905030307030503010311010509100f0c0b1005120705092d130624 63
    0x1c100035440070050000e0f20f01160001c0c4131645490713441e03100600d074001034411600d007540303000008115441c00e4405c3e509000300558014400417081d1042c3c030368100220b104002d1008040c000129141c48901041094030803900151103d00c0d014102d803440e012424500810321800c10007040700180d44200034100e10040541508450151004098201171b914420006900030020700402c910b940051900080b25007a4210b900643c0c5031046490a4010140554005074002100514903c3d01e940501d034030444d041055000c0ba9134502c0020b01d15400440220049003001c0010818010b180314071101c14035080c00c200c3e10301000d8030000340c10800d44181e002c0512090003420f08035140305084103480c56500c10300621850400341000d1801822074031603244201c021065094040101291602c2114400761004010391900103001e50240e00450321044070240300382c00d0010088a0700c200700d0050003000380c40704400b581d13030030030b0000d403800381d0b0701860204402000014120661810704045400c1d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 681378714 1250 681377464 681377491
    0x91503020a11060c221503020c0f0a0c0b0a030b0324010b0702060f281107050409080301060309080d05040609021c02010e12101a01021c020606010f0c061401030c06090e 74
    0x106032171000520b01e07070b4200130714840d50781a44440c0d071a01a8010444402a0f0003104c895a03030310341d8040e41d1101c03180d0004000003034a0400b001120003200c0505064141400c1c08149004130782e011034a0840c1c0200c10f4203d4042040c1d01c40352180501c003101b80940506e8540c0d074039080c401e801245061090024001001d40c000507810004000d003844940c2039010150890420340c4c4026008240c913500d2809086540116840004c0e1490a44030703241410b58054401ca0542c0c1c0303403070000d6000b0003480c6020b41340d41004105c2d08034000304a12990b8171540c0b05031400164101d02d40140012921503000f0704010001d00c12400c80580c1c4c2103055200e452004443e440c07285104001c841c0d06000f07162420482c11420410710503215161505400f10905007a800c4400c0141185078a01c10070110750404d8025800000c00305429500c51851100d103466903091038441c40c42a60344030030858803c00004542c154034040140304001d04190881c00038881031401c01c140c941843c3c0355411615001d01002140d596 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 681379964 1250 681378714 681378757
    0x130b1915091a030411040e07150c0f1b080f060f0106051606050402010e1503060f030312010312090b0f180a05060409150e070206070206010504050f060d03091503020a11060c 76
    0x280e0192280303000c4001b510500040024403013240c0d0703421440c084c0410215042e00040b10591140807a42c502035080413404500309540d1f1102040001000088240001070005c0440c1a002c20028030045451a000902c0c2d149401c0810b0b0120030010b030888020414100b200b0281c28100c24542c0103c180c00420020380344c0c07502c0c40161664005551425040000c007180c1c44500464040514410103040e00c1495401055204060326807041c10310040740c07182d1050051001ca040084003040c0c0d9030b043d082004505840d40c08440b015001104ca5848040000070b9126681042c500001000304003521009070482c2080c0000c1c0e120b005d180034900c4925900d608c0f03554155200c4100740000d000e4030741c03212032500f404003000352102011101d600140c81480e0002515007000c0c441e0600c1020701910300d6605448100c20400f05070800030094040001d07039070707001c0f0b401c07400b01d0606203c1e64140e0300d0050f5500c0007602c000c1c044503000014000c50740c0206040201a04804088402c012070503141c00c01c0040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 681381214 1250 681379964 681379973
    0x40308091909060e060411030c0a17102c0c070302190b010e1605040e0915090d1808070306022503081503030a020c130b1915091a0304 59
    0x100c0011541c0790010307860340000300701800fa4044400d03140d0b0300040c1c0c00503646410501c0b054460303621050700c1c480720410001f4503107030302c0c01e0181000c2c107002e107015414092102d00544c450304050310f1481c1c000300050740800281520201c01e090040841c0010000c02420095540000c2e60040c50340d0400e00000480104041c400e108001c1080d2441030041c04412141c00c1c0002d000809006040310560b80901044030642e203004180b40b0901030781d4442d0f181500788421008902c0025240100c58405d03070007005503156908520a11947c0042d00901c060607c0e9540140701007900700c07604001c28001e1406000b07541001c00ea2030705690300030f040541e440d00c0282050450345102c64503120b0081d80c9041d46c0c030415a02001440c000c00c42c8104001007004400e0801d40c1b40e120b20708008000d07074480c1c4000c1d56181040c061089407070704140c0300013801034021070104403001c0101001508000c41c905041c0040000c5209540040d405890103c80c4a401e086001048001c8640d407680d41c10f401100040802 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 681382464 1250 681381214 681381229
    0xa06030b18060f0a1403060606040f0b090f1c060b060a0c080c0a0b0108061e0f07030b1903050f01060f030b042a0b120a0209130f27060501050d0804030809 68
    0xf00c0002d400f43c0c04850395190405017101e10178208074442d0040b0008a103851400400741c9003614200c940300d000c554903004860480394008884540c218102c54102841c954422580282354404041000d00e44245480c1070300450f0001c1c0d851034440c0905122414407564003074945201035520010300e0b540d81c101d131345001d0f141000c0f4010041180c00244004500c0c0035000c51180c0c01b0710007503100700941c0c00c509440b41d51140c400302c4d0300d82004d03092000081c01540c071135006446641c0b8090300010324440c03104611104848030713400640f01369000c812070454004092240c00018541a41070f1030742c40d42142d880e06107219000c0c1001e0b102d11041c1d030710303800d510115040c0c0701c180700300030111b020506940c0c02c442c080c0d64204508884400c42c50b80b000a8414800303000316800c400c001001c02d8070080500c1d14040c018840c0204100c1c01c0307943e0304c80ca200900b04041e0007480351109140c03d4202418185498001d90f40c050f003006000300041102c00001071010b0082d80e050302e0b44030480644034802c440215481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 681383714 1250 681382464 681382489
    0xc06051305061e0c0d14040b0f0a090b0f0a08010f0e07050a0210060e0f0f1621050705040305100e06131e081e0316030203101205010b0a06030b1806 65
    0x2000004014001d82c02c00608074094080a03146e041c100c803002c4282018600aa200790804082c0c100400100080508020f000b2000d070b5090a9561035255134214050b504210060140d5200000300f040e032181d0000f401da8010a00c001003480c0d00c90a0848100f0b2204002e0440c00a00c000480d4a0300c20900a0000d05400304049004000c0356540308030104c4d8940090b079038800340b61150300c04240140c2d00c1851140c8a01c104c51404400004000c200301c9041c00b0452084108206640e0110000007850040d20b00031581551059100c50841c14400c1c20302d200c1c003a03d140d040749424031020201002103407142d40048881500309d2520301e03d00f000c655000c156100c154041113000604420000c441d03003d4845510003400f80a003110408220403014031003503817100302d4603582001407010907200307400440d4040009500f0140d40da94441403c92200359200c0200d900b65180d14040d080b40c01c2060b4850001c02c10780c98240410102132010a0a0700baa0f2440c0c40c580200c0d0b00000303010b9071140c0490804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 681384964 1250 681383714 681383767
    0xf090c070f050c041d0d11010609020d0203180d02070902030c1b060a0f14010e0c040e0405030c011a06031501030b03030c1b09331203070c0605130506 66
    0x1e0201691a0803a26000100c0a0901c03452a050070000702a0650240705010400c4c1030081c099040c100800743d40c10341c45d1000000d0659254607000c06c07840d0080c0042c1c0f00702203000c1c60160310381c2050703350413144030240402401594029a055254640e0016040048502c2c0b503d0042c1c2e2501c0f02d0000385907910460148081c2031000b61314046d003402c1c000404d0b61003144160400c00c6500c41107140030007030740c0844800303820020300c3d0001445410510260150400c1c07a011541d03181c20303a60002503001c03850031542511144c0004c2101c0382030a50078000d0400b132021540107242800a003038001100d600010f403180c079403584200d0550403036901039445250700080c0102220303203840001e184aa50b90350920440562081030b4040c801d0f490800f1403c0f1401607100c00070103078084c0d00c050389582c070b1110809a080e00b00c8803401400700740341e22000c0b8504031800340100034543d03070f814904000ca03d40341c42d0383c4454100303c01000480c040103d560f0401054170000c40e1368541d100440c058012540454109190 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 681386214 1250 681384964 681384983
    0x1002030f030f040302280c081606120603050106030819020d05070f0c081009020a0b0405090624031006080f0115050c07180c0f050304110418140309031006050f090c07 73
    0x43c44040086c86410141b142e100070f0581902e4607141c90321114415500d80b0b1010194400344401c500491000703032010003508001401659a445950035135a143c1d005555182c0300161a400c142d0701c0141c41c000c0c03010680010100020750b90b1000b480392080b40e102424408090300c6150800819814160080140301c1c01c8502d101c142d03d92501c0206090a41280f04420310a80001c40070454825030301214030090000c8207070ba076110240810441d02c0d902d41d00800d200d54150800e8410740754040c0d40038017515031031560650305100380542512400f800c0c0340002031007800104803201502d0225020990545441500c4d100080359061a1148582000b01920305031481c508002c11a54421900d400440e81c900403008030907042900c042c0700641c0c02410365011400220014241900040703030483c180b26a0350050f24854499588024403180d403030131075030400600a071440c51b04000750a003401e00580c040045501d081d00280000c1e82145282d40140400720000e61130408140650391a141c1000069 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 681387464 1250 681386214 681386263
    0x13082208250305062e1202090106020c09040323160303060b030f04240e1e030c030d050703060506131d0606030711160f051002030f030f040302 63
    0x207032100310a5040c500000c0c40c8180c40248800846009801c4907000302c0600303101d80300d98010708035010100107012100200c954100074003401d000e100320000c00c103c10340c0140881e810320400941e8403060f844101150b0021040311003950399500d07041d404c1941400c1c0002e4034059034030701d00d0140c1c141c4440c241001001050003013440031260030350300030a88039540401140791070b01f01c0c10300c16000075110b45280d45400c2c800100080d803066a458190b4020720021501000c400c1c2c549004d90b03050810010641c1c02c15003018128411100e031a10040d074005d4055820102e00d00240da50701d01a1081880c03103540c079a0081a011030103644034601601010382682e03543c000c04014202042c0241c450640916071000d44104400703c12107921340203c038010501d510b55220300600f07d82d5030f002904810f585000d52140c004c110b003401c01c1000002d041030551056880c2c60702c01044414940c1f07002440c1503401c104030604140d02298100ca602c1100800c2a1105803281c0c10224680792042040040f82da6030741010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 681388714 1250 681387464 681387479
    0x210708030f181e0105090105070504030311010b04390c081b12040e0f1014040f1a0a0e06030703121403072708030f09040f0204060c0302060708130822 66
    0x3140f5684040c0c2000340183e880d5000214205d0f1812146000050018401840024031a00e80b130960343c6598000402c0240001000604076484522410050b4600d4040d01d2581998a26046061481810200e00c20401c015001d030000107002e0000307008201c0021414600200c540405280b080030380100d400c5a4582c0e550f80360700f580640030b40c2e00864102c0000a001e03015510001d440740c0c5141c01001d04aa152000151045020580c001c2c0c0c071076190072185900e04007034400e81c0403558040c01c8a00008420350305200705001203411500c80d050498080091a440000c3c0f000200d81e403200a02d00d821840c01d2044504c9840c02e0003100d03a0f04000000e000d4000d5020303000c2a4001500d200404107403d04110560550109102e000c070385070014060250441c40c0c0c10007038031050f00080d0010550710403940300c0b076040780c1c02900410300ac200d03aa1020424141d040000c203500149a08140c1c00d6420f000c001c401000312004c40050a51800050640c1014070401250300110b1102214251294407200d0307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 681389964 1250 681388714 681388753
    0xb0403030e06010f060c060504062a030f1a0d080705161d0613020318070315051012060908071406040b16170601020c0d05210708030f18 60
    0x3010a010700c00c2c0c10001c0f803c450800b590800b00c0d116900c5d900c0442509960364800303031000074425514161303150030451103000c0c0b00301070462600c084411f240d58024400d02c058100d418200303581c0d00c030760300d8000c1180c400b02808401c46994641112021040506498141e07054820400001c01c14042c44001d00c40707260303201c65914140c4400040100402c411030460400b4034030110f40e03403507220002e28851402119a503000b550040107451074800c0702c2020952040c0340c9a0a03a02c210b8001c08280811150020340f445925040542c2c403012500c054a000d0304140f01115190020305015610b000312020040d64104807104258000c0b40b906030f44944404164441c84112800e0b13070009400000118140010810a99140195103c00381d000030111840003035864000c00c541c0c1984a004403e924075543c00c00d034168028410b000a01044100400e400c2d5000d071080c8010001480c240002d4002030040d60070359078418000c0311882c41d581d49503100100b0740490300580f4174071030044016100c1c0c1d0894201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 681391214 1250 681389964 681389981
    0x70524060307090507080f060109080307080c12040f1a0d050f0603100e03072303120a060b0403080708070c0e0c0406180f05010809012c0c090c0306040b06070b040303 73
    0x74250344100b40d840c1103d909586080354150001030300c10000441c10802003100742d810410601d003900c1416120305100d07265511550040c2c03030b0380401080358611004108888080c0d228100701040c2081c1c80c040024101d80e80314028510807420512200440c421044282c1d04464101c280910450601c03085081000200381c800c580a8018482400c0d00420f003401042003500c241002146013101c541c0342c034810380703551038041441c89000c1c071030a140606040000e412122000705000c1101d0130500d42079001c890041c3d2081d2140e01c0240820404948031009954400e41c000c40301c50340d20340c018a481c0c98a03544541081012280301011310040242c00000f84c41956115110a0000524060040031482c00752180112040e41d4107030504c441d510800050f500303d80c0c20000801c200243c00d485104c1c84030102c0c0070f01503002c44038142c8007110b071042001c407021100a41b24134600341000c011b0600f583c84020301c0640199100d140015403500c07410700300c0300301e241c01900744a03007410645802000b410b8010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 681392464 1250 681391214 681391219
    0x50c1c110f01060f05060c0709110a08100506030109270302010f1a030703020f130507030c091205060c0a1704050c0a050a080705150d09110109060905030604020607052406 75
    0x30600e80700c140741c0501c601010368121080c481e681d540342000b08905030340030910040c018015081e002419844500805200c02104143e241c2c841071075543c01405180014254920100b01007410407041c0c8440c8101c03410364034410008204a4154a540e190303030200c65902911180c43c001d00041815410350104001c2ca5003224140000c1d03034040c0810710782c0042d6000c110f0f03058002c80d40410061601c40c54913140280e0203086403030050602031910089401c2201d012001c240c403000f80b8026141d1040010029140d04460f6950b202c0442e1211a600c1c0030080440024040000d42d00741114011058161614000709440701035241600e04a17445800c0409030a005082d21600440d5a142182200c17040d140c401c001401d0980ca030100300000031008500c1c420109808115040e42c407080c0740a02003a5502440c0006400040c50b000103200d207180360b0214080000a900c18052035030085a0140c0250b0122502a180c4000742800b50078402d1500102c00e0703001c42c04076603940d6499400d2506202c0e5108 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 681393714 1250 681392464 681392473
    0x2060a020a1403071a07022a040501090c021005090c0d060f1a180406020d020a050a020c0a1d042307090c09030b0402010507171b0c041b050c1c11 64
    0xe410b603681c0d07401041401400f8469140b000810305210711601780d0302c007400c1e1044503a070300d217841d02d20781011911070100344003048102000c0200341842d0040a004041a1380108400280004000d403070f10107101c3e465801d01c0c0c403000800c0c2c030420100201c251403c802407050740894400c1c0f03001c000401100040105940c14004004c00c0001550001c0c410076a000e0100041c5501e00100c3c42030701f440040040340d40c0e03a13080c41001c40030405803003e001420590b40700d050b640c4040c4440640303002c00341d030b8005109a00a000600a0006141d0400300020743c00308a6143e64650346080420b1500c2410380b0080181321181d4100d00c81e40c0000e80000711141000200a20408036204a40c00c08040c04050a604d030f08201283c0154800c00003800031501802e4640305904186a002509030700080600c4401852a40e020407800350900c00f2a0007000100c03010443d0060308030043d1080075004903000144880810301d01000703141880124610810000390700f03000c2681e40400f49c1100680030690580744074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 681394964 1250 681393714 681393743
    0xa0209030609060403140a020f030708031e04051f020d0905071a0a08070c05010b030109081324031d0642120109080d0e06090a2d02060a020a 62
    0x1e000c16a84d01641d055620b01d508800c1030318841400c3d9010252800031407140405001d4a4103051000c0e184140c410b000003680d82c105132a8654114071441d001040b064200828040020000030702c850914030702c0744400e40c01d24001681d04000303008114400c1030042c00c2101c000d041101c0030400400b52141c403040c64a034046201c45030901800341c60481008140349601090f1628000d4485900aa118000110780d400011003c2400c0d2000e212046640382004071301c2a1082010104c036001600d449134100c8481c00c01440740f07010020443c1900400e25079261403520740040b24000415400780303258100c600c0c078140000801c100244080000510099200e00c007100c5c010b4115a081800d8107100c0d251a06003504010041c3c6001e1081c065030f00d641d40c3d04494800502024090443c202204000044600454031038504109000700115101c1d000810208005803922000c01d9000f0009e0415044912182c101000d01003503d41c0082c1d40282c012030040042d40e80083c00303c1070988145501d100000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 681396214 1250 681394964 681394981
    0xe0d080706140f1306110403060e01060f08030c060115110a0c090b0109080a02091f0b04081b0303180d2001090906060221040905011706070f0503040609030909050a02090306 76
    0x5105132850503401181e41e0809010a01d550400440c0ca0400c00000f0710785540d0340d644108689444e0f101d0782c00c0340d44451041250302d140d24030040040c5140000345141001442c0b40c02d8842c0014014080c4c82000c00800c0c0c0c003c0d620540454501600040840f401c150607030030300500c11942c52043d84e90150422006014a5100d2074204081347c4055004010004055017080602c41000304081520701c140d00041807141c029400002c02001014904ad5481d402c0101450600d4941086891442d082000a441c1501c000080760400c0c03005814080c5220200310004815082004001e0180c551110105800640305010701c01441c50076211841c41c0c0b41d5400464080d00d41e40d02c9440c003d80c0150302c5400d0601c4420707001140304111305001500d000d03264103510040b16000c1e001145641c040c0c00d4040c00d4883c0400015410a4840c05c200c80c130f4500381940105244401880145019110360303541c010540500c003074002425400c032080c002443c2880201c0001d4011420ba02c0c400c0c440c1130042050304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 681397464 1250 681396214 681396241
    0xa140a082212080d05070c0506100f0503010e03120903090402030a1d0609030a05070f141e011b050d0902030a080306240d021e0c010603030806030d09060e0d08070614 73
    0x119880b290f80c6003400a443d07850001050300030515014041003010400c0001d406004080c41070045003180b40489040606c0d81240c0211504014020f83c0340860601c0c0402001041c0c1c1d44c1c01a008036030305450b03503400c94018214064550b07a190014008424855507003800d80284016180000d00e00c814440401740301c554864060310040c040b50010032103606103520a03801040428000d62403c6014080c940d00c0f038205141c070207041c51254010302110702d1400d01890302107801014500080c406e040064070003900000ca00110074042c844c0006032541100380d030b03411a50006400034180c42d90030b0710706d04141d40300340e0044034081d2052402107403400a5110341c100740c0521b10180c80069041800300d5121600030b40c01000d04d00b00380303000d100c0c0c03087c040c4c41c0300d5004040d240d0300000003007030b140d00d0b6240c060301580003d0201c901c42e82005000920b4694070403500704c2100c55600c0c1c40005031800a0101c0c18040c11071902800078440062100140b20042c1c00c401c5400a100c2e1400655076100030a81c01e03034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 681398714 1250 681397464 681397499
    0x1d012f07020a051003020702060c01140f0906060105030402040603150c020f070803031909020a06020a0510060b09150d180203120f07080f0d0219200a140a0822 70
    0x80700c00b0702802d00007414480c130352020451031405c00610301074141d00011a903400042550020b6915075821000c2c000703810b40340d030f900f0282801c0744045130b050000c3c456488440041c4028100900880040d0641d511034010000450704140c11310002010b0240ca0710250000f80200009807241001c2d510700303000009038541c1106c0500c4080c60070341d203480c088090703140c0d5817010380c1001d85d1719a605038000d0f0361043c0f500c0c0300906c42500209401c000c01c0c90401c0c145240c450024040b81d103001002c0022003101400c44110140880785100e80d09152808142d0170f00a07001d00c00c15145c031301007491580202d1211050300321802242102c0420008001c1c0c41c0892241e4080c11040903818004038002501901c080d001103019000514100350343e8003048000c1b45c0207030504100c00c900403a40112216044100d5100e00031410003d20070090079101c00c00e0340ca4901c801c4c014a900807034022802c1000c4103000380d0105550011141c3d41d694a41e4144083d54040380303d6540d55074280050001b0340c003100861903400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 681399964 1250 681398714 681398719
    0xf020c0c15190e0d0203160e0f0f07082a0901111b10020a06091118010e0c131e03150204030507210b0c0315030109020307091d012f0702 60
    0x185039099000c079025050032003150b40000d1342092a00c01a5024003914170080e4400c2508001c2c90325240c44019081d8000d0700d281680d90000c0144501c080c07075010060b92146207410015102e884407660503c0c2c50100184081e450814440b0f0010349101440c01045c9941090342c80c200c4108026464548a00842c0e80704410412201003e800c0c6040019135168820b92a0042e12455045078960f4001d807000358030704444040c580c0c000c0395180e107014403000410f400c41090100381c1d903040081500d0501c1c009000301498000c042a07481c1241c041c1c01d1800d0140c80050b004468440b46502001003121290004581d20400d01070030490002c500e20035101200c1d084401041d1142c50150306052886c1e4070009560321303400c0244078038041848200707081d02403c10036040c644d885c600000101c00340800814824482c0c0d06103070030180507a82c0000c0000550b1600500011080c1e100c480c1e104c2e85008034030445906508103112a51044510310041d001d083c950800001c0c0d2915406050441e4426020000d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 681401214 1250 681399964 681399997
    0x6051302090901051c05012a170411060715020706060e090a02131b09031401020412060b0301091401140705030c121008030d050115050403020d060b01030f020c0c15 72
    0x100d14140c110000c084801440f00405e02405495540c292040b007800564400181615407000c942c2003007110308402080e181a06c2c0011000c08510001c0ea07000e08098071418111400680c41e6880310122200a580005802e00001640c0c1059003e50005403094401500e006030000b030301d10701c4056192080301c004005d032040c0f000c2a402c1002044001140007200c0f691800300e22448940132800d070440080a444143e102c40ca1850940340d58000d010100c06280d0051004005040600d0321004109078015000304040d10034401003030050050036005096010040c800c600b0448040d0b10604201190621642040e560b17500c042d1003e10050b91400d0038124200005503024940191960b0800f003c0d8000460443d1707600c030502d1441e003116050408113560b4100400844840544200c541d0361103003070041c103017480d43d00090004500c0101c06021300f0f40314a0103030a240c0c0705c4d0b440702da0918800c820454540101021040e6a1010100000d0090181d41e5009a041101c00155400047d4030326440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 681402464 1250 681401214 681401219
    0x5090c070302010204050a0305101d19050307020a0315060f0e04020906030c0907051804050606040b0d060f0b18040e03030a0c022b090b040e07050f071506051302090901 74
    0x11259008040550840d5824400402c1980d166044c920045001d400100300349140300b91480201e403400c61000d1440d80441c1440301000c00042200c1c500030140084030070300101d4500b08a4110b120781d000003036000700d483c5000310400003071610100800d540d12508111041d03d030f20b07000840c0016409020551001503002800518061240741da01c90701c00340030f5604240c25a008110250000d40e900b2010038004203189105044401d801285036030111020f00a60504001080049c0300c0d0b4020005c60440006801c100f0010b95013006000b00035443d410040e075130361341c03000750740035080181510001c2540305040c80c00c52800380501000400600e01071461901c40c842018018004800b841080d8011032441c90b20700020036107420417034010f6035080c005031481c0c600010708079001c6402c030711110401800140146550f802c00258090307118208550781c1c00000800d030b8850f0198410090242c98240c514a0440b10701d070f0000401c4540548414180714125910501a401140c010303680285290004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 681403714 1250 681402464 681402481
    0x70b0702030f0604030503180c090a0518070609092d020a020c06070f0302060c0a09091e1d1603050a200607050a12050f180a08010c0c1406010509 64
    0x8250040c402000c88000b9031010000c2410050210340c20303008180d0110400580c0448542019080c10200010300441001c68001030b08a00029042c41c540c50354503000100701c40c141c00300c2c80d03100640d4401244c80241e610314000f000410240290841c80d42008100d00500040880c0b40c0c03046510038085905205040304043c00940054146100b144603801d98041c0e07980b101d00060550601516205450015604010380340c52406042601c849100f000720400c40340d400528481503a050f0300002c02d03440d41e10b400c50a10104a40c0a02104d07030310b0820390442503401603c15440090441042e56070215442e0341d1151400c51620018101d0b07040503040e8000103046401d2000f5078a0410041c1d64045906000710301250841c05003290103910040002081c0400c502584404c0035191030890b1501d0307501c0c4440032150241c0c000607224891040b40000c460b41e1840070640250122400803c001c10751404020310a28101c40c054940006119141d0b590300d20100700076040e5100905100c0041d100c0040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 681404964 1250 681403714 681403717
    0x14060702100912060209120a1227080f01050a0c09030314070f050d030b030613140a05010e070f0f0501090608070e090f060112152106050c0712030b03070b 68
    0x1445402c0220084012903002d01180d00008082e00591006031624500340134041d07004140d02540c00607502140d20480003c109202e003409005080c50b0000d00380502004e10141026402c44020f00c86402d0180820340c4600014900c00703100307800009200c2603d07144c10500842d502c000050001440100085c00400d0041445038040540d449610b03241204d140c940145100259030119926048203c544144a0b8180504a4100ba00b00c01900ca0307801c1c102540505506480300040007000c4495072041e080030180100c04107150010b0092040c085907490b0240c80c0c1481d0701550440d01340a07080801d24040c2096640143c54044c3c42e4402542d050010135100350b000145000b080080d40080d141e21a210020200e00401d07080c4c40314242410034000140505c401e0b8003c2e6498503240071100d550540c504121001110310240a0a01203400d0b441401c03c07007808104050101d50904090200320800702000780001b41c0540f04001c0700c00b016000071015113015200c82645540201c00a0240008240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 681406214 1250 681404964 681404989
    0x30916060f14130603150801050c0904050702030c10050603070609030c0303080603030c07080c041d060105010e030c0409051615080a0c03021902010b131116050a020a0e070914060702 80
    0x402d0300d040c00e9181001040c03c6070039811940010762118011418000e000071400e000c6c00c107000007800340b031600740180300090103415451417007603444401140c107150003801203c1da52a40c000640b003150640e01c41c00c1025003025030b0b0550107446101c03030005000d44074030b0707565042e60f40c809000107030302c0e00d151011540f51310301601040c1d03d8007081144041c5c103441081200002c042c1040030b40748a0302c40c6000c1100726600d203c0302000380c0c0003032090201c112001040140c107450742400d0440c44c2d01002c01c0428506111404401e0f0068a0311400300140240008c50241e620180c01e0384410082e29401c90741400542040080701140d102d1000c02c0c45194650409040c0050915005003010b4210141d00e820410b80c0382d00c000940d40d640400c01e128182101075410b52041002c050281c0d00c03906a40d0f08a51003240b00301c0c0d541040d108209400c000090041200c02d580013062500002e4407800141e108010944104000c2000c80f82c0024202010084818015000030002400c00c1d1054091201c01d0f00040f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 681407464 1250 681406214 681406247
    0x30609030f18031c030606030506120c101b0b060a06020c090f070e1e13060b0405061309110d0b01020109111c0c08070303020f0604020607151808030916060f 69
    0x500c04503102d00d84803401542c0201030385e00070419519014019085400250075280105401000f40304005400100307206151010748840030304050480c001c40d10300340003064000030120290326101c1801441240e041c00b402085854880c0300e41c0d103090a80e40c1c0d00b100044e15410601e0100064035440c40101000d91005050074428200f0b070003d8002146000d0104540c4a044002c4841d1040f03410004004648100740420401125080c014801c1035401944215849200000b407049001720305412001d004003010942072014001d40e51803030486030003200398841c0c0107140c030042c24240e42c8140100f0151a4006c5505030b02108010705000c9c00030362036155280b180d414452540000741c01c900804d070040203102d003e40030440c00d6140080c1846000d8485501e141d00031020302c009a500c240440700c8442e80440080030542003802d54a010709080240d01d0130440343c00c4240e400380062000190700c070354028000d880c01441140c00c036007040a450302903c80000e286500b911100c0c0d02031640381c41900b112 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 681408714 1250 681407464 681407473
    0xf290d14010c0503160801050114090406330e090604090501022a153603070302030901320c10050c0712080c030c0a0c050a0b0105030609030f1803 64
    0xc20619420744882e20300800029400200f000095440401001d806020f24503002c0c0040d40f40c40300007400342c0021010158030800020b508212603680d03a001c0c00080808210016001e001551200100c81483c20450780d0b101000d02541c0d09240708480403c2050001403051105486103014007004061070f8104480c01e44d820000c02900d00c11841b403084850b000a180a68542c00034411182040e02c4205103594520300002884800c0c0c500d10b04480c40c50310b0007030b60407010941c859104051040022003415250200207030460606501000905804030207803a04000004c00340080c0340b0381450503244003501402c1000d0009a03441d40030082040b00d85001c00c40d5054080c071000c4400b100c0c001d549140301260002075034030030041e601c400d51300c00380641d040c10a0b41d40380c0381c1c0c0c0030016031000802e1070304031450018000704094014000101e00e25082021a0708001551800510166081c001d452092161030000342000c04000111402c06c2c005a4207942041c0742c8003410320030100c05440d402d526014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 681409964 1250 681408714 681408743
    0x2070c0b070b1501110a02040b0307030b04140c0f010206040b040204110c0a02100503010e19090b0f09100b0d150608060c071101020706140a090506030106030f290d 72
    0x5010000e0708420b03005411056403420241c440428034510418410305104046414116400c40400d01190701501901c0100d1134030078640020742400d006400041c4a40400424801400209241042c141901400702c13200d080e01d810804c00000c00084001e401a03002d800050700181d4070110107900b0a2020f0b0021408003113644481450340c0151a07a49a1130b44400d0800081d803400000c1c0666000311400d00501e1541400350014440300001c0111014680039240c2e6460281c5030350052030044c0d00443c51901d01e0800030344402d00701c01c094803011054030590300f002c11656860720038850401c60041a40031050440d90782c800709000301c100d10144c8256a001c0c0041d618009101e40b034401c028a040d029500c401c47c0c0340c44100401100d0750281150302c0014107011807034100010f180304004112049440e01413003e4100c45101c040e810040d00b048000c400007174015050b402244015519840502c501110140c0207550000c0c20a00c4c07002da5540c5048410060401504207a0524024103c4e13036140d42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 681411214 1250 681409964 681409979
    0x10e2701090c090b010306050d0b072d0f120c0e01030b0406080d02160803030f280c09090e12030606070302100623012c18040501090615150302070c 65
    0x71881c0d1110900b66140c07002440c0542e8141f290300c018000c00c981250f50030146031100039581d5002003002040c0004e5180080c400302d401900180490040c507010446108400e40040198401c0010a004103482085152103600d00380a0101110103131f41d2001c41000f030403001180a450861003da8105030b8400002c0351040301808034107400ea40c16002044a86801c0069920840f119480f80541d60428400d204170701010b0f4195541084450f0312203513600d289500c43c40103240001740350305652031812180d408a2038004850004550401c03e0810514201004990701c8842c548198100c1400810019a0300e16003d40640000c44c028812180c010103c030f14400111360b055000380451400d11528003262003401608061007240c2840c0601c0c914412500c0c00408004081c6212010864120044e805071610a05419424844610820103060504059000341041a800c1d80d034a800c2246086258412246000854041d040b122040800541c021002900172401c101c0d13901401500004464 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 681412464 1250 681411214 681411233
    0x240301080c030c1e040c0e102a0506060910030c09050a0b010306050f010e0f131b0c03020304060809071208132115090821010e270109 59
    0x90103014028824040d484041510b80208440010300c107818200010409084000c100c2c681280181e40c0440c1e04841e03c4810f0750307184000811103421150929200f2a4075030f02010240110a00d0903143d0040c00031912081a42503082c980580140c0c0003101040032400c0058400340d202e8818078403950340c60340382d995a0170082c000360701c48803001c1e40f070b1000e1040b0744c1d90b23610a0f5003000100742010804a850803000c1424840160500c80c140035a480c4a4169900d80d00d07031150400340d0083c041a40e034096405203030024003006903801058003444400c107400d00e00400302100d03100c4e01600110b0800d460600200c5940e88024080b0000e4001c140c0c0000300d51038002401c103500742c458100240c95000c3e4496414256140c2c0c1d0001a031a090303070303c40a051032035030030500b1480c43d0403603d880c84101078402d03010058030301108008c011440029080e50a9806d544000d50004070741890f09440303980e076003c0f001d4003410036203981d011200d020104040d404900300355080191481000465071a4072929540100e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 681413714 1250 681412464 681412469
    0x160b061206130515071218021201060e09030c030318010905070b0a081014010e030f0601140907080108030d020c012c10020c150603120f12010801021602240301 70
    0x100b4010600040070028103000d000c1c3c0700b40382e444021a592410460007004241280f0350f82502c41c3c0e880c4411004025085c80440290f42c020f0022000040103451207402440540300d005454025030000c40d0b5000800f000b101e0101640c00007c5086403101f45000b80812486000d90a96640c0c4a0102000807028805000140708024444d074a80d41c00c16800f0304001e20081c0002901545524180009004d02207004408202880c0c1002d040841d18040781c5040d804403881e84a5101d010000600d86882d011081c9502c403041e241000d02c0c0c1c0701c000f81034946200030b00400d4030540052144a442a40903130241010700e202c0000443c0500242001c21102108451040301a03045440303800c01d001740412142010810800f8210700d081403100c01103449001c4032100314500c0c0500c00204403199010810524085d011811080c0d4804441c40042d40684c80fa09554044510040000800c0c82040c400d0364044401d4619800507800b4075420007420a507100c164034208803096529980103904280a0342c007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 681414964 1250 681413714 681413731
    0x408070b09090906101701110414030d11030307050d1e14011502030403020411120a09120e09060409061d2401051311190807090b160b061206 62
    0x15200000002c0c0600160003d1144940758400c00070b000c140c165040040b41204c4000c00c650607000345d00568180035041100742103031001c3d030100d07000c25031143d050034805c0c50b143c0480854140342448003055418410b2205d107007820740c2091000070415400759000b00b918080007000002c5080802440c090b48041142400601c0c03650b440d50040e56100b1070103110701600c80105240301901e070001e0029070b288280d002c028080c0e900c658a065194800109440620020100440c0c141ca08400d200b4000c1480b4002640d4810800d42c04443c4036000e210b2800c40950003030b00d00c90480d5903050912010308a5030700b040710743c5d41c0e68181414021800024040c0307200403081c05024640d47c2e607200400114002c660790749903503219100402c0156201000b090744000c81040200b4a10880c120f84110307406019031081251300c500925401c420f0307000300e5051144040c0d807942019103845404103407030b9002d00d40900c0c60910090711140c0c041041804483da103d00c0051130300d45034040c112021404d02000351800f02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 681416214 1250 681414964 681414967
    0x20301080d030b0609030309060d0204090c32030106031e02030718050a12020d0c08060c1207020c0102070b07060b0a2402010513020411090d08040503010b0d020303030403140408070b 80
    0x509250b414055041d42c00720407594281403140590000740c491140480342071082000095000305e00c2c0303194054070000c108084c0c080003070701286400900070500311308003090a01e107007000300000c10b024003810707012602584005c0c5040d030707003050800d4004090344140c2c0c480850049035485c6414105000441c41581035540388503450368a05841c081c11b45c020341100b0700c44d0380f900001b8050255415103410406da0101d540b0071852400c0e0921006180c11600598500c0c00307080704104085589400500000003090f410011551343d11000b26259900500030346c1c010303040000104050f503010009888041d00803200020124112000520304032010740c800780b41e20542c1010744260707981040700c80503404040c1c00244420314001603054252031003503030700a200c0c60742c4135203401d071420316a0b040c0c80700107002400d01802c000d01410f1801554000d449594031943c04d180c41182c07a420700c1c2c5540d42805078050025806d58035140d505446000364580f82e85010403060000003100c060410903080101800b1000b203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 681417464 1250 681416214 681416233
    0x180717040318061d0619030203271515130213091b020f0a0305030f07050f270a06140c011118031207210302090a031103060f010b1903090602030108 65
    0x9000440c820030745104605c1400304581d2440003030302007015900300703103001a60707a03603a04106629810000f01401c00703280f04812508400d2000111400003501d040c00d9068141e50311034290a02e1030018100c3c0f60004e00503401d880c5c1c4850741d074001c3c249448000541c09001134507554000100c500002440300b00c2c4994050074207070560103002e4032601d0702040000e0240a012610094102e22019240c00801c1c105100000c2c04103104009942c4c651600004840e07503805000e0742d900e551100c060155500448010802490349850042ca50407140c03143c69402c1080110034540318150002e00f001c103070654803020b1484101c2c1e4144000c03c4a202c1109491400c0c4510906040c58a0b61040480603001400c10004c13000c070701ea01c0810309d01d001c03d03116100c00c0610b1420040340a4019940f5003504904404408010058040d0b0b0b036200d4250281c0c2110190740e00c4001941441c0c03000c1c070030034a465808200e0785468a00d0a00783c13100c00102c80c1070208001c0c030255100300c103e91090b1b010042c02d800034040e9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 681418714 1250 681417464 681417497
    0x6160f051e0303040b150901180b06030109200a0c0605100e01080a11010309030e0d020d0b18010b191518060e030d0c020a181401031118071704031806 66
    0xd141c010b6140d44010b41900508804500c50039410f010f40e0380349e07010340c1c0d40b50300000c40c0b41d4120342d807201409805139459503591000e42d0080c1440d444004a407132035440c1c03055034031123642007643d0003009107a840c00c60b42146074aa64000701405009084101c840360000b1a07491458045c0d5402001d581000745103454450400020a0309800c4445042500f00f96110001ca0381c0301840388540c2208a030348528540e55440000d80303020345040014458450b00040101c032400011003408102e039484028400d03140031008000f0b0b512058046a5841548244c0c02d0108114041d0b164000c5d90391810a800113007402103030701d403075007015501c01000a82c070078040c4c14160800b4481c50082c0300542c144016010496400034903903407144c0c001c07c040121403a4603004100707020f400c03e248054181256036401e50b140d04040141e20600072466001e5100f0304418942d92070b0603844140f003804199a61106000107810160000001030400c0e400c00018031190510705010b6009038008062a80f42c3d00c0d072101c0700021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 681419964 1250 681418714 681418733
    0x405090403020d0215010f171e16051c0b0712020316110a230102090a03050321222a1a0a080a15080f0d08010506160f051e030304 57
    0xb540d170440004140100901b40b00c0012000c00d4076000a180d0400c1080300a2191034519001c0d00c0042e42d115811101c5850130020412440a05409800c030f56069100e1742440103000702907200ca09200000c90410004c541c00b44034468000c0d401d880e0040c03440000101c4081079070003e0b50580e1000910442080e1015041280c25121a5003040500de11405940390040b003c503c03030a074541850466165440004001c0d81152880003008141c405400d4403800c0c45640e82d04260b0f481404610318403a480b0511502c0303814644103070214840c5031514400404c070800c034904802400c0b14400d9480c090040d205080c10413445c0c034407100d41d8400003824580861200c001c084e02440301c2040c10100300607010651310012981d40004042000324100380c407800581940c248551080c0c0c4c013400b0304c030b0b10a2402c1101181401941c3c4065440401590703c3c1c6c8204070082c4500d03d10341000707403418032500001034010400403184c01d01900546102500c820414031a102c0740c0031030644d06410000400040104503034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 681421214 1250 681419964 681419983
    0x3120b04140f040302070f0602071502010509030d091b031a070305070f0810030204090302030d06091104090c110318120f070501110109050106170c010c0201080711030405090403020d02 81
    0x460600040c203a00310078001da104040e00003141030509000050916000304645030044c8010341803461907594400c002034503940c0314010aa107180c0540c4410340f4681c814010701e0b00445da1100a149003400503540704000703200401d002c544401141a48425031108145240011409150f03503d100c084812200c81444e00010502c0c01803500d00700903c070342e440d80710381c2801940da43e40c1070480c126200e2031506114521141e100940c001e080c0380c01c17a002c140c0e000c00500000c0090007028481035495130f5171007007650744210700481501e0051004000162081e00510481c4c00c0314140401205940d05102782146e21081e105070086031559281465414079603044041c018086000d8040341a9402141c1c1e100c2034140f1642d030400014a10550f041c28003980401a602d074408003c0098582c0c0c0c8002c5081220490340708441802914181880b86d400340d038443d28210340c1650744029503038600505035050014401c5002d01c1348030620001c01c40e83c4854800500860090300141681e002066000b480d00c0400b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 681422464 1250 681421214 681421219
    0xc070b07021f0c120e030a090b070210050d020702041d0706090b03070302030421080103140105040521070c0308071b060e090403030e01052505040503100207140a03120b 74
    0x103210030107818082d2142041d4051400201042e4408040801c607032901c0c1445210203001e02e014541c08089800000505a01034a174403001103055a405480b0841c1c050b043e4069046030030740c1080031a41d4820f000400d006101d45034010305045840d0041000c903600e1311390300259081c00203042780e0101d004103c1c0c88024051480c10202003410700740d07540c07034074080604142e062640201c04202003140d8100d11003000310403281d8640a000c1e68a100030070208081c8000c0e030740c0e05008440303403100c40c0c41801014030864018000b048111710504441400008003900010801c0050201400280044890302e0041d4000c840c41510b1f152079040942e5500c1c01c0d030204031440c0750310145c104401f41c0c0040c000300b11b4400864107110103558130309064028000c1c0180c082c0300c5519100400c405a003005034400d03208030b8074041b5604000d810110960701d80c4618001c056040d4800d10542411107a00c0c0c0052444500c2001c2c00f401307200e860042d2078600454a5401c801044803840c042492105a00c16012003403400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 681423714 1250 681422464 681422473
    0x509042c011808041217070803010e01320f0604060203120702010b0312070f0b070309031206081e030d140103030e04050106050304020d0215160201030506040e030f1c050c070b0702 79
    0x43e5403800c40f82c1c41140300300c80d41001103400038400d000162144040c0d880131841e20707550310122864009110f605c24090160401e03010000443e0007240051a9003491500a080942d0802c0d50301590080c820a1141c199101c111445081d20a4076281d0241c8024a0386400640d103900c171006041d1408038004100b0801c680c076040140c100c039a00003c40d8030b01c192111069903518503c0c1c3c18140074070380002c0006130001c440c60b0180170742503030b05501140c6194041c1d9221b420389220000c101c401d4441d070780316000c0310780c1c46002c43c800001d100c400d0341003d400c0c400701140d290040815011050340c41c84c2c280790b2039110080c0010024150031405801c0d15000454082041d903043c440040c080d40005400640a0f110001e031400440d152040640015075910030302c25160008800900491524520100d0029040c8000303d94682040c0c01a00400450b220180d4106222003c040301c8540006d09010b040c2e8110314003040300ba107000d101d41401440910591503950941d41401055020007500300401c5601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 681424964 1250 681423714 681423761
    0x1b0d0204080615220f02040308030f0604060f050f0118030b090f031e0306010c0b0f0105120a050d0509130509070e010b090307090b0301020c01020f07020f031c0509042c01 75
    0x840010a28041d21421802c00302d0a030300484c0c1030000d1084109200b6103074400503000c0103004005d8051407044001c0704e002451661120148005e4400c14480d00e95064907030071051000e850102d1031201200010306d070107800e50008100d1140c80d2501a80166200205c00381440002d4105020410b0b1200c0703008000c41c41d0407200e5121110800c0d9145044109c80004030100d41d29038030890040424070741020384142d041c140b0640001d4008001c0c410184100368002d04041040c80c0400ca080c8030581210251818941074602070fa07050b4003003045141e2244000c0d55440c2005036038410980180b49031001030030828202070a0124203007040c3c1114803450340c01e2201251a035030002da00070503104400c0c00803408081c0c48000c46e0290041d5031052956500200c2c3c0c4600d591140d0018140c1e56008079456160b0f4400e440a040e1a90001013134003010314140c8003210302c446e00800c0182010a03000e440060300e42c18804000c00141100442c168441680480d600034420090058000982702d500c0c44088110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 681426214 1250 681424964 681424969
    0x726070e1e0d030c12031a03010614131805150604020405030d0e0a170f010b01090b04031e0b0405011b1b0308041e0f0b0f04020a0902031b0d0204080615 67
    0x4040034800391052050b90070307800401d84100024000198810a41459015400b04c090050102100f100c0c0c0403aa42446031100c3d0300d414000c5104a4034002805ca003880f144000348140758401c24403011303800c0d450f10000c460f940e48444404048902410203440e04041c4402056002e00000e054944202d00510080c08140c5e80480e106030741e2509405d1060081c034500b0081443e000c5283c0c0414212241e4680e24409080041041004480c801c4000c2010851040055031a40d659001c1e511015900380801c1c80090b44160b00c02c0d00203007003039089949617401384d9210501c0482c01c41d000c49159440703980c1200034800b2501c1d42c44076680c5a051190f02e007004034404e2302410f40c2c1010042c00308201d0b440481d0a0280c040d0340d09010041ca401c7d26022540e0f10b052031114010781301c101316000e0840b00001600341000180b443c4c06171782d0041c000c2d0041898240300201a41029040301c0e074548103a2a078001c0803403002d009210140342310102603221480d101d5014201761006180035140020040414480e9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 681427464 1250 681426214 681426259
    0xe091204030f1b050a0b070510020a02011a0a0303020d051303020307030804061803021c1e081c0501050a12021f0e03010e030c0c1c0b0c04030b070e0310050726070e 72
    0x190306c010302c015200c034014100340785808800305140c0c00c020f1000071502010b690641201414035042c2c200302c100070702504140032100046200c0500160001252400e145128800800d00c4a02850034124080c1d16900004c1c249401030740205c504880000f010414950000c4600340c80d01025582c0803d59481c64001c1070b140340d1131403000e80492205103101c1c0100000e2182d400c080d0500035030002c1c850481850100403580c400003486003e130303041510b00700c910b281c20300440d8140c880140254017060301d03007001c1100010340c80c1400ca0340f00d503448011505170303800b6646d01c5900407000d607501d028552181d428942107904518100140d0b0f0010814903071400070010b404030b4658416220310149095000071800c5c004041d00c80181300300807031000d0150741d80181c4058401c1d203010380c185080603162130b0820b4414030034091006400d90480e04410904d640c4a0b0b00c1542d1020050074250000031001070b0818150180b01d9440d081420500240b00b5001c0e400f0003e00e0780402e041e1160840b8a000e00d060a40c076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 681428714 1250 681427464 681427469
    0x30605031c181a041a0403120e04020d02030f0601181d060312040303020f0d0813140705130e010f05010501080c130308030403020109050c060f040e091204030f1b050a 73
    0x1070000314100191a00c1450800c1001856600c01d030f01050030ba000c1c0b900e0b0035030f40140703e104502401d6945019050800d803089800700da03402940030202c4240e20b0010b031540002d100440741d00035400d1190f01d042004600045110300e030b84103850503141c5805000035220b1205900e4801685850450500145840c80b9203030481c3c1509800c030010076030310080040e14000a2109002c0c9105020900008050300000c800e1034010b54032085d40d0800c804404110751044003103d0b51009a041400d9040c003250003005100d04009540c01518041c0d80c850f00031034a2852400a4041c01d9583e400310340c65900020722480c40105080c00091005514040c0000c203052000b92400d81c1103d40040c000c80329048040001c03000710b5001c454240c80c0c0c506410040d008004801c1e0541e95809900e82c240910702c3d102e41212203020b1100150360030a81402c41504242a00810035a010720a01804100b0301440001034401540310300e06100c9007454034030b0194030f031145d80e844450464805100500c540c2da140c1041009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 681429964 1250 681428714 681428717
    0x6090b0a0309050309040905061e10030f02130501080304031a07050319020712030506120c03030a0f03091b2303071206090c080c0120031b0703060c030b01030605031c 73
    0x1114411814800d04505c9140517059106144c400807804114000c01c47e05c3c03192081500c20010700149011010b2007a6044454641c80d056121040c0001340d4070340004900d65002500c0708482219480c1030004172503003030b04a510f2903032011808104028041c403c1420a0b001080501c04505241b44050958000135080400d02210a001d034241c11103650305542c1065000490804090160000036000785400c0d61601e000700a4010061083d000024483c05e2038400600107501d003130f90122040702c14107070780b1000784e04040c0c03607280d001c0128000354284084c007821868150361041c0b91254420340300601c1840e8030402e904502001c000d0785d6020440108072503040f8030221001d42c0c24a4508010002d0040080c4503400850003c58400c10005031034030b00d074100380c0321407401d1303000300e603150007101502c60304046140c0c0100082680c00724400040054041498100d0f40b2458807695441c041e41e8010700443d00090360352100092560741401054010041500601595808412880c00388002c42c000c400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 681431214 1250 681429964 681429971
    0x2903070b030601020f010c0327020a060e0f13050618011212030b030105070306150c0803060607020420030412050309060a111b010902040c03020c060112151a0a06090b0a03 75
    0x402ca03034002d00c8042401c40340d5000800c048450004040c00810121110f1507a400b02c01014460300c03400d030054444130b01e400a2840711000d00c0c1800444103135100041c100c0d00207806190185160b11180b0480821039400c0d000459070b441c0020901144d6181e855041001c801a9001089094007030b0100018941d0050307010061200090000c0d00a0980b00420340e0301076203403104100809034954001020b4a0303a10480c084859842d0400b00c441600c44500606a0071040020804c10b18205000f0540c191000d080841da8105040d1183ea550000350079144210900004005c10011036040c420450745203030400b2802e5050403a4800e40d10a030091621400560300c1d01e85810051074803090351212402484241c050009201606029110300b8204900072400e0450ce40441e900038025201c0300e032000c03401000c0c00da00c3d02c00b24a0510090301015500041c03400500302070040c1501809a201c643c500407a61101c0c9000c050000303980c610382c07010702080f50030401403101c080c0b00401c59003840c07490f16011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 681432464 1250 681431214 681431221
    0x70906050a0905180702011103270c0604030b0915040308041e0219140f0d12030603080d09120f09060c0c0f0806070f0306030b040f150e012903070b03 66
    0x40d6200c4030b4603000701e41e0040c00003030f40d42824000b54850310f02c621015030080c0410700381c1e04042c0a030381c00242c80700c6c0c907000c42401c00c5420711410154021120420700b000c4036000c00e42080411000c0d4080e0308165801222441003000300c09040100b2811a0f0002f003015801d0b02d4076447c02419400040c00081002480c06a040080d0008998a81c00150002c0140400c0025103d492200410920400540b05040741a0b41c0207840c200201c15100c040103400701520100c6641d503102c10918a040e000180340c0d4a0720003002281e00755015158034840c0c10800100c51401c1d0400c1c440704074500a900d41000034040240070311300d911000b50b44c1222450b0400c540d15400714079201c0d1249003150451240f900550350001900c1c40006840c034000c1c51541c0310a5210319191108405031021800090001c00c0e01d200810000340c1d13442200d001c0d9030b0007110302030402116807101030b0603200c2012084490780e450321072035143d001205d1070b01d0009207640341f140c500d00d43c5401c021a4581045102e90701c055000032000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 681433714 1250 681432464 681432467
    0xf18090a17030912071a16030b01020a0f02040504031b05011401080109020112110f0d050a060b0f030103030e040209030d080609010603091a04051203010801060323061f081006030b06030303070906050a 88
    0xf21010703040715070403140040c82c15500d0541c91f00c0d40507250800080c106075241040354008520500d0781d5402101c0c1ca407185001c1c3c0c02741301c09054041c00c101e080041c51105001e0803e0380f1142d030440747d44210300100309110045040c2954846c11380144980d42d03d002c1c4d6500045c2e80154000c03c0a0042c1c4030f01050302100300c07002c0c0c002e0f40a4410210050600045c56404980d0241e000724458201c0c1da02c04c004480e140c10111004c0d0003600510310400000b00014400301c0e0081e00c4402c0c260078001c001500d403c813440080380c1000703282960280031a00000600c6500c0c50720403d01800b52400e880c080003070000301d0316138410217800c1441c207c0304810400045000c1c002c3c04c0c45122250200320b1086581c80d65510383c0079000300b009100a031403c00018415a00c00751828141d20b8401010800500d030a0722010300402420112150041d1b45020140c000034a034001404846889a0395400004889255040202007480000c08003032080e041002006481508600080700344e510724649551200d2000340e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 681434964 1250 681433714 681433733
    0xe0a390b16110409080403050708150403122a080619060e0d0209190c0c0209070315030b1501120902010f051b070b0a1107050a050f18090a1703091207 66
    0x2c1d01070304103060802410134041914010b204880c1301c2d100300c0f105e1650710040b803a1100d156030304030304d08030745010701080101303218000792494075182950000b443c0b200c241e80014111501074204682c03086446140740c003590401420b9500c114181c80c11044040341c4140d1601104460040310b080c450088039100e8251a0381440501c000d501514105860400c102100b4601c1e000c108401c600034100550421aa0721075000b9910b22a4090015603003922501015006086000380b100503c4000c0d000000202e0303603503218240608044040c00300d41034001000101504004207580e010305040488807070050740c1c000b105208179405490881d48401004d841d03041c214800c0101000c4600c83c050000c00d0507066003000704546042e58a580d0042c0402c99122912400280301e5640e001c02601ea0820503814031000020391410010300401c860940c0c0540a02d650b1400d88a89902c0d0b030240685000704035a100c203040800a42c180300d9801c526182c50115a103910491588001c0030002c41d504080022016 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 681436214 1250 681434964 681434993
    0xb03120a050c06070201060f08030702010509060711030d1107060806030307060b0a1212081503060403030b01050d05010815060a0311041e0e0115051801090e0a390b16 73
    0xb000d60340d107030400d074200034081c4c01203002d007041405c00500300003000d40f030000498482907410f8485a041c590000c0030400f10382c01c1401c041e103003130b401c0c1044951142c0d02400b405100754001e131904500e560b0b002d0316451601110360881d80c1030026520910000340e130000180c0f100b0b02d43c402004281000d500300821148100d40e40121030b407101c08145241082481c01048108100640c0d0380621643c070308000044c40c1a00b2800103400d9008600480c0210f441780c5c209101045041c10124903002c00010748000702d540c260301c0b5010341e8000780700b646548030703164519130381200e022200225050b0960303e9104090400101c0c06103c1c903920048401e5510503060304195028500c0310030002c3c0000d0054242c00b800030b5041104c009820240c01252901e4009a00c42009a005d880701c8016801c0036141d100800c01415400701e180720306c104200000c0c851040460b060b664502041d050407030621206203080390154500d5000c3c62809800f80a0f81c03041c00162000e108400b503904e01d000c101030030188040041030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 681437464 1250 681436214 681436237
    0x111215090a0203072d0c08042309010b09031b01120e010b09160e01030f0902061b0f07060c0b070903060e160b0f0f0309072103120b03120a05 62
    0x81040152003207181c0e01030742c404d14440d26030b103100c00c1c40301072518003400c8108140c06074a0100202800020300c202c07082c40c4568454030070176181c262038440145010145800c07010703480c08652641050340c20081d85541c0140300f511101030418400e000007a8032407240c3c034410082c810b84d18080e03201581c81181c0700008100101008c206d62000600c02c24060300300d200c00f03140281a1078020a6501d1120700320001c070300349180d4031414480d802e280114050249142203114103500d419035407015a0302d060081420b1105507907020644508100d8007810009030742100c2c002c9401040d400c010701c0c1d411100001c80203070300011020450365810401d0303950318a240c00103001c00303260107003141c0c01110001d800344c400d410054128601c1aa0342955011503c071740500f00d001d5000601c603075190000c2c810702964110741c0714426903003000d032502400810620105403280002c00725890304402d15800c00c40c0d540d40119000f1040c09900c00000204e9500c2c040c0184040480200217a00d401051058041c0c40c82c5c105034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 681438714 1250 681437464 681437479
    0xf090d0602030a05090a260409020f03060102060c070503030109020a0216030c1404090c09050c1b0a060b1008060105090d0c0b030105180f190e0d03090b01050301111215 74
    0x124240203000b504100e80d10b10a042c5480301041e604080020341105059000001c00810a9600b10312600300304a951101d0400a082c0030103d44503405001400e11800100b08880d03c07407800100080c0f0385080a13007107144021f410020000803c80100c21641500d64404016940301c0c12094224030f0503564003905210800300c0c8001104115025800e941114405006560b010b90314001f088202c40c103103c0010070544000c11704000740e54658003c15408242085040e00341a00d40c2d0950b0b514a007a07441c01c110302d82200040304200b1903148030b1100080c1c130541d02d0b020300c152000b4001d0414030000d442c050500c107012411a00d19030b600348a984450340d02c2036501c2030ba0355845260007926042809100e00c94484508410034a8101d1011a40315542070341c8049101d031111544a080c81d0306058000710081e845102c041346d03903c41040040c00c0300856a400142080007800c10300090401a04010300c03070390501d8500c01c0c40300c1542c03041c2c0314841200a8942d00ca51140140030000c140f1001040d50003049 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 681439964 1250 681438714 681438739
    0xa0803160f061a01120e03070f1106070308071d131d07031109090a0f0b043f020f10020f12070f02070e07200f1204032906060f09 57
    0x18049842c40c0350f00003a03e81044d030044460049060395038070400c101c956401480300ca404190aa02507894950080340100b10030100040800c0c0e107544a0581035010501c3c0b0700600542650002a803001c5612800c0e10b44041e02c40c0c4400285030900c55494111440e48850010011280303401014641c580c01a04560302d00d81d0381e14103191020009558288074060706800030b07100103004103a009581c2c3c1e014040c490000c0d6607540c3c0c1070b107102015006840d00340c800211150050061500c2c0303400008110300aa000c1c200a41028041151502206046410201058099540000c2c400e42a40c00300e07000545c0350595040740741c105028041c04400420b1002c42031141c00c507084115900e0407501c682c20388000ca500d840405d071210400f50745100c005032000d07100313040003031290580c407206a1038882912004952041c01919119425081c902e40c03510010b01003007040304244030341d1980a02d030140c01c0d661481c0307070950105810008141d80e0089900042860707e4150360340c1100d41d04103008155042045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 681441214 1250 681439964 681439991
    0x305030916090f0501090204030203120d0207080d060302030c0a03080915130b0403020909010903021216060e0c100318110105040807090621050c01030c090e0c0d06050a0803160f06 79
    0x8843e4400c1554145804004628000c19000300c8064a40180003030081e2000044030403000d920280c00460529030034808e410008000314010b10b640001c180740465a1801c41c010075007802400d43e9150b1007807120b194100000344426060f00c004040446509800040441780ca01d5944612000458500506500441d000f019800584143e03070007620400740755034a920001c1d007220760702940500568004407040071040c2c1c1003070042440701c050482418240c043e5541c1e0200703803a1000d210f0b400980000c41d00035413908240c004841204071900e02406845984070310b036918030032885400382c19100000c41c0d2075603e0340039404690040c400c0740125031100d552400000002d00d25400b541d030310580f840d00800018007542100100a40d042809810041001c100550041804032500e4041c080e00400c0000c890740d0700050113105413043d0420541e0707041600c410b01c04480154026900c5240441c000b840b440e64004261132044c10b1b072110080d100711407400c1c0b9505641e45140020112407c0c07491074180729 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 681442464 1250 681441214 681441221
    0x9070f080601180807240804021017090f1b1c0609170702010f0306053a030503040b0108070308041215020315031006060e0409020423011703040b07030503091609 71
    0x300c005440e100055034440b189100003c0940c6d04420005600c0c401240242c501148a0301c0910b0080c1001340e65400f120070117000c9904116245841c1c1c5d00207109021805800344406190760b1f034800034111003034030b448001901c0c4140c1c0c03c4020361031200a075a044200304080c1d000311040b94220304507000588581d0305005c0f040e41303c0d820890000e4480005079290354000d00500055a10042820b201080c1540305109502803941c002c0320692a001007040e04103021501c20b0031254000e6883c02c0d9680341c00e0401c015046010f90180d082607001480800128000c90300361020713101504442e6110710198200340503000d21130402210840d10010502c50544c1d00120760100814059090310f50101c1400030034421103c580c0305074804680020083c0e4034502e410b07031040c04028401800029025244050a071303d40c09442d450070b60210560f001070040040304c0c550949400c20b100d000350710703090825801c10b00318050040010248407000c008240b03412014444100d21134000342d443c15840d9910641c3c00f016 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 681443714 1250 681442464 681442469
    0x230d050a03090f030b0609070207030b011404051b030408030a0e070e0108060f0601020613080c07060c0b0901020a17060f030609010f140402030705010c0512030a02041409070f080601180807 83
    0x3181100b200011101c20b01154403040781d8000c0d440b48582d50701e035030600091140042190b4114016201c02200186652120350b000c2d100700b0741303004009001d007801e000c00c4030400351035180307034030f500114030602a4000303412030f0b03480360740440881d4a1351501c1d44050090513601e00d2a00c094003030703201d000c41c511022845aa0413038484104903550ba4442c0010344400c007209840303443c01a045240041c90030350003186034440d15440b55400a00c0c0030003801c2c2490074480590010000036048625250502100c0d6000b5600441210021481d20a00c2100608254440c400e07002e8100517102c0020043d43d5129035030a40c1503c040d05031580713442c0c05d03145a0300a16500140c0c244e010700d000c11040d40b4008a5501e284101d50182c000d1081900740b600640384c0341e003021011512403054134101e110307070300d0510040c5010314070308400541c84504042d942c00140440180d0070340100c200b00f0800c40001c0d40044126510380300b42c10a1070007900d5000048600c901d00760070700e51040401c0107000500d44000940c0904 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 681444964 1250 681443714 681443717
    0x1e040b03190902090408160b0a090201110601080a1704031406090129040e2e0b04140a0e190b040b010f0e070e01030213090c03110f04230d050a03 64
    0x444410a040c1070080b520706450207900301c210600040c2c00140403000030300b00060110001c140c100d0b542d903250300d5011000c84800d1050754581d00c45404558120707012a00300c40048002c1c241070760506900560f1040e01202c00340c6195001c0007030010f1140c0c0c030011a0042e50308056004585c040c3c910703400781e84520584240c0d049618150340503140ba048a02002c0810602e415180041c440d15000c01000c0c2818025031f0161f40030fa40700c03c0c00d030100d0007020305090128a940003d0307010010303000389003240e0303000c0350040c01213040c00c1000e41f280b5041d603540c683c01880f880c40007801840b40c0980c9803400341071900e043c0070007103094181001d100e81403031020302c220b00c43c840b10342d442d81c2c0303540d400e1441c0610752051a9090008202040082d03000c3e45403a04a60380601d001401d024000c52842072090055000b001130966500e12422141d41c18091918040f4550341c0140c03400a1409490f401c174806c034800c55000d8103000e0081000c000d06161040c80d4450300800c1c000c070047c250b0510343e071030b415107600440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 681446214 1250 681444964 681444991
    0x17210d020f1b16140a090e060702060906010b04050409111306180c020d080a0b09010f060815101209080d0c1b0c06350a0b180c1e040b03 60
    0x1940c80c400003c41c54400301031904000501441c0404d078030b034101c0d004030205501400e000004a50941284201c00c1c0b400d803d400181554249200080e0914a001e090b5100344c0c1c1110b4010b120392003c1904540480310300741c5000405040b1410407541841144440f5a40f16042c996a181050781c550020001c0d9101482d540e10072002404130030b000c4a01d07072800500960046444800d070140034102c5030354414540c44001c110781d610200001d6a02000340c10008403800d80c410b00b400440e500c200d038160b20a078800c20300361508008400003201604d654a0380402c0103004000c905040780700750030101505131301240d01c50702c602c049080b0704040c2603250710140000c0c21071220314503801e45814142413030941116074004000d0034240212181d4031011f003800d400d20140805100e0b0141c1d1390024810001c51a5503900d540e003440c100c03050595924514a500c01c40c0010401800f10100c0610640c102004499a03079403a0103462010300a102c02542e0300701d03600004507000414a420310020b5105211180244 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 681447464 1250 681446214 681446257
    0x70807050406082116060f0605010201090203060417090d15050705040e01030803130f0507080f0d08010b0d18030e01030c05072103110408010b0a17210d020f 69
    0x802292080d215a50b00d13a804000104040f0ba40c004014800c59a40a0520b251201102c4205146400305100301c520030f03a00c3c2c1544100c20f14600c40d0801801c8248028480e0054640009544a201070000b6104120184803000111020f00c126880980013a20b04050a122800d0040191038600e0840d0b900d5403c00000600740340c030540440d0117860000d80b101000c0c0c0d09548030542e0f82d4200074221480a03102045e000046a680204106003030722840081041901305401c49081600724082c566079580100280c02c0c03135582041040b0b064561480c0c2d41e0f81c136004101488405800910469000300001c1400301081c19804100d03440b401400b178809000c4100042c0044a4502c6441c0300500704030540308188030100b060904c0d004110480c0d25010620345a4040c005c0c242d94003951002c01142c1d5180004125410070f110300e40000e04040c0b00f000300a4501104040d2a15119010344d1b0100c80d02001090340041084103407003146010900c1191250310720300300c00d00642c0c8501d40c2d41c8040404080b50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 681448714 1250 681447464 681447469
    0x14092401050405280f0b03070509010201060b030f091c020d050903120301060f02060f04020a090c210e0717070e0403050f0f030a0b031c0c0c080609010605130507021b01051b07080705 80
    0x5c0008403007980c0d2800346140d64107107081700c103078114000c0c0e681103540b900c0c0000351100140c40514007902107005001c400d400c0141071107240078000e05204581600010a1716000e0750040390b0b0031180703a00c0e800c00300d50f03039008140040d003003003502442c0e501e0045005c0004202d15034003562800e4640840e40841e84652640f420172307408074804940027540400a0842130028601d40c0e00a140d20002c0f034100920303800144c40c80308912176464400b0034009592102e8440d030a10040000400401000c01d074001400403040050f603ca081b140940c2400340c1400002c60308040c0708504860f4050781c01d03d440e1752a0f811000414500f030f401541c0c242400c50410380c210b410b80c41e020610364101d01c10103002000d10119480151071400601400390b50940d0031032400900d100c02800494803855120000095071402c080800c0789802c680703044c40c2e480034a0b080812200344c0e0006810f80a41d40200307481070031021480b004841d180303d190320702c0000030f1130030b90200c0781380c040040e012003075a03c86001e8a00c0c051f100e005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 681449964 1250 681448714 681448739
    0x2010903080106021c0c081b0c0a120c09050c0c030d0f1b0c1220010504021c08031308070f03080103030e010c1a0703060f0f1409240105040528 63
    0x2c00000010045e140e40c460140141401804184582521800c040702c03001a0b10818034034691940a40d04001040c60f0b140c5000900c40c0c020b440040c200c401c0d5140507880c8c10603120351724008c1d868002d0f0740d1800b250a0328040320982d070350078070684100c981c0c030b040804810340070b0249161101071050610102c01c0c607524030010b07503521040382c61f910078a0659168443c0080d00700c00e4240e01003444611105100050680d20080300c00340351900c00030890341000c0c0b050281c82e005034a051800c40f40100800c10005040740c0450b83c200c22300690001000c501800c007503180e03205d1a01c00030924034483c09040d00305504020041e04890080d22400444d8041c0e400656811144140c014910152840298541e050307000e01150420040d00d00082c10307a40f10b192408020809421194070240b038668100040090f000400760f01c40c1080e0b80c01401c0381000003004080707400c4061032070135468648130b20340143d900c5030003070301c00920004046204048220b03001c26400442c4a1807140d0324030b0359000c080355000383c949 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 681451214 1250 681449964 681449983
    0x60e010e03280c02010f0e040b060406030203180a0c03030c05100f0506090903251e1b0501050f0d0c0e2101050c090919090606090501140d03050a18080d0201090308010602 75
    0x3c40305006c10b0309225046403058100e50b41c89901c5a41c0e10200030003519540080e1001e000e460b140141c6e2403c2c05004010986042e505d14442da5218485280c00501001c84c00800c699160a050710041c840745001c40c2045641c02c940e043d903901e00401c2050a2005400003802600d090701c5c80c45081d119010b1150300c038070036017071034645500408424902c00030f02a841c0010745800b40502c0c000e000d942e02c2c514210140d94040645142d81542c98005a200c9104401801000c090030914680440300a500780503019021b2000f88031030361040ca01c0da80d503002c0d8000c00c2010350000c11060341c0101e01c0c01c0020380c4264003981000550f1802c00003079410803190301260305401c030080c18903986030740700030398801105400c038000e030368103510b5501940028003680504805000c3c0d000740400c2c1d40d0f041a5039802c544103010b0205203c4c4050381c1d08440440d40000446070b60148a1400c9140b500464021850301491588020003910802c25001c5000e54194842c2090318882c1d5076030270159076030321012030b5110400c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 681452464 1250 681451214 681451217
    0x519030c091509030b07170723031f0608092404020f130c0206150334080a390b0a1b0c030c080d050304060e010e03280c0201 55
    0x1804148142045803020382c0b504440d601d04a00100d40380e540d070844046094943c900031407a070136054a01441e650b03603900d034041403514000c4130f0311300c6190248000145914549250310030000110f0448024183c1d652000300a48900c0442940c2d1000d000307050400485450000e8000c040304802c1141c03c1000404120702d41d030400c440c0c9a16944c0812010060781510075034044101403180c940031a8601070844481d8054000c0c019900d05940c00700f59502040d01000d10075001480407c0d01c1c540c0c088000703118454241e88507540385402c0c00d02d10454903515009134400b403044403421010014101504400400d000d00784140b500c4002815003400701c440c000d00c144800c140802030040d0341d0910085c20161000f46081005c0c0406500c81c08041e1703090280507210000f03000c1060040c061404d103840018000803005011007509494010842c0c000580300801945e00c40c440f6402404007500072480e040c1410003500c0d920003080b882a058401402402100a404100a00300c514020301030031400c282c06 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 681453714 1250 681452464 681452477
    0x33010504030206030c091c0303060e0405100e1905070f0801020a08011e0b0417250302090c12190b0a0303050f032809060501090c02120a02030c0d0519030c 68
    0x3150b007000704680004004041c042c80c18803a07400669580c25403041640b0340904001d2050503070303003401400c0d501e0a42017404400004010f0200050001450010050680b90001001080110f84600f440302100000420130000040c0b1402c2c0000803655070116074541d4400702d00c20756230311001420703801000ca0200108248000411960b2401800103070b10b99484e404029095803a00030300009034006801c508801060101c0700c21483d80108505100f01c0401700102e031004c0c5c030504550881d80c4040c0002401201c90b800030940009561301540c20003041c03100c8070451072030000384100c0001c000c0c881245040741401841c115905045d050304003600e8155484c1c80c80c10700c900e4141691584054480703201a4410292014a4111a0900700109605c1d200108200d80340d8217080040d10b0043c2c00101c04245070004134074076143c000600310540481c0320309039a110320040e6026030544c042c9180d035001d20300508501c207191a038840000c1241c3c00055140002800303c3d00701c00c87c1101c40489440021464 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 681454964 1250 681453714 681453719
    0x306100b031f120f0209060d0b0c1e1b060a0510060f170405010b0103362a0302091e0705090f031f050f16030b010e0933010504 56
    0x11031042c04940340d00400d0442c00e50799505803481c10205440f9080c0c0740c000e081e401c00320031854500c558031341040d0121018020b4691070b4940c0c01c0c0d02003014240e4840100009600754039204141c40002c0c02c0d01c200710800340c071340001c1d041c0d01d0924201d030b1031000143d014640c0011101195403281e0340c01240c180d0307640c40300d003410100203a4801000e07085413414048038403200c1800e80c0492044d50f20036880f4200106495845c02c0024094070402ca04014000c01280c021408803088070342c2e50251207080384965200c40f01e05090a4183c0d42200d001608510700d03c00e188440300168292500449100b5500f21101e580c03140c40b1010071540f090740b1710401100c0310011400691054003c0e0005041c020044581400c064002170310b804001c9858058554504092003c2a14207115543d84595190311800103407401c1006140311503111031020041c0755841d00e64000b00e9100f0703462003060000140100b0080d05095014800024000c0f00192064130104031410161070130041042003108103844c0c00c0d003001d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 681456214 1250 681454964 681454981
    0xb0c0c030a08061302031608060d08090409030c0f0602180f010e1011012415020303070c0510050c09040b01030608150a02090604060f0306050d0c090510031205090306100b03 76
    0x1070020302000d81c000f03100240496102d4240c80118000c0400d04664400f940107c58060705408005003071a00c41d01d0392181e08000315203054121004048100c5001405c0c2e0701034a001d91301c1c010500c4018007210210312040080108540c001d00c100043c29921071101c801000400007811220010640051081046002c4500300380c008001e09200b5400d101b1101601601801e084441c0300c20b20b040c00901d054500f48140107402110005071549600404040304040700107503803488083e05030f2040001c02180b050038004140310500940100ca0000e001900313058031000070310342100104074441d0385442807281c0103601900c91003044803102e502400400a00144100a4ac040201030b003403216003c000c00d02c0542d445000420140046072180c40c2043c00c41d00b070003800c82c0c071107401543c010b1400003221000b10310040000c00460350f14440125565540c080001000c0c81280e100800142001c181d1403400754102000c0d00c0c10304401d404451245c0c2e203140c0e00701102e240d2442502d4540038208041182c0c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 681457464 1250 681456214 681456227
    0x9100309060b032a030307080f0706021c33090b13060b0a090f061202090613060503061306031e03110708060a110c0c0609030a02040f090b0c0c030a 65
    0xd034056500025104140004030741407602e442c06080e14002e9452281242da4450003a101c0030715070580045041c0320700741d6100a402e114141100c4c06a03400412000c0030030901c0d80407224034220b2003141000c440581c030882c10140011300303811403083d404040d42e003141c150b4400c9017410320920880d40c058101d103428041030080141c3c8a0454005030079800c4044900824080d0000500f121844265101d0809000812040c45071b0001040004031901c1004619440000104490b500c404016680c012020000b00b803881810b40b192050040903100064194014024501c40c080942c0c0c5030400b4000c184040c401c079402400020801101810700c2c20740c0c2a41c0c4c240c102c1d0a148641002420079002d8911107107000c41507071200040340d01100030010303101c1150080c40652940101c0c0c007400c1607040503803d521344110540c060f015400c0444c0c01b0b074056908003c003056003074000d0320420140800540810140c02c2d034407419101c004442001c0740b00940b20a00301c030b0380762800c08007a506200210100300d50300d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 681458714 1250 681457464 681457481
    0xe0a05061b040518060f010f0c0330090204110c10020c1608030310050f031009030e1c14061e06060f0a02010e0c0109060210050604090c030f030e06091003 68
    0x2441c0d0502c0081559294003001d072142d010000f421094503c1c3c220b080024400c2c500304210b04204d480407901080a0304810798500c202da0608090070750710810140d071110018420ba408040354180049026a840ca0303a000e1100140240d90038002d85140c4850b00074148100c001480c9540e1000b00e044826480550241142200550541d81d50301d206602415a222407500a080700d6040042441400480403c481d0010002034421111100300500003030f0b04e03001040d80304040191290f944900301071290200340f40b038107002400468160302141e0310311010641c010045032400480609100b06010010f41e580c464109908030201192041c0701c040002d000c084c0c207298010380d05103c1c0c685180d200b0300240441802903400003542d40c03494504a49010b52215046040c4109050140001035000c1040c0b420034007040f81c08521900c441020400070110300d04041c040084442000c4100300345807614148450180e610030000902200400849200b0000001c1e80913040d4004092414084e8000d03800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 681459964 1250 681458714 681458761
    0x150809070e010b03012d0902093709142703120405011805120c0a12030c200a0210030906050411040c03090213180c03050309040e0a0506 60
    0x1449a030798821110101d000ba000380c9100b02c80800140b002c07010042c118030410180c035003204038100c0d44041c0440b030305105006540c503540c0c00040482058461404599480c11721682420b1030141d201d686e40300180c40324049147e4400d8503c40003c0000780780c002c2e20464a007403400c6525036250305090030b1a11154991480600d044524007203403202090014000c50300d4005d034903190718605840c105084948040021111007850304024020800005004140c60481082c09030354410f4403070f144d4540100d80c0d9004110071110a40004219072603044211002403945a01c07615040f031000807407004540310340303074130703465200100400151800015900105030a0300380082d12000ea5201c52050b42c004aa0903158011020042c4842e82803610401d5035503916454108a624015400101d06008803080300707030401c1e00c540040464a40c48840a040c8035031042c0307a001480d640385055501d9800480b0744511070313481c0280341d1460240104030840c006070b00001518665035101c1800f01031a211041e98003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 681461214 1250 681459964 681459973
    0x207150c140f010605010906020312040303021b0106090e070806040f060915020d0608061f050f21070e0609011d07030b03070f150315060c031209031106060307150809 73
    0x1d089101404801c500300c0085001150300e904100015000c8501c1340d015008550040100380c010202d0400015002a81858050783e0b401111a1040d1100c43c00e01052003c0d51812400140c2c141c220740c05250800e02c01015110101e07950700f1074a4440c4411200945041080c00c504000100c0341d03400010054800c041c0209000b5021010400300e801401c104800565a890b00b4010304c403042160b02c1e40142401a01d100383c00740c1c0048012054824070030f140c0100380301030b9851083e68480c040d4641c00750000008110302002e20401650740d00030b0748144108500300c1c00c040340c070a003002c0d402c441c16290100c40c0802502c2454a5000d0010030007080c48c4100f50b0303212404550b65905200603c001e021084941d802c1c24104007200111034260659a414940f900e2055010007104411000c121025420720014184850038243c4413054042031511110b89804074a80c20181c2040c0d039980c035509540111a2241d4442d41415a6003a2030f0048005031211203440f001110703c501c1e42540d20031250030584 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 681462464 1250 681461214 681461243
    0x31e190c090e160201060e070e060f0c0307081c0207020f09071701120311060112030c030e041409190221070e0901060602060c0702102f0d0f0207150c 66
    0x3082d452010380308100d030301e515040b18036078190342400f400c0041c25a01040d6603a44c109140040d03c5140711080050040e50046500c1041c52180d4098a06810b40c0800307503560780400e0728100085030b000c0c080c0c0440f90341440140c0305801e0010701c00c0c1c42c1060741c0a81490300c031800c07540c20040ca80e01c000b00040b040100328000103910002509005000344850424060a04e0701071078017400b80c0c02e10085101c0a540414010013281010403060030a0681500300b0304045906400c0032101342d4410340240da00320742400038840c04442d0212200380306000704d40035030741d06907120031041d00094042d080295200c5000c00c80c0140075260b4030009aa00000c1c03d048038480d0780c0c1e40f8110f0b801c448045030103d03a140d540318010803020381c05000181d8000780383d100c6240750170170550000d040034401d03011890420400e48250300c06418000780c80410b60100482014420700311622440d40d60340b000c00001c0c00a03502d10f540940c0305000040d003106403170042c2d00c641da407011085005c94129401c800705880356902ca50300f5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 681463714 1250 681462464 681462479
    0x60c18030d031e050f0142030b030a0209010509180111040f0806040309140a080a0b090d0512040b130b1f0b1207110705030f0102031e190c09 62
    0x40428441c5442c00f00d503000d800c02c0c0304a41c501c0310062840d03119013020101310203155004481c0303066070340c0036865001c0007480d90110362610780c24011901c000d10742d8910041c4118005465001c030060300b82d80610100d02410141503d42d004500000e400020b52001803201e450051080c6078410f003003041403500c40c0381d0022141c0c01d44900540c504040003002600348410001d100c4001c0107480e0100060030766041568000f4642d200611803403808400d00c0801e4402c0d695001d0304000100400c40490b608180242000b42c1007a50540d0b6030800ca03c02c03450b001c06070500803000c1c0c6115401d10345903211155140c1d2038a04006500601d2a00384080060030300c4009005050402d016001039a00b0740007600d410100e40c68164140d030410700103801d0a2040b1a8001442c100c7c2c2a480440c40c80c01500c4404510f088500d0000507400c1294580210000b110040304150b002d18801c86652241d0300030a07482e5250410903800541c1c0c41c0e4404038030303d4140106200150003042c0a40614030300103450550300c085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 681464964 1250 681463714 681463723
    0xd0c230d030f021c0207060507020c03030712020a08040305011a0405070c02060f040e010b0d0c0c020a03060b18090c0910060e061b01020d020d050916050d050703080a020703051e060c1803 82
    0x6103100313880e400305071401481943c0c42040e80c84081c0340000c00300c1410000c0029601d0040c15401004902d43c0035501c0308032031080c000320024640c02045141c66903103902d0410f018000d0740c51004131031090345000d05903a1915000b11400745810ba1122007406689070244516580103501d03c2c0115481000300103000d88040d01d4190082070015981c0d511600310400709004d40700b2001606042010001504000d641c07980c005404583c1d00040004018030354070081010030240368140038000d881e00c8200300c00c0081c04914205c0c103910807200c1d01250303920b448400c3e8203a0b030305000c0e0000085940c070030200c10b8144400200301030b04036004c440c6d1500186c070f0a0582139901c034840b075404081e00802c1d00c0d00c030600140a5160012000b8014102c40001441d082c445800c0c64400c81d482107610908c0e900c1800000c3c0201d030050360300410050364488400101030358440d1184030032141413241e03240118454185200c1e00004141801c0601155154000c4903140da03000040c5280c0400c010010b90780c101d40c0d0401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 681466214 1250 681464964 681465007
    0x906060714030705280c0e0402120d020c0406050102030f2d0f1e0304050a060b0d060501080a030801120b011211040203130b0133050c0d0c230d030f02 66
    0x10050a40c84c90940074100000000a07207042e6601135482c0103800140f0401c21801510003247d143c442c0740d9158000a03943c1c1c40300d0354000704207001c0d03110f03202c2046a02084c40c40c0400400d540c240300c090390344e500490703403842261f0050395051000e2001842991818807502c11125040c1c03480ca07600303000041d01d0480d40e40b00c04203140c5051320009038a0488001c00b44040300c42050340708200d0552602e521229107840410200800d0f11340e69800c2a1400e6944100c07409a40340c02071400c1100b5a15885810780d075940400082e00885c525070000560440122507141e4042d0740002542035036442c1204001e6021100d038000c40f2040c0c1c0f403041800c011b0300c50344055445000d89180e4650000f0440c1026400f4881c180c11001d098410201150f95031454804010420f007415030381c0b90700c140202001199903000e1508580c1d02c5004004001d10820303440810218118001d034a0442803c0d030f0101c0c0701010000207811400c50307070014400081e0b4540250f0140d411070801c090003510b00440e0300c203440c0042c030b1b104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 681467464 1250 681466214 681466223
    0x110c0d0e04020a0c020f0a091a031c1d06071a061203040b0406180902030c04061d22110d06090f1401031704030c030b180105010509060607140307 64
    0x694a002909520024108459038255811071070800040030003404034600e01d001901810705122410000d07280c50701030340014481201c04000704248000403803404900400300718461b224800d040e41c28051500700414114401c3c1d01c40038100400242d0800a5880c009a81903109405000240101b421020746d0359840443c001050361600d80303582006401f5400d11240e600d254070510041c050100001c04072000c5e03aa803400c1003210419084035100d00c03d4015005140c5250000c402c0c0001e40362100040c00a4a0b40c9844d076010200080c010340b1171842c0f02000555100ca4031001403c85c0c1482d080740c0020802c0440b201040c15050b6100d4040301e580311400d1091115910f0000f008000340a101d03c8001c00b1940100f407103918102c40b0f642480b0b24041c04054009100d00c9a0020584040750807100110340c410300001103195a410900d090400882d0b516500b1207106120190518042c81520b060b100010200c3e1030303540b180b505025180c1c03c5030030304986800c4458404041507c0400c09400b106125 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 681468714 1250 681467464 681467473
    0x41203030603120801080d11030f04030305040e180a030302090102011b021b04050c0405010e0117100e13020112020903010e061f0f0e06042313061503030c060207030201110c 76
    0x19450710340d03e01c0070f10002c82c00400c102c010040c8840580860214440e09080c5440c0e1a0881e011201e28118030130b1170381e10b001405c400140002016004070242046684806015000780d582d008012122401034900c40e145e5003045210710300107402940a0710403010188000603084940088102c02c0070803942540c0701580c0152850703141da40f08010082c10340c14003030305c052026007041c1c0408102806540501c506100c52041c4644159102e03a502d0b101c008025192849103003814031001481d05041c2c020104003a214600288080d000c040544420b154183c0da10041848400c1c000b00007900100394060785952030b51290b2800702003c000140c0940d50300f9140c016080308135406161607260786d42c010398102c00100d004010800028003019070102098601040c400c14410303a60032607001c01085d420711048503006000d44404c40406101e00c85118000c108104403035040f019902038001e11009000a418144080005d2500e40141c02500d11900010441010b082e0810206400039522b0080c198403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 681469964 1250 681468714 681468719
    0x3a0f0314040b0907141e0117070e0901060903020609040b040209060a050d0c0801050a061110020c0307020a060813320a0b070801031e1406010b04240c170412030306 72
    0x82480b20074001d0440031704918403580309101090207440001c0214a40320720140081d04030380d010b5007003203100c18010002c81100d849e140d50050b000381499042c981c000c102d00c00000c40e186009114680c25290010500c50a0824807010030000e00300c0c441002d50015020b01c49000e980c0c1702c0201030a04500c00340c40d92a2aa00f0b11041034085401c603c0c880f004100e80c62004020316202c1da15074100751900ba280c03145011030201d0702180350440e40d40b00d2050740c80c80064004400741c4048050b01c0c45910072107500340f05507034841c011144084242c41e80200403079a9510800014000702c0346804a040c0044140390700901044040c0700c8004910341010190000003d000c00c0008900480380e001450b418504c10650451f1540c800c0d8181c00c0322003d00c2e20030142c408070f003449881441210f106220303008403034241d0b840b01034801c9160002e100d002180c082d6503010000c403c44048540160200c16a40c10090100b01e4071882030508440407040b107040c0d420400451401010440148000d010381c034041608c61 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 681471214 1250 681469964 681469981
    0x13060c0909050c090a1205010e0a060504050f010c080c090102070810050105011205010e010b07020609090414210d021309060603142d06120a053a0f0314040b 69
    0x840041888a002030200300526982c5d0380c2640c8003068940209480f03480c81090701d052030040c5102c10741300f001845070042103403c0104a40081c0d03c0383c2c0c482c0c4182d600e00c070540e9640900340d803c40032800d4041000c4000003004d101420020308200e070414812590130a030307103900c06414022040e2101c0981e40d2624018845541c00c81d8140405508005003003005616140c1a0302958106002d2007a40c414005402d505556984044d1070105500802e12803070307402c10786444035460301da201c84107503180104d1264000c4919484c4440c0c1800149155440c50022114240390003980050319111075038801c4c1c440450a003a06202d004058180c0d0703100000c00d1030009080540f02c02004014455541440f440d00c051501c1c0384406a081d4244000800c0064a90100284800d0440c3c89107a5540c8a154020070501c44009640c5504030003a40c80d0240a101c800001d00f14030f9064402603c80b5481401e800042c0c41c41607034002c030b216a0340e01c0d0008000c40300741d1040c92500001d841c20b4036221000818401c80f20f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 681472464 1250 681471214 681471221
    0x28230408010e0d0203042601050f07080a02120c130314070801060f08030d0902030309060a0e180f010b030405011407030b1921061b05030a0b0105130e13060c0909 71
    0x40102e03000348181660351000075605e200713a00964070001e121403802c0e001008500b5102c00140b01c0c0c040280b115181c19401c08400200885035400000d401380c1c0811140c081c00d1089405250051140d02042e5a9084924125900a0350010801160003900101040100344074101155044000d080035070319240019094458070b401140c81a0241d01c410001c280c1d0003c11515201c000b4440451088094000241903020701900c01d80c029900150a2414550001244001c15001c880d0220008850860345841d040c0c00c80780b5400c030200f080e00510480d0034480c051503000341b048002246609c48101600d44064065403010003294590340c1a11241c40d208480008220200207501803113494800f240d0301c10410f08400b281c070356001e00009414000c00c4d03001142204100e5035200c4000d80402002400781c3e20031211440b40501d448004442507204d0401c0b184000d66691b03262000340e08065801c266400050b040550071640c5207141c500068140c02461104040c988603403503003528092613a001e5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 681473714 1250 681472464 681472481
    0x305070311010906050a080a0605040615080a0b06070212010b0307060c02011d0901180e03030c09101e050307030e072403050c0a0305040f06020f0403060606052823040801 75
    0x500180f10030502c555940f05064030400c4655183c82c2055403103c0200340000c0039180c0115400509200001c81c2d0300031100c80c00d0080030020b56a10400ea5500c40041003100c030421009940700c20204048405840d02c2e0701202031194120000150010701c850010b4030b44041940030501052900843d10255a005080384240c0140c19020782021459070001502c00c600502a52001062a00c8080ca949005900050108441c0301c1280d550f41018640180c940d040161040d2040e0040028502c0705403250044200c0251920142100352032400002d4501c0c1e00300501c20710816039924510f8400032400c0000d040144000640103240d000108804690019114002c5080c14185170500400b080e05008840034003d10f4980094952220314010340104120440a03003287e002050520402c6101d000030000c0740d101e18810050196074120503182d0340a03000c11403140410100300400c0c14000d103814040450780c0d40c40c1a0300b84104100110340442c082080c5100b02c45008201844110400d100d07a125 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 681474820 1106 681473714 681473717
    0x604081e0309071707030c050609130c031a0102010c0509101803050706170105240d0212040b06030a1203020a03020d0f0221010b07060504080f04030507031101 70
    0x20349407034600072407406079584c0ca50001c40103c001034203011a64844c03080900300340b81000b000603a8000f0918280c000003201c00c01c07030031064540705a8002200689001805098040c01507620107902c03910b407410f5a00d8a2659412650081d00783c6402e56403c40b080300a40f09200000c40d14200380540034a8401a40e003000720030000045000c03019070b80702d95a00a48400c01c00c00030382c01f040080c4551030300800942240f8082d519941c02c660403111041da50075250103280410321040364410401022000480ca060004100c0e0415019802c41000c400070032003103480d034070b8003044800038005803424150300052307081405000b074050b58030900030300004000c40812080000041c0d4000840e202d28559074648038100700c040903030345038160340f03012032100e0404080d41c1e200c5d4000c0102030025030780c151060007681c11313034070326800140702861081c40602503042c510b28004a5a601c0240d0032030 = true := by decide +kernel

theorem cover : BRFrame.Cov 681294964 681474820 := by
  have h0 := BRFrame.cov_init 681294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 681294964 ≤ n) (h2 : n < 681474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
