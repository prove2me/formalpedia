-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3892
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:09.738668+00:00
-- url     : https://prove2.me/submissions/33987590-4c7d-4cce-9a45-0798b950a4c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 699820143 ≤ n < 700000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 699821393 1250 699820143 699820151
    0x20d0612140109172b0c020f0304030c03060504020310020d05150402090915010509030124080a030e0d02060909040b0a0518060c03040c031401060312050f12100b160b0a 74
    0x16107030004c0c901040e54140c8510070001404001000301100900c107441d1a49403c80c0b4181c0c80396007014003a2002c43c440000520990b40404002c0b94007000312002c581d17011300c0d180d034034500d160f41c0c400181000620036079050161002c1e68040300070301d00050021450500340003602c1c6c58480001469050340101e4140100d105101c01c1d403c58aa01002941180c025903d00f0b224400360401252144119200b00b909135080030740c0c6c20201090107000d10410760000c03500340300041d00c40c820b4a907651002075014001444549000301107042c001342d8000014000741065140c0307483c00300420f400311000c1d07500b100c1c07001750141000742e00416032040030f400c10010b0700c2623803108005a0341c1035641d5001619208442500001080400c400c400c1864011a40703c240c400d03040d446400401d000b070010788030030b6070001c2541080e28030451103401110260f40d40208040d0411240640840070800c0050001050003140413000c540e03c41350802400841642c040c1c0f8a840180c00c3c41d02d59031144015204a2030301e410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 699822643 1250 699821393 699821411
    0x5070302031e04060617010504060c18180609021204050c1e120c0306090601031209031505071404090c14030c1c230a14060f060904020d06121401 64
    0x10790a800c8180c0b0841000032156601d45080500060840c0d80c000c0d0402d003007013120b001d01c2070419008244520701401c0c013001104128031082d031319458814941140c080034451305101541d002e0a03032070b18440c56003a00184c407079150405403049a00403020615892a21810041006005c0049900d84801955030705c0a500c4d0140f070742c0f001941d040700304034071480400c2032403102190108862a0710b51760040488805c0d003400300d041034031000280005d031190b902d17070443c2d1905240a4441c02044941c080451034005e1003c162620090101030502d10410010100a0341c000300e002c030250000d82455440080e0f51404440040d0100da115207440c1d0b0030401c10b108120071102c0704425181d03814803011100c0e05050514480b00020056910a505030494620040c00440b4011860f035206100b804420003400c2c0c42c0399001c0c1e5400a00300c449a900c10420200d0b0601401d02c44080c0800d150040c00250400e08015103003400c0c0d80c02900100c030400d65154042050001c01600f10703003841c800000030419a94 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 699823893 1250 699822643 699822661
    0x602030a050610120c03290a080c090f0c0d060306021804090c0303080402061b010b01080c310b0f03040302302109010f150501080a05040305040506070f03030507030203 74
    0x104403c0c5042501d0707078600c5170181c05d9019802c102801040249440c54844000c2007200464000c5103189005502e034000100d003010300000c5240e00d8240c002c041c5038080d50307036244103001c101000700043d142100c01d0000c02c480c0416400b03800003862113120003507180e071440300b01e1402c4100d40c4004144520309202004001ca868a10050b0603640c16181580d110340c0c1c0c50002c20114030904119280303203480e14685011409040d0302c0024900002d990366209034560300010340c124001c003e0980710070b808078100c1801c5a46011169040003a50840d00840641e0b03d07014164290846c0c0007541e18401d0001c02c100416a050204900c2400c82204000708003200300c0380155410114006651003690001d582403200061031001000c1d900b1030030140c40d61380740030381c2002c1c0070b090048607585c0001d080c803070b10a29440281c52118255001a511484140c0d41c150207003010345070160042e014131400f0000400c40e038441030001d0140a01400c054400d617500c1e4078008045901c01001002050b20520920500c02c0f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 699825143 1250 699823893 699823907
    0xa0b010306020309010917040906090b030d0804020312070b01050306060a03030917010f0c0c11030319050f0403321c030c020705091801051005030c2b0602030a050610 73
    0x81d4000100603202d5407103010003401454020390103000780c081c0c200b84400f002c200310000c000303658030b01005200c1150b84010280503103400820480e03254202d440140c0b15944107d64940d03106000900720349040d0103100c1d1181c01580101820743e1051203940050103281020040950090020380d031200071940f454a0042848241d0700483c2070048015200180c0350700f0035084000403801a910400c20202c0400018014103009a82150380e00c5441102d001107140110507505003c140020041000e10042070480f0154002c50141e400d40e00203000100200b580c481c030742c114485c0001140603008000049900c0341205c00607400f21941d011403080d0051580081c808001e0100318100801e00505a90060342081f03c99004640c00c8283d0908000720007030041165550b0b0240341c0003c001586500f002c46003500110701030582c01d0b500403020031401e0f003005d0b03d948882201d40c00000070f0311400404520a0b50b40030702c4003594056004018050840c442d0b01c01c054010704103d41d0310000700f4079294081c001d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 699826393 1250 699825143 699825149
    0x30901021e070203210f03072106030b150a0806090703170403020d12020a2109080601050f0d14011e0518060703050a02130b070b0708010f18060305030a080105120a0b01 74
    0x12411040310040002c041043e41e04551b039100900e41c0300c0c0762a540003014000380007500c1c20040d010445403010400d8038410381096a030404180140c5035145090980b0741405100007940260300d400b030018045e40103110340c0e4016076500015005e200d1039406e0101c1a03401050700c5003102d00c8100800c000598580481d012490342c0003c8080c081c00348102d05900f0140124005022020036040380b010005281c82d4440c00301d0065125030240e036491b12020340c0c0c1c030301e000d0003441d401841d0800100820301d400c2d00104141031149420011010300c4040040c25102c6039030308224900c5040038654508802406001c3d0701074030010a8801c0615268129a6100301c09401e280900d903444010640c4d8100640440d039a21000aa050603a140d40351900801580200c10a981140c5400302188541d4031803130030281281e0710b42400c19200da0400c0400405e00d60300040c0034a42e15561540000042c5040c4090800202c654540604c990724240900c804012079014600e600d420030300c154000a40031084407415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 699827643 1250 699826393 699826423
    0x10090e060915040515130c081801091703010e06040908071211120910230f1c1509200309120408031c0203011202060703090b030901021e070203 63
    0x941d1203550107034440080c102d2845400070300703080400c1401542000b03407203508003007690340050b58075040407001300311800032200ba400251b000011401404a81e10340e40c000f6071814000240c00c40407542d40fa49160302e14000b6089401e40400104001d40759030100c50341c820000d5405015180d229552400c0c640705201004001e840707295960b40540d4441c2000f41344c403015003000c4818944078012801090f03044414401d2103042826070002c5580c3c81018202c1941181040d401984000084440780c0c40c1c012006046250b10700b4400e04c09000032045100204c0303100c20303a000544800d04801e02820024580025041c5803c0282c07101c910344111200c5035101c1088581c103a103e440d100c00541c2000400c03245122080804074010400310750105c001c200e61023440004910340107980c81c00c00c080e07001c00d1180500c0c1c0c80d16400c0c01c80250519a0043c09403c2c4640f03080c0c5205520740c444401250815180001c040e0f60220f03c4071410f9442c00da24140c010518490a42401c1c100d0307001981c0c5521554010700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 699828893 1250 699827643 699827659
    0x30901090608041407080a0203010e030901210e010c0f02011d07050607060e060708180f0705060d0e070b04050301062909061b0c0a061e0f0e030f0303040210090e06 72
    0x2c1800300f01c2c040d0410009013182555002a40d5001e155034035441c1d010b0a0344613519008104201c80350000071507500c0013060315246000c0f442c40c26400d41041c52400d071880c0c0941c8402d18003001080c28030070466103220580f542505008040002030071182c5002807686031190080c0e0f003400c0c00b840001c4c1e200031103008032a05035680d4400d140c10405030002d08660341c1c09114031400e002c1c929030040d8100d1320540e802061000300450703500e81030ba80c0b40c00040e2004883c0d0094001030165040034001040c401c001e1383c2000c9030446850b4100361403c50258040341000030081418440e03840c0a01460f0010000329000302c0d60b1200c10501700d0388448240400d4050f001000401c01c483da12114180d03526581401c20700c100300c0c03000c0e100140c1c0351180c1c00c1080d4495002004042001809a007243c0c03883c42c0c0268940c841d04002d510144e801d206101210700c103111040006002940d000c0104840e0181140701440d120300b0188107000000c0520203844080c400d030a5030501c140405910310541c010801c0390111 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 699830143 1250 699828893 699828901
    0xf0c0b0c0f0714010204030311070e01150306120f02040f06050303030a09030918051f0b03071101110f1206040504031e051c020a1215030201030504020f09042102030901090608 77
    0x490622507848000c10f25030802285034051041036003d0f04c1202d00944545d80004103c0441e40e880d00150300810040841d40001030000e01c5031030aa8680c0131802d41000030300140c5a20b0400b02e20b243e0090120f0b041090148540c08609241c011070303412200205043c1700076070401c40081d403a404000c010b00319080e9203072101c0081c0341c0300b0f1115000a0030444581c010740401143c0031006040c044402040100c0855844a94451460144800c8031511034030107003162141c0c201103618002c0e43c1324a0320f081d901c03070700e4074108898900010601d08144000c450395504c041240c0654022008043da03200f40d03d07240401c004240c21800341103070010301451442d0612901c50f41039600c0d000d0703054814600310f4840c409806048140d0300801c40395501b501c803070a15a04089414041c1c8404009400e80000c0b10340c403c0005502980006400ca480104040c0d001c40000d40410601c03641140c0c29104281806089860b50600f1940e504410a051010310700e08000d260019145041610864040210881c00a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 699831393 1250 699830143 699830167
    0x1020c0108090c0f030312072a02010c03032003071d180105091b04140108090a081909051c120f0207060509040b101110201b0303160f0c0b0c 62
    0x1c7e81084c9140c503c1301c42506024000404000f00740c09000c1c64030003150781380c2ca01400540d05003c0050381c16541d0500d1225546e0b4110302500042d00d010301480090354900005107490b002461240484d50350700c0e403029417400390302c1010310b1a03400c09900455032002c40000340f046a00203030b81540c5050781e21230070300d840e00d60422000c1c1006462038001d58401150120f90b03401c88020034002017009030f0701e0309881d840e070419440d159480410700804e040d104000d20881c0d2042c00d44800704d15403460402480540e61040403400b10008456100c521807a800c1c03910003003008000d130061114565160440398a1007603a4007a580f14000c0c0640c41c1440350110703880780e49a940d43c00408507041c0240030041d28070b0420307a0280219065600d50780d000d000302100c0c0940108a44142da001d009007101c020003049540c880c00c4c0040c3e1211070036200c92050104981c510540030001180140032002d104640c141c03081c00014220700d0b0b250141d41c10400704c14580d4010909041039103400280c01c002176581c0c0c42a240d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 699832643 1250 699831393 699831397
    0xa0b0301212d03081501090311010507051905073002042705060106021b0f03160b030405010507050a202d061b0d02030604150b0901020c0108090c0f0303 67
    0x50114908050400102d01c5814180b80c000780709031035921464580000544582001c03185103400200d15800800100d40340801110f41d417070060520381d14150041e1a29420300c0b003051201d09a112030380490708104070040041d0f00003040c1207400e4241e012880142c0c10f094044502c02d11414244102c2d1000655641d0b03481101d40200d94030300b681703044103605001c075201d45281c038064445020719800043c0c540c6c0007003102c8075446421482c82c0c040c4111142007004601c02c0480c6940c1601c145e00000c104000084068806482008561600e910389032074190300350b0300000e084008002c024400412402c0d04080621000c8684440c100224005544030b50700c0c0c1022042c0b0f1089070b0b0344500c002600840d00050b10f80300218200f0039140c151341e49401100308d1200c00d28030707155092020007059000d00941e901842e04460010302c0414003c0007204c44070441000c80d006401d00c1d010020302c03000c007582c0411500845410a0030068107926100c11019187c03409402aa800344481403140c031020350303003882 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 699833893 1250 699832643 699832673
    0x60810050418061b050403020915040c02031819090207060905030319060803070f0b0c0705120d0c030608060a09030c12080405390102150a05060a0b030121 68
    0xc4100580c0c2000100710a04020b1540103a44441c50034540c04011382844a45200c0051151182858030385543d080c0004a940140780805055500300c04040503503407409400c401381c11a0f401151515208d2504914000c200124644036029080f0280f10404048511000702d90942400503100e2040e8207040e00509111a00240303030f804000100242e402c1c04a000c1c803c0001c0c00030007040426100c040d565078038459968040c1c851610f00d0f1034100011042e0401c0e5501a03683e035021170500107950340341031400303245658410300400c0c00305003142d60000314070850351480703a80c3ca0140400b40c40c0010149e180e080180c1041d641d19103408c426030a050180c403001c40d41503400400c0c107401d4400800001c003001000e8504540c10f0181d02240654014a00070200007507100c4002d542501245048071a21300080c0c1091905601821840000c032030841c0c0d10252088501c1000480c02d468004200300310b0b40c0b441d070411801000140010f0202d118411440880004141210460030545080c86111104400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 699835143 1250 699833893 699833899
    0x8010302120f07030803152706010c05070801021b0a022b020d0602120c0708032701050f100512120a0e061602030d0903030206070e040e12041706040206030106081005 73
    0x99030000070003540600844c4144240c0d240b034406c543c1000d0400c940510140b03820717a4a64400440d459081c80041c102503027001b81410b0880c3c00691a0740c510b4106101d560050b01c6a950209130300c04844e803001c111001100420001d0802802e2541c001a98100311000300c202014012010004021540b01160503040d0000c145000041c45460440c020350b00410380307101b4440184011070116001d2600780d80205600100040c119605d109409a4100842c00391b100a2a14094600700382e94081c03188a00070740340050241c066141c085601030401d0b80d254441401007400054001c40000081543c0700851150035080d50355502076a002c03100d450f41c04038a103501040000755a12800951100724a080d03100b82c0aa821441041e0300641d210b82c914071010340560000750004110a1050b5003220852000400004080a000c6803091034960510004800007078000340c1440b2034081d0740242c0c0d44182e1150003d25051506030b0105e64240010710170f14080c84407140c049010307503030f0000088018020103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 699836393 1250 699835143 699835153
    0x2091b0904020c070302040f020f272706060c07061413150305010902070b060d05010e100b0a080604120c0c080a0606140d0b160509090c070309090c08010302120f 71
    0x180c10410b813907120f9840100d00c120703d00030348140581034038020703101000d00d00719000342000582d507646045405035149103501c03002003401e8100309513910041107551100e01d07102400085090300d800d20b000c54005d03242501c6290140301400070b0034400903a00041d9031261414018016a541d000c80190003200342110b00001c0605001c0380d04079407000502d00741c18040d80c003484166a100b5011049114110f13011b0401014480003a0060519010b0002620321400000511103100d0703440c81d0929080c11859907a103074480c0486c0703d45181070f084540c00f401d80c5801a203601d0400e5912040d101c5400b407154400c0c480b49000c0042401390000c1780d00010225601510070401c5545003e50060000340101c1f4560302c1c6042c9001400d0904090f00510107a002c038140c01546c803040c10480c0c0f0245091420303410404204000821030703c030118110300070320049410a4403a04107150103800f291054102400c0c01346040c0b100b0004a911640f4030b0b0460f82c05540941d00030304850a01402d0144420104038a403042c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 699837643 1250 699836393 699836407
    0x90c0a022d060c0f0403021020060a0e010e0303060907090b07050d1202091305220c06020606060a021b0a0314100f0209060f13051c060501090902091b090402 69
    0xc03a100181c0d00a001829241140c0d940c6803520700d40d0180308080b82c4542001d00084c4014140300003510b010600c20b041c00c03040d8100203010640d66075000d8415482c0d54102c10244020b40004d4083e8040c20f007a203c000384100248403001c03907130300d000090034184205003900100381090301030300003000500003505800b541c5d4007090803c20b5031191220030080015840041100e80c0c0c080302e01c01c0d2001268010004c3c10035811561051001c0c040181c00c11030404c20020141c21014003e401c3c0a5101e4420801d0032801031030010082d0134444000e00d4a800348904100301280c807076020400051400c005200b442000004002042072200c09800042c0101e0802c0503410709524000707111220704c1541c5006114040310b84103034100b80e009401e11190003c20500c07614402101c00400303880104468000d4061255580300011010f80c0c0f200e1080400301c3d03000c40d81b58213008503070050b1405803c0b800c00502c5030b640740d6808610702050017032424074654a06002d445610203003800301c1e0703081c41f4004c0c419516004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 699838893 1250 699837643 699837703
    0x8072402090109051c0b0c0d0606030b040c080405030304031d0418111e010806040b040203070f030f0b01080402060c2d1e030417030f0706060513050105090c0a02 71
    0x11181c048680800d15038a0001550300d000d0080c0801c02c2c9550380142c035002403940e41d221101c84082c01c8001100d409000900450210703104460060400c1d5601203803d41500041c042210610102603041010580800021680001c100ca03007259152401000c0030000c405d1104607a0303c1c10401d00c2d8042e00701039800c2c00c0341c4005404c116905004010b6840c0340b180d800b003080100c0c800c240390700c0030148841c010f45240b0340c01500701c9640804041d20105510300240006022a8012216100032400240b0b101441c40d905120302c0a80d08140d0404011107000580041e00e0444001c100a00c80d810000d4140450745007440f403280c0701191443d425100304038010300d0040d4450240802e030b2142c4903940550307080b0900b400c001c100c0c540703402002d140380c582011102e510104440141c0700e27640c40304002489462812000504005021740800500c4504050400c1145e603690740e002500305061400500290f0345104c460b0740c2209103082030560b41c21b16a0026400d003031308070148a402d0b8440030202c1500d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 699840143 1250 699838893 699838897
    0x11b0321020a020c100806010f0207081c020708011a06031e01030303020a020c030316080c0307080d0b0a0506030402030d210203040b04020a0806040c03330603030f051608072402 78
    0xa80302d5000e4611019110040c40303008000f15888400003060a000308906501130301012681010ba40b065404440d220503400d480c050501000304101602030410042080e07041c400f1002605084000b8001ca0b0003d0424650b454081c40c01e5901c60300c800004130740103044a00ea0110f071005203820004807036a40303003005030080d04070520f80300c05400340800e1140c003031601001700e503030800c0030740031007001300506032030f0050a0740082c0801541403004001c80e402140300300e00503044540100c5008103164100405211a1000c280d21081c0540800e00c18000140c0c0d01192481c42e4030500d140500d00c18402050f1800591a242e0606407007030320020501041c8042120f0b17040c4514000d50310340c01e900d81e64081c03140c0d5600d001c5801400c40410f406040c400546401d003418103039401d00c0c24040c04410301b9413482240d5000151050718642d07466104104054200c030642c03c0c1001c0302c2c10300c030f82030001c0c000703070071030310100c03030344004095050001b0030f00c040109500c0d00084103060070b1008130040d0010807200c8025 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 699841393 1250 699840143 699840157
    0x8010b0f0d142202090a0903050c0a1110171f090c03021e0a0801090b0d12050d0e07050a0506070501150e01030b0609130803041103100c031505011b032102 68
    0x5203c1c3d48164814441a800c64202544c1c0541032402d140c1d030b1a0400c80c000c10642408808210301004a50f071030900400013500b690340070300700140c12110329504101000300c1040c404002c0c011464001c04a880c540d20300e40303510401c4480e207084180c84074000c1c40080071719904115100e0f0300c2c00c450b88061030780c558081d00b0b8020303800b1034241b01401c00b18402d081c00e0084206000021b0000c04c0148a6241c40c0d8206007140c44007c0c0403080403110300d40d10760080d00e0f52403110f040043c1020031071028010103809820740c801101c002030b000544c10000070070716080380c900440340995400104141000002d6020301b83c080007060407000516260510460f5038802880306403a2500c0142c00314610340b610b00348490265802d60707450016844150396011260308010000e4988130401080016035032414070a00804003043c410006040123408005812a02013807000340c41d00d00e0340103040c0141d0741c00022075418001558071031900760100d40b404485500c1220102608109040b441d40c1c2c4c5c000480e00940a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 699842643 1250 699841393 699841411
    0x12040b0d1113030f140318191511030d0204090509100204060906350711060108100504240b12030a080a0b0406090510030b06010f08010b0f0d14 63
    0x1003240100c144000310300807840c000182c002110010000a00c00a28a181d5030f4483c0d640603582c118003040140c1143c004001000b00f50035020f0b9207030050b00d01088106607140e40020340c500c2d0641880488525401850303082800d0049103802c09041c041700b042922281d0b0541c000543d941c40d20303410040058075040d202000c0394860700c001840c5d214001d00956094824980c2c448403064500303101202c5404014680f010741c90100000d04640745076810f00c890300c1c94000140600e903400e0407030001340362004d160581480b6421400040c00032620201da62801c401d45803c1c003007040d4840e030034001c80c44011440415500200004003510030070a6400c5560030317803012200c040c809801c3d00307111500da00c907136000500081e500720300050706051f83d40d10042e215030f000351002543c59160301621041707490a4a24255102e80c0341d03002c00400030401030042d030200080c80e24810446540d500581081c0307040c0034070581840085140080b461242081e40c0181a10000502c42120003d48a80034041d090f25002e0f5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 699843893 1250 699842643 699842651
    0x6010c151e290919091104050703051f0807122a03020a090b100f02010209060a0309020a080102120c030a09080316030c0302131802120f010905060306070c02011112040b0d 75
    0x44240b0f484850144a901c030403c4203031814640c01941402000700020860b10003d030385152250540300d6224081c4903c550f40c40008407401c00f6000c113928450f83c40c2d050441c0100500c020310031210301003016001c454410300020650542ca180c200507201015200b424115070b404080c40e0300d51050640c06c400c89000391105119151200001030076155514201904010b03502e46140d12180f2404500b4142c0c4064400103003885128800220f01d40d0001500e2000a43c0780e90146081d89440d428043c01800c03404002c41c075080207014126000c4d00001d01070548041c0100000d1100e4096400034410541d0007089245d50745001c5c400c4140d881440266074000a207005501d20400d8040c1c0300301c0e1210402051100e00700e602d000c2509074010100b000b0004190380a10001c001003104a1142d402240c3d10f642084140d030410004104440e00240411322a80c00801131120098209811780211074084c0b0f0b20304011951344403203525080b85074518a204d9080005c000944c041510080c00c031610080c80140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 699845143 1250 699843893 699843971
    0x2070302092e1814061309080a1d09010e040f1a070807080a0c050919050405090109050609010903080a0906022206090812040611070807030b010e06010c151e 69
    0x4c55031003888414140030100c000c2042c91815490b16050110300303c20120f2250210b40d00c00d0a1038104107100b60214100814009c4400180c50480341014030554144c0340d617614000c05c0d5400c2c1000500041c0c00030722906511001d0008039079900c0f000d04401401507a40e030410010081180a003223032480001b9080380e021414074019401809801003440d0b4903181000540020010145000240380a4482c13048400054684440c000c583c416031240c400000d0351450f604180d410031400600001c05645820100000280c0000d01542c20001c2000002420080351401d1340092081c842c942101c041e00109074405200c124205200755545903a406e4074559560080329a039445100c003807843d40c04280414040c2500c1900842a1441808101e0b2180d903685e014640c00d0842e941c01c103543c41072031000148101e5018402150f00803000313103070500c1c41880325103c070084032202001c012071440d2100c80c1c0d01e0000e224000c0862a03000c4140b01001480d40145840180ca800a02090501c2510748806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 699846393 1250 699845143 699845189
    0x40e0103021804110f04020c010914060c0a090923040b1f0b0906070201140c01020a1e05271801080c0d0206030403032304050d0201110a02070302092e 66
    0x35400f80742e1007800e042c05a0400c0040103c01000c116226411560138000c140d0141400d0150102141c020742d021001407483da0401e5003001402072015490744c904000c1048900d1340000c05034210b80b0b241d403002803285441031501048a10112061098009078814001445100c06910340282e00308032070304120300c0d0166132400b203544c0e046c400c600f40340000b842000c3d01c1c1c1c1003510052105030320515207002d0b41d201c0901c41400a130480c2d003c01205a40c00b044c01d04180341c12004010001c441e454030004c0112800400030403074498120707407002c11b900c441c503c4441d9031100c1c90301d10b8140d070000780032009103083c9240806c1c0d418400d11a4081510813680c6030b0b565800e00c801070325a15900900364610359650354400380c0180135551503000041c403110139a6000c01c010854070900441c8030394058034001c0c480c14402400d50300d080304440c40d0b40b101040b0394900c05800065010449906540c10802175540910460907203403140041035070254144803841d607031440c004454040c0c58a0000340300802c0d00b02504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 699847643 1250 699846393 699846439
    0xe2a090a06080c1806040317210402060306040e1609090c090c1709030c030a170709080d0f02010e01060f030b250804020d0c030309182304020307080102040e010302 72
    0x184a811810070041c000c9070060302442c00410410140c00c00c1d103400d9488d59440c1d440e523400003c804a1340d4020032a40f00311200045441c50028192810320b1003420301c0e800240d681d00c40503201a1080b0350b01c0310200d060000902105e0251341d603001d14408038682d076109000c007420700b00c40b04a422100ca0a80030400c2103161080301044c80007030340d5000c020390301c104000d006500c01501c800d841d488180300c25513880204000070000040c16964241c1ca400c0160011000010041d00752428410300070414800c03620006070070b10f8040310700d1400103400c0810300802d900508060789100d00a50a05801280c004540c400000450f841803103050804d64401814007140741c0e056603509281c00040c40f03400701c082e110f40c255070b4002d030004103e00072072410360383e8a040088856200714013050045000b000381e00000c15840d070602c40307400814011001c2980d94200d20f804040c09013022001b07900d01003000d40d1010000d007000340a08500856445c0d41780c5c03c1070742000c542407104902c0f42c03109001141061a403005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 699848893 1250 699847643 699847651
    0x1906151112030a20070c14040b030d2015011401050703020a0605060109120b0106033213050f0303060a1a0d050411040906021b010b09010e2a090a0608 66
    0x7040350858440e12009800703850000c150620038a400b012401d501c5041038010003440c0d1042c04560301841c039007140001c2d0380c21486001c610803480c3c2100008030b9100031418240f0f501440c036060058a03a00d915102040c010151004160300c10006c00e01103248000400505840e103603003218083d00c03d890011101c1d44100c0c540180141c2180c010100054a250400754004005041030038025440d20035010000700512416501265080010441c00d44c0500c51601c02106507480740d0034040c011032544000104d10204825500c0c130742c00c0085c448803400c106041641ea0322000750f41c0c2c003007182c041285d500d0700240d0b0014070450034104000f8413401d540304045041c0304217940321818240c104402c0f00080c130300100155070318100c004114403169102e1051240070b910440c2c0050b100c9071201100200c19007411000a40783e8944980d41e802d603510701114504452a04052000c10340c3c03448010b501860204001202500c40c40841d0329042072403401a02d1014030554000c00b805a4400003250050010b403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 699850143 1250 699848893 699848923
    0x60907090e0403030f0f090c0b03010b040e1b0a020a1403041805070e1005070303240e0a1b08150a1404090503041203020303010611030403020a0501050319061511 71
    0x200c03007084011508051664001e0103420000342502140c01d8140540352451150f801c802d645100c01c8080100b141124409801040d40c803900310b40c1808028540c611441c0141d036890320740f1030001248150190390034031260070000c100340d868240e90398010703586070283c0381d0480394041c41400c5c04609207000000d6404450421401080044c404082d01d001040090809010001d40014041c020786400020410341d210981c0c8140d501ca0707081c1030003011100c100450030007a038000668600151b203031070895810f0740d10001802a42d902c48000b00d400034100d051807000c031810b1074080e00400d60340108074540300f061a00c40c460041e0000404120f854420390244010660f0048541007060510b548600100d03480b40c000c692a0586840940d01e00c00040d81d41100164070000061250a038488030980e01d00341014002d40c103081c01c5500040e48d02120b800703080d040107008400150000d51500d89c00c0901c0b400302008006480d200c0c001c0d00100007041400001044030303a200c40c0814940010b01c500340078054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 699851393 1250 699850143 699850157
    0x602190e01021903030b030d081608040f120c14010606030f14240301020f0406030e1b0d020a03061802040e07030b1501140406111606052d1c05060907 66
    0x82031000f120980d8007209508041e1340d04e81111150310104010001403406851f542164505034008a03806e1814108031010068044140300002d005e50b2035010451740c1c0f00c62226042c019a480840d099261450064035507690443ca1940303e80c0c040d8461800e41e4070b44c1d9810b21600b40c06600c0142940c0113240c039440e618203d880090000b166100c40700d2404110041006500c056030700010742a07800000900b06042c1000030200f082e660103100f041680c12418001d8085140c010740e0856850201c10241d500481d8001120b008642d01e41d030890000d903910800410035a1407401100389812041c0c60105c0c09149810100c54000d8000282401181d40c0440080865078404cc171120b914594228900d040c01304040c4445ca5a54254000d04080c0c1140e83e90364050000e09800189000c6001e5940380c40603507170030002d01120b1b03400f02c111841240090b0703c044800034a40d120300c60486007040c0f13509603d44040390380a000c404814856520620210040c071035921007604101c410b078020781d1502c000c2021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 699852643 1250 699851393 699851413
    0xc0c0c030723090f1807150315120c03080901200d020d09080c060702030f1905061e06011805030616030f060e07121803080612150c0d060302030a0602190e0102 70
    0x5902e00030b030902401c1c071086c0c586065881d800b82d0390303507400044004007103038840307140350240358249c07052100800ca070103583c036110725141c0c0700c4101c09002400003410500300040e1800581c0d02401440c02d4001c1a480c0307608131107071801995600e41d440c802800005004480048000d0b520881c030007403d441e180c1020382000b22584081050a500080c401c0341c15002d03081103260005000d0088241c0201c054214107000001c900d0003904118008101000581c5d14051950001c183e90398410ba04c03480a00b44071001c2c54804440d0707803811142ea48000d034103108081c1009110300b00c22910750300018079a00c0603c5502c0d20b608519003078800700d01a03245181d03230010000b0201072040d540743c41707580c03400000040c1c244040b081c80316400e110f040054001c287c0520500080e4102045803440074004140509203410300001c60703d50707440c00585121511640410f01c501c00903915409400250760007012640a20b5062410344041d400040b074880902e440b03050391028040c0103296148419074164080c180440c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 699853893 1250 699852643 699852661
    0x91521020a05060c06100602010c050901030c0c0510020d110f0703030b180f1b120c09060f04170114071b0c0801020a08090d11060c0c0c030723090f 65
    0x6010001a40e01039440c0400258640343c000040c40840c011601800e65840d000c2580010301515a100c00d045a14141c00c0e11425a880b405a0300740c03480034070f030200c1c6001600c0c10498501810501c06070103130261245514403142540d00810300f0000152050114401400b002c2140340210411480c060030100072903400a440303984902d0700e180009283c001081210700754103118480840d00301c000c0c0600301d0244142039242040003c400102004501c1c40c18100740380c841c210600c090104000c1e1000030580b0b102c0c0ba03462509681d000e42d400c4481e0745d00c1e25a100081e0542e585113400703902d203d501e003500000c880009051410b00c100c1c100e440c4d00c0c4000c050055405215084280142d82d814000c51000c1001c0c40f00307000801061845503102c01c42d0b0b0078045080ca04151100000c2000c1c40740b2201e11441404001c188180d0103481c0103070f8280c03100c405400e42803d10312000c0d02a0b030b0600403108041840352429920000598000aa4030284803004044c05881c642c1035404c0d41d54489001c0000d200c3c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 699855143 1250 699853893 699853949
    0x914060f1008120a0903050d0c050c0d023003120105130c08071214040f060f020a092106060f080f0c0d14011e090b0c031608040507030203070f0915 65
    0xf20ba2a00485c8550789840c2c440c10110516103840004010100b0b00013408000c000c858034044c800c50380c0b00c4c2c1d20010ba42c0090400004540c009100c0341005800251100c031000880d28100d404034156581c41e0050f4001d080806803d0050721b21609203000c1c0034501c00301c1886050580000340e2121402502e40d41d005035140350b0040f000c0c50115484040300f29941080204690003240324071076043c1043e5043c80c1c80402d480e40700321036100342d07841800703072100c62640250300e102280c2c051400045445a52010150441410321000c0d000500301080042d000d00640031130421100034070241c5295541c03d202c0c0c02e451315864050154020708090303290307012a40b550081005513110318000524600285412020340c2584031b01294180d075100134070018080c00d5404954812114040c0516500c0d020100d281c0b0f0040c014204400c21000000085c100301c400c120041c040d40e0003c04070780c0c2880d6100d4100c49022220f014082c15181050548d4410012038503016080e40d0803500d02220340d4032586030442207a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 699856393 1250 699855143 699855157
    0x6210a050f0f1008070b0913290d06090503040501080907141c050105011412070317090a09020d1e0507080705030903121509070c0816060914060f100812 67
    0x705018141c002003841013040440001c0c0010401b070398441d00b000b400c21115000c2c0c00c00c8051402c1c10b2811106190030003629a004051600f00141007010000b004561341700d040c00740082c200c514154032103050100001c01707041242c40c00d03038402c3d0103035544146081d02c03024244105000441d10071f010102500d40034012030340c650f100c40e07415070100405454660079520300781d0050503102810410407000d0f0a0448400d12103084810042000030700e15911118802341108801682c2e00f000320302011550380311444000241a149010364a4130040c0000340000d15012405681c04008140c40d81c1141d00307240a450b1045450b41c41c0c1216603910b004040d074907940010124400790008202042132030307200d106041c1c02140c10400c01a4111083c8050107681e00002d8808014040c105094500061108040b203004500440d443c07103240c81d0324034249024100b190801002c1c8040f02c203603c2940140050f000740b0501002002203050380fa03643e00d00320201424000c885ca00e401451000f050308100c01d00038500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 699857643 1250 699856393 699856411
    0x61f080a032105070309111008010e0a060308040305160e04030c02150409061418010f0b0a1202070b040c05011b030c140618060615090f0f06210a050f0f 67
    0x2c0c2210158500045800803074200000c2660b8003443d6061054003010400d182c501030f1a1411280d1100700054619441445542d428002e96030000c1c83c5070802d5000040110b60150000b91920b4aa1800d0b5498200305c200382c400c0c07407400700e1740092600c03603003030005c0c6c020780d00340e1100540d59440e0307007e020f0324031640000983c00c19820000080c6103281da1182030001c1203254100c480c3c4148801c200074041d41204921815915060014402101203201c3d40040745c1544900031356800e211801600c02d10000e26901401a00c045108400d006809005034425403064419445040c0c481d0015299881060600c441c4c003264020f8020029010341403412029000340144108a00d820051030b180040c120340d1002c3c8070700b01003119038603144d0821400380c01c048111400160040022030500e0180151017002d803085400341c00c0c0c003103607840344004900d0340341000c0c00c01d55482801c50340020403001d07002240058010108002400c0300494802da50081a19440000882d140c1d508400085030001c0d202e03102c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 699858893 1250 699857643 699857687
    0x2102060306130623030f013c050a020d180308130501020903060411030706210507030f0e0106060e010302040f05061b0f0601030c120f150902040e061f080a03 69
    0x80541a40c110a114200d161011008131001c074814181020004001080d0307907030401c3c43c01400c00d03210007400303007441000406443d401c4030303107800300341c0d03010901030800e02580c1c0ba0805001900d5001d4000307140c05580042c0a010170740d40d09070106c05150907400302500141c09080810203051000715071100c918000d50001d4204001600040d003401c900f82c0e4112007150400c904007d190806005400c028901ca083c0601c00100c03c1490350290320302c203080201d18541d1903000030a214007a80c000540800400c10030444d000d280504103008103d140256000300d403149001c40da4541c480d00840d401d0310004d0b0410641c1c1d6140400b40107030303904104c288040b8003000001545584034100280030340b009070240140250f516509002103019070b26040640d90010219070030003c0f41c4048081342e41281c1c0820071002c029224102a0010b10444000a5105040c02c06a100710a40000c0c81c50080203500e09201002084080c403c0c0201d42d07910a08209810031004440403034040c11143c0d100141f40c4900603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 699860143 1250 699858893 699858899
    0xc010b15031b030a093f02070603050709030f0308071103090604030f0804030f060506090a110304032a1b0602060603100b010201020f040810050109050c040306091a01080721020603061306 82
    0x801900003000803046ca4541b44259902c110340a060590355a4902c584003900c030100c480000303441d01041d004010505884202181c1e055104000c0c2000035900200c46c400f100c4844d18000f40691000e803510750000c1e1121302005038a140100448400c0c18009048078a058615640d2441400d9902c0d41519200028080003010030f00c80303461008400d1098600150703600c0d08404104900b000a040780355518178000ca40b61401c22500100c1b5002078050921000d442c1c00403880400900c4c81805000c20042c915215004101c0c141340601e2040c11b03018910300b80c1d00d0304d808007241e85860859219078154401603004039110a02e5002072070b082d1040c030000d480c010904031b4025007640154401180d80e8000308000c030140740c07503100b51400341c94150b000344150300b0840e107020070601a50001401c4c0303030b5070368500008001e00000c0c1010140000c0108541941c0d40d00b03132981e1a1304043c401c94120103140e848440740e100c2d540780944103413a401429181540c448030140700030802c2c2c4982025108c1c0e42e0b51004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 699861393 1250 699860143 699860153
    0x71709070b0309030307090b090f0409050705100e010801090509060c0c190f0311061b0c0a020411090306010e0105010c08180d05010507030b010c0b0c1c020c010b15031b030a09 77
    0x40d4410f9500000031a5603003440c035002051384c45141c1c42450394440c1805007003002da40e00c3c80c50380e1090b8402c03240400c080216081550811640c0e40c4025404440d0f0320048014640151a0070445902602c0e14a02c80e0707038503a40c20003598001c07034a6038410303041080080d45000c2c94a01815000300040b08490481350300b1000d00e0558075100e04203540060fa00d683c18420564001c510300a00c58006018040342e08121068000054030300526842102c000b05581260520412000404540050013484600301500d03c2d003d40358001e040b428000e0107544008980c038850041e01c18106c8806039118480020182c4500c9515001703130107400140111740800306119074400c4100c003c1c41d4007500000035141003081c00030b000c07501607a099a050002554050000c44e07503c0b840103a01031002400e05641d084881400b00328095948002050903202045039601c0c0501503001191a8a080d0ba001c1c110134038605202459000032250101050507990800c2c4200c510080619007000c0a42c201140d076110365520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 699862643 1250 699861393 699861397
    0xd0503070f0803010504051f03030516020406031103060f011409060a170609010b031b0d050307021f0e090c0d09080c1209100905150a142709071709070b 67
    0x1c0d14031102c00b1006000d14a454461241c00410400030b10501c18140b4043c40298a810305c005028001d0129502c0800c10000303002600322580240100200c907100d1400011140da42030140307002e4410b83d00041d881c1683c9400c458180c58216020700f5801090a00300b1612020082419030800ca081c0c00c005040b50b0b00c4818043d928903040080c01c0103250490f8005e003128000c0580394829849802454012403c00701040c8411500b51540d0004401e1420502e00d58442e6a10003504160341042c0300103101c64104d441100c6180340e65848580c40c441604011480e5003c0d19144d09500c820402a02c46420f254000072559100340280c07801c0c40d81d205d0750582011503115202690000001300d0706111310b80034202501d0f4407064188442071604003004140c02805115807070030340c0719001414147c4640650503141841103120310150351792000d000381c100c11300404540502d1035118260404010300c2c0c507082c0d20303118507070030b50301c0c14141c20100c0e425048101c0040c000c003119000c0c01201044940500300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 699863893 1250 699862643 699862673
    0x901090e0a02090d12180f05090c1b03070c080d050f1605010c200f061909080d0c030c030603020f060d1503030c0b0703140a02030910050106020c040f060b090d050307 73
    0x2013411a15170100c06848400341e8000041c00300b11004080c01080ca9100d6442c094420a542c0503159a40f004c445041f140b25010302c44107414410049900080e00c00801080441e05c9401c040300341e540e4891810f80e4501d0400c4568001c10018403820a403811800d0180103908010343d81a10700800c10f0f20303080e0071aa02950700100184001602044040e05d07000100b0082d00c0b070340001c0010320f0300444502d8840c5c00190400c100e140c142030300344008001e02d0301b01030111a00248103d5540b150300391860001c0407162851400301c1e00304000d00c54010302900c52403003181e4001d08015900710042c010004142d02c2600c903041d06503a11054142008080c550400c082c61203a2035000c10007850b800e120850050080444013010300b81101d48802d8000c50703000a403c0b40c0c410001507100d84455244174185201c00350000d00c114a446c00004142c0d0340020342c400000304c15a01000003034901f01c0d0100a441d0300d40502800b2801c20842c548040c00c0080110b164107000c0c0041e6801e100190341c800803e9211a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 699865143 1250 699863893 699863903
    0x1f09030c022e170411150d0501030b06030f0a110a1a0408060f13110628030506060a05030118090506010b09030118050a120302040f18060b0901090e0a02090d 69
    0x252000c0e280c250400050b001e060b2441c01e00c101803030480d00110340b6092000304010203641c480c07040d44d8540d403240031140d40c111b55030000090301d400440b01d440004020910082d640c246118011070410304000c02e841d100f8400c0b0304c1c058111545143c40e02d000034403024250941002e854100000c0207002100464911010404219501c61411328040d150644c050f191000c2e80260005000450030001c00788881c4540c040210b40c011003032000020300b00e010300401e05d0405110b20740000d107000100e02e6010350101044c0c50801083d1a66000c0c04000e0040000c84c2c40070540400050110307081e080c2c945420141201030101d02014196030760780c1042c5003a880700c001c0c1600030503101142d140a0084211040e81070444020498081c0c894076a104155600074003000100304840c0d000c1842a01140c015100c5440300c082402c0d45d440c4491003101c1c2c04112004024500b4102081c0300c0440800c860481700160351703259859052808082c040345018103480c0c08141e0070041c0307002c7c0c0c1d1207625280041070300034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 699866393 1250 699865143 699865189
    0x30501060905100b1909090c02060906101d0901090204060e150d08090621130201021632030607050304150501080d0e010306031a010510021f09030c02 66
    0x40810341a2400680b04400d105028003080c00300041103403d5860300c4551405c600b68000c41c1d103400756524109900b00000e101e0403c190701c01d17595000106140620384440071030701c0b240d5862080720f6400c040c81c020384446564070101010760b80340c100003003600314511a0001542841540c0014210b500551040031000110010070008100d5510403540741c210503160142e0b0320940340d81d244158480e014242d4450600400c21106042c0c400c01008044044250a0020760a10441c00b1030390810a4004034014801d03a17501e06070091080e21038104881035400d940340f4107095038440b0b41a0088505285600c1182000201204d98041000d2801982c2680b1826500d08090828100300c000c0c2900e100b8035035041c0310042084403000160310807090301030b260601c10070311100b004038050701c80340c6d1000d030501500c01c880382680300c080b2002c4c03070499504a800a010300e0f500030080c1e85a80d8000d2600c1c032940c62000c201c141000050b002594039601c00d16054081002d00d9000580d540c0041215032807100303607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 699867643 1250 699866393 699866399
    0x409090c0b0a1407051603140f031206040e0307120306050f061206041d0f0312090a11060306060409181506120611311d160504090603050106 62
    0x30404a01000e003034000003952401460000240c0360501c1070200002e0003400103903c009110091010700103a6a24039000c00706030b5564105542c038405240506900c601522055140c0c60900000310f40740c0960402c124409071740c9910400006107a22000038246000400004001404900c41c01c00003d5540c3c4000813428100700600090b00d0600141d280520000c2140c0d03840460200030350f5520480031100460000c51151507414841c0b60ba6001c2c48180c0300b51480c1c0701c4006400300180c900c8280c0c004004015a650001040d0380b038a4000340074080075843c45803864582090b200840c0d1041014040320302e8640d9602000084035909101c3c2100ca44041c03d1280400070700103142c100c15030b070b00304040c04168185003191602d01c0d2402c40082c0040e0f074030017551040a580c0700c20394000028452003903107440940c520424152000301c10200c80d0b482c1c0c3c3c800110354098200108240356449a0600201d82e50756400d04150a4941441c1001d00c00213000002d00d2034035030700890300503522a034004900a49 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 699868893 1250 699867643 699867653
    0xa0c0801060f0804120909140a0b0a050901030f08190f080604051e100305010e0d0305010806071d0307080f07080f0d020d0c03030f0c051225050706060506040909 71
    0x2041c1c00400c1000100c0101a44070780d4044045074005800540150182a5118041c0c4844482c4e44c8074001c006e04100c40502c041d811052924072962020105028841c6a0020401503002c103001d400c0c0e10150000050010410407071601100c1407258a000340380240403481e1100c82d1580b00740c4000059030316002d903c0d00030750010300c4603049001a50144914107041ea12255805480f031940400c0c043d002001490a900c0151508021a0407078002c1040c8040b070030031b40780c40c0d0188071107400100342440300004440500007100703840381c21035556a00d120b14400005518584400f2807080d4103104841c00400c8040043c007100d0701a404c502e00030710302c4031b00d4009068284151031600350455041140120151500400d040307205020b50710300300320304041c00e1030190024941c009001501614000b000092070307800200034100011085078401c859a01d5070510b1440d00520384440049492003041e4980c054000c40c09032000600c6100041540b5031200c010a4075900305510440115803100c8100090007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 699870143 1250 699868893 699868907
    0x10b0303190909050f01050321250c08070e0114090105090c0d0f0e1e07030308070c0b0f071b03230d0203090606010f0801030503090607060e030a020706090b07020f090603010209090a0c 81
    0x1400c040318156040703080d809c8149440c05804042070400c4001062600c0382580c94040003142c0760300101403114107480b903010075079038080c0c2c0c01107c0c0c3d080604c0c00003003144914035141c62000d503070080950803d40e080000348100800007900b200c20b848018405025031000c0c0b40640714550b4010031002401c110454407051405050b0070700d03103049900d40c40c5207134192080880c0700c000b6260941040300184d10f0780d0400f140d80483d80d50002c1d001d1540501440400b01190410601404036559126490f40050b2035003040441a110001c0128400f010356840000d2400003480c481c014071540b103800c040f40c082004041e680200c2d410342503034101904002c029078001c29100541c07922480d200a0542c15665000e5633440307030039220380c070074000462403a042011540055103c041140f050301c4d00c40c81c443c18041d40d070b500c50713010704000316003851000310b60b070441d81d420713075007841d80082503000600207180038442441d2000d000f0395019502002402215154490f002c2d009003401c070390009882c0c040b400d00a0040b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 699871393 1250 699870143 699870163
    0xb0a0e090105060403080d1d03070605071715012703080702190e280c020f010e010e030d0e0a02150d05090102180f040b120a1103010b0303190909050f010503 69
    0xa0070f4184400e0021402440603600e03c568041000200901261304000000d9025a010851444001034a9013000102c0d04418010061a00ea010319000d02101420001c041100c01a186480c0c0038603400c510f40c0301c0c0c2070400001c0c442d05640000a80804600c4081d900680c00a407820100001d40004500f0300c02c800310a003542248c04400341034100800c10204040291401c40d64483d030a024400c0b030f0301038000d48000280c00751410000b0b21030001000c0c0d1182c022248450145d446c0c40c03a001001c40b0107005100d100040030b40514644014410700b00002d240d0356140f480640300e8440d040f40140c1740c2840100b4000e508441e284d461b2440d0740070800c280c1d20028204019a40184654488245500310b602c116100072590905e404040c0004070f0300502c0c24151596101e41c8558481d4911a00840c50f00b00c0e0600902c9240c25801052040c5404d8441a98040d40c01d640100b2006c01c4112100355000072904c503c2c80e10340303400340da100000019210155284181204070400420407440c0800c160f8042c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 699872643 1250 699871393 699871399
    0x90f08040825080a03120605030307150c080702060c0a09090203090f1212060111030c15090709091101030e100f02190f09090b0406081504020f091308130b0a0e090105 73
    0x70a81000426920340301c0030b26006051240e1b070b0f14400c048820307581021001c0c01c0c014084a8980302c0c0e038205480c0c00d415441d0544825031410000c1d00c0f1302c80c440c5000705c1c0722b01e64a13001400d16407104420440d417640082c1c45c103130801000e0720000c030316000300340000d5004405550050621601000d81141020128840e034407485d1410001c41d60f240011805c0241e100409080007001d4404028015045100b2030032000c40500518000880c0b840d20300d82c0c6540908030000403501000c3d114400350b0200c4100f100054040c0103031800300c1c00320758032075006440c406042c1c3c1d05480702c0f038180c4506402590150748a554209401051000112030b0030040812410061700d010640c4110045025000d40e0b018003800c200591142060a0540c0392034000c80c004006d9030080352480e206401610085c44806c0c2c404902c00c40c1e054120740c0c030a03d40300b406c50b80100c862201c0e58404016075a100c0b00503612801c00b90f1042e01c19010005004600c00c405003003907c40d03940f206900c081a0004000025005800840c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 699873893 1250 699872643 699872713
    0x1080706090f1a0424180f09090c03050f0715080c0a030c180e0a0e03091530090607020303190506130504150f0b010f03090f080408 58
    0x480b20391900b4110880340e1204060f00058500da890007030911860700400d0307075894a011002445540584a41c404c0c104540e43d40b00984a10b090b84864444a0310540e050150320350741c11312083c02c16900046480784950020320300a9500c0d0750342c60401e00392a07010b22040c3c0091904028000036510404482e40311450f181040385040c2c03c2e043c42a0044000404c10507550301109420035014400307460503080d000e80304048441d680c1010b806201d0b401c440c05d5032114100b8140b003480d048004259904420018140890f034214950080a113030070414000404014100902c803071100b100d9400d00ca05c08800b0200c03007051501500740c41c03030048050002001c5500810411110303511086540c080c4569600c004907254680500241c201c1d14a0040c540352985440f042c80100541d00d032a1a11200041c041800204040b0504d1320071501042e1f9158085004800c21002e0684640c1c00a18254814250302243c03501c241c813040850b0300990084d44550380880d01da01c000c5184135501405030b600808a244e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 699875143 1250 699873893 699873899
    0xa05061008040606030c14190f0b1305130509061006022a060310031401020a0e1210090c091104120b06030304080d020c1c02211509060108070609 64
    0x28840c015801000c03400c00000001190420040c0d030881c070f00440c1c004111904068030368000c440081d4100f0409889509100107842c4404881500c4004032030800c903101401c549400c0d180f1610390311200c5090442d0a0700c450100315682e0300710800b19200d00300140010f030b9107046921603103448000b42c28482c8903401244108049640010b00c820404050700c24404500c010b8003500c2d81c640281003540d9030095000c4100704403450340d040240300700c1c0d01401c0c0f51000070710039071111400c0b40b151402080000d07011a81120450400c200360149404021003165001354031188084115184c104086600c1566824100042451805000d401d5403600d120035103002e01d8018441c5902035400d2008041c2110040000c2c050b80d0107100fa42c0081c2140340a0b2440095440f500035150303c1e01c40b04c0e061103000f9115410450300000586170b0b14841d400362607030391020b40118188540010b000ca01260511032640d4120030200700944c22405084114014113141d410041c5050924601c1d802c00e8080040c4a4410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 699876393 1250 699875143 699875149
    0xb030906061302040512060702161212110313150e01051803010b150712030b21010b0d06062102031e0313080c0909121c0b0d1a0a0506 59
    0x441e04140100d590035408400207a21801034041d950010b640440d8090218428030b101240480c8504825426a07030700c0c481b0b00e06404c880c12064011410010025004500022603194240c10100198103020149030a1081014690784c00744001e182c41602c42c0da0200442221425846160f405034140785c00302400600c0000d01d0b0740a542071080140050640c16107007514290702210b09040c0140000d400b40b076440c010025030782d22184040311540f000c00c0c5075003080c3d4840d114942603003c0042c881c10b41e050040032045101c50702c107c440400c0c0d544c0c8040d62a40c43d940d031000b28502500c20314002c21054034008020300c2011400c14401e5030fa802603280440181e501284041300c000804040b0340442d0291412070385107000d1b51411441500c221040810f44540000d188412101c04480a010583d1007050b03040d10341c02c00d400c1c002c500304818820110120904e0302c50700c079544a1484005180c100f41000100c0d0f01d0b031240c1c0141c0c1c02644210345030144040310003070507503c039190110a1000741400004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 699877643 1250 699876393 699876403
    0x1111207020f0f06070f05190309180e06090c0102161212030f020715051e07030c111e060106090b04061b0525050a080705150d05150a0b0309 62
    0x2881100301c2c2c1600040740d07848801404000902800082c0c0b03504044c980002d01106600080c0c5040c070540e100204000240c0c095141802c5c2d040d43c800e241d95241c040b01552040110307000c544110748500703400c05455010000984540d02a0000b0403499040b000064146070744091402510000c04409103c00c0c42e0100100c0d21322540111060900001d00600b00c008008443c0c5a044540c00062400180b24203121508800300101c0300030040e40e1074460541070300d0300912440215042c81c00e800188518042d41c4001104491410f0466850306131444640c00e15404800100310007071310036084801d1500400c02c1502614450811600300350501240c5481402244500c0c1d0030080314066227030101050703101116620364040110744c074420240000c210800944c1000c068880c1400c00f0020701482c0881710350044a002c00081d092280c01c02c8180580c2da040c148032400e811608000d010034980b0244101c42c03080d400a95030040c0201e20300c0c01c000c00801a81e120011015051050048607400412 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 699878893 1250 699877643 699877657
    0x501030c0813080708040f060306030c050102010b0d030f09050a0e041e051507030b04020310080615130b030a050f010b01080c180d0606050d05032107140f0d0507030b011112 76
    0x2480350307211491381c60031009034030494010030031801305042c0009a50760150025800c0c0c902c81c5030003100d4651564012401c030352621100980c88041060340300c0100380180b442e03036190005031906a0b4001c1d222000b03e203140180394001e80c081e880040800080c0407401499480544602003113054060f00c0d80caa8598991041004081200140d40411401400396000345d42c10b90010b00255128a031003406802c000c582c52160800f64090000010809403518546000785840100003d000040e001e40b0b46c0c0003050a91265905403184400350404103d003003020402c200d1f0344100124030540d08000041a105010b4500c8105010910000c05000706041401050040544070302d5040031550902da000381480d540010303081988815040284040800100000c1982e41d14141d203203c1d84400d000740f503d804440b04400140b2400601c01e0240a0340c0041400d50300b540d28260505410072200c03c00c50390151258400309550f900c103200c3e1560008041c0101240ca00043c201c1c40000a140f0446841160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 699880143 1250 699878893 699878903
    0x20d0203072004060909060f060506120c160803180c060703050306150d09170304020a060c0f050d090e0604050411040905030f0f03041b05031903021c05040501030c0813 74
    0x42000208242c0712200c2c51204400140103101295075900040e00030300126806440340c0e824002945084044c82c010541110710203440c1310700d45080318807080560700f0080c0000580c07041c1003203c0740b40f1a0440030300b041094011801079903a4244401103150401b004655040e00c0e030003075126801707150740300d0060b00c46a50b01400c00c25500d83d20200003c0410a40f1780a0594403000412103240e2404141d20890429104864003500745521004150307660100301c4d4000d6101c1080034003406210712607030161460f94800d80d880000142241c1d0740318280442c203582d0b0000969200d008109901d90720b5940b0360400030035202000700381859160f118894551519090085445600c0042004000c000b1169044500644140c50710f00c0801e044055a1003640c05035080c07106a00c0800c0710580d40c06004c01210401002800182c9a4071104008144858416800d5002d11050b00c00038052500f4415020742c1d141c1d44107640d86050000240844204589060400c2413090801c2201410683c1d1000b556801c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 699881393 1250 699880143 699880163
    0x90503030c03180f030315010905150c0a0f051c0309150b060f030103142b0e010c0618051227031f051b0306030303062206030b0402040507020d020307 66
    0x40c04000800508658224051140b00880302c0c69113408405076004560b2034005414020007400110307002d000500400b80d00032921014070f48038450410080002034034400580e00308405030b031510b00c8240351030981a81c040d00072507400202462461006090104503090400c1060090b448801c1c901c034016980a281e19a504960355859944000f615030b403422406001c3d0303480d83c40740341171005a007d810b180403140c03050004141c0b9154074088480300b0640020082100e807250714000b191549225a0101e040c01030082040d0301140c520300070a002d01c1140401c13140303481010702c0c004d0b1506124407104811070300c05018501203503002141403102c041559404c00c81a01c1c01500083c288610808000c0d90a41080614015013151380c028a100e0303048161605041c41c014506060140300446041d42c3c50782042001800e50720709407451628100b05007034424140c400c005480c60460f80749070000d942d601c040038200000c52802e80201a48101180301400c00c80001c1d50307000e0354034080d0302c070020061000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 699882643 1250 699881393 699881401
    0xf06120210031d0c03010605010203030705030411040603080a230306030a0b06031c081603050103030905090406060503030d06092306012106030c032108150a0b130f09090503030c03 79
    0x403e400910700b106594082c0c04070b00f9005241c10350b42e00c40d80c0100038000c1d400c04000090a40c0040f051300d100b02001d840e05460f558443d640c00055810b0302c903445500c45d13980c450103c040b03138001c80541a0401c4980314943d5100d2a00080c1d00c403500048649029200700704100841a140810410b0665034070640c0d541441d1a070b080003d0511244000c1c0d1042d5100c00000c00c1140c662000200d4000c0181c11491004060207100840c169402400054085810146c041100307041c1020b4080c0d0041c001d16002500c0c64844c3c000a0850f4080441c0481c0903440e42401d0000a070b5074810f0300c0c2541324044204403030302c00040c0c12082c20117000b021107052050042e0600f8802d03001070010399041c0318404040100035281c0c5403402c0403810500041d5100b1001391102141000d5500345640182059125410180c3d141c032081d00032842c201c1011a003100c03000350000b0743d0043c4503018062030308854401c5078030745081080480c01300c003450f0f200103081410503402d040420b4012003100c3e00400c490004503984e5031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 699883893 1250 699882643 699882647
    0x618061006052b1113120f0f0201051603021b0105120f22080406110a0b0f0c0715020306040e0307080307261608010909080415110f0f010f06120210 65
    0x42e08880f01c074100e41048824626070b80d00500800082840904002d4460345500d02401c0103d010300c4000e000c4050980040c01194811003104803141c41403500c240f8003c03044a4075546c1c46101202180503900030482c0c481030144840e03140c01c00301000e190160508040350b02151440c6c90280ca00865080118003268044019a041015202c01d40c0080701d1980390700d1038860441c0d4042c2c80f481c0c000918044001c03d8a56001c5504245a07400801c000040d45810407a240c440102428500345400d0803c0080c00003841d0080700e40007543c1701140161245003a009001c280d07a0701c00c00d581a260030030007140c07000503602c00030b50f504008640307080d0320b24440441c40e04040341240c1c01d10745803411240d420130a5160407400c041d0300b40300c81c135920032826903070301c800d11025a03070303444001011090305010500200110482c40b502045451808003a02c4141000950402c1440030030000700f9080b140c1c0b140f2825409028940b04d10300d12102c1000110b01d00716854509480040000f031140e9403207042001824 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 699885143 1250 699883893 699883957
    0x50607080c0a0c15291306030b16050d060f03050c01020706050a0503100f03050318120a02151603090608091b0420160b01091103060918061806100605 66
    0x100a11085c5c4580c0601e103080c80000890004101c0e1040698650810b15095240a554102d0340d011200712840c0e110240f2808954144100d00410403009100d0380c83c01120078004c850040c51003108043e5050b055040c4207042555844c585070642d03012220412441303500100f26800090031749000e503202e0322900480c005100c0941e10400c3d903c00d8100002c403d01101000078034400d45d025a600181c4c3c03854200f402b2a070075603004040c00c0382d0003000f181005800c0c01c0c81100554071485d90783c030740341c01062034040900d20200c0c1c8050300042c02030310301800500d030072180c03ea4000480400a0409002c4801804081d04000d18158016502e50b00b0103200311048605911181103030850058403811405215a00e070a8081d0040d03a0442e050340001400c0d8031325200300003078500e007403012503e183da0b039105000d4129000340c548138400382000b420303002901c01400403d000300d079404a0a11a101c041c40c5c101e01c0c0000203050a201e888441c0d0302002500d03003040488100740c1c00c07121680080798120614600103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 699886393 1250 699885143 699885161
    0xc1e0304050402210601090503120a03020706050a0c0f0e03070b0f070c180605011b0809030703052a220e0c090a020403020307151409040207060207050607080c0a0c15 73
    0x70380085a80c0304c40a0841190b00c840d4550b00c04a007030696503c07001160402a00e100c3e40b44c044c0c000301c00e8061015010802030150340300c2c50401505c2c1c0b02140d50b95000301c070300031070720705d5550384d55030070503070001c1d54000e0301c1c5d001d60360039881c4c103945206464000035141c10f03082c4500b44509100194986e0b9880400301542d100c541c0024640b0b2090340d40d40004034030345803014845914149001408100c0d91300030351d0400d1f0b2900302c1c0b8020166442040e40c4803000d0f54007070010030b61b240c0300e01e070400030014030300704100c941840400114548024001c5000307035400c1d40200701c5a1040c0c44550015060364429145102d1008121201094464862001c85c3c2040b00d91850f482e00003035000d04200724104035030002d00444c1e02c25811115034a5980096880c00810114000b0000ba03015240b426116035502c003801000c0d00c014801840c0019996445d422a881000c0440301e9405c003004019020382c00500c165400800341c160036103442400440241815014813004250f0428600384010404440c0d00042903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 699887643 1250 699886393 699886399
    0x5062a0a0e100305010512030c0712050106030803040302031c0207032c150714010b03120705010b2206050604050f0402033d060c0f020f190b0c0c0301020c1e030405 72
    0x441c0b108003004020b0442401843c0c06504811404180940000301f2103c0d03241d181d102a19202d801c00303280401c0c02d030300c00300c050b03c0329074840c08084042150301c001076010303522030740085640b1052003029801045d0a002c05020645c81400801c0201e9040f5050348031000381140d1000e00481b101100d5001c0b281c070214080e40140d54001c4400904c10302c080200403041c040e030044403d5014004040c0c0c05e8074050280603030150000030803080900e05c0c03100544401e0781310b20000f01d031050742000851044204140c4090102d0144500a90704070f0891041c0c1001d440d0944480e4649401c042c04140c20408205001c1d00441d800000110328104001880c4100189807a82860705203030052403030040c1741e0704801d41c8003250480700000703100d5000740d5040000583c0000c50403842503040d000c200316055482032082d00008a00b18801c0e8980b524503060000c0c06030950116110701a02010030302d007a8842075510300aa20402c40840f20010000d4800800008005a231b401c1d0030404124074118042c1c0d40c03140790 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 699888893 1250 699887643 699887659
    0x5090d05030f04030204050a150b03090304091a1906090b07020a170f0f0c090106080c130b0a02120715020a110f030a1d180c04031a0405062a0a0e 64
    0x1a04010100c003d1048074000c503801d002c2c075140d00401d00308580c05140c1e07042051061203c100200c40c2202c0103140d006202000341c90030155a01b081c00261071015418400481b083c20b010009840c008080c0305450150360030b802040c1d0308080c2c025014207010300600110706e201040850440d03840041400c0581000000b803681c50805181e256074910f224007510303940c0c0c0504101440d034100002080081540001c203040b50607481c10000b81c400d200c02820100d00c0480401000400e4030702111541c0080c004010340036a00e1001e030358001c0c00d18800c2a4030350840c41c810054a00401c400321546070034500204401039a901e01440160307100120705110105500039005020b44000000c4090b08040700540c940c02034000e803090642038508000481d25500c48029040362103007034001b0030100c0e407012913038804c0c0340340035140d480320030800815400341d10380c000c60710082004221041c0700c0c864021554800740da032340040f4181e403c01e4001c0c83e10414001007101003028009544684041d0243c0b8402422040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 699890143 1250 699888893 699888907
    0x7090603170a1413210614071d040b040905060412050c100213080a03050403050d080c0304030305072a060b0907020a0303050606042c010806190b130c080a0b010f08010605090d0503 79
    0x2401c45d041c40c0c102510350614040c00000280c1d075541d8214820030180d95039030751038000720144a40341c0640440440d005995079550280c2a00c0da441190042e6019000415043c5410b10304002c480b0000140d9008202c4244689848411b00140300c0c1141c140741b03a0013580341c00c4040d180001000c0d241e0b100d000c0d18411110040140354204004106907406142a6640c096403044107803140c003410b55514003111010000140401c0c4070794001d9820904500c2d01001c03491101c420b50203680001111140aa40802045420480c0ca48505280d0140540d44400985843d84c0044c0d00d413003402d10041c003855202c00018030716039a00400c44002e0203c0c020070f04094544065044c0440d4810406803610100450000c20301c6800050b44078892a420080155140240344a03040608034441d03240303810000a40302c8440c030744800e0081681010155451801c0b034030700f00c0b0401c01981c1c1d82c2e00340603051000011000e042d10741d11500070303410350343c0c542881c990f200d0295020940f6411040340c003510324000850300e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 699891393 1250 699890143 699890189
    0x1e03010b04032a06030f0b041109280302060c2d1603080d0c110f0f0706170703051f030b0613051302010804080c07090603170a1413 58
    0x50402d0380c0c020b070601c6a09070640f81010148103d0400b02e0002c2400e180d10801074035219401c01442c2016961021892198a82c0801c084d81d0440c2001c0034100700100d80c000c41070600708980c00748038515001147c2c24141c1c1046507000000301d07000103400f42100080600241204210b03400000001d500b500080b241c11500c0c0305410355150001e20707154020380d00c01c05007481500040714141c0e50000c406518004014007203900138001382608605110204a030a44041d40c01d02812020301201c0001e820305c51400b41465040c608150864418810710a805254003100d0f0380c8215804a0b450030300180548401c941890444051f01d0454080f1030300b40d034080b040042c2904442d000c3c51080e10755400403e02d0b00022010b942046035606401400410364101541c803480c0c1940d0054064440540b41c42d8000b001182003a1080d000203494035101e10040003000083c41d5110941c100c00d903c484e0604c65040d02c000c11485109000400e07490002c110ba0b403041c1c01c0035602078010310180d0b808440400d00c40d000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 699892643 1250 699891393 699891397
    0xc06090307031e0f031a060d020309010e030703050703030506010c050313080105010f0b071b030b09070612141f050a09050f0601050415030c0311030430090b1e03010b 73
    0x100b01c0000701046010344050f09000001d01c00c95000303880303400400b070724140c080b0021720709112000700d106e10f0b111001c0501d8554500a20820492020240e62450300760541420740c3c5004c0c08100c0c06520400c84100420f0b40103050300c0310103505140218854607a5401250700c0001d800c00981785001c00074018034a460088820b00c201c0d94011300a01c0660790706c41844080103854411f00c0312250040001800003216000d002c452036010600685c000c2d900c0e500c0b2441e501c0320840b4200780e1640451424000143c20030401e240c5595070607802e12982a1101194002c4040034080300035440c0307246292030341d01002a40000143c0001b0304160081e0b992460032101412056480a9550032080041841035101c0c8042b24181c032182417103108a09183c40040b002000c2c40c0450400301641d403c41c0e08031625907140218090b901882411039484084c2404c500042303420b0138003410716403000c4415050381e07070810142c804a41182d02010f07150410340b82c0020ba1003903c1c0c15500b01c200800400480c6014100c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 699893893 1250 699892643 699892657
    0xa080115050123071b0803070c08060606120a0e0610140904170f0415050903010b0121020d0e1c0207080105071416050109030e040e060103020d11060c060903 69
    0xc0c00c400800e545000550f068090b001c1c03100040a25820300d4000031140e000280b1038144550084402d001d01943d086251904030382110302c240c0c00c0041c0440c18850700e404510040d21168015246030300306440000c15510030b2113101040c04800d000010011003040c0e0054501c40004402e54a15183c404070300312005015024420346000d0380f40d07000007907050000e540761040794040856241144008034500c81070b000f80984810780c84040201041d400e10800b0070014003c16a219691145142c10130107003541c2c04415490f04001d030401644801d2459986005910301c4c404000503680c8200c00d003003801900791801c850340144543e4840c2685545c40402c40d1101c000643e00b0755000a844800041c00e072031095600300c000450304e441443c071105644004200380001d4107011008030195507111800d60700c0e56401030b0003003032550491601c1d50520380241c54161040201501b019070441c3d002038800c82c8400b40142128666411021042d11010110f40c051100f66080f2162031800d440c00d02e50b260301c00c80c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 699895143 1250 699893893 699893921
    0xa09180f0f05180106122d0302070f1202030a03050d0207061505040c0f0e011b120f0809010e03070803070e0618130e0d110715020604051c02060c0d0204050a0801 71
    0x8090012902e1040c0b10709030503031b4101c540d03000c4200296181e42c918003020000003551001600c0400c00ba60f0400c0794030041c250310a802421440d4034210002200780c2e826130188016071070b0661140010780e00480c00420302030381401c2980e201c0100d1410a0f0090241040c001c000524280354482001076000e0300c041101c900b110284240130b80c2c81c03130840b0101821320843d030100340d0551542c812076010f0744610058940181540740341d01845d840f0302024000f0001c4d040045800c80701d4800b80710b5881958248e001003020001d210942d50492010713660702c100400034004d503074040042007041d031095005540040740200455142c0c1500d4107010030911110040d140b10715004d0a0141c8010002d001700610000180040c00c5460441c4205954a403030f0719040007158020b01d1008203130900700c050100d07882419030703004080500d418506a80340c03200403418950b5102c480c440300d00d85964000707001a800710302080000e44540340680c810000c3d02490704403130b91041581c00b001c980e440055101c01c4080d0307416 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 699896393 1250 699895143 699895171
    0x303110d030c0909110f070609020411092d06120a06050d02090609060d050d02150105040218012006010303050a080f01050a051504150507170a09180f0f05 68
    0x50301582160900540400400e00700d510800600d0801d502c5440500310042c1010b2030310f142179000c11070b154044101110580c0e9184245000d6051601c03034290040c0b4080d0102c2c4c40c0880e4180000c0d9141814445900198400304040c0f04195900a03410700c0782001500786519103081c2c1121410007602118844402450964005003525280c0d1502c8002600506005001d8841109005140c00000c6c04290003000c9000d0400c00910b003041081240e19240d0701070a0480b01e5440780d03280f00c61040e4007840c031807401840130444511000d9410100c091003424003a184111000d100441c50310440e840201c82d009440c000014184c2140051000c2d501d2903480582c995110f20002809940078081d0301d420820140e800d0185040204040030072003e00c04403a41010b90f920001007813580b075621404000381003c140e080403c004542c180c4a46262811014101004000001c20179800ba00c01d44102d0f0000c0701d5614100985540080c10040500009201080d094160440504000c0c0d40400c3c9418903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 699897643 1250 699896393 699896413
    0xc031905100b130902031905010219030b031b1201020a090e0703090f02040510030f060606080c070f080a09031506060e10121a09090a06051305030d0c05040f030311 72
    0x4910a01c0e0b00900010700288100d0100100c0000410b10383c1422609441914800d004410890b10345040f00c510074000580d88010440e044c180c15000440400141410301500b4009580c0c0441e140000c200d0300070300c10060721581030000342c1e0044c0d00300860b030142d48000b504620055020300c0c4041915071450421565848680703045086507594075001c2c0225801455075001882d00f5008250400040940e1150007500c1e9114801c040d400d901c81210100e64a220410074103800003480c5078812448203849080c2000e640b182c0d082c1c240d507500d0013030034400009201c0144c54020049500a50307085031540403204030200c214001042396000b040d002c902820301d0001141b816061422195000340e030740e826000e00640400014107030041d18058400d80c81c3c0320380700c85a01c40e6940a131003055080024480160141843c0007140d5028080718200b414680350503010a40000460349488103c3c20002860740c00000c040302c060240790060700c0f02c0d2018400c00003d0551001c0b0f000710380d40403a8240c40c54001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 699898893 1250 699897643 699897673
    0x528021912110604090e070e280e1005090c030c06040b180a0302061210081902100e09070e01031d122203062c030316020c031905 57
    0x251911030512032116028075003000401c0b11030181030049001c1d000b030b410305031119a55810b0b5040d444030150103903c07120382002094050200303140c000450b42242c0030420030a540ca4030400c2c0101c960b0000050b00c3e2155400e1190040004c040c0c40400d400f4100084d041c50100503480d0014080241c7c0f0900c1154141400c80c80c2c0030b0200c80407110f200c00b010740351810324240711200308448180d40368080e441c6034000000d030716040020030003541103001e1581d01d841c00515115070050560030881c0c4030352000280c070181203403a001a14019070103e4201407200c98462048074051200714030b00d03820080e08030900002c03580200501c0c8061000340c0f0240315448035012b040840e02c03c8001da1649552000e0084c40c900c5441c84020003a0074500240c00500c4a440e140c09031a0005952080740c0d1980c0d80d54210240c00959001602d1550314482002a1034000c5d0064a54a00024003200641c844210700322803824000c106036040104041d05441e0307100c80809903403030707003040c2603001f56440e000b01113413520102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 699900143 1250 699898893 699898939
    0xa081818061f020309010c11130501150c050d0c0204150311030f0307020d02060c0a1202210a08011e03140d0315060903170d0e0a023307052802 63
    0x10b5030380c0d4025810b040015004403014030040b80c09071000c141844e80000d0644607004034072590b1200720408a000d52401a86c1c4008403070500000341009a140d040c440010808260f4802c072561301e151180000710f4a00003e001810301c40c565011000c201140001002080a910f04011074120291031080e0240c03d0030715141e110703114009501446040c61440186850400340585a6414040350340101d070b1991251025502800d9031405a4010340001031002012601125010080030280d428030281c410040d15917007060203038165071030300020a809803a080c045044011604801d1b0b15503001e0000030769a4458232800b00d1880002e007003d1f10021704810a2141e81e023241d0035176640c841c200385980c440c0112029100c81d858040c503000c100340c4242c0c10a602074081402d80351000350910000314410808100d150915100c40c1d100d2802c02803914191450040c56100d02c10400c082c0e9901d114641542880c42d84408821030010300100003050440301d190a41480c0c0c403d41c1c1074a050300315540300c0201e017 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 699901393 1250 699900143 699900199
    0xb30070f0b040b07081b0601051c030509130f020f0909010b07030c0611040e2706010b0d1104050d0b0108070b040e0a0902041509020c07090e0a08181806 67
    0x38100801c200c2881c10b44000c0c04000c0c065411242414a029446c1910b64180009558581d0007400107000600d003940503070760704400d002c00f4128044150340e0302810700d0245a410f180b04400800000d036104045030404511280400030840d07450702d158160300c1c9203800452031240252505c0001007501540301085034207003030b050380340e8400e8030f002c0350b0790314000d400781c1040d21603600310500000881040680f82c660140002c640c08154a06000306031440c801caa254040c030a0b903020070300400010800e03004441d00740c1001480803408003101840c2d10420700c51035024580020760380d890402806816030480c0d0507070b000c5105941025541d810042d01d180118001c403511440140701003030500e400c551000c0c85180c805003000c1015240003880d240018520b44c046400583c00160380d56070301d54240122800ba200d0303040d08215030460b00d03103450745e5040702d040003c1c07441c1800110f012900100031891b6941440003409001c5a90345d0040d0340c030b401082981c4050041419107102c4940095145281e911 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 699902643 1250 699901393 699901409
    0xf020c0c12250b0301060f0216060e010f020708030d0e1c090b1b2a09011a13080a0302030a090e040b041101032003070e0909060a0b30070f 61
    0x2d124408100c40d8201d801c0d50041c008410346448001516400e001c0240d8001e1440c3c1d03c1e0700160010030301c0040c1c00d04001043c908034080c4a48024400c6541013002c1026100083ca444c0b241e04440f41c1d0180c1c5400901e1704010540c0c03102080c604100f000540082402c050101d0580d031001905035401c060710380039945084003042d9861820300c003000900e0701504017440b0070204050312000340d10351303541040e030b801305102c0b080200940402e0a5900b040074080b24002c0170b4036255605e40c505510010142c065802150303441400203280d295418880b0b82036070141c83c01c4401d0303070101c0145d468003940c0e9a1100010b640840c2411000250b02c19034145c2562180da00710302c9030340c0d0355521a5142e1720080d869203100e80c1030550701c9074440c94208200c3d11200c0a0100c01800990b030f0b0400d0b0901600d01c82c26180040c0c0300e028040100700d200c41c4007186250708000c5c03501e40440c2c110742200c0002c1091301c9c00740704154950302c0e020b030248440ca40564060700e40c5034580309840d24280c40305100d1809419502030b480b5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 699903893 1250 699902643 699902653
    0x9090c100203040807120218130c120804030602071109010b0a020706050c0a1106040b07030c05070e04031704110d0f0b0108010b01090315060b07050a0605090102270d05010f020c0c12 80
    0xc41b40c081102185811440109003001c0701103500459140c000081d01c6000205410010305d4003001b0342468207801615002c0400580320b40c459607480c94501ca5400018030040e00402d4150802a030071582194582c0002c080c113080c2c2d80c41c1c03a80c41413160054003102c0010701c51120700292241c00346040343d101401c064060b003110011a111001c044060342e1340703030341c102c1c03020000000c01d8644200601211072095503280c2c0314802c1da09001c2d19102c13860300102c2d128000c20080c003000a4114030140c0583d02c0b40c1c18071340b243e95030f5400c101c544490155030f010340102081c101002040720352010b00304007600c14014000e10f45d0b00e0f61f01c540d0803241402400d6002c60407ca038240042060584003d210b9144600d01041054a17020054855002000100c41a07800007a0030002c101941c05a503a0003003000c8021420051030f216000041f101e034580403100080c0c028034040a03a15203a0003031004c03540190003801421a4809850000c1d1b024003460403150052224481d810319010303900b8100c142550000301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 699905143 1250 699903893 699903899
    0x140d050d020d08070f090e0712021801030614090612030c03041401020f0706140c0f010f060617040807020f030c0411040825210510020301030b070c02090403050c0c09090c100203040807 81
    0x1f1742003000500780303505201d4011046c15104200d030000f00b20f5110a0044501c0c80310070f58001400340c805a8200e00c0310034138851020b003050b844849845921810031518040c030103108404860a511a0f03021809081c0000200811042e83c0c1d203850412441e820b908031148903011040c1180c8400c0c0d81d00031080000c1804100d40c13414120b58020744a4141500c0a541008030303106100e81c2124822107080880d161a220100107040d001a001e520b00d0028078903462551610366940c103101e2144c180e00038443e2101c4200d0300c9042d03c0400171085490000741c0200490640341c080919507030043d01c26020284607003600c0448040c40610482c10003001c02240d9103502e800c101900c1714100781c2c40c0509094152060344640410400c001c40f92455801a0006940c0c2d411418500041c110007403100040c05064006100140c54040c921980541c261030810340b5081c0f0521043d041030320f5010801c1c0d200038400d090044514004c942102407050440da516007091709250140c0e240c1c000c510941c0c800f504440f40070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 699906393 1250 699905143 699905159
    0x1008011a09060102102a14040501300902190b070b090a08070b1f08100507090b2206140a1809050405010e010f15140d050d020d08070f09 60
    0x2603800401c1401501d100c801070604010858001c01071805143c00000d80c6c80002c040000c2d00c902468255242901c40c0c0300300c00408403500d20881c800d1a0400c5003540310f01c070490071035880724124645c0181c440951420a0a4104060490100c060784241c400d580059024001c002c441c0f0708a9401b10560750038030f50180c90301d0400323050013010781a15011f50841070000404900003055010320030850f00c0b0250905080410341d454485e0126030407800b000c0e0042c002040c00050456103041c00e65400f180640e5050b40c1100c44c1030b540d5010303042c074940c04210049907080c081e840c04400d101d0341e0f81244440c0d589510449440c22021020314000b00c042110301d40c0503100c1c0c82440e4004420040080300f95a0301d000f00003c0310b80454050350300d43d545840e0f9481100c0e080c05040802d05200e44240000c0705014010681400b15200b0100760302c011000b00103040d1901000941a15004003e40e000078814500194a402d008903050002504031000250114014800303046007600a540300705440d4102034007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 699907643 1250 699906393 699906409
    0x315020a17151c06060308181008010902031b0d06060e100503040b15030a030e090f09071509050d080a0206070504180b01030f0c0e1201050c0a0302031f030503031008011a 75
    0xf2400c010910035503100c0031400c04d002c0c0c0c100a51003642c0c06030352607007c43d1051680d490841c104900ca01e016290740c03080207a01070030160651b61401e00050352a252030901c040c0d81e8003980c0507000181e40202e8038103440d03007a0740d20980c11140315032100700131120000f0030400219040038420b000302c0d1092001c100805d100c0c07880b140c1d1110304400401c3c9024241e8001034a00b0070048411030010b075540100c0905800e04520007500203e045030340a0a500f8103608031900d668103801090b0140c0b22a0041015113885106050b00403c03001c0c0000542074810705181c1803952022203003d000d4481e0002081516116900300c0c0c2c03c903a0200000d40302860160003403030113420950b60003410181c8624294900500500c80c03404000f0789030300ca03c222040c0e50b1041c4007015032a10204a5541d140504000552040400312540100d035464016a260303240e5144a00051744444030756400c480580c800320400c5400002140907812003950348070b4641e44c0384002d0b400c1c1e030300000e1501e40c0b94424524040075800c01c282 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 699908893 1250 699907643 699907669
    0x30f0203012d090513060f0c0c0b150d05010204080705150f131706010612020c150c041206051f0b0703030c20011b03060501021f060315020a1715 64
    0x4100c200c410760310390f101001d580080d40e501c2c0e00d900381c03010404100079952003130388040c4000400c2400030020301e400280c8000680303100901803510b940002549080107064001c0b481d01d0090104580c940c143c10100e0007500a405024081d04c00d1417401304003442c20281c2e01e5081100410344c00e00c3c260b00301030000c08507002503800300f81071440c4210204c1e41410f903c00e29503481c1d140324001c2900d5072401c20020840b0400110303010340d4510411555100000204841c00490303180c01c03600009403220802c41617544150f40c007190850090300084002c10072035030000c82c004e0808130024840449030060080050740319100d482c0b8407210810560b000680a500601006070b400c0c00e00a0060b041c0c4020110081195103140846035900e0040c00c4031840d02140385070b1440e1035403404000c610701f0000040d5444521030600004c040301420031010b280e5081c3c01c10b00c0650b0344190304001110a81c00010301a40000c4585008124581c805140c658400c030031030740c4114688040329940f081c030941402510041c06c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 699910143 1250 699908893 699908969
    0xb1f050c034614090303070210050703030b060f0403031b02062d190809010e1c0f0809030a140d020a0203040f0b09010c020f010509041b030f020301 65
    0x400100d0121094044210308580c503000084460803615102440c031141e6110880c00310191488200b80d026400030b603540481c907030b04050700d41c0ca990301000a803030b5000e902c0d0002d510200179512013000d180c0c031002a2040a1181c0c409024101171403040001c0c40c082c414081071407542c188010070120b44240d1780d02069415102029002000c90b401040c0264080010b080040d541e440b02c0d144060710691030800c1e00c030052510075040000341091070300d4128100030702804200d51000400c6260100b0341c000504c202c031003412a1201040030304502269401c0751a038030041030000c0f944404a502800c0b00c00d1045507990040c614240781400b0946a4500810140b0143c81085c4603040495103e440140501c58240c0c0007036468a10b0708184001c12026034001390100d080c24416440c003640c010004500c0c0983c100c6001c50809115030040b29140526420305501900301a4105103048084003908140d141c1641c05008107160040900700b13030302c0b0078480c000844461035551445900400512010aa111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 699911393 1250 699910143 699910147
    0x2060304020405040f020d050d11060c070b0601140715050105120a060c095006030a0f0203070305090d0e011b03030204270606170f061507030309060b1f050c03 70
    0x141c02140004441d0982102c8903801004980d45130ad400c0341d2004080003000c40200800d10780a02000f40a0181903002000028103201081d01350b801005040c501c4505522101e40b52030103800d041481c400c0d000100300d5458034040010800d420883d401441440a401c01032225545969443c0010031a03400d440040010304d10340403444048000314510504100c0c039901044007003107800b180c081401c0e050204c6550081c96042c002c5100600b080c602c02c940c0459031551681e03201d1039503001401c1030340707100e1051510000800c181d00e41c25501060107150800119003220580c01ca05652408207c01c04c2400b050b41d80380c41811040c0400400040c491081c900542042d030385920f0f0b00c00010324200081c0317000c80702c040c0c43c4520383c00741d115860041880d0b1a10241c845510010455008d201030103c10800d01e016000035680e4480980004a84090307001543c0d81d80d08508008004100201040ba0013a09000038140c0301e241c0440400189451840301c12004545107000b0786150b44041c1c44800c60b4042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 699912643 1250 699911393 699911423
    0x5030f0c04051201050603060916140f04020705030c0d0e0a05131d061603022a0a1407090506030c0619170c030a230a09020d0c060309150204030206030402040504 71
    0x740c0c000f520003d448480046241e00b882400c046c01c020340100801c280e03030301182c40781d020307049500e101c40d080362402c905112415044001103100300c40c540000540083c0001826800c10100100a215200d0248144d400403030440c00b01722021024000e000c5d6009001040c140a24a09039200c010b002416040c00150044002e0300d022100c0260504103000307422a0080154030f02c0611810080c4040c245003c40c600125118442d0304003805244410038100b002807038000f00711040044090160f04035110820100c00b2904107540c448950243d44101401d04000c07030780ea4200000ca1001c0100000c00c1141804c2c44804040311600e04c0c1d10803101041145070035000c1c40d600b101d594500500f0010302c81550b030701c0c0000821080d0740100078034000125150065035560482c0d0002640c00c400c2d040310100f61902c150001940515624a010b41910700c2c4510000304140c240d0301050029100d68400f0a42c0408082c04e00c040307000d1440042c5d000042000003030300619040c1d0000c0e030b0140c820b2540b038040c0c1031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 699913893 1250 699912643 699912649
    0x7022d0a060906050702061b18010203070c032001021b01030903090e090706080c160206091513060201150806010911041203020d09090b0f040207061b09030605061005030f0c0405 78
    0xc54a01c2c150340c0e0940d50b10500c00d08550500045500101c81c1c1e9100b140d401c400c0c200030b6040d00c201c416641c5a540320b10130501c1542e109000715484280c100700884103c507200c1c145003c0d40b0100e5041c01d81c1ca0300110350b52030703007a50012070341e21540e000f14908002040e002100540c00741440080c100c040056a00e004030b207042d00340c288540286c50a00c0100300340b50422002500c60301e4060300406d00d8031000d00511018128460b805031100e0b9040e61000d031a81040d6000c1501080c640c24500503050002c592401071700c0c5001201c40031500564000d0003240014660341d103c0303280030700032501d1300d810600042c01035541c1074025000c01d0f010b06041c40d142a0b41c9442800380b000e0f03501130450060b0001e50480040030f51245046000d0030812204114072410b210010f0b16031116004c009000c2c64003c030341603090048680c828071303400419684043c4600540b02005009c08030500007156600d00d0280440d0050074420050101d2880c2504c030300b865500e801540700c21007280103003003956081d000c0001260301e403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 699915143 1250 699913893 699913901
    0x6110708040b030a1118120c030a060e10021c0903020a080a05130504060b1e090d0b011d07050304150b030706050909090a2f03030a090e07022d0a06 65
    0x8a002010b40fa03040c50780c00035058800e40000a10310308030501c0785030b0216030380c108035203181001220b5139051040609145400c0580200d441c6a02d4041c00c803005061080903001081407100002c182c844505a01c00e000d0124007900800d28405920503c2500907000e00758000034496000780119400c6018503030340c04280b5408400340000240340466040c4014598100a202414040b24207000043c2841401002070003001d236502421400da403911503031562014100c5420b0300001e0328118414040341031160300498280300b8414000103400c13284010440e0b050040c0e02540f9250340e11403868696444401d5580540600554102d60701c14040000d0754040000c0e000400c250307140c15449a02034020802d020900034007a803050f8200200c200006000050901921540c40350a19445a030a000904d44280e071400c5843d090300c80040c80400940d001414801155001e2a5898103940c030200700300d0300c40e03c2c8000b82d201300c1c00d01900d00910090340c0c4408014010150b0b001c8402d01042515108151 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 699916393 1250 699915143 699915149
    0x506030103061b1d04020d0b090405010605030d0807090501111f0e0705040908160804080601140f011d090a021e070317040b040f020409020d210e06070611070804 71
    0x110f659461014107848800000c40070700300306400c0013203410090200c0ca0340c5410762101c0c164030a5500060340181800c0344ea020540600700948151164035280c60064020003a50243c2e80c400d21a1403e0030070f6052003010f200e84a4102c41d5140c125441c0b40000668007450b4000c0302902c0c600410900850304040d20640e02c40c0e41c00304c20380210b0700106800b0000d041c03105a0b0020b50040d03052445800205032482c3c12100892881405602000803d0400e4410b60003070781c214658500030300000040558610000303800d00003080700c40700a803036510301c010f540c1d4007122090010b0103600d100409071580f80054400c1d03400624020b01500c0d010200d9255206003440d81715904441038041440420300d68081c441c0d180d03d000e086881c05490620b031f00c61001542c2f0040008103003c1064035010b045403219000740d000d0f1580604500d1300c4180f035140081c0110341110900d0300d00134601d02c19004240c070485200d100980090f08181c078180c1e42d40c90740805000d070100d000304804803c01c0042d000034940801007000b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 699917643 1250 699916393 699916403
    0x20906120702211213030e0d0605040b0a091e140703030c170301081c02101e0507020303070c020d0204060b03070504080d05040303120b19090204030b06040e0a020114040506030103 79
    0x1990004860f0708003246900d94483c2c01204280f04c004603c405080e94241c100050007803000b01404245811994190000c40b003641000c0c0342c03c01d403c01c000d5250442800303a4812403410105907241c242000407550041c034086c090b11071021000120b400d480b0585c0c5200d134012440100400480c04040e45480011b60080780000c411100b80e509004184c0140034698a00503901841c40d403501c00015603600300c0205828500c03203011711000015008100d00091007172100300501980707420010b1002651250600c68101c41d0038070000560103072010003164881c400e1600e40041e90300c156001e000003c1c55400e070480c1c009030380d10300110700c1e20000303000345104658503928140d13203d041c00c00c2c081c148007409011205000d0140424000a90021015089641c0001d400280051420009954070503520814514510240c00c00709600c10f40d0380080050b240950f500300003c0c6c0740c403c18003044071071000540074030b500100301ca08015803140c880e030f84011130040c12503070a16840342d0006100798820383c82110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 699918893 1250 699917643 699917653
    0x30112060b030a05060118091a190b0102190204020d050a0207030906140a0f02100e0c0f090c1206031c02070603180b04030f030204030804030c0812031603020906120702 74
    0x80248a01a4201c1c181058000d844100000c2d6107555039a0018040c201541c2044078684007494055849503a0b0aa0004000c00054080c040d807025001815103024071039404032a04000040814080c41d40c0d45138041e4024204c01c062030840101102108038201e90103502008041082042405407c0c000c0070113a500507542c2109180103444c4040e1940a0414000c005240100c020082c00c10f64403501940c1c105207003211004107040341000350200701d862115141c0501e000101c40c00140d091603804080e07440d2250042e81d002081b400d55800c030369240ea012410412482000030705410f240d0091300c00b60840e04a904440d2102c040e4100510840c030040e400018108035541e810700450aa5034001100c480c1000c0c4141c40b6030807004002440602805400400d50240912a50480780196040b101560300c2c3d5460317140c440c480c1221882610000e00c100b902c0d4040c08103c01c02183e000e207020710b400c680d07081d4404000340d010f03400c03d05400303510020901c0702c003925641c0245524800c42c5103501034a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 699920143 1250 699918893 699918929
    0x90632040f152d0302070201120e0a05010617100f090b0c130b0a0f08070908030d0e060108010204051e040908030a090c0e0618181f0506010c0b0406200301 68
    0x9000c01c0700c5480c2c80b14100c511010180c841d1071207003d00c0221a074140340140ea64021400141d0310422003491900c0411300e80040000a041c0c0403e003000d40c2072086009120032030790b49400900d0791030802940000750b0400c204403880b1090640c080d2802110840340815491201d13158100c0400040380e40030020b1100003842d6030003189a0641030080d00c1425031107420003901c0c0388020322502052401c48280304403040450061030060003151b00a100c558110780d50b0f5804801d840010348440344c2120403030300c945400030403125410300943e070948070090441038490301150003880b03e09080100d240d03085980d800c1c0d10307008201c8c04401580b150140c0300c404902d5183d20700e01002d502d40c1035446030a02406d0007041c030109603241001e20b140070400b00103c0590b51201100210410040243d41c0c0491240c505400c6d00303003000d0001000848860601040945c2d500c00040d216500248401060f090702107001400041c51b40d0b00008140402c01c800c6007201c2d07400080c001ca00c0d4030a80245403240c8241c403444d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 699921393 1250 699920143 699920147
    0x709090c0302160b0912030c070b01050307030209060d1401090c140a0f0909080c101d03030103080703080c090312030901290114130e0601090632040f15 67
    0x115045005850114940341030003442c0d002c4154910f900800e003289400100e26944420014042c3d52486403c0380d682e642854a401078a80e4070000b0110341490450f000042e0510b000300d02c02044079000307400d120316652024200a80c0b0400c824007202d9074a588210f01102c08002d2052210803882440541909800d007448c1d10358503103040c81e10354418054a041808015080300021f400c540c0c0301100840c031030341e82d4a04503043c0d009101001c1c10510407140441c00020701034200f80d900d101101d0404040034288401d1a17101d01c000d01015000c24020031901c00040d108a0159030b11000d03241046041c413803004000303428503060b40c41ca503074549804003d02442c0e110038841d00b0482d068508540c00b00364000f9540b1440008401d030180c1c1800100710307420314841c140b00c088515040240801c2c2d2081900e90602c400542c0c030554a03103002a414000100e51140100d520003517580440745904003010820390300d038910b50301200b9400440c0c9018040092658500c5690030040c1440b0001c6d542031200702c40340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 699922643 1250 699921393 699921401
    0x100c02030d1b0f0e0a05150301050f090103030c030c0f12030e060c2d0f1308010f02120411030c19140f0a030f02150406110d030209010f051c0203070909 67
    0x85070003250151901c52150080d181c4940001c140c28000035424060313000404404040d401290019081c0906101c03103504c4000a506076a022255000304041c1c8400744002e44000b40001000705030911041d00120740100589003240c6c2c46601c5460483d2526078aa0300c80c14071448101003c641c8609040609807810304c00c00d58022a401c00e0181008581c2d030711407200c001460521100c03004041040e0201d42c88141c2102c41c80d101811000d0b54810004d0062220081c8900c01d50107a03500e000c405496010803802110005005330400c5442500c4544400032001c214494281c0e140c0b0a1918189a81c0c50304680210044110050900c0203443c2a0010b0080c1042c0f0030040d100b08000e524200c3c103070b80c2e071000640680303400808550b03400341c1c03074404500541100c032144440b07a5408500011030b594481040d0300401111010b41c4c2d44104034440070350590081092140c0414410880880000d12030000b80150600e24110b855803841c1401200040780e005880140c000303001000180100c0701a030007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 699923893 1250 699922643 699922661
    0x13060609020909151005210103240b010806040c020c0907020c091302010906180b1902010c03050127270c0b0c19060b030d0207090e120f0c100c02030d 66
    0x14500030314074240014880b40c905d8005203007441404110984205036550110f8150071807900401080d5859003040d2902c013191014900207170000b40e080c50354640366405101d40303410f010707141d0442c00c1c0c80d03100412010b007007090102c2c011445040100da20681c0c464a4482c01041240c0103403026072204014040820342c0244880e95060410240500603680200c2000444501d4035003003070000034012603008c10b00390a5102c0c01c480302e4041115500c40464002041144000380c000b0019054010001d80540d00e00f4810390001d0119a84500c0020409181800c1203202201002805140741800308c40640010340200c030032400c00034500350402240000003406440845182400c1c014124000d80d0b5a15168451400414003203440302c00300540754000d0448500b0080a44a00c1c02862400942c0e40b5581e11460250300e0400c0441d05224402103001158a030003424114a002d90f80041810181c0c00f9046035400b80c854200c40c1c00303a402151040c3e404800b0141d01a50b540e1166409a40c240c4050d29 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 699925143 1250 699923893 699923911
    0x2a0c01080408030a021e07030305190915020310050405010902040608060102300906030901150f030201080411060c07030b0115110a0f0804090e060901110f030f13060609020909 77
    0x200788000308450304162580007040e840050303a00d0716000d0300c0c200075080405076085503c4000c160681010303015001944202d580c41c01034030326010008244419188071410180140002c441d818a210303460781c00460388080000c00c01762180c2d50b500e004c81c1c12641c00341d0050b043e05601150a1049a070f0000c05603070044806d01c0100781d0018074144041c24072a82220f03442003003514041c1400750102c420140e8140850060106480385426566580a07002d6001109241003164801140880b940c81446013076a4069544c0b0031702d5559a59111402014800465445541481025440c810400c26000510302c100d00076207095241410745904142e00c0740782d24040c415030340f498003220140055440034072908401c1c0d00c4008a002d05103482d10b441503401a40e855400c4c0160460328142c0010901d0180c0052402040300d075a02400611560090315003c4442e800b00f0004101c031104076030001c90704090b00886424000c803043ea10708080750442c1d03001e1041c207a008a41071405162111a0541c400c8100b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 699926393 1250 699925143 699925157
    0x60807060311040b0a022d060106090b0d150504060f030b06010503040f0609150c0c170a08070c050102091f1101050f0a020a030905061807090b03030a03112a0c01 71
    0x300030502540d0045026030382041360081842002c45100b00907005854000e03024002d2090f0b041034642454514071040a10203100d0301c800050b0240c80354113072004650601003002d0074110f00c5140c41c4060103081071101c3c031600c030f4542c020449075241c0c4500c0c4024401c5070003e800c0c480c51840c202c840b101004101c281400300601c10440820040082c0d40c10156200300000340c1352203c0d04e4010f02d1034120b03041c03043d8658a0440351b1001540c00070381c01b481e10b90140d10700076003050041041c10681e10408401c0e000065040b0042001540030b03151180c09a0300c40ca002500300708014012541801c140c005149001e24851090003601e078001e400c044111305d005000b44000d250002419205820162040002660024038002c11500c281d0211601507401410340d406c42c20513003010f10700c1115081c1c900341d41e805140c60015001c8842c1c8240c0c1c001000241c044c6090040d01c010580c0105852014481d0034181009280d00e6484441000e0a4154400d50804c41085241001515100e50340041038107000d070b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 699927643 1250 699926393 699926411
    0x6270f071202040b0703110a0f0b10090e15180a030207060f030b030c0112090b0a0b1005070b130804030822140609061303380402010c0f0c15030608070603 68
    0x4c0412900e0084c0c060500001c0c1902c90f18501e4984401400050450303600c51406a08106864a4071400748001c1c0c054640780540b143d0300d031070440c0c00c807800c040b81c0d9500c980590551013450002140e03108256401d6132500740d0b242d101c0142031800c903010441c01a0003458003031180c250071121407074046481d80743c10480798607a0004240c0c2c0b00081e00c01c842c144058a06880540303600c035041040e0041d0f100107254003904010020302c2c05801c0803510380d48910a800e003540c811900c1a800e0fa11615004004c00c04503403600810061418100303501605d00d40b00c10080880426824001029110301d068400400c0c003042c29002600f100031504038401c94500641180401e80d03590065440c002403c48070381d0390f10501d2102d031003068070302079100800c280c12441440c0720511440d81011040e60551860038034100c1c114407040c4900b9000c44009000c52030458101c00403075001f03140803091034498200c00c1d8503151100c100c140d2800c121710003000082d44030081130040007014801c0c00014200b60400740301c00c840c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 699928893 1250 699927643 699927659
    0xc05030601020a061d070303030f06050108190203070c020603040317010f26010e01050f0f25030f0b040612260403031b061104031e0b06270f07120204 66
    0xc46120040c004c05c2d25140303006480000b10500c2d0042103106021150070a6403464013401520b04448007102d46450040c000540b54000c0b014644200101c00005500803c1907032141e0003508003814100400590404400040c1c594400843c00750b4041d44500c1c00700c0c0411804128030ba1303016040010b40070040c800411a050f104a606c1400c0c1f54030504079450038203040303042401001c1d905a9040315600305030502509242d0824014091a00c3e01c1e641c203255580c850700d000d0b15580114410251200b07810300941e00c03511075032000c00101d5030b24002081c007050200004040e6092074202c0007048180e40c001c03c081201d408840349281c4000c5403806007034004070008032043d0243d8032010b0240310101080c0c0c402030100700090310440340d1000c001c10619000c03034031028441e04140000c68041c900403400ca0f08190105580840c1d055000003421003a80d954820300031115503d0765a80f1101200c6030400c55400301010f552442918070401c01e01c0c10740342c030680051030048001040c0070528410401845100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 699930143 1250 699928893 699928903
    0x80316020c0f100507060203070f1e050405090c0918150a03050d180305030f03040c0902090a0303051b011407020606090907051504080d020f0f12070210050c120d0c0503060102 77
    0x600304a0700400c0040f500581070740c45228a200007408244004104842c440d04500804900b10031a900d255890b0398203040480640781c940800e501140081c0400c1219162040070300d603100c0c035291960342c1440d0b004404a20b03503c1e92007010840140b00501044541e24403988000c4034403002b11500b00140b031031500d031640c80c3c00391203071140200000845401c03640310900c02c104c001168010110307507542e1403444499080e900241c50407119114012030000c0c0d2800c0c0b6000f0782c2c40080004080102440ca0b6503030035030307a60b80144241c008203814107400703d912103801e10400107010000102807501d4608400000d0428400510f5103214400c058140407050400086000540d403003640d0340368505000440c80302581c01140d1200d9100d108070f20300c00480382e03804034244410007952403c4482884151a550340c036550080785c8241c00381400c4c0400c201610f0400c0d0010080e5106003401845c2c02048400310f82455103000701d0b81c4280100041c42c03080041c5600c10004c0c8160185001130440c00c0000c0001e49803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 699931393 1250 699930143 699930169
    0x6030f020603091614090a09030f0e1309151803120c09030c031a0a0608030d0f061d1509040209190605060a02010608071208040b130b0403080316020c 66
    0x1e00000b000048502408101d120225900d400209850a64a2a40400c92242c00341c456020f81d0401c40420240d03143c0d4000e0019403580b5448403065040030034000c403107000d030710503050323500c00d0800580608104952082e00c10307150040b040901d050350101c04200c20b56403008032590b84075200c0ca500d1740200b6803003640c0c604080340704000070410780d00e646400c450b051400c1e00090b151110209000080040d03440c801d00800d4280b030040c1c0e24960b01c480c403030b60440f10f0510840103030340c00400c00c034100c0102a46c0020340c000780c48000020311076110504010000c05090240f0f9020184500b4080c5049800074641003030001150310700400e1400d42c0c081600c41002600c40394034119421040380d20001c4030b1304410090b11002d401261104400300000307020703020611588050b80600103012408461449440c420f040e080381c200c138a058a40144003485030f005000d800e0f40c00b80c8211010a0f2a108000148001c501815510b81c03242042042c248800c03601d41c400000f95803051b111201d0a855880c110351403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 699932643 1250 699931393 699931399
    0x509091c0c03050d152303060c0904020c0d0936020304140d1e090807050603041b1202091614030603030c0f060708010803040303120f0b031c1206030f02 67
    0x700c100c06150558660103005131071907580d0705010072240b24a4040e4641c1003114010040012138a00014803058445069050580c158102d480026128036102c80208920200644010720b04520f41490794240494088203a001031140700041100c0c00d0b00c0c1a010a6424600e68101c2400545080b031000940d03240300c1307146083e0b4000c400142801a50b0700e840480c50124070a1340e0b29000600c10062070340700300c50322011191903840c0d0342d03800e00e5124a812034103582800c0001c12000d801c2c1000c0010a400c000c10032100300c03039081d10000c02c030815991140014940140341c45580051841000900d2000801401d010400081401480c0340d010101c0b280498004020542c3da0301c1d0000400e0941c440c648080000f03124000d810000200002001c0c1e00c1a80540c0d181c0e415641c9030500240c0301c0c03003140b202900003096988980c0704034072568404034612004040000e40081c081c0040707400c003003030210803a44e580420517004100c150015000080343d002d10104006c42400d580c1c80e0382307025401130001780c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 699933893 1250 699932643 699932657
    0x80c031e07030603023705030a061503050a03020706020d1d120f1509010501050409050a030f021905250f030f020301060b0c0f071508040b07090317040509091c 70
    0x200c542c025880907000d5034010744a0100e071303003c0b850103800820036000119070a02c100c1011480051040c00120309980000700601201000c684803100a081c4090340754451030b14440d0004000f4a0070090f1b101e020784650007920803d03180c403001a0500d4034480c40b090a210010390b0104041c0e100f080d0101c0241c000715485200c80c1c010300d880500c0e15400c00c00125213071103130300d5984280242d00d00446216071441d8000f031010742e0300c6a050000f80c99031020024141e6101003102400240980c4c107501c0303091813500c1250312300612180c4000b1081d507103d00540d2141c004d201c0d03041c0c9800304a1145a048882c00c001c411240d4904420480d184482d40b101920301418100c60000f15982900118010840700041585a1203184056501e4281703602e01e04d843c2d0f01c512080001c003840c0c0c0c81c0b0403e0718007032142c0301c5001d01d580d5078907403142503000200b002c010409100804400070384110300740480306807540d15041d2210300340018040790400c00b0384099032039403010384810312282041c00c1c62080c02a640c58585 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 699935143 1250 699933893 699933901
    0xf0c100816031b12110c030a0c0807150203040201020c040603021c05030f0a090f1406300a0209100c0503031602070b160b15030705040b03101a01080c031e 68
    0x10b0052061041000060542c061400661644034025100000b110802089001d06210b07074110148101031103010710790401d0100c030303007800d0003100040605806445100e03c0c1c2025503649451145011003403850039507001c800c2c042035590400c83c01000980581d004c115940c110f40001c0e44c1d010000c0126082c441114601c4d6003049018015034146031640c0008544441403003034098619400340c0641030401810000015149822006014078141e000e00118941500030b030450050381086a401075110911a111740700c41c02251403403e00c81c0701d1034440161103d249100b0000300c16545000c800030066030445000c0800d60100880fa001050909a0b803014034a03000140c0c00d10300d04e60b10400080070042800204d4149071547e00c16a640304280c600015560079000403921890300300d0381900744c2d00c5078174240202d040503408241d8220004044518400880c0352101c19201c1c011100c50390883e07090644051540c002c88600e0300444c40460680c11803a0034800400082902d1001c0140f085412000c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 699936393 1250 699935143 699935147
    0x9031101120e0703052503080f0f0d0b04050106030b01050f21041b120305120c0418020912030901051801120204030b100821030c0c030c0f0c100816 65
    0x1100784580d212014424848400e103659225107052000740c499015141c00111051042020130180c190f41d0340f8485481030540e101d940c0b942d08910030780c004001c02081034401141414029014481c1850000706204801c0b40030300003518411382c0702c0e80c1814140703507004900760b820509660354051054039582c0c444004c0086001060a04846040c04d443c000c03041c0f00030b1050340c502009105183c51107155a00b0707030303400c1d418646052005010340010000d00c0b20b29401801c1c50b03a041e4220b540320482c2420f00e43c90301542c00301c0078600961810350640c001108001403c00c1c0c411054a403407640042d5040c8101c040029000d4480c040c0045c5442c02c408c4508a2968020950222005906442151982e8076440c04100c00079044d9145c9131060b044170307400546000c001a0751440b09005a040d07401c160628070342440f554102820b070300c162440c284480394008808001800000011600504180c00112807003401c02112030603607402602e03200303000d4075641d41050f00f1346d4000c2640500c90030200082401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 699937643 1250 699936393 699936407
    0x9300304060209040204082a060f0304030909241409060603040c03240b030d02120a02240601080705030610050913092402030103150207031205070221070309031101 72
    0x43c0341d00a00c041008501042c002070a801c10180f2071100014010074045030418030074517050415404142045415180c00a40d400b07160030911900f07140c40455140c01030325050700c3d080115800d5428019601100b420241400d900040c003120060f400e0900c00d200c08611f0402e8010306070350041e4400008581001544c41401c0021a085003607000c1940c00000c4800b011044000c004918905040354001c0524010840036a1940380d50010300c080c41070300e0f10300c0e0900d402c46002501036025040e04c035000e01c0d5402c0000301601c0049007030b00307031240f801d42c0000d020084058401c10070880140b00700105038035140c08044510704141070043d2074900c1d50000901d01d070160315000c51210f09240403007040101c1c5a001031180100e07401d4013010740c00444020f00c101d0000b4400035040d0400c4040500082c509a130081652902a01d00800d00c02c18901c0031606550098425a006911464a1040d0041410f200e040b07404104540c2c5880c2946580f0001c082d2600343c040503202128294084a8580c000d5803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 699938893 1250 699937643 699937657
    0x201050a020a080f070623070e0102070f0b030108010c0f0c030c0c05040e010e0105180c09100b0a020c0906010507052e0e0606030c1c0f030215010b03093003040602 72
    0x1003e0b41d44c0d0340d40728255501034104800071545182001d0180f41c150460b442d005c014030b8664070119440b952102012501b614109080c9815402401008140c0c034518000c1030026040e80c00d007146c0c4c0d80d4034000240b4210758065903940100007010302010b0060344e0000103d003c0c80d405103413080c280381603030921001440c0079030301c10355102d40303814400f00c008141074000261500c1034400801c01c90390303400d10004c0302c451030074024206070300800462456032915454842d00310301e4201c00506401d8980074040055403160040f84090382c007852610034985000840a5031044003881c000703080c01c0b91a03855564405140c100030160761200c03000f880201100300d55038030440c2885102840200200f18201d81c0390340040e602c4901a0040230a04403460406041024211000741c0051100040e15140e030000c0319507a04040b0214000c002c14000e03109145003086010703103000000359649090105100b41741c601b208501e00032080d01c001428058120040c803038a154018903d0742aa2541c50345000350091094007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 699940143 1250 699938893 699938903
    0x1a090a06020d1202030601090504050405010605090408070b010614030f0604090203070b0d1401151b120e091608190b030102040b070b010b090a1401110607020607090e010f030201050a020a 82
    0x1aa0014425500040108407a1a02d40b510100c4032081c0d05003000fa880200d401c0341c041415042e04202d0740c00c0981c0403660240c0900f00010391241c903000000c0c0c1408003603800740e82505020039018203000c3c00c0021180100b8881c03c048a80b0740050301e40c1420382c00010040b0604519407070004207243c4031904500c400d07690042c00d50740e50320340b0342e02e4114141c3c1041041d919803c0c0b800c20a2540800b0a100e22416110301018124400d5481034040780c15516880f41c8001202a07a05003c0014480f800c060402601c251140400340d1268018051100340060008031200b6580d8001400250022605600191002140074200381031460003000b508400703001540540c40010002080c8003040007410605100d1400b2038050390303880901441714050441c115a10213000c0c4810018000140121030600c403040c1000c20300c0303030001310f480c50503c0401c40302040540c0141040041076640040091302400c60400d502409505100700700442d4400c03404001c1c1800790005000501d24002c10030281c1c9039900c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 699941393 1250 699940143 699940159
    0x60b03011d03130b0c0304050904150501030c06110105041a13020a030503090a0626061c0f060e0106060221072a050901050303031504020c01090605160e0102071a09 72
    0x4079000c0e54a0348420518124010041000714000c00000101c0c1c81d08400c240c001d604103400c00041081d40c02d40030f8022104d0488203404c0524103029405203500075805422010f41040ca0080060001c94200041c1071040e4904020000007072480d0001203c0444000100031030b6540e11880710450152a0401035032044450340300108000380000101414201600d035030302450751713440303003a00e40b04065400003507003110900d4040020a40c0e030417560b43c0040024a110750840039580900117512000c5410b582c0c2c0c0e01c50a910000384212802400340f445130910003000361528140000752600e820a0b00c00d241d07060101f010380648000407060b0340701c0b60b0308115840811780b044510842010620f03006a1284c60b61044000303410300c1c144900178101c5001501551555503a138960607003180001c4201c3e0307070160b400d0040c800104001d214500e4960f20400c40010681040780c00340e00e550002c0503140007000105c600c41540381e42d01241c06801c517444486401c410180c2089040030744c1c0208010950090302d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 699942643 1250 699941393 699941441
    0xc1206220501031211060705090d061806060e0c1c02090a2304021e0a0c050d03140a061d0a0212070c06050912032e0608180c030a060b0301 61
    0x110352049040f64891210141041250300d82954410858004141180c010b80001580701d0700610080100c0a0010300a0388914600e80e903220403152100000702043c80b41005e280100441031051002034100c0303911820040c03600705c01c070210764400c4504104a130400201a4400c500d41c3ea011745003440002400c0540301500d400703218001c2c884881004000c414840c41180140c14988200d50041e0300a114005000350348106c0a00d50358040305648040242c40d40ba0780f40816400d01c42680041100c0d58049585504030b102c400c6071540241a01c9041071410100b00003d034400114880b5034000013881d907507103540b00c400d220001d00992080d5451186400304100da069401484500c146208520422450326488071040d52840d0030710400c404610302b0400302d0408401041e52401d60026544840501a804031850340e85040c503900480200f50150b0070b0144ca019584180b2402501050003450100c400700d0000c1e50343d07141d054015080654030658020b861703c00790041d0b19550b280b04018131220305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 699943893 1250 699942643 699942709
    0x10309060b0405011d0717061c0605070f02120f030a0903120f020406080703090b0f06120f0a03021c0203040909140a2001020a0804030b090c190503010b01080c1206 72
    0x1038190170300c0c0b01010110000664084c000c02c4c903010b20035125800007415644d1202801410345001d06401041511015201c002640034005c16104011345c3c5e03504558442c01c50703030203450300d08414028074010380c0030301c0780764481c490300c80030303a030b40660b06410100720301140f81016500c0785001486005400d0900c00e104000c00f003143c005004440c11603039101c000d82e0b2400000c40c05c840d4140c000a02c40b03280300010913076040380800415003200000b062140199043d00003a41f406d07075441c1100780940c21503540e076018160144844a1414446071301d051181c1c0c44104000d44034441c80c015020655641c0703000740203100e000c5603a01902d11111080381c29101c900c1c00c14950115220f01d206030054500c090341810b5520114400401d80e078400b50702424181182d40300c1d03072101c200400c60100c520400c1c408804caa92545e00030544200c0707405050301a5801c100900d070a40750017407000d41c1407082c04414004101c2c00e100c103d03122940e26084259082e1544400100c11200760103408040b03100e0140038901c40c0c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 699945143 1250 699943893 699943919
    0x1031b02070e0105010801050d110103020d09141e06011a120703050a050a0213060503061f050a1416020f0f031b21030f030a140408041701090809010309060b040501 72
    0x40c0b1012418512680c0c4d4600443e6100d00902401b60441c5542c1c001c200091a078480c004920001418054203011100f4074403400c0f116184001c0d520b80301d00c1090400711178414850300c11050f50103009007580d0711002424a43ea280188a01d003000c2200e25a4401800c02c00c00c246c4410312801c00e441042400d00c2a001005001c0554a0000707840c940008100d1515051088641c0c08003903c505e0000d803450240191966000244025000707400445816200d0a9003844590165120340b0340c2501c4010801c0010680080159402d01002c0104080d0a4110050720310b15220b6504035045044a06008013043c01c01d540c80001c540c051058024206c06000914a1180c804074285c415a8504a6440700740300741c880312454160b2107800800230303035070394402040c011a4040100d40c1c02041400b01c4510791118100c084800355076800002c00e003844402060741da14005421881c00a01100d074603510343d1003141c0f2583d903c003414141d8030071f262010840d0980045d200c03190004c001304241d61351006000544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 699946393 1250 699945143 699945149
    0x51206061912140c030a0321061805041a01060c02130e06090c040f0b060703050912030c0115060c0c2705040602041505031b0904061211040501050a08150601031b0207 73
    0x5401349000da00b03441d09000646005943d003580e5461000303111503051902c07036400b403496810f90340d80320309000c59207440d002c600c0c10340f203840c00000103030303034070303050030103040204100c04254003442d0b14900410030558014131129410350120345041003078480c9003581c0c0050030700329041d4049000b0300f001c03c03200036400b10308800b110303109070340c2482501002c0c503400046030380c805400d507840002440040b010a200750040c040e00d8a0142000240c1e444400502d8035540002104040c3c580d120752603030502c540c22500c1c120040400782010005030b01550b0319905100158050131004d4410864412861105040ca03170070b0310704000170100154102400c1420117580103004c0d0429505010078403624081c03298048910ce51454070001a15004101101c00f260b44480d80b001e9025894003408502541e6049015075081c2c843c1095076195010801408184c0d44145c0c052481001c4040041204d500c01044056041c20300380d98690443e61060010b80040000d59042100c990340f00d10640040b580004000b000d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 699947643 1250 699946393 699946433
    0x6050f09070b0a080a2d1515120911120a060c050a0c030e27040b060306010510082509061403100611010b130b0a051206061912 56
    0x1003644030400d00c102c5201c1c9034064000120301c000040c060034959406091000da107101100c00c85400c40c00b003102d03800400c102d88242d5542e216080002c00039030410b031800900203940300c0ba04509030b283c030140c43e45501c0503068100b503458002d8102007000c4240181003c2070000c225541c2c55030034109031139071030302c024208039103461400c251007804500840c11344845600641c2c0c0d00080402d140d404442d000381c60451641c10a42e420394001138003586280403000c117000d08183d2a014075080c14103802c91000a4001c2d8001d402c010010310007900c40002503040100c80e81010304880d21400d0340e1441d01103002d14922114808035a400c00d80990000d08038040310655610500003c606080c4204584019a080c54a69111100c20070000340902621003404040c040001505004940440c1d52102c5c0f41100b5080300d43c0c0e880b0383e01c20350f140500d10b080c00b404c01946d100420000c06040c045d81c80c0f4028007060b1140c1c00101d37145002e0402034521070050581c0c00261502e100c49481c040741045408200429 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 699948893 1250 699947643 699947653
    0x906030b040b03070302150705071203021009050303010b160b090303040c21020d051e24060f0d0c0902070b04061109030601150504050a03050a03020706050708121306050f09 76
    0x49185071a0184190b203800040c090404645150f0800240c03001540340381000100038401c0340081034003800600010545000c0300c0d000503c840c0b030020f003004803850400da000791400c0f02c0240446c500000366410745016100f100c0c0c0d1000c62b907a080301040300041006007002c0703007102000740d408004030280d4000c0d0322440030441c03810344490510760880c0080342a2105030090250300740140c81c0410b10015601c2c011421b4840380746c12019001c0c00315a407245452240da01149a20a0000007141c580d5031703200401d14a072000f0b0800340002034007000c0001e40e00d4400c030000300c03c1d02c0a11640034407031380042c22003d10465507800b01d0314003402910400c80c0c055618030315203801269807001c00c50441d0188480100500111703802c14000403280c40c8a92451420801e06100c04200384d2145902c404c00b03140184000e00e038170101898000e00d0129160231900801070107000403130010320410242c41c2075445803041035000d0fa4610a441c03595000c001005070200c8d045c4030501c040c240c91202800d004040c0744054032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 699950143 1250 699948893 699948911
    0x20408060928050a0803071e0f08070504060207140103140a15060f0804060e190b040507050301021932070b062b0206073e0a1206090210090603 63
    0x50300440e40150054002e07006503400900185d1301d00000e6520403824100520141100089010000e02c1100c8130300201e00c98105c20840a6004801d0a134401c08900d0034900e0241084802034441b4071030310551080307803000500c0154070b030f0003600300c0c000e200c4100100340c980b46001d119030b10140c1203c0440c00f40c0c183c5500008101d0501c0381d92150030411058441144e41c0d04e441d99181c0007001c8407050404217008559032071110122940007460b5080c0110140261030500d81003035424145241c0c0028441e03841000342601552031150305051540c02402c00000340e07048207015402440c10210030003030910000e2000089401c50380003400e0118050918155a60781c6e00041c40104d1030480000521085809103540070102c0348054610b1451010f01020b00708142c5681d10b0514000300303240c540c0d0351000d4900c60144000c0054140c91500780007026400441903e0002c602e90b001140510300005c0c045244c0c010511005070002101c1d268054040e000c0202e926400a081401e5801041c2c002070901e03503e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 699951393 1250 699950143 699950203
    0x1609050102060103020f1c170720010c030c050c04020304080a030e060601120c140d02190c02061b0a120e0a1706060906010210020c010b0f01180b0d0204080609 70
    0x2c03605803640600311703c400c1c140100402c100d0903072445842008000100c840c00000e21843c80300d00d040e01b1442c100c0d646551452134403100c448080400481c080e0810710b124003450382d00426650aa940504006520b1805828620b0904c244099136a030424000818001046007400041c0309880040d5020807140707940b646415254801650540c1c000381d0302c0c0b0b040b00041c885907403003006c0d17100480c10074034200f5060460300c12140d08071040f000b000303a501148054840c01e00d43c2804655030300700e00d4016900140c1c0c1d40010000d006142c078040100d501040d8099a2040421080c400300d90001010a040095201c000f00020a50840f180c02076080103c0024460107110300109009000c1000d4115551102d0078010f081c40300030703d000c0c114400c15610009180782440140032020b5600000300ea001554018441039601c141c8517141041040c290088034811200b82d040143c0e04c0c5c0902a46d691040e50714004003038005c580150025014250521101c0240042c0f2a0403800300c040007415402644048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 699952643 1250 699951393 699951403
    0xf20041a0a0b090607021302071e05100c03060b0c1b040e1c09120f0501110f0d09030e0301020417010509070503062e08010b0117070c02060915031609050102 69
    0x31554201c4200310040c020150320001a10803d80041d00c401d0074806180c0005103d60320000300316034940d40c0000d1440a0000d135416117401c5510101c4101c041c48602c0c2c0e20b49503100038102001c41a40d580e00c9022200f684290090b40040180303203510303900c2c0e8180d0746001d5114401c040131000c0c1d200c4142e0720520581082d01420300d41504c024013615800243c030304400301184c40300030040100506d1400115a070010a00300034032550040541260001280ca0170508407010a1010110203c00f13001103481e10301b058048600a515040000c9565100e92409403500c0d940c10a00562550000c03a02050380a4407070341d400345600964000f440b00d911800540394030344d0214000c540c1c01d50080000501809203000c248007240c140c1c1800e202d03150046213141c0300a040d17150480c00807a51900780d514507a47e030096a003400300d11003050701c8025040038407000d801251140d000030f0080034085007812481c2d8a500d01a10303600f1414000596a1410110013540b10400802c0c8002158048030301041d59440024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 699953893 1250 699952643 699952691
    0x91503010e160905150a030c060305010605070b0a0209041e0c090e0915070912150b12100902120a0b10091103010504180c08060604060b190c0f2004 65
    0x500202803c00307078810090840248a40d081e0708004251803915110a0b000300d00840c040c0008003007440c249074004003501d04c1a0300c201c003002000c1c0111800704014292054004841c80300060350380c1280c0001c18007500c61190403030003c507483c0d80b010303400000c1c0e904428840d80c02503441d110403607200c000e10754180900703450701807980d8400032180341c0c0b109211041c1a0440d100d8240801500d580342200381307045901080865840304801040030b104082c6000c1c030820071804584c24805241071118440d40c99440035a400e49290721100321505540b100b00074004400e140000780d490f5580c070350409040c06c0304144c030145000040814001021403040c03040d41c00c84601c8258940c03131640790504110240c0300c5074007403038004c1070b48080074000168154000350091200001130102860140100011156660f11501b21140c040202640d408491400703512842240d0400400c44222410080010b40c100300c0c00030012280e0399003400844e0500040d484503458100c40c01d101030600c584054800b46c2c43c0301c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 699955143 1250 699953893 699953923
    0x30f0604061a01140d180f060f0b0904050d050a1416020f0607110d08040b0c0705040509010603050c1917010204080c0a080c0f010201110d021902010e030f030a0605091503010e 77
    0x8024040030100d00d80000c281009260100010ba5000b612070714060412418115082c07991102e401c09d8001890103940d8179110110f03104041890503131034040e210005240000208440040d01d00b4102e4000c00101045050b1041e6180d00c880401e40030171590720402d00c083c1d1040c481c00c0040885894190202c501c0c10b42d00c015040d034114031340014412544041c5500710b514240c28000030401c07140c450042d00c540d4400e10010325406190200b031004484010b04000c040c0d905200d4240003060000801e44801c44090f102e44000e8903007011030412050040e04070030007409070904194a03070201500640262100c54050fa281d079003000013005210a0781388180300d41b98110703921907107803440c26590b007028010060002041e2090240341040c030661041004402c0c150f40400d10442c48040d4155000c0c002e02e042c0000c01414521000c065540d000c5d41102d03003003150300080002d445c130405400c101d0041c01c001d400800c803403d1804001310840e1400304098003a61030528520310304000010300c03c4210b8044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 699956393 1250 699955143 699955147
    0x212011e0b0a0e1215090f12130518040b070507211710030b0109060b09060708040e0705030f0a0b1c020402130602060609090304051c02030f0604061a0114 68
    0x1c45010851070300301d1180c500c18070040d4070780403002da194041801c2d6502c0ca0840a40360000d07030302e0309060031054060301e141784039842030702e0031822050b00058078480126003065694907070b15a40800101c049854016542100028101031076801c44151014021449010201c0c003c0e500d01c0003c544a003d1800050f00110520034188802c1902d90b084008030b56251808004554143d50891108030060394a00384d00c0f11006410001e000c0520442409081500410b10074a03292049003c168098031103028030504000440d801000140c0040354024824000031409500d00301401400940007207420f07282c8085c0781400103044580f1880350300d040302c0008026030441c0c11500c201c001d006141003012600103608208240c01181c3d003102c102c1c010102640106170602d00101400f0501d074001d00750540b5644148802d00c042d5070380e0404101449a0700014246184582c00003134035016060700180480c2c0203080500050000c26040b40c06a160f081c80f01069521800d0011900300741d04000701d801c00e20b01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 699957643 1250 699956393 699956399
    0x80405030a120207141011090d0b07020703050a0b061e1503060409051905010c0207060c0b0a021c06060e120703060b041104060f021005070503130318090212011e 71
    0x169070721078203050710240014200841645c1d4002032681d40034641110303a2015618100c640054083c3c1d10514092200f10350400440704041805980100c0008003550120000100340d14420030800b80250b422600316441d02c0741d10309001c001500196130180c05400505e48011059815900548038014042c0c4045070140d050762a1075a90b0300007610043e4081e8440b800900403402c10069240250a07282d4010158a40d500d011421590780e140d040342990064502003220b036812840304401140c01c4400c5800070703503500c01110700a10a0f039010020440c04001160051195607018005580042c1c4400015443c00002c001107070400311900e083c10780c4806000d000280c5076030012070305201c026001203508019880c080415400ca5041700000829043d6180704069041101054101c0c2c01c4004104905003000014124032000f0204400b545003d1020740c20144502001005004825608103a0648503404000654059520003100d6180e01b000440d02d0070130801e06100281070400042100c2e0700d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 699958893 1250 699957643 699957647
    0x80406030501210311010e07032f060412020103020d0c020d020f0f1e120a05070b0c030f06011d27180a02010f0e0301141f05102f0102030405060106080405030a 70
    0xc40d510003000c4035500c03a0821f140070007041040e600518881c2e01e140465800c96a440c081c440075141c1d0380b00d40c034131b4074000b01c41d29a1910400c0303405895074400c0f460a92402800140c01901c15403c920000618105a60903682d0340801c02e81c4a020180c3d095981007205449129a164481540e00c0d0194100c141c464510400c0b20321086c400004030800d50b840341c2240e00d90f0b140305802280c4450f0120784002048000c00c018043c02684c414a50a80305040d401d20075910313002030304000d0400c0d06000c01f80340811108200760540d0886104002e000d040c16606404944035444429103030009072512080114203d80c006000458101e90203038001e245661040d0011544020b0560900e42884880744418405407400c0c02803042140032010310304c220b41400280320b2100101000000003113266000309101c603603a00300c610b402503403081c6410a614800840c114400d0340c11590240d6041c00d45007042c001d012419005144a0b5008009440081c0e0342c1f40c0040c0d5000d042120b0042a6410420a04141c54 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 699960143 1250 699958893 699958907
    0x40e01090c0621060306200705060a111314010f0c2a0f0905162102030c0c0106030b0906070804110603220c1e0e010317090306040804060305012103 65
    0x141c410703150014000003030074404440d141c0d001500e4640c0caa0f6103000d00d842c80800781903481602642601c1c83d00b140c0b610b82c1614ac1c1030207002c0f0b075480d9803903001080c503585407042583c10348040c104510604eaa030711a4810080c0c8251040b607404078120030419071000b401109101c4004d50060083d801c5c080d20b40e01900303101500d074600d2070381d1421110070100b50380d800a48140003a016081000a503800c020110000640640c0548020080260a16102001042e004034001805684050303229210020121040e0190762030801c071961030000004103200e00c020600e402036084e0000e5900689036420110750419003120054100b0401c04c40c0d03c01a410004002d6500040d008480c56508a04411000c2d061081d803400b551044022641405000459072a01c0204184400404029032030310313811441d5444148030203860600c01c28141d00c100c00768001200d0307221744002c0913504503241501e000701a980180c000c40780000e02c1c2c0000404e0758440c103500350011320416039102c03c00703080950307044506c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 699961393 1250 699960143 699960167
    0x9020c1f0e030304030306140a080d0c170711041a0102071526090f06090a031103070b0c030f0903070807060c2f250b07051515040e01090c06 62
    0x459903002006007450042c009075000e0307442540c01040192900b43d40c0924054a03d000c2d612509951004002e030b0000040c00344100650340c18100d1a0200d1410300220608000b10b00500030840020b107402004409a807407903014104035000c004842c6505221030501c05904101e42c090b0344000301c180700404c0244142400b4414a00d45100c800900000c0b09840c0740305440100d107056051014402c9060052051104f9211658000e00032450141e21160340e03814800c40103418405002d41c080034008050048455036074004c00300c04001d040c2044001a1544211b8803090368502d1580842c2c0100000b2040751407054001e031101e810000303030707885210040c155200c4d03241c28850400c12680310a42c1100c0c14100b243c10442203103580011030045682400f8940d1540c98100300b0a010401d50819041204000d440c040041d0549072100c82c41c00314580041400500e00d102051401c2207104120f0309007520070910183c070203021030b4019424641c280e8640620061580c1e001104c14000988512089240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 699962643 1250 699961393 699961453
    0x9090f030c0c051908010515030615041b0e0a0b07050a02060f0c010c02100b0a05030726030711130b010c080a2703060b0607080406050d230a0609020c 66
    0x415520380010b030750030003604c01c004031001090b0700c20011014288505a88442181d2420004400010000c1e8550000508281d850b90b00f04003c1c8915440742d42c01042101d5480320101120394010700060411a02803002034803540c94031030301085140c003540039035032030030350140c014100324866a0800425400c200d000c031001035024040d051011509004241121820750050b000d4000040400b9054030314034100f2038000c020450342000152030019140044441b00d2580703004e03041d02540d8494034942c0201103080640310108501e800d000907107140320b0700b0032801c503072031304031111400c24400c20340d09810a4240403508442d4090046203425005095080c0c0c0e925201c04100c0c2c541e16a6010b40341000100d844215450405004210003880782406811040b200e60f1b040030340b15611203010384180d01480c800c220780880c0405060300960402032100e0503100100141d00303101c40d004048400103ca40f01c144a04298001543e03210314400c641645040782d02401918085a074101039441e07206910340d503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 699963893 1250 699962643 699962663
    0xf140c010e0d1d4020030a0203040609020a08030c150c03061005090d0c0e060402030112151404050a0b10050303070605270610051813140706050409050109090f030c 72
    0x803007041480c2d601c40380f000c000840074032402d00c20504082103132150b400c040c0045c8624080320410314160702c241c96110706460306c0580c2e00d688614114001d40340780440290003d956420104a018020014000b5000f4010071100a0410340151402600b4180c1e14610450b0040000c98918104400015010030341c07410b00600c0e00d131f075180210b11444021001a07603000002c1d5420300108278000381c15500958215015403c55050051401c09482c16480003024401c3ca0400c9980018158219a0705002041005c5045213000d040480c2c0b03074403401908070b50000120300051000c0e120950340e041941c1002d80114107128180d5a400c0060801810b003c060030701c5d80d9004d14510301d011a03846002c8180001034012400c00300c1c1c0c0305042c2829a040184030308944000840b40c82e410740714807940b00c00c103021400014489800c000c43d40840d28a0008132a004408020807025003200050040310140c1104000580c3c0e11170811048030700000c7c000f414880300c0d03900c0802080c400c030049540340c1d00a50a540c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 699965143 1250 699963893 699963949
    0x111190e1c03030e0f03130e010308040e09010b030d0807080f041509050c09010308070b010605090108160c0b1501090b1306231c0501090504020a060f140c010e0d1d 72
    0x40c0ca4100a03001d0001d143c1e2000600c0011280304407c0316008042c441d079030b40102d505507a2400700d01c0c0600e004245800001c00000b440c00c450075081503203108009000c0c1c0d05401040d4600619014080310040045403815010645102c403101d4500d01c504c2c3c1000c841001801c00600d290301800d2540e4081d60240b1038018840d2903907442c0c40c1464000c3d882480041e6860019203400c9464110580c8070070103000040c058042e442e60000c5845170301041902c0d9841120400e031400396a10162244041e1116003540200b02d41514101c20b842c030189800d1300e036802e8896650300c0d0700a503803250f03040041501d0400482044401d000b1a24412800400301550854004045a044454018280f0840003101000841c4045001b510446000d440c5411050007249000c1d00840c0e103000c0503102d26020000c8004059407214820b5107902c000c0400d0044255503001c1280c400c5019008940b03001101b40104103c01603001d00171900311703040580c0591f049540700042020000c00c522003070f0402940a0f4000e40304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 699966393 1250 699965143 699965171
    0x10608090a240f14090d180308090d050d0809070b2a0a081c110708070210051e0403050106140109090504030e0d050d0e03010b010e04090609050111190e1c0303 70
    0x10201410040380e1044841c548038049600e000146d00401d410310146010b110214007a4019680c1070f02e0f0800f07030307841d0b1340c0b2600030100b0104c810b4100041d04a006614808243c1075000c801d46024044d000c0860f908551203100b08003261255484280e8200d42c8140b0b07201c03c1c5000100c0c600d0b11480341806844114600d03885012207507001d80320341c030880104c910f4113090b0140d1901c501c500c040110340403182020515940e00040c0d01c82c031030001c0d02c0f0303ca500c1000f520a0f1701c5402142c03007029000103800410062181e11881c5a002400304a65075420104003203001059075000344001c5105966400c00e09290a9009005143c00791040d0100441c00c6161a540d8548405449946100b070f001001d8210000c0c0b8020014172681d41154441c0e4100260035102d03a0b48100c512280200072103000800d4802858058014144030000501a50030b10060140001d07644004d446251444850903122002040c0e044500145c0641c00c950300400c400c2c2400e907980c4070309442ea0f80403807290400013042c0d030401c941 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 699967643 1250 699966393 699966401
    0x120606041703070302011802010801090905010f0f02040f1401091a0c0d050d0b0a03051b030a060603030206040b07050313140a200f04232d010608090a240f 68
    0xc01e400035840002c000c001c03d079092143c1c404480c11a040c1c1c07440e08025030300080c50300c00306100340601e40361220b059500b0b01c20294400c00f41244084810000062002184c4c006900f0511440030a003440c203100040d40301d0803809503010683c05a40c0c13079507168103182d030400c9040e41801c0c864040020501401c401c2c110200241c205820b21034031070790b4860030b11503548400da810003900c141c0910703d90b80040000481c000341c142c004464100119100200742c102107443c2502180019044030300307056002046c55008120113000e1030144c0c82034421541c8509040e5028401607684000c1c000410020802040452041040a548440076030315502d4032a164640080350f51021410100c0680406100320700c0d090310000ca0420b01034800344a001d00d0403156881c5864001e0094090b413004400141c0040c1440e072584001015218282c0b40d041c00061004003404402d00030180490b485001041c0c9051340040e041400652115101e01c080441d510301c60000c09456150714080c98403460f80c1400f018440c06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 699968893 1250 699967643 699967679
    0x100803090f150f040b19030903020c060d1104090e0c0603090a110d1b14191a0c060702100617100c0315060e03280b0c07171c020f12060604 61
    0x20351740d4a41c0301c07a03040035003941d1000d41103d040c180b4003010704c00001d8022907140340c0708004a0b00140ca0380c2014000d072006d09000d2402609003d400a0003158545e2160302032091804a6012242c152003901d06022140c03000344c0310382d00a544550070361800901d41d12021030b010340c0041d000c03004030400759403001c030804080008650f540d0000310302800303810744500501d14030010443d000c982c0d64a042e42c1c50072a062640c02400d90030096070320107408101d0000b04030349100d01c0d440300320360700303847e1141000351203c1201502504050a107440000c24240c00710345414084c0031000a00340010040da0300d01d004148400606040c035456605008200001002002c0100615141c154591034000d0400d414200042ca441103401d04c00b2048490f0408001c01c40380d034543d0b1100d94055a61114030440d4158000c402000304283c048008000b1512911b00c081c003100c0e10011302c42c0c0d8202c01040740c2d41d010b0340a00b54440700c0c1c240050120b140c5100c2d055440301d400810281891b842c0c15190030740d4880030700c1d10306 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 699970143 1250 699968893 699968909
    0x90b0712090f090e1618020306040219080114100f030c0306030501061d01170601050904170414030c18150d0206030c250201080711010f0e06100803090f150f04 70
    0x40562100d1044c14054075410360524051309035000d003404d0303040309110301e03500744010b20710303804000104244c030f5a5040719080f034403407164550380c1007000d1307001080c43c0001d000314500c0e02020200711070303a41005440c19040d80c076036803580b090103040b40c0c004800420800d9007a00405440f80d0002000c42e0081c40f0b5040980000b100fa01c040020a50007042c1c4000182d220b14842c040c411201d41090001142a906651048540d0f400c0303a140d07418248108901d03d0340304c0c00111800680014648048030041d0300c2e00c031065040d41d42022141c2c080121561409030703c80303000c00d082c100080b207160345c0e4000300e030119000411091640140b40c001c82c41e96002140c1480345550b001a145c0807101e0344205085c0380441005020072510f40e103600003004120041c1030a01803001880700408070507404e411000c10b080c0407840401c0100f103902003c0c1c0d45c40d10252048403800090b444c2c04140343c10003000b201d030180d202074112146000d01c4018496041081a038070030030010300303012078080c8014003002080140544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 699971393 1250 699970143 699970151
    0xa08040501200a090e04051926120f04020d11120304030602090909030a1205040f081c0e0f0715050c0601180c0f080609060f040c02031801090b0712090f09 68
    0x700350103403034003200f50040401305e0302d22010000050030015016040c180c1d400300100c0065110300d4040018001c484030325802d2417400e042d03100c0e1181c0b0700f405130103801c92085150481d81c1710b101491403501800e0710081c4d00721403003800e643c0100320308003a540c010b0040a080c030540410020302c09421038110350401c44490717400044190003450849441500100e410025500d4090301c050702414942c03084150720001a240c0c1c001070b040c0f00c0f9000c0500244d58110002d103642d440181444201c540740300043c042a03d1504a19038071103080098403405000310310f0f0060944508000d42c800540c8178000c0c040d01040340070422280c050206002c6176009100306800403040c0030103040c4080684011300340072000c004481b04542c0d00c80d41d01c52a150f4009006031409a107a480d60310205070141c07040420326402c1400e00f01100b01c0c03658000000c140081810001c1c55040080c100116009031462140d503140203410700c000b40c01b080714090880107811503401e0003da0140d0746c5106203000700f50365000000b81c81c2d071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 699972643 1250 699971393 699971407
    0x10b01050702132a1e02030c03190c06020408010c090b04080a08280f02060901050f010608100305060c040e010b04050a1a070c150f020c10030c02032a1902060a0804050120 75
    0x2603d45c01d00243c44600256041010314800365949014400c40c00080c05442141e87da481402182a4907255800103130a5658075186e804990182005205440010341c1c1d01c440001c0941040b4281c40c01c0e82d1001c40074100801c015242c00d80309401113487c40400c02d11410000c03014120340e4443d02101c800300d48600644d990f4080010b0b042c550300800d42e10072070f4100700401986034900080e490556040e07007041d124544032150582e146040039000103081d0311600d010b004803e20604050000c980e0702082681300c03030381c8443d107003484c1d401a44100c0e40c01140c1d040301402001e040d034460411610003d000141420349a48520880c100964001044410708100a10040780d0150f03181807404490b0004003102c48070b17040451f451104400c0c0900c101a60355000452281c82441110700e01021801101420a40c02c01410380145a141c01c01c500d921406a601100701074105808003001d4006020701d0170310141110907502000010f02c01c4506541c1c90140d224a190700070408000d41980090903901c0d40c00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 699973893 1250 699972643 699972677
    0xc0a0e04050f0c01020705100c0516230a0e072601150f080c030711010f0c1803080403080913020a02060901201c15031202010b01050702132a 62
    0x790b40000000c2d41111540d4100750360006040c10850750180da02007040e665040084030b40b0800100010400d00890b004d105007413401c011884162400250001c00080d0030101d46002e451940070107581081307424404111a1074540d2009500040300d0600c4030f052209454201e0905101c1c000c0040301c0c0d40e00e600144201c1c05034030b044640c501d0507400c008509441b0035401510726800280b0606030034100000040a541c419079448405030315400080c0304000c20301040c18060840101000001000f943c0c1e02441000c0014082e803c40c1d41114200d03103414211f48032914a40e0044080f0f40e00100c101c000e610017003a0901c02081e10364004d5000e80038a0902910203030940f08420024a00b90440988004045041d03400b2140c4c013007440c03850385400d8405984254040c01d8180c50b48803810102c088000288011014201080d0105a000300b12407004d1600560361030007000b1010750000801c0b080d0720b10f000030a40c40a0300d100121035000c00ca0701c086001d42d03403031001c865110380c0004400320010b2095407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 699975143 1250 699973893 699973903
    0x807060306090b0303032404020d05061003110a11010b220b0609130203090f1212090111090111100609090b0c03071713020a03031707020c01050a110c0a0e0405 70
    0x5203610180044503080000940d40d020291070949401d0001c610201f0300d00c003900840e0f540170b41c045d01c250348401600700c03240c2c01024219035207030083d52540f40e030399031300c61080c410300813001d001e8140c1908199600e4821503e958440402005a41d81c0f10155881035841040704180c002400b100ca41c0f441c070101c0070003c00c1e511540c0c2c1460150a0030304c44944241d40c0d982c42c0400c0400c540e100181c882d0741e5515030618002455034018058000d640101d800603102000070400c24407040b40c0e16515488203c411800c0724008a0b5800503150b0a0040500d00c1d8840d0180110a00c0f84200b198075200610b07c00c28211601f07640303ea03080ca1784c0c40300764400700310051074655808004507076810b09502c3c180074050210005e00114040e4a50040c000031204545084a0328a0a40143c100301c2c0040d10b07032070040e2000d048680306083d0310f07034540300151a903480041c19920f0713140c06039034032400d0a260782c105485069510300c01d0101c9019070a180447e54a407400c010700200082401c505043c105402c005043c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 699976393 1250 699975143 699975149
    0x1112030108160503030301350f06130f02060313140105010f090e03030a09020d170318011a1002030c19120206010e0402101209060605030d020d1d04060f0807060306 72
    0x401d6440b20200a16680442501e04590050800030078450440450b404080e0a10421443d158904d14040034480070000b18424000c0a20301111501d481d030501d10b003010199028020802c4c0122040355006040c4035000c1d542001d201e840040700c0d50340d00c0d9a620303c45c2e80075078a1501142e5449004008500802e00100c00a1049440c00c200340c0001060707060300c80c44000d0807001c00c00e0f12800700c11300b151200007078580501d0300207002004145c0c424801007482d03803065416030340c0d222120048200840d01031184402100380442650540070703114083c0000e00d1760100c1e8060035800103002c8070060703101c00c1c0180c40b200c0b103880b40d20301e080ca01c2a1400b084083c9a8000700d030110340c020b20041c002d21b80c044841c5500302d074046078005816400c41c10304480c0004441270032510300d82810184810403040d42c0004054540860940b0460440128201e1381c1d08104481900050314156900625080c9040242040302d400b51002c60f00765240d26140701010620f610101665011840030030076079905215803409 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 699977643 1250 699976393 699976423
    0xf0f05040315091e0803070306050411030601030510081506190e01031104060f03080c060c0915031b0417060108010504020f1003060504050112060e010e0a0f031112030108 75
    0x302411a00c400c01c10300380a92040180940e2541400c0030b00609503074010071500c08903030038010001c091418040c03a40054501d400428101100810185854080e01d080900515000d900f15a100c40044003d010043c04031420380b03440c2c0700040b070503260521100130300859015200c05507007403610a000009215100c071000500000b10180a07074007440d12110704580e0003034185103d101d0401c001900078521070340004d440c03c41d4000b0000401c80b0348405010312040740802e95806966030b06a4080900c914442d45910104c21102d4400c1400080e000d15000300c4502484103600f088075100c039540342d1080c2c10540045041b4070070038000540400c42c20740900b0b000d40080c041b0781880e43c013240f105650039100c00d109045030000d016641d4441c1e80504e004020007007085c4a1969107080c0809859031301039055800c00d00305800b802d003245050190400c500c1140c001422600c0581c0c540c0300c0da186075003408408115070b000f140fa0818000300310009a12566852865595140c2a90a4903252280b11180307c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 699978893 1250 699977643 699977647
    0x10031704080a030f050c0303100302040e1b01032004060c02030d1b060e19080a02010e0304031a04030203120c03010905360321070e1203040302011416030f0f05 70
    0x2080000101d48440ca050f49410600f4003203002c100142c45034001c0d9401c3c0c042c607220101c00c0006503c1c3c1d0161142c1260f000b5681003007008412580e150f258800e403001c1c6850f0007400e81c070188065100b9401503400340d041c200b00107100c2e0114540c00d08203a00035071044001510b03221900007549002d02010411070641d0402042e200806201c00c007240c4070741500901810b9460396807078011401404004034000d40d1613641c002c2910300d032070044181e410030000e01c80158600144010014000411507054a40042c100031110000000c1c0d0004180f004100f10114041800031540006101c4045030050a030124076035100c1d07040140072401c0300c4c001410f074900c4e8542ca6080040c441c0004511160380b110000ca00b61208031075945061940c424144c00341c9884e504401d0b030141d0b03941021080c030301801a071343c0c80c241c0310340c4a0003c10504070003c0d2919030098008000410042d0b020320404c540380b050410b1034609005003000301c0d241c2d5900500090300030585c034414040e10360ba40300d1200300600c081c504100c3c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699980143 1250 699978893 699978899
    0x10e2b03171003060b0f090f071d010e04151a120a0207150902043201050105040510230f0304030f0f050412020a0e190b04090b070c0f0b10031704 64
    0x100840c8010f11000c0e0155a40d0b0000001c1500d5082c00f422460750082e28403a11400c010340082c1c0401011140c0c440050401814601445c00141c011103410030142e440001f000c48030000c010040941001205800d01c01c140000b403c15420a1041c4980600b003042d6a118501c40842c40400180140120355251040254000141c1e0300060f4098030f05006800040d00c1c80c03a880814002c0c42d00c0000b125901c1c000401250780d80081000036945500c0002621010780d0344c0c0c00054030603019a0080315030040303007007040654091090401030034505c0b0f01d011182c1c002a40311900b0040f60702480d19488013600c00020401819003000e41c400c11580a0700d01806120b27600301d030090450181e400b508125036800c11065042d9502c500041000e030224079103540f510708007400002d00c600c0c0c001840b00d131607134201134103c481454244204252290815010725099950714012240e658007154111902c111310480800440d6400307600611506030055001c0440b0708604100e00c5501c00d210480a00700c10410040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 699981393 1250 699980143 699980161
    0x2030301061209020a05031e150f0c07080f04032f0915030109060e01020301080601060804030207180e15060f060304120809100f1409030a0e010e2b0317 67
    0x20000b818100002030007140354400280c0301d41040d0302c1158980f103903040c0340311003e000340101d80442c02e0100031200c2c900b0441c880000b081004a402c213800d40340b51030010f1240c02c1910000c001d41407050a8803450119001d580032955041754006441020b80030000e07103c801003020b4540c01a03c1c0c1c05684620791240200061911807004110b02d0401d0300621404100341c409402880780c540c0e104e14240320b40001138240e14000d41007442000007e204040000031014054401d450049416034081c10141d81030101d00300340c1ca003000d840b0700b611941e181240c0304c80d64070038480e060700040380a01d5907000d410704d07604120380703c00d26071a600e101e48020801c0c40300003505011000070042d403a04058001d50b44519826041c03246241c450040c807030520b800e5000e000d2450344070981c00606141109135030b40340d00301c1141d5603008181030040810580a00547da542c018006504945d01c01050300c41c04c440c070300d07024118410800410034080241180301d0320170950894590086030b00401d41480481c40d0117141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 699982643 1250 699981393 699981407
    0x4050d08180a03112802030c0111060c180904050f060601020d05090f0d0b040606030210030203040201020c01031e020a1d030a0f0f0204020f0301030b07140a0903020f030a05071707060203030106 85
    0x2000e01460081340c4038408070034003242e10700950303504446010a42001c200a4243c11540c812486801010b24103002c5601890001002ca10071b200200225030b101e290032022030b4009e080c003003940038404140304072079601c2c0c00b4028401d910030000b925070354509140c0c0c180381610107000141550460b000f08508a94054280c45812004403442d00ca804138035400308004450a00c170250800c880c4008000034400039420000441e4820740d000166064824400c600703d00060320000e0041c1c0048014203030961003904034900090b501440c8403070203180c200c2840100e9000301d040c407001c1414940407007030300c0700c0404540354070b860140c002e0080c2801c03c2d40e5000c1e100c2c84440c40240000304180c841410754850340c1c181c8848010403002641d40b942c513400c0c01d440c2104200d070070100141c0d0000e10f01c000c1c1d012100584815000b241c80b034440342c41c00c607420440f142450782c1c8071315014402c54a5031004110100002002050841441d140c1200040d00302d9060541641000b000d40d842080104409640480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 699983893 1250 699982643 699982663
    0x6030506010e010503450d0504090902010e030f010b03150601090b0c030903070308121506030a1a090103060c170103150b030a050609104a0604050d0818 67
    0xe001940c9907181e010100036070f05031500c1d0040c034048440b1b00c042010341c103941080d680e552858511401885e000410b5689071384642c4007500050301408204001007540d007211003200d00c1410052080311030755010038542241c03145409c41c0c9a44403400480380782801c0c002d0a08440580d007291840c1c1c0b4080c000603200802501c90000222070000c0d40c4d2184260a00c00d039070010070000c00f41c4200959a007001e46032500405002d0040382040e0001c1190039002c0c0c1481c0603030741c8024020381d0030365550305141f8004100c00340d0410182c45002c80c00e0341c41e565510080c180070f94407815000036888130300e103c0103042c0c0340000c40600d1852098001840801d418038404011180e01000110302c2016030400709040c02c600c034000030018409d5105100c82c14001040c46903840d0654907007008000103100144071003d1041001d008003207002e0010a0059680b40c07a100024005106111203003400e0600b81854900211816140740e0031485022000d1a07201c40140d4004c001c0c03840110807215000d400356102e505402c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 699985143 1250 699983893 699983897
    0x60d0623101a071e0f0c08060403090902071106160c030503180105070312091a070f020d03090b010e130803010b03091501031e031817010b090705040b25060c030606030506010e01 78
    0x180c0d1420800245c00401680154403c6240134569500c42c1d2141e510001501e040300858074005010a0040c0c0c54405e403440642c000c52600c250503845814042c081d42714104402c10300020780c4c1c1420111741000d9600004612420042d943d4083c0c80c82140d0000307004644040c1080010820000425440081c400e20f482480000042c0c0c081c461900401c0003841c0801e00303035112070050820142c55041000a044d021903602034810700102e1890840880303401c2580140740c0003528006015842c0355406a5500c00004401d160030740c1590788401881d608260b121a8035003c000080000700e03803052100117106000111004441e50550740ca02600d0002e0491007800c0d000c506e000ea006042c411034208000e146d840460031036481e22401030919110b904003000240d90709003403c80d01c8a043c15201603100781095a215410141410001c44082c1d001003068500000300302c2d113000c4802510b00f680120148034400000d40d0034482e100c042c090b5181030b4880c0c001d16113080200007a59820028a0041c51024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 699986393 1250 699985143 699985193
    0xa0506060702040c0c060608160b0306030f0115030627030f031119110d202104061d030709021c091101090806060d0623101a07 56
    0x25000c00c415005030304019502c581459089001c56401a84500d000b41c01980140305050312282c0b51661000c4e1004c8029000b501c51104000081d11000a135811040050548816040c03e0715024290b420740c40000d014541402020010000e26120b0b038544010944058200c2402ca41b103031000b0100c104401405120b00c00542c40700651082c1e02605440740c200324032548800c3c031340d8601161180d20340840404643d003030034a140c8041002414030f1030b08400360303200691034504490011100000c0c80c0034003031038030840d41820b0003182003254102c154100020701a403030b2032034948010249400c101546140840b41c1c14090800d4902184000540d040d00c00c01503130750230320000124115811030700e6110100d8078147c140e0080005131448d800502009030380c1c0d060a10f80314080641c4802099035803a51282410104600180d25908900b020003d00d02c040700071642001183c0310000e03070131510f814110824180c10300180d0b0f240310b03500216030314101c00a401d0410a130b4400030a64050512210000c0d40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 699987643 1250 699986393 699986401
    0x9021509032113060804080307111e150105040b01021203130501090c0305010c0815090406110319060609121e020a030809090112080316031b0528080a05 67
    0x308100300c2c15078032401c8881c800400203005051000d03411025031038151180529000503124070441c0164002d0790840c50040c55038407040800e440110400035403c0f9140990006152101601c6115441700b8151001415004100d000343c04075004050300f103c5d10071441c103078070300103243d03030005070840100d01d41c4201550700d44070088500204502c820004000358201495130017080103440058084a2150b0001c0c00711580d514420356842c1411038240c06c031803401c41d02400140c0381003110300e90400c0c060000040c2803044864174000c0e940c402c599418400421174280c0010620a100f0003000307104078989100224203041844804400c501d0001e01410001894400e0044070200a034585903402042400700030f90381d11304000980c02c0b4003805445402407500001d022201e01c00102001d03540b0401d094519075401294858954240095070105592101c000b0a058400b440c032844043e0280c41d11a00c0e201504c1280700d40000020101c04440c80c00420a07241c103030040f10b441c0d0824401c00c07000c04d1a80e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 699988893 1250 699987643 699987649
    0x8070813110f0607050309042304110616031707080717060a120c1410050406111501060e03070b0c030a0f0c0606090504120c0201120e122b09021509 65
    0x3140103100303500c480001112010005c00000600007104241c030280519031000c10b00d00003026418a800d1222030680c000100020020203104035541c07070003820b42d4106100030040302c0e81c50107541c4c0200d02068104801c810502000c5a09560041c02c0e07141041d810314000303000410003c030601500b00f0104040b000709116549890394400a003d14035102060b1400784e050503082076a0074400d001c1d510040f0384180e2041d09003800582c40c04000e548486182c1841c00500702c0e1901144030390030307425010b11400c180000c900c07540e0f800e0003460703140e07106111815030404040c28526150f10014a4100c00c02c840c070b01c1480017205440c1d0310096400c0c0701c10614011345042d100780303107003402c014446842c0520228400c1d49580c8a00c1c007450150a008044089e0240103903008810590040d000c10750003190f40b00881c03041c0d002554441550b4003514100c1d440343c0071b405410707004141e681d2440300c17400e41803507903a60341c240079161006039400d02030100089540120b411540030003400d603041900000c1040c0340361 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 699990143 1250 699988893 699988909
    0x4020f0907091e03080a0237022b030f030b04090c030809060d180311062a0423010e0117010302011d031009210e06090102011107030f0807081311 64
    0x61700105803d644100d144802511484c5042c0e000190390040030380652469820040c4042c1c020502002c101502c249400300034500c0b016240c0c68000c180c2c80c1412100d004d400c102d0300f400c00d61103522004140c0ca1280b001500b82c550440b20580030320310701001c0c0d07000b14118400d104201e1741c0202e1032070383e00d080500c08100c441c40782185d00b964031800c0c4440c00301c0c002e490940e2040410300035582e84020485001803640c9462b001c3c1e070a890803c13560340301c0d503844401d03032803180c0031800b00b001003140f401d03030b542044071241c10100b05081d03c1040000d0038000b895821003e901e810039801d1070500c1c900600c49071800b1070520180400790411071261410704046100401401a0711001000c0b00d00c501250f05200c00a00f0340900704854688224149111100030038600210703040c042d48491500540e44014040181c001d001c0580c115034030780603202c250b443c4000042007114005d0350781c0c008010f01d5a0001e083e04a002d0001e20805c4851003c111f00300755002c602103503044d404402e00c1000e03401c0d0400100d040d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 699991393 1250 699990143 699990149
    0x9050705071b0503060a0501080c0108090c04060902041706010e190906060e100e0601050913060e010b13080307080306010f090305030301082503080f030903120c0304020f0907091e 79
    0x250320b940c0d01202e481004407012030448a04400320344680c3d550603031100a4800a22800f905030380903c100216035806608400d41c1301400d44200c0311904000340004d416645150312600e0010340c0014140016480d00001100c41800040200241d524204400c806414010320085014030301d50360714503402d801c0390850a90786070842c0080c03004903201c0f540159407130002d590a114141503841e0004160640c1202107204680c142c44150a1004c1071081c06100344071103c0442c422603423948042141c01000704428041c1c942481500e032180c03400303418944541c9583d000040c00303900c1800900001200e080860703503c09420310389a400e030300c0401d405440f01001904010010b010100020030301c02030000310203032542c1240304141ca4503000f840f180b40050880c0d0201030f203400000c0002ca80c800c3e126100640e0040303140e00c2201d00d400e07852000c2501c441429600544110000028007003549005413445d05044000c607504007070f60401900c007a19100380d42c81415150f2029040c00c40071420001c40060007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 699992643 1250 699991393 699991403
    0xe060a12050115020114060102120a210207021306050a05010c080d0c0e01030b09090604020625050109060e010b090f09030f03090c0405010f03050d03020310120302010b0324010905070507 82
    0x51940c58105030f21600b4840802500158a014007108401401c444914003c40060b0064840310000d40118851940584800000d22880440001500b58401d01c0d081444164102c010b858018a10421910781035107250705900d5820064107215a0b51506088001c070741742401c080c01030348400d16050007940507420090641c0c2d07103000c1c4403031001030f006002010b80084c2641c0c100a100154803c000e03003000191411000d55108030001001400c210004102d8404a244c4103445080c58201d0120624007000c811580c0342d454041420803c2243c1c000c407003c0b984440005c0c172440e039100001c5981d60000506034004009000040380e240642801220000410b000070281ea900c0d0880403070f5070720421302c600d060091b0f01c1c000c00081d0f002c0606c0421000e980d40f05c03015181d1512024012000780d040a000c1000d039150b100800100c01c01c2800e80c1d90f04c200d1080c2c0001c98003100300303001c040c04d10040c58084083c0f4285074003480004010a0b807030a0650313602c0d11000070142c60795001100d29005072200149 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 699993893 1250 699992643 699992651
    0x11130603080d060515070308060f0a17030c070e060603041b080d03020702030c01030605030a03030207110d031110020c071e030f0f050f030a052d0f090a050604060e060a12 75
    0x320784141900300c1000d1313620946a089010041c0f001800d80c0b84900303100900010002c101250107481c00c1d21070091640ba0042400030290f4484540703442aa42c00201007689620024182c89014010300060b0300030a203c4022588620341a00031031841c0c840104002c02d420ba15101c030350060350050007000e002d814140300700e40b02c00400e290060f00a5024110923132182c8a0714580040543c0700b03002d19800d031413020300503000081d404d0380c099000c2d41240d8000c8a15008441c807002c110380380c605d0b0a50a490283d66220030801c0003035105800c0880584115480f1030040100e00421000010060300b2a03000108110414005070001041d8010642005141c032481d55001003e10007014007045049000c0c40968044540c1c0c070014990324801c9440501c04180c0078042e418412030700b044ca0034044000d00b00240f8410680040b000b8565210041c4c0454081021483c1001c0d03003408140c6002519003030700c10318130300703402c2080280103031a0b0010000d20a0a001071204d4207e0300c1044d03011103a1100c490300340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 699995143 1250 699993893 699993907
    0x12070b0a03020c0708010b060a0c0809040203150913050c1207080a0302031905031b0901030f140703060e2413020406030209010e0105191b02030303010e100609031113060308 76
    0x1c0280d03000c203240d80380c00d04c594507011079040303030610410381074140060045103440e0740a0703800d94003845103000a0700c0340d03c0d081c010310003e1707141d600040d03100c2c403002004002810880d40401c905110080e00300300250400c03451381b10001f4000140c40c0c882c08812030f0501031900707001c40300314034054640d00701200900a0550f01001c0580020103400074150b00b28110044001c3d0703220881b4a804100c5582e0f1101c00c3c5120f140705190804001050041810316002c00d200344440c0d007890903a0390031804e44400c21011001c110400768144140e80140c02803124007a141d0030112004d620040d0b43c556100048403d400305150b41da0340d00208559242900141035440e2507030303180e000e0025004181c140d27010545140d1242030039072242084490010002d903040804410100702100c0c13141c08115071106100342003520f50050303035041001c0c41c000e00b60000b0700405840c20807144040d0b51419400081404031810303040c0002120080040b603400c1003505d40d01c00d42014007003002c0180001e50300141421b40009801c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 699996393 1250 699995143 699995147
    0x403050a0b0a05011a0708070201030e0303040b010314030c0a060218030706050301091104050d0b0a110d02030a0b0d0c0911160b240112150b03010f1802120612070b0a 73
    0x420b02c159003408040005a0f0780b6207104445454181c1c1038503810a0810000000400f030101400a03140107150009142014a9001d0704c0d503803080d00c040d160b24260000400c01c0021481d0181499810b0001541c00c0c1561490502d60314214020003c020070380110f4090601d4584a4903180c058078000c0480d01c66681d55000601240e000b806030100c46c40c10700078030303d44110a07401100c0441e100a08884120303043d58480303503203944c0702920440c1c40d2034644080e900d8203221480a00184010300000503583e0421801000884604a6009000c2c0701414a0b05000c0f414800f508000c980b0003d00106841c81c4500407806188103014008000a90300c2c11500280965a80654890790340320b6000d020b81c10032011181c0300d40f2110700d030290025000103a569410702c050b411400c0384191940c142525180c86660b0340040d90800d822101c2c41c680080805c0081c03801d90307161307030214a1801604501d0000d1407560010050b40040001d23005550803e03400400c086c0400040300204110381299840750048480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 699997643 1250 699996393 699996413
    0x11070515041b150c0c0503010f0b01030e07050607140a0b0f1e0105030d1101020d020a11100207050304030b0c0903071e1707060c020d120804032615060403050a 70
    0x162042c007155202c500465107604422819505801161003007001c8200e000c44058404000c21120704010b2000050117031001d0107246400601042e0100d030141d9040f0004044400711902114113a01c001340030001c64848400f140d54403500880f0034408140b102e00800e00c0d0000b500e03c0280f0a0010000300040c3c40c4459650600070303051004101442c2c00c0354443e0588411082c00b5441c2c0c9500a031000ea400d20740208a640403050a003c00541440c0d401c8043c1c03812600401020f0000c551341c0c40313040c11051414081c01c03005401c146401c42c18140d42d0b4507015a41d00503400014a240055004280100001025030b581540020100e07640c913500c5000026203d904541c1b103030010b051540000c10182d1140149491510020004203161813a00c032046902e00340320b01060341c120302c080d6420710105d0300000d0715240d500f486885840d26400d25107002010400003401c0710304030300c1001450000307111101402e5071b00000c102c10300c401c0c088826800100380c0d11070743d0700c028042d21440945000700803000304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 699998893 1250 699997643 699997651
    0x302030406050a1e0f0905100515090114300a0605011203021c05091201020a08011706310f02133303060c0206061207050a060311070515 60
    0x10310103500d5a5500c3c500b502c0c2d844403070484c107000100b1011480851903001a01c01c0710130040200d40c0c4211910740701e0414070441842e02409407200100b042080c5424810400010b060314451629132512800d03040040900482c9441054400506003040340e41d500e0030098640f44444c00e907501c64030006a5640c411000c40100ca201c2c0c2000000150440e1440048000d540c01d900608405c00303c0910401c1d951036900c03070b100300384041405035042c2c0c2d4651010f03010280c0c40940c001070b92030f00100009005c1d448142d03c041d0309060a0000245d018001040c0190044620602c844c1c036907240c9084440416000c80071810710b04407001c110014440000015690a4006c0e5144241c0e155450b2502081ea124040c010514501800f503001c030b84807140d005113400300d80100c5c401001903100d5840c0e5007612450b000200060b400a130611160307251082d01c1c2044041008014250390b0710300b10114104900d039104583c241941c3d4509509440310304e01c1100c2210394000140c44811b1040b07008c8150800e4156 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 700000000 1107 699998893 699998903
    0x3090c2d130f181403030606040905090c120c0411041a0a031407110f060411060a0201060302060c060f010902040617040f0615170312040224070303020304 68
    0xd00c5000c01c0c00d50f03009005031107260705084c8410790913003e800c1c050483d0400c0052219030365400c0b0456086400c07244010a0315554640d12900b84010b80e0b9800750059225903c060031004042100d034400f2400310382c200104055017440900f580594042c0300c00700e0a040ba0400000f411040141002902d03d1801080000304400d18400e00c1d4419604800450f519507000713442c29809000c482c444c854180c004291902d050384407810b1028111101c5030060341e0005801c07400d18801c1d0000c0020b143c0240010303640f907044c040c50f02e646110481d425911a4121800421007a00c5402103c04807002951460800402c0c00440441508090411a103055100c214100020328901595103c01c4400d49001c0c882494003110310040c0c034a81545a045810400c24020f884400b00d0303074550801c3c0c058898202c2d1000c4442d54580a042b50b840400e014200810304030100340c0c0c1a0001e5100301d2041c = true := by decide +kernel

theorem cover : BRFrame.Cov 699820143 700000000 := by
  have h0 := BRFrame.cov_init 699820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 699820143 ≤ n) (h2 : n < 700000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
