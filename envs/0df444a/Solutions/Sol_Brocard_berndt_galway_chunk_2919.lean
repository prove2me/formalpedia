-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2919
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:08:21.829097+00:00
-- url     : https://prove2.me/submissions/27545910-7276-490f-acda-55a310a11798

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 524820143 ≤ n < 525000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 524821393 1250 524820143 524820161
    0x105011e09260f06090d110709060e1501080c1b0c1f1707090501080406020c030a0f1d031e070302042406030c0c080a0c0b10080d1110 59
    0x501040700150301c10008100700c40d061152282042101640824245440203000c0e031620180c204a08022880303c000c0b540f110805440d003072103200082c007402c1190030304139160485030300e5500d49480030400c000e00707440082c0306000e02402d645138a482440150b0b000641200c01c0f030a424810000c5c80041414282d90801d206c00d643e0807607940055203400a0440c0c0c140710600704025040c1c51410000680c4800982034043e003203200c01c11075060409004100021901038203040c8840e10b0085000c02107d80d0495190008640590361030f1a0f8140d4010440094500306000048488034070310451000740700b400180c11401030003041c60881d042d0003a010703000618444442400741001c0000540c03607500a0f4174508a4415104102c0d203070b407000d80e218104054101104041c1782000b15040c16402c0031600a00310f40003070300a074954440601c211205c0b44d8003000240721078084411b10120f03910405c0044181c80e544400c1d00e0302c50720080d1003111061100c030841c108591003150b02ca51503004503403221281c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 524822643 1250 524821393 524821397
    0x32160c02060d0908090d0b222102250608070e0109140607170903240f1305010e060610031505120703050706180e15090c04080f1c0201050105011e 64
    0xc100190002601c0c40e95035400a0300c0200f85c4408110144001c04007500c18401981280c0c0031107120354860021300d2100c270313072522401c490070940907607414001c000c04040007140328401964280d41400d0046c03071020070720440000c83d00c0140031074850742c05040c16041980c4182d58507008140303000340391a00078820b00d03401034014808209141c00300d941d510340030144800002010340e855000303005051806614801c2c84c03e40c604400c10700c05903809880c140540000190043c20316946400009803200004039000800c1d9610703207050741e2034652020030810320501048a40f5400b2040002040e803d58100340100c10016658550501080c5055030031034240414030b400310b038078842c0c0f83d60700d59284c80361940022011600c0020380103003070442c445804014105d1030304e1110300303030a00003404070b945040c0a440d2441800c1d004001200050040c0a0f100289406811105030182c20080251611070302186101c99102d580544141203005000e494120781d0180d59000e200010a11980d907440b40300300c80902 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 524823893 1250 524822643 524822647
    0x80604060f020417060f180d0509060d06030b0907050a0b0427111201210609030e0a18050a05070f14070c0306140901050403050d32160c02060d0908 65
    0x1c1800749084d030b0400c07288410f40200358500785005110a5a800101007841c010200b04020340944c1021850440440c0142003094488221800280050092451240070b1a1401c2d80000c00d2090701404203005a010314240c8038007640704d84c00d1115902481c02000e5038514200800c00803c00054a182990500c8000910b406da2100000f80e040e075651110100300320303001181c0801090382d5107080038010310440c150f50200c01c00c10210582d01d03121200380903000035503400d400700c1130500514050b05041801443c03906010340b94485207148045013995080414076000000f223580d4100d10070303d0300500c00d03916042d907aa00b444074101c2d1140c0c03414003900071000040c0300041c0001c42a480c0d90000d148146804141101d241040340d0315034200501d400300582c1028107000120360002c00b141d4070684101c90100e6002c412020a5450030b4041d6050b100720001104400b04840c1101072460040e0110f203c21100100e498000711624540c42d40082e42c400030800600c034200c1d41039840010f0305c0d446151058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 524825143 1250 524823893 524823899
    0x8160c0810020301051c15050712090b07020c0405060d0f030207031e110303190509062115030f19240614010311031503070b031906050a080604060f0204 67
    0x1800c2440c600e503070199103a0040014482d40c50140703980030044000303000e0700100c00d206854810740328a01c0441030090540e1480420320040c8219807000c00001c0c0c0001c00e00c03800c0c0e402e28144804103411540e0720014090f4040001d12032400c5c1c002c190040100070490301c07100c415030312984804640141d049065200300840000003c5101c41d50120380003801c2c1c600e222000075410701810080c0c82091045c4039402c104002541c10134800d45102961915260094982c03140d5000f1603900d100c2c40741e54409802c3d0303a030480d11460749660710007446503100c80c050b000301c07030380300f0341415900d6101c0e00005d6840c0e08103400181d050a01103080140050003400c01d0b415108217154150b115444000a28048070340b82c2c00140300341d060800b250050b800f020301e400c01012041031100035103804090030000c40b01c3c03920641030111781e504001038006840f0010b0394a5580c10071b014404103440440d101100311900b45071700010545850005c5800711740b4020702030000d65959030382d1080145150342c00d8401c096802d200c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 524826393 1250 524825143 524825159
    0x402180f0319030801051822062d0b0a080304090e010219051306020c060702040e0a0804061e0806060a05071a071815050909041e060207150908160c 65
    0x4a080035000c0d4484c00100d5060001b4410b00e05c1702403a802440c00610300500c02035410342003100c0c40c148080f40d0032840c00455882e1810141c01c4091400c0302c00c051804145001c10420300316140b000022090030421803d554040c086865560310500076140c006020401981c6030700e030000f00300c45181c500010b19100d50380181d50b9100880040c0380000900100e601400a0301800c60303d0003403c0a0300007405290018000079080c2e208200c2c000b4003950b06d461a80480300b03020001d580c255548404103c0d00c0320303140c02c802400600c00d16407030210204a4045007900a005030b03482d90099601a000034130340151200306480c0e07a03000020481d0a140041d02d640d0040310b41090307aa02590302075640e6035010600b030449070320501c01c0e40c01951040d8000740f146568145c1260485042c1e650550311542c0c265210306003a034030040e2042c20300c0c2e01c40d501641110f04000c0154011712610344070340602000b00d20030840c92421640000c80007400500200070254407035054580d0842000d1240c040300b103040e80ca074568 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 524827643 1250 524826393 524826433
    0x624060f040909141516200304090b01090b0a08040311160306020a121b0804141603060c0c030909020309031b0609071505040b0322050604110402180f03 67
    0x20640c0c005000280d80800d81c0c4043c44403034520002c40034010207900b02142d0111146d040d041d45070043c420701e0504014440b422100700c000010301c0e0010360707803a01e0303a83c64442e016100b8442c80a0001d0030118000c90741011400039554011401e50350007034180c2e03883e84c050b504c072a41c50f000400507200350256640c040b09622a020b020b103210302409600c40303520882c0034220b204c0203c0c03e51087d031705080d040c0010140003040090001c0c1c0601d821040c079202c90501510241c5a00020022409802c00d00841c2e048040c1900040724030800040200d05102032045405466002005001459000c03007001941c8003a0080c0d9084403604c825646048940303011122101c99082a003c8950000da0420495080c184070142c020a210b400100c610241c0701001842886503000d6a016210044007144d49450400303d403046140c4149551410b83c00c1e64100719a8908089404a0b04101500c44000040c1094000e42c0d004005920312007984020f510304000c0040c1904011540503c031b0100740c04a00480c0c152 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 524828893 1250 524827643 524827661
    0x604050a0b0c04060c060504020d050a141203060603180f01090f0c0b250303090b0903071b0609030201030207020301090812070201060608150d03020f01020a110624060f0409 76
    0x1000346180e2516151500301d403400180503588269003440100496038000101243d00c543c0503030b000820b551103100259500300c80c20006003192042c201c0c501c04110102501c00e045907260001c0362145010034484001501c41250300c0c2e9040441803001c6003100160012a92a50458805941c1400c01d007406960858030020000c0d40d514018080e188180410701d680c00f406040c80300c4041e450140c0c5400b162078a00d840744520907200361a2580b42003030601c0303039002c05001e907031100d14092241407800445036260000d40c0c065407843c8032140034000000da0810300100326074698a60128407440c40e00150020740100714141d0701035484d1180e0500080c1c43e03400414900e00c030610142802c0c01c203500002e0848140c2d8014005010b040000d02072254803032105010054412103c400000240303203012401e006d4181c07142c507400e600119015942903000145000c42d0710a80c401c40b802541c0e2210420890000d4240e62155181c102024503001e00b4032030028500c0c582030800c903500d81035840344160100c8500207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 524830143 1250 524828893 524828903
    0x906040e0d1d0402070804260d0806040507090302010806190515070c060c020f060c0f010e010605102c0109031208060906061801081302090906181209090601110604 72
    0x1016480460341003240d0b06114081514110309085840e40d440165208500402d1901c40c00c0b1000f4800168600d07080803030b0107120000780d940c42058140040c0c13861400b44c440520550030100000c16580c031a413494400c03247c05a458000945609062002240c640422040740c0c6910f2400841d454880b0030a1620b01905924896a2500305013001d00140540d43c100344100f1050440b030304d000d0b82d140300205034540d804540b0306680d260b10300490341c40d002d403420000c80c00754244030503201400c0040d8404001c484084c2c5040b211914640c90444c1c01c25003504030a03440c08401001c0c3c06c404c14049040000140040c100141b0481c1c681d00c5a00703d841d01c1c20301c0c090000784000d01300680f07420195949a0881004d07101d035130401c0e010203003480744030115080080c100160000000c03480740e02203c003284085c1e005000200181480c840040c0c0310501115100c0c00000e1019140c1411040040c921003010f03c51140b2070b0800c12080100490594080c190a041214040045142e400240b1003a40180d101e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 524831393 1250 524830143 524830157
    0x50405040905100509060c07060c030b031b030f0f101a13051608060609120111180306010512031b1e010509011a0a0603021e040f03030206090604110906040e0d 70
    0xa61070301070700c0c0c00516500c4036420060900c000861f02c5030a070750030036600417808202124620801c500a2001078246941407041d5040e4004040400d500060116800d400380d81d40780b280449030b91340c1c50708a00001c500c10351000140c0540c0c1e50490740410a464070a09040041c0e024181c0003c49020081c2e0f4018055583e5006124640c4a100c440026444030b504244815281400c00074440307010b81d030400b50142d400c060880b41202c80070750100c0f04070a01141200e80310b5a660b0a00c1d02141c0029212902074400d881c0040703224075207420402c8951800e0b070000d5140c5015403013040f10042c2013200c01c030154860171000204019103051400c00c08001c89000041038500090341c2800d440d550388500d00703d0b51800607105200e4840c42054400e5078140e007005030b03460091040c3e490381c00c20f80c50b241c2842000049804100c42100c0d079005000c50303000364220790054030b541541c10b85031031007501c0c000d01403040824042100d04003031098541c4a00b005000184a03e0f6800042d401c1c040b1440080c4000360301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 524832643 1250 524831393 524831413
    0x7020301110307020d0206010506031602280302120f071b150507050d0c050d030c0903140c091b03040f080702030f07050112090507330c06110901020a030e01050405040905 75
    0x10412030310a44400d06d01c000c0449525060100c1c0c007a2101808000d030146241075030101c40c0e07000708004a0b0b1013012030050240c00a801404d8030380c000c1191401c03001070051800302c01420150340c0584001c2000118410300e002060b0f5900c190710241c0000032071070320044520009184440305c0410105062907125103580d00303000e2a0460805240708090000d100100003044042500095038207003504140c01c00280588030042c0542d200710b4190b200402030303100341140305403409000c40c1c0e0420001082d01c4484032506d40780d04082080038032440c10424081e0501c005030209144140001a4601814081c1d103000f1194001c01c1c10200d000400031681d41c800d82c000c20071075034450b10b0ba0340d24841c4c4800c00c00c00211141e503095105c4072a032141c1c0c6916503141c00400c4080740c6000c44034004120004100044004003903000e030080b1040c2a040c0c40651501d01504040c0b0a40e10856001050582c041e00200109035015a0144101044941085014031011459480700d100301315005005e80028000449 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 524833893 1250 524832643 524832647
    0xe0a05010b03280917070308010803041a031914010501020c01020f06040f05030f07141903211509140a092103150909061103130b04020607020301110307 67
    0x2069100300d404140c20010080648012005000324010460040051010f070340c00c03d001a00e507403080680401c1c01c0780100c900c480c440d0001807000714441d44445655a07030312080c15481c0c0c0100d01c01e8800704500304c000c608007400302400642c1c1c0468140e1000703452000f14000d0b08100d6100802160600898200501640d80c04011521040b0b00910040000940102c411a101c11700600010704004a0800c16410000c0502c20740380644641e000d801d80b109401d040c000c030303a18014024001d1501803c0e20b4170b54866807003902d090f1000d4042d00c8140c0240f0010280d4204103000580c000301c030583c0c0e07134401603c03000604942002041040f10224034011516140000e10174040d04013031125281c200342c900001c2d01ea0581e410750400c0d0031072011244052513002d070042c1501c004c030703401004616400890080800d138000c00a460041c0b034100301c444048079115844d484195550301100b40720090301000900368400c01948940b019000c076040402541c0803d0039190305002d034880d04132020041041580d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 524835143 1250 524833893 524833901
    0x3140406021e16031b0e090304151b08030a0608010e03120105040209181f23030115170c0a090b01110c0d1403190504050a0f180e160e0a 60
    0x24100b002404034034400624030340400c0050303c8001c00c0b210040a06011440c0025551070082c1800718000d120740c60302442298507507000e40514800c0340b00505100c0c05940c0b007169105000480e0144103e400d011a0311900700c41e03080107004012060721141e000c14501e8080c0070f513050540c424001180c07200e01c000d4600000d13000580096000d02d2040c001d01c0860390324441d00da081001251000b00094840f143c46a00401c919909010080010100022070307c50340682e2942d60700b02a501c2080d1082c08070201402c1e81c0e004581d28500342400c0c20284a0840d0034401004820b88640c1119650119100450790303840300c980c0411410356a4000f60f05880d41c208680e04480c10945014201505a80c8001598482ca00101400e10000c00d000310000880400031254000030740d142c0c204104102103002041d960190081c9400b94a102000080e9610440e007284141c850340034100c51403d0101b5a90b100400004030545214801c4c1c808110b01c28008901ca0b8000e404000340c1d0514a140c540c5a5800b41c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 524836393 1250 524835143 524835193
    0x1401231b03160e03070905151e0a03031b0f0b0a0b0102070305060c09060408101e2a030204031a04110109080d08060f030111091305010501020a030c0314040602 70
    0x10100810402c2035211140010705080030850805005845500300400d2030310480d074020040c1e0700e10300801d100020000c0c000390748a030407003211151210440981e079000c094103c51491a08040456401e0002a0007240e401c0b1695800321303820f500d071548a2300ca01104409001060744e00740d110409012014203940144050140280002e1101c1c501d5a81c03107075665000101074001003440800c4a000c107036034070400c40b8002c200180468100d8950070042c1002404110148981814401d00413001400303140500461180d1083c880350305580903148c0c10002c0c05030710010004041d420080440007480d1034140d018a080075070300102c640c1c941490082860700e1140821410f10055041c03c21071b1403000071b010044000c039031410301c4482c0c032402d0125904420441c00282c1c0755081a07810f13207030110004003515107040c04403444202aa51076850408807442805400e005070800c0002c500442d01450310710041a100745000e03142603080114a0000380c0003500501c0050704284500c1c3c480a61071401400e00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 524837643 1250 524836393 524836441
    0x40306050c040503060a0209061b0105060a09050c0a051c14160207030c0501111e010f15030503040b031504091103010c030c020c13060e010608160c0f140123 69
    0x2502e0f050500003540c0d58002001d8802440d00000c440d03034103460385402d403010301181c8131140551441e10005280a01401c0b02e149000d0a45c9034800680e0030800c1c062107003d004c04080c1a4940b00150a0898069011050702d8180c2c83c1c0e001c4401c40034a81520442c40800300000d030000c41410175140c010b0301448107110890455218a10a00101d048140108201c2ea400d0030702e81c1002c0071035200310313003404041a00d940c10b040145a600038030000c19040200e081c14a01010042c40c13102405100d200e00301408050100d601c188403c0c0301e0346031031100440d0052000911168043c1c032242c005410f84055280454013041605211100da09090168100c9001542028001c0504950000f96941d00c1110070303a2186e810380c0c11200780d0809607444a80a0075076510069030640e100c0c1c0001d00841000e80710001c401801ca61f00240c95485140c00300300e844c2e400020032449070a66260441c03040101a08403506545e504070f80e1020401c00118901c6070104423844288925040c2e01c04ca50040e402110108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 524838893 1250 524837643 524837647
    0x340605071b080d2c030c0c06120114012a030807020c10050f0d0e01020711010f0c03030506060c060a0911010c05031603021609060515041409040302010e0a08040306050c 74
    0x40b01030382507842c100d92030310f400500794262041a8003200d107541c813400d060312103130b41614548182c0800181400c51800d02240e80c03e541400900000744140c4248a0502411400501501c041164166403c14052400001800d22107045404140c00d0480240103080d10301810030405800c00f0b50b0366130040103400580b03100002c0d4400300c1c0d29261807244000402c00b0014281200044003070a50ba20011400c2040000a070010700c064000e40c400c0c1c800787c4c2c8405002d002c621a96110b20521044a030456603540c0d1142c40a540a030080e01c0c001c1c11580c0d0100c4240012522500204240c038400c40d20050003042580f051304044d00701c0700d01200719504000a0903100300200e400001118242c141c68150030188900d6070400302d0a000b0700d0050020890008040004c8a1110740c00000985100310340d100b20240034848200c005200c4c41c07041e601a911045011111441c00c804e100d5480341c0240004118504a184414140100c100e0115107c410114050041c00380740c2c0b20b100d42c04804144c0e814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 524840143 1250 524838893 524838947
    0x1c020f0d0305010518091006030318050621060406150203030703111801080406060e0414160f030609030905091305070e0f130614040f03031802010534060507 69
    0x480d592440f145c030101460f0f8034400304819060030400401c0300041403100300251074503031600074288044c002401180710745070040030610386460021201c40c11190f040504850b401604610302c02c1d5801800c441d07205035a0b02001458243d107170054030314564958060340c2c1e81e14059901800305c60000c071304009484018800d98040503200101c0030711880c402d0a1030341940e620352402601500740c4e13410014150954400303000c10807111906440780c400c20082030300c4000e43c050f110b20040480d9441103207030302d03508040c0030004074040c0d5008098190080c5080115aa260004183c02c51426921607001030000398038842800000e12911014090404840e101c5007049070030b050308c044c80030f003003d0f1041565280c0300007080180d50000702d04211030304040302646480c0c20704070b002816022095000c01e0902c1c446803202507201a200403d5a416120300342400c081e50130b103005486039450208521407501032440e5140c1000914140d141e8401c007000302d81890411002851030040040e001d44850b030070302c086 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 524841393 1250 524840143 524840149
    0xe09010e0a0c0905011b1b14010807080f06060706230121080a03020c0307060608010b01030c08100b0a0504050a09022503050904020708040909060c1806020a06020901021c020f0d03050105 82
    0x9013184080c10003140e000030b80d0500305844e802c45480c4c10003000702d400c56800240b00d6200f048c0c81507242d20980b0746103041d80e6a482e00346c450800480e10486440400c0e000240039240c05406071816a002e50350000b1455100425219101030001c090864001c181e401041440b40081c01c144050754038a0040c4030400f0182d48810365400340030001424540c000c01d001d03500780c40070010364034415041842401403550b6608583c3c001c002950850b80040d04014007110b5060051000500458894400303100325460301d084103110340c010f08176070b40c2004000c20002a090f42e602e0410720240c0b409600c01666291002600e4461b021500d1101d40d40070000c0b004040803c0e0008180c6117800e0b01a107025a942640b4a40f5081071302c503c0e0041824946408219070500101d5408030071019003a469011001d003000c09024402c10341c40c4900401688000c0c400c2d40021029005010054010700486800c1c4106040c0b04040700d030000706c2c403130050788030303c0000b172050a04100214940440d410204181d5043c1004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 524842643 1250 524841393 524841407
    0x708220501140913230f0a0c080402040c02070f0e0f0709050102030703031a101d03030405210c101e08070c060207033005010e0906010509070e09010e0a0c090501 71
    0x1d45110740c184569180c013106658100d501c19040050030380d0340310700c0501e000041c000b0086c1e0707a681103001c040000a01d610304600c600584484d00742c49401055a03290b080202130a0b82c80110000c40c0200500006d00191050585001c1c2c0034460100c20b440c41d002c3c01c600750141c4000c00c0c100c03c200b074542040003566004011a06400d4041c42e01003210000c038440d40c0c0c1251104850150050000d1001c01606a446920000042640e2100c01510120300c01010b5590055014440d408200c0a82c601185420503424218104c1800d0a0315011703800303013000a0000803840314801c045200070b4500359040b03000d0503c26000300b1003400c1681c01c90810704801850540c107128000c0180d5400a520340900d80200132003011358402403400c08010300d80c140004079814140d40368600790f5051030004500c40012580840c4200b148200420003a032030301080240c540809011a020301280c2d0300644101c0c1c654640040c0031304143c1c40345c0312a83c2070000060048914000a020403c00200d00602c0705130780c4000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 524843893 1250 524842643 524842657
    0x10e04150b0a0c17220e01140a0b0a0503060306010e010303020601060809031c0b040f020f070f1406040b1005010833130e07120b010b0f070822050114 66
    0x1025949800250b40103441e00c002001c000303000e004c110f15022225100e4507004144220140140185482086840505113806809083c4800000d8401404207103200311501c299108001c0c111000c4940e10801c0d4001d07640b0904035140010300c00003c002040c2000c1260314010100400f600e04590303d142c4000351110418000d505c1005000b01c0842e90984040050302c2900461100c1c00d0900510030307070a0703002061000390460050f41005003961503800703d442030703501850b58409120f2a108940c4e81d00180c034075038840d046680700d041d00304180030382c0010851103201d03a1040da42d00c40329003000c5584403850800c41d4859030402c1241000c004004511894004d00d280480202040704907a04816515540211000c1900001510f80c9881580d0658203c0e1100c0001c4506540c021030700c414400200c4400b000024000000002c010041d03a4641801030200300d481c5c02e1001c0c20401d40d50395502c01c40e03109114520300c2c0040240c0c11413000d442010480700a000c2401c0c207a94042c0180400e401c540602030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 524845143 1250 524843893 524843909
    0xa0e06010809030c0a110604150c0c0602010b0a05060a020f071202041a032d250b030c0a080402010203070614100803031306150e0c18190e060d060218010e0415 70
    0x3d485180c41d407544003d5030f011f40102d9540d0108042550000ae1100e101c0c0502030b6120400c1500001e0300c2c80c01072190040713042c405010000241e04080c24040c45610007650f5000310301c00c0c0310901012403400e00c0008060081094048020f80301d6004000580350390a2200440c0402c440009281d0741e030004107442052441405180c202c074110301d802c40c6000340c440f441300e59400b0b8052920002907281d44c007a200c04589100d5400d9040c2c55102411050000302c501d072040c83d0040043c0c003903650161010541c032520502c1120318004d404d40d0b17420300791820012592415100002441100340f0f03031070600c101500800c0d00440c00c5141c41c0070382d106400954040904055611810000b600b079503482202c000d00304000309003030705090403a0881c400d0340c418605e42035000508503070501c1514140304c0c8220780c182410440e90080d410000a0410311b4000b90072103a100031400d500c000081c04d07500240a404040b0005012000500b1000ad032444103500e40345442545044e0016000d41c0e800102c0304150b032850 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 524846393 1250 524845143 524845163
    0xf050d050a0501050c0703021606021905030903010213090c031119020a0503030c130f0305150c07021503061008060a0303030e0a081602130c12050a0207020a0e06010809030c0a 77
    0x6410128202440341d500a03200d94200303000c000d50703484c83c00c00a00c4003921a9080701e45646015040c0b00701c5031658014240103801c850400500d14122600006041c1e0003101568075240402c00024220f83c0121750100d02018804400c04c07003500070303104252a4101505080c8200701c85e1900d1100c0c2c80c860340c00b81600d0351900500042d15203100300020007005601c901100d90341d05080306041c1450300424074600640d100304101055640c0303c022a001221b03030180041042c0c07a0075444c100320043d4010050540c0307401c14000c103009030395030403130000d000e0001c4090700740d403801c042084c060350905180034034050041d11001e00480e0303100c0c1e02180003144d4242c540050468600d80a081c01c0c5101d156002e003599102103a24802c8050078000020344074400c441404c00713843c07011107100a0f51965095036003c1418810200500031290b003155500c81c80c01c1100500c1c24040d03900090502620ba040401c0d012104003c0000c596080380c50715401c0098000210305002c5015502741da5a0000c4000030078990003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 524847643 1250 524846393 524846419
    0xf060d06030f06061e0b070803180a030903050c0301060503030414030304120503090406140904020415080a0501020408191722080319030b01091a04030506010e070207050a0f05 77
    0x198040c902555200036203520400b81400d0080c0030702800d0240d50b0305020403555400d4031658560145007240c001d600140d04019483c0c46100494000502e5407100854400380c120b0340080502c0b101c10103622035180d01904a046081142c90702290f2130074280a81e16003c410b1010313a40000594045520310044001c100400c00c010908600440c0e1021070483c10024849080080c080054a81800d05440400c40307a40d035000c555021180e010b0317040d130700840000c000c1009410a0703040804155030640c1100c2d1015500c883c40e80c074022100700c080e100d6942c0400d081c0091030061000080025007100040b84229407900c50707884030748010b00c000440380400620a150f0704403489a07010746110442841c0a1180d07120310064807640445080d4100303940e00041650811300a200f8145955010380d220103000e410425603180130f001c0840881c0389520f0a0100100084003081491b02800c3c00d0300e030f04065030601100180c81c041d50398100d584104808641800641141f401400869001310340842e450a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 524848893 1250 524847643 524847667
    0x140106170c040b0703110f0c0612040c0b0307090303020f06280b0402040b071b141e120f0601090c0e04050c0c010614011403090303060603060a17060609150f06 70
    0x102ea94001002c000000c030390402499004640303000c0e050415810358101034498001c0e40d48545d00b00c1d030502c0e888082803080d06440d0103458a0f00c0e40c02446920602c131001e4443e20b0f580f8150700200e50200c00600c050405000701581808240c4084046000a149900706041e0a902290505030301800c0f40f00c00182070004aa91500a00749801000c0c10855840d07844540c484040e42c80210162040e46c00041d4032400b2640000b06034003201d48074030901000e0b942640c00c021001c505c0350102103c000a039a002c9085640380c0d04607400f00c044460084c06d10100e41c1030703040c1c00d00344160300030b008091074146072080d03117a040f003c0381c20040801c960014050b55117540441c5103015482c0368815940ca011804900d0f1b056a45046130032003001d0325183c0d041c0c0c0c84034082d65000d2000b00d40000e03403508284003060480c101100a141c0202000304048032040d04c440401c0b1400100b20302c5200c582e440f100500c1703801d051084030f054000e00d100180000c3c04401c0c0000c141a0040b5501040c0510000510810008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 524850143 1250 524848893 524848897
    0xb0a0b100e1c1e0309060e1e130209090f010501030b010507050604170403080d0c08010b090a030809040608060f01090c0f022e0f0b0319170306031606030f140106170c 73
    0xd0f0007034040d00001c0c021304000b0140d1140d8001e04000c10f12000f200ba03220320b03000803440600045010011081e01214003031051b14401c2c400d205091a07024040211981d41e075000031f42c464056902241d140358941b2000400341c80e203103d64181032103010071540001c100041007490707010350800b4801c1040c3d004c6041d1060b69100390342c4080c081c41c60100d040c08043d009600000c00c940001d0340d9090b01645c85a1528095208402c07289600000c0312070200b00146042000e0300100500030400120184e441d28800e0608004a0704400495403500040c080400140308401d0060014075000710b8170111500c002e595a44496250544c941c98200111501d162021f4040701c984000ca0040c071240703403601e05040280c41d110300014401e00614508261124800000c07003482ca4010040007102107101c182d00030030b5032015200a402d03002d104110907001c1c0e0b0341c4001c0c5000f0070080d40c002828200c0810003c04440704d940090018002d0306004001c0c5907400841c40c0e00034030010300c035100c40e52070341ea0001240e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 524851393 1250 524850143 524850173
    0xc0706020f1b0309010201051621061a030109061406030402011b061a180708010501080a06080619150f1418010e0603070e01060906110a0b0a0b100e1c 66
    0x100c0102940512003030200143c40c1c4e010003a0002d001d29103810f0f000030031160642c5000c40000d00103104600c10b80d013112041311b0440c003068400090b0140c0b905c0f8483c612031114818040e11a030000b004108965a503c2108010b001e22085d007010403484a001999501c4041c102904020b1f401c0d520000f14250398040c200a2980500100140c21030740044800281c8500041441010b0076203c0c80e8041e50001c400e03130300c82c90301c5030b07182003040c1e007040010764000002409101c02240d1b6014041a0154100500c2d03000c0c0344c1400c03007000c603103000260b8602500c001000c1c21807400b04810301000411071018948050352480c07805e111103207010001190b0000d0741c00b41c626000d10020300001900b043c01064090003248280c06480416469140303501d2211803c0c4660303c0064400307182042414802c050441168502c00700303503584140030380c03a550029182076900842d4281d49100c4070f412487c18810352500c0083c01c1c1003d00114000c900082d400003c00c041d504021414840c1d04000c000d0804031000c0c2ca = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 524852643 1250 524851393 524851417
    0x901030f050109150602030c0d030c1b0b010f051e100e04090b0a110403110f060409021b071202030a02040506030c031f0b09010302090a09110d06090c0e0c0706020f 72
    0x7280d0703580c100c0032001d41152010b4440e030052034000810020700c040100d409040d0800014520600b8087c421802083c01075000400c0040e105800c0c0ca60f0300c3c9500c02d465035240120560481c0b0b504040c40d8450003001580101e10444500d03041084100c1044a0203045040c11100300c050199440e4081d075071030341c036103201d0380d401440c1018100403c0441150f0301d0007a0940601040301c2c45c4010000c3d515442036020107440b00803200c0301544a442d14442c0d050000001500132410950384040b4070050760820b88820581c20002048190030303000800506009003100f41c10340b0030b88902078010944490285102038020ba40b2940082c0440d1400c0004000400010303040303c44a14034181e41c52a9403080132289409981410503461051815040c4c036414cd03600148100501d403034220340c66004100f03114040725401075821030080e01d545c46030003507020b003405084003242005251520892100c01a00075031010034000b0140b00e40681d0103410380c3c402c5607004100503034030039605d84110701c1401003122900e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 524853893 1250 524852643 524852651
    0x80603150604150b0d111608180d030e0f01020303101e0308040e0109060504060302010f271e09050708060618060406210902030c0103150b0d06031a0405030406050901030f 75
    0x30344c42c02440001d01c0c046840c81c00800c542c2c10001c0003407a09205030050706049684402003800400e805800815100d0202c1d1414604003001d030f0b001c2041114010403d401042140070201c04505007003104000c640c400344040c41c40c0d40780101884c18886514022094241181249004c104000981b420003840c2c210441645440d5120304101e40031809000306044142418000103503410a80280000c1d2541612803480103d0890411140400c01044c03030041c0c1001c0c0c42012512000c0c1c100c007117025000941c6034000c0c4510b46503c0414001c0c03c0ea2085102d00e1420b0104004c01c5d90002d50b27550883e80c00c6070040c0c4c1e2007008031903070382511072114102503100b00b00141c0000c03200e03000310210b0000c04a000d04051610680c55100b4101c6034481070207505900000f4440c5480d62290744100c40d01c0012480c50184c8a8450b004181c4076004501d030080016511801030040c850208008884406404102040c42c500ba9860540303e02452095505200003c02c036002da903070203600440b95200c46044108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 524855143 1250 524853893 524853899
    0x21072105220503011b1e091202060d05010308190903110d050a08030a02030403030b010e01021b030f061e160509090c0904020a0306050f0402160f0f0b07030c030c08060315060415 78
    0x2440c11207003400800800c6e201c800e650080034042191402d042d1141c0c441c987e0302840e040d50058180300c3c0c14002c1b40d014504000f41c4194144511036180694083e0300d00030703143c07005225a40c08000040d05000d041c440e041c4410800550a01540e8020320740030b450044200c2c0c15440d0080c030300115050001c0c140700011040040d44855540a18403e902a0750144032894040005484516a03442c000340141c0191800040092282c00d04040c0362a01804413203204410b100300a051030700030b0b6500051fa040c44204000c1b5816810221074020840c51003c0c0c440e00d4440c03002030b00034407800042c6401000900d0000700c41340340e40b005407054410301500555542a8501009004112901400b440307803400b0000e20030a0704142c802c0ea042240103120b103203804041a2a140000b035964101103030100c0d0b0102c01080040c030300640319401041942c40120710405514000750135110034220900030400001c04200490b230340069043c6113900c0d5811180291340790b13940071401400300406007403901058a4400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 524856393 1250 524855143 524855171
    0x11010c02031504120c0f0623280e0c010c020310020c10060f0f1202031903121a01050904090204020c03041d09030316080901141f120c0e07022107210522050301 70
    0x5960050b0001d03108902c4060b49e0350036400302d4841e80403c1e00b007648591004001940141c005540c0d941c002400c49030704103200325414085c0d82c40104904843d8015840041c2d480f40300340034030806031018064502e0042d003060b4803003c03913250302e10880019038007130701c00f4006544040c040c4170f50304900f017076007441c0801141c100a03114640c6a43c401541d546002250b02c0c1c040c03120324070700c030300c801c4141d40f0b080c90036090a0811000d4100304005982c40785d800c000e502c0001008200810041c1502c501e40c07814050f40034040d1091050040488429400410410030a04440396880d000d5540a040044554696000450041c0382c8035406404043c481402c0c025008601c121002c3d090030030844452803030b0f8441c2480d600c4100000301c001c01031507060701b05020008456000c941d101d4401d01c12242030341040c40880442031580d00710100050000221641400b264001c50a0f0f400ca050412410703228040d50002d0462144280c1c5a441410000c11030283c04044441140103240050003170003421044850 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 524857643 1250 524856393 524856421
    0xa030801061805090705090301110313150501060e060d1d06060a0906080309060c19081309020703140307020f03180108061002070311010c02031504120c0f0623 70
    0xa010202d5002c0b5020322400030302c544502c003070740c1c0080c00f40c0d0740c2621280740642d11a080100900e50654803290702c5105880c640020f0351085d441e404075a03c600d12641050000e10f2460603e0201c81410800103002c441d410900121501d0002d841850361515081010030080c54803c0c10305148800e05001e000100d00c001403060701800302107828800490f503440d607680c22154248034100b603c1d042408650482d02d020301c0a00009400076050715046030034504161496081c40d00c1c2100d0102001c248440c1030295076240d00058a035400c0c0c03c41c070300746503034602404100310b01c21007806105000001441c5d141c03003401762450800010007100e0721100c0c0603011041031840005440d0024140c01d00065240c81c0145035001c180e102070300a8140ca03420b40d11000d400c402103402003410f003c1c01034050001078a040000c8103124245a40d984600c2c2040c3c6402242d29482d03480c1d060400c0003950044c00450854a02c0039213480d4041c0c800503400c22804c074600012952260150240320703058040240103000d0300c43c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 524858893 1250 524857643 524857649
    0x1d030604030314160e06070c080a05030c0715120e0304091e050a060308031f051807090b0c030d02030613090f0c05091905190509161211010f0507050a030801 69
    0x301d0401503a04c42094100780c0b110b00700720b8400500c1d1010700c18032504210005000181c0100450240151200019072400c192040101d03482d03400007650841c01e040c10b2108001800c104101d100e8100c01506004240c101003c0040c4a060b60b5000309640c141400c0003100c000302000e94040c000f0f81c10141d1502c0380ea0105d01e440000301400c1c0800100040c1b000c2c1724100940c1d510241c06411741d00e480b035807142c00f0043c041190014001c07450f00802c19030b407021612103120910b81c0e0103030300516100fa40289180500d5120092030702c0c0c18840302003a04404019200d000740c1040c001a181e0740d6080002d81a001ca140350f0f280d80e9403070040c42400b84071313004100d411914004c4041d180070a50340e10038440070a03401c881140501200000204d40800c02d6002580c0041480e2062402d08209617000c100701d4070181c2d110b0029a01454034240d41c3d4002104035802406a400c88a00e00243c9407200c80302010041c810340d0401c0188031090790a5070054040c4e6416a0b004070464001e45c0302c44c0360103456a4406c1c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 524860143 1250 524858893 524858921
    0x1101050105150c2e11040e01180608010513051b0901051002030412030e030f03090a03060c0e090a0e0c031f020a090305030403061509020316050f1c0911031506011d0306040303 77
    0x40705e910600907540308490440c0c074402944100c980ca0054040310135101342680514264580c1030000d500b40c2c007401000e01030904907440c1e00c0c00407920300e48030745444c1c0c604030814001c0c2e481040696007039840901540c1120b2041d5040e00035024005012411440341c1e401159200071841d511a050590001c0f102d80040c406a0071111401075556501e956401820300c034650209000740203000148540c0c02610b81d0f01240c0c107121850313090030000a00c491808aa0300030707610b036841c030102d0101d071420041d0010600341036025140b03240c2c4581c101c01c6050b907100c20741500a900000d0100d81244522421401550841c050340e03206c54880c503180025107100c00441101c5409e01a000c10202d1091003104d001351a000700b0400311555181065070150003184160b2041c1c40f0a02101b0f40c0302c00c405052040400400400107012100c41c0f801c5642c03001c204180c18000e07405100e0403031400c00c080a880e134016009007002c00c0340040302c1100c038036481c3c240e003449034240c0141824041016010340100540078040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 524861393 1250 524860143 524860151
    0x61a07021813060902010507060c170106110c0f010e0d0317010b031302100302090d05012a05030718090e060f011a160c03050a0f031101050105150c2e 66
    0x100425100c0c0369000c0d03488540d14141d0600e41c2c00041d409070301c804981c600c1814111f041c11410744a080031180d82c545c0c9400482d04081340e070911251b101008a000d0406800d00e0026182c0c0c0c256515503514034241403e000d0f07185210320b403803c1e078007951a06040c41e400030014800e1400a1034014103080502c9a1815001d02c0c02e0004200303d01c4c2c0c60141da1040d150851082040541a000c21446002a40403074040c16400c100f003010b2925480d54002035980124004030309010012071842c1011180181007140a81c107116452140703510000300c035005601442d00940860700c40c1d101441d841070030790000d0802031814070111341504010440d203202e131303207080c4046595a03a15095400880c1c10082015400d8800f0800d4051030421400a0145d090203001d0940d12107850741d441310301c2d1a040306816146c00c031030128810300b05603203d54000c400c2c44490000b07008035450701022074040e41c1080d8840d0b800c1c110218401c58800130810460b680003c0380c01c6610010300350314204c40c149880041c0315003031071810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 524862643 1250 524861393 524861419
    0xa0506011211010c230c0109080606090c0a03020c010213030b0702150c0c0c120705130207081c1415190305150c13080304060e030a0b07080604061a0702 67
    0xa8203003142440c2c0084111031112880001161090748048003141d1310f43c085d0b04c040d00e550019802020900310350800030b00500c1800c000240200401c1c0c1d02075a10b07680f003441000030b01e4441602c21034000d4201c109c85611000841000c4e0b0181c050b075541d00040d0343c404501c20b0000749a9042043c102c900a1403080c1e000c2d1503e140072621a241d00354618604180c480121700c41c1d60035035005000740318210050b00d8140c545d50001414800d20041080d80541c03114009114501d085110300a1311428420210324104035a030766480c0a009001c0001c0e0381c401c02074100040c0b00c0d4160400c0300300d50881080c4601c2c51802d00c1c4517501140c00003000743d020f8030034441b55000c0b554141c0e00c3c60b000c0c1c0303400c48010410070403030180c01e4409507001800307251902400d014210700030301d07081c0c11103000d042d00c4005181c8940c20710100030400b015483c8154801d901c00c450450100e181e10030300c90f81240d154580882e03144e54910225000d0085580700010203c00005c500004560400240140900c01c40e01d41c01d101103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 524863893 1250 524862643 524862659
    0x60f07080d110706050c2703010902060f04080c091501030b0f130e061b19021e0106050405060a050105072310050103060b0103020702010813031707030902010215010602070b09060d05090a050601 85
    0x903441c8a00c0d44100603003061f4410800d0003036140d00c0d80c2070080001c6400c41c4240d000c0f0b40c80342c014250341c8400c5100802c0901050a060000e000303003450607960506289050164840c100c042c03e41c41134103055690088890030f40f9071030070280d00300c0d03409050305000788000c0c41d04c0001400d00e00040e015901482020030024901c0c0c03034420600c1c0c8240c8482030700340300842a01c3c0088d0042510500203510500f280c070400101d0703220030b01000c4a1013034000201240380c8812322040e601d008104c5446802809024400c681c0c202081d140c07002c1e040003000403002000d00d500c0c000010561000e1000d84141102030106001a41005044c0c9201e2041401410454001907007031340901c51009020901d05000070721711044440c2841c002d203000b884c0207100c084102a20703c07161107040c0c038820002516601d00c80b080d544c040104010290090106003419803404c00300946500d00d0380244800c00d403001600074810f075038000075120040c992a00402039424216a1945c0d1034201940807a003074050306000280c818 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 524865143 1250 524863893 524863897
    0x4150203090a09110f090f030f060a050114010f031d0304081f0905060721020301030b07180b0d15211406070203030105010f031812021506060f07080d110706050c 71
    0x400144200d5091010301203176002c4a40240c15655000000002045083e54080180c2811080301e00040d001c0342c10030280410560303005030803106848129988000c40c69a0042400347d1650f00b0f440c1c0010018541c04542500c0e40f40c03d00e22504031b100108001c500305102103004024a0b508015007070b0221482840a4141c1700070746009000b82e00041e00240d800e9001799403003404100c03491400c42014010308a400100c0c0c00c01c0e04240c40860780c01041040d040c0e0059510a40c60141003000750500d49880803403ca103200766451640642d441c0c2c40340c4103e80000f00c1c0c50302d0113801410695110003481c440c81c0081c03a00d07405810b0328840b5405010480c44031000ca0524010046a4003862960b803c080042d202d5289810850040550b22040c201005541c03c041c0302c4590310074140e003030304605030190080c60914014106055018071074180811990744000f210852210840b100d502c0c0d003101d08200d01c0500520607400c1d4a40d05012100820608020007003c4c402d00c00d5200704041d40b03503444000b242e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 524866393 1250 524865143 524865161
    0xa081309181205120109090b06180402120a0605041202120a0e0405061c0501090303050603030a2f062508042604150302031602190308090304150203090a09 68
    0x607104610800d03000c074106045110103542a400c020345051120700000082d000241d0200c894996182c00203800c01180d82402030704604210784140308403a0f01443c920398100041c4c4000d10622802034903c43c030b030380148107010445030051020080c61816052080100704003500c2c11005000e001c1184012030007c0050310102e080300d81c3d40c410541c19150600c0010000500082c0d840002012241c1138024202988a03550784510004664082c0510b0003406603103014117132500c281c0040c0489203040c1e9200c0b0034140d40154040030a00c520040066001c0100c51400c03036480c0c07a014080400403404002c40c03008555039404000704600600c0c0000c00c43d0b5510f015100141488040416542c0d5600c10803440c1c01c1d254142020f16144c95a00c9081c00c01421450f0005400720390040108558000001140030140166002818001e41501c0b110403180e861003100406000e00000440c080000030003d48020380704960340000000c02c0c0610181d6a6009450300e0383c0301b40500103000c82e000c04140110849 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 524867643 1250 524866393 524866421
    0x5011b11121516020d110304030206070f0627200901060c1104090b060f010e06030901090b01141f05071b05031006051509060c03030f060a08030a051207110a081309 72
    0x681c1d144004803006c184003c004513540c031003400040050303910a8000c000d0548101c1d2f1a40340e642d60752400a05980030054149035400c0c104d03d400102001034804540c0d203940c0840042c421034103200420320b00c0c150340703115030b500702c4035040002c030713003603070410302d64039025009981000c804108002017105503031003602c00800001d24440410002e0130510100d1002c4241414180e10301c12281001c50200d40048918818503074503a00084240701d41c102440e0f01500780c034040c45468104e80400320304101003013000c25181107000c0440c540d400e40310f141075801055012103c1c807038070b1a205011020003074041c0503052181c015600080804401c620410044600203455020b00d503040c46045611900003008094024400700400c4240b50401d00045201c1c03d00c1c0a001401810a2410702603070b8083c0703402c4100329030b10400c00e4030030440d008416260743e40402c00c850310340c40d66800c2d402c407404400c02030b500500740b0600c043c0a04219203100a02079410320389044071041030b50355030020140d0b035020b01c181007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 524868893 1250 524867643 524867653
    0x17060c0c0309010f020f0d1e02010e060c0a050d020d0504170705060c0c01090b0c0c070e0907030209040f0f03120b0a05090103020d06020c06010b0903070504020405011b1112151602 79
    0x101d03501900c66403403d13030a540181d450000414100c04d050040108810340007611001030480c5107260180051a0101c062000b00180c481507001680d4502015012100e40ca00100d64100c000e40300300c040320840860102c040d505d800b14546103030b02801d0240c400300e40c0c0c60940000e03d01d40030400000d41d0f00da070f40c00030000c0002e9210522070061035031080850045039501c5402c03810201d040740c460507004803801840d086c0e403800e5030b010307031428101607410034084684064140508845c0c0000d1807002e480e0111255485a00c9614050680003003508c1d00a090301d400450308030a240e040311179513500705003140007800000100ca003000044121801800d9000c14681d0050025060581d02021580e101c3c0b140145015552199189403d4003640f1032424001c001520280500302440484020002070b20305508050800c8000303400703000401c40004690240455010520441a055a45d04a4040c2c099101040e240b181c0c241c484d101c54010349100070a0302c0c01700d400600c641d41007001664056010304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 524870143 1250 524868893 524868907
    0x7050a0507060e09060f0103053303060a0504080d050603100501031a0108031c090503120f040c141003150504060f050301270305131503050702010b0a1413090c17060c0c03 75
    0x2600404019000e080e41c172030140c090206030000c03400c0c0c0b01030a0b803400c0122b0b08910428001c1510304080145035510283c240710a03c4000786655042d00c5115241c3d1102082ca5540c03080400d00e8150f411745142c0e0250b041030000018859880400c4403000c103040c2901005070303210500b4907901c0c428044507035658051100c82d01c104a40943c00b41208504c59019285844200e903d219100381081d01e800f2000002030301400100030714403203c4402040a8001524020070950005202d4488a0010414152600c10340081428540c1c2950042c0100038401c114407503d40c0f1034001c014140c0c2c09814025071900104d0801c2103988007a4840c011304400d0104140e00040d5001c6400d40c019000e40d4590018041010444110759a044120704425580c009140c0c50140c1000303094520340302c142400f8010950041c0407600010340741e005911401d076101c50540340644840d000510210b14064044420131501051440a80081c5480c4203040c1040f14566202c035185580cc0d4030510003000135542c001c02802c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 524871393 1250 524870143 524870147
    0x1a0406060f030216050304060824030d1116081b040216290702010203071d100f02030d09080706150b160317090a03022e0e0307050a0507060e09060f01 66
    0x81002401380018203401c030311980d0301c0615540158101c140032840340400c00852100c5041e003200980d6101240c0c040c0c1140c440007007600d0302406905281003181b810103180100c007082000a142c01020180707410b0382e540e20f444058951b20100401d40801218241c0810140342500955070031081c0080a0f20014a280c0d44002181d00071410410880207584054082c5860b141917061040c00076030005a0340c0d290444005100180c41e9002c02e070400c40603007050b001901d0340c060403650901c40381003c0d1002441014107a24bd070003075240a1051505003116a002c01c803500010b881d4123031040405005680030b0100000c90740c280c602407444d00100610400008000f81512014a94060b00746030028566020040c4d44a40b4100c500310250741c081c04210301010360403c003442c0c980c84101c1c5104007408000340c0401450311000320480d052030b11207221060100091088690b4503a0140484440b090b41c1c0c50620307298900d41c45008007186003207039800554103140d040c480c801d42c00103142020040c059001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 524872643 1250 524871393 524871397
    0x11030c040903091701090f0b012c0a1e0603080405031c020303130201030f020d090506010501050c0a02040509070b03011502010e070303090e19061d180c0907170106031a0406060f0302 80
    0x9114096481d520446c000c40d82036681040721900031404412990306201e2074040c014801c00101e444003840614007602d003007140030001c2e0880d9047c400812024155550f200550b000c4040a440d418500761000080048500042040761429004d036040d90b84281c010a8003040e00400c180096001000050034801400031451007051050400052000d110b2484008070b8000c0c202c80444280d0350030450091042c1044100d004040901c1e01ca0714201003030501503140d0281c100002e01031510340c00441c890030404e12104000e006550085501c2e50f03514010200100560340404000d94a0002c2c01c1206d0800401c4a40a072a0140c40e8100d109180805060380c37030030000c04003000c600511090703410884441c05840024940c903105003800102c0718002c0441d443d8007030000c18100c102e02207444d40362400410050744015040f00d10195aa40d560000da0362503880e0601650300c5940100003141c3c1913015840003940c1d40d00340b5003400861061400f8442120050300030b42000c640c115100d222442d01c01c2d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 524873893 1250 524872643 524872679
    0x30010303050319060815100e130f0804060818010507050a1b08070b04120c051218100e0f01020a021c17030c03010e1e16030605031005060306071404030602090609090411030c04090309 80
    0x2a02b90642c0308140c54484043c3c119800000008052405111101101da548821040402c0c0b000f040a41401792000e02980324401c4144180000903040c014810892403992800e0303034008824659030201807910700300f01101201c04560b000d0400103c04c0c4014410300c55a0110ba50110091000e03814610000030281c111a00a54004849100d0f010441d2640d1540195038403407500c520900c0441c1408000c1098010a800b82c1150b1110481e50096a5460700205214400020492047c11241041810040b81c00300e251070b002000824003201d10900c2c0f00850486500d8401d5020584514030312102d190400b620720720490801e2400325080020042a0380203041150800046040e03851001c241843c2550409003809983c1c1d90411042c1e06007840690342c0408149064a0001a112034164480c0100d001c040d012a0340414120303840d8440104640e001c2000800d1541c261401e442d204042004900c09940a801140410745041c10140200d00341d1640c980c44a810b260308088021000c540c10007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 524875143 1250 524873893 524873903
    0x4050304032d050c041a0f040c0903050a0f0c17030703030b190b1215010504060c0f0b0901020a0e0906010504061b02090c30010303050319060815100e13 67
    0x50b0a00d00d4028006698070301d07200d40050103050103400c00b003001703d40035141840040f0020138501d0b2015a2621000740030004c08540c009035682074600210358040d800d40000f40710703119544903803092201d06d81030244098450010400c0054451920310302460346410200c3c1d403a44207100c0d500019010b50403640d0f0006000c0d1003060510913f0100820201c941e601c100d03c0000001100705092012011080e400760307106810f0380e81405c448000a01b00e10a9105003c02c0103818041c0604201410a08511141d0032203020074a40c18010640350003035200001c04008034059070400c845504003940300ca486480142c480904040c074028081d00c01c10b0b80350785840e0081840c1d00e180070060fa18110014000c401d050703000b5845d05000c020002000d100c201650143c80300307111100c8402d110012815041d640e2502e4403e0312500d4001c020314000c0102000040d035070f4103180000c10b42141c00905c4000302400d040d4003898545a101400342c1c0c0c148507010b0407084150203400201c002d1038943c80588994812 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 524876393 1250 524875143 524875193
    0x408072405180d02100e01031b020303061e0402130e0601032c010609020a021c083607091b031802010c050f060a060e0708090615030708100b15030405030403 69
    0xb0350014052030a0000c0b80c00c041151881c0304c00c500c0d48c0c103104400c1c5100c07500f49110101d0080400c060b503207004c02000688600c140c000c036840c010340e118011516105c1d000d0000e6445e42c100924140c2e5a00084c06141c41d4155600002202503100380100540381c0d240c0c0041e1404005140006e010040d0042c00f600e405640340c0b000001e5014542c8020700100603d0741c081c0141507074810f0509140c0e80503c105804010310038040c040354080040210030798407045103000310704e0f84042d4660b00200715120100100c1d40160440040d10310070640111003558900040c420204034103000c15800c468611450090103603440085100550055860714142c500400072200301b0007429002030324020040320b8103c19103455150030070103102c600402a07007003d080e042c2003c061401c4415596078001c010404041000300c0c2c0420070194900b4054500601500d84c20b4440c92200300d039060340508405803019015110700d0304907105c0d9940c01c8059901071a0f0027401b85190a14540300c54903008402d64001500c4407403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 524877643 1250 524876393 524876419
    0xc090106110c06031e0705040b0d0216020303191e1205060103060b03010b2d07030c08040f03060e060903164d1009030323040807240518 60
    0x20700d0f0185100f1281010700c4182c0030412031900026600280c401014000c0500003440f0b28041d02d0140d074a44a4040401a11600d02d503028025665040c0006901030000044007461203103030708400c2c07410b10071684400541200e5400c3d41c00c11a148041c28800180d0007100700c04401e422078121a03006203052601080307250701c6000044040d4000e0740a5802a8000110b030160107050340120820007110301c202460006c90540700003550b00c0b03020b00c02005c100c0c86402440402c4030711000c0e00c029103140c41140200d607840c0c0c602500100305400d000f0340c0c81d104200005805050020442d07840d484d101404d03840d40e444555440c08600d202c0d45100641c050750041c1c0c0500502500412082540480398a00300900e040052404084000109900400000c8481d40f20240c110412104895162802142100c1c03110394244103003003000305403c0304140024000602c4600000d1130026a010f40c0414000c031039128090143c406144c50040300400d109021442c50340201c0b04600c80c0d40308019102d0058425 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 524878893 1250 524877643 524877649
    0x12030430030f060608060f12100f0b0d170310030512031608010b0f07020102030706050108060709080714060d02090301060924030c15020a05160e090c090106110c 71
    0x5264400005940a11506150216414000d040c100c00103001d0800025013401c100404202d001400503001c1c1061540034602ca48818046044848420007138507217000c45e46402102400784840c1c080c5000d420850071204501d402c41c41380300c4255001c07240142d1500300300c2107010700350070081450001d8000a203000011840500500301d4160103c1c059580e2031030610300c2c01080150591640e402c004400c001031240f0070a0404450130810024400c980390400751004034514450600004c0c50380342008000150740d000059128003640c2c654030750000c00b45e120546140c1d07425180c031606864210302c1450007602c1c200343c8010890b100502d9000751800001c003002c070b801d4074000c1d8403468005039100c4020301c40c015101c40203044203e40b400311408681c51030319690000c1556020740108440d1100c2e0040c1481d008002c411349407544039003552100300d101041e41002010700d204a040e01c04100000550200300442d05881d94440208001c410380d08241c411908900f40340042c07489880340e02140b604940d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 524880143 1250 524878893 524878943
    0x360903090803070b011d0426040f031202060f04031d13020a0807181202060d020418090201080f040b150a0b0408030c01060b090d0f0809040504230c03120304 69
    0x40c0103041410301545407102203001103500c07213186001005141c00340400644623241246a500c5040018110301404680c000701d14411688691985c1082c54400000c0040342c076031140c00d00c0c5d0705409481866448408101e1002412200140000d0020b40013840003030310000140700100024110031442c00036001003d0899000101090109400100308441c599003e00e142e15407940000d42c150441e80340c02c01071004d03d940100028400c140c0444d1451041c203d55060710020440102c10b0b186d0000c1d031490840042810040a9000500020000b82031345030454140b030080d580550710719065a505400120244081000c0c1c0c0d03409812194000351000030ba070043e2003d491104040e50352140e0a810850840e5615401050301800c2400103e1880d56220007884041d07410101c2c5440c010a1440c110f13a071403207440c51b02039010f0300c3d083c148018040c5040f0600303040103000305181002d481020b44a82e4541000000540c90751214a03807050086d98000955002403240011160311029140300303030320702 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 524881393 1250 524880143 524880157
    0x70918090204050702071d060f0409140c09010e04030c0201020109080301080f1c0215090c090a0c0806030a020f040b0402130308190e151b0a03030204360903090803 72
    0x10351919030305030551400e40328013900400b01c4d00081620070700d80208442c2c10440810061100740d40e10000401c0358956008031040014010010401424203250041c0018080f61016445203d04142c12006080101c2510b05a071641842121a071782d030303550111a5042c110100324115501ea100c0390001440d882c1c0a98042c21200010b443c140d0000c3c4071841c0303007400e4000022102240c2e480c010303c01c143c000c540302a101c052940d012555580e103079090786c03410b0f40c81c00016802042050801420280c13590101810a04650341c84a8a4840c0320400d5903a2030615400ba500851100100c03000307140c0f40e4010032381c2c110060700140c10309610444404202c00c455006403000c2400184003104104481000b10b004012400d14120b5070004801260846e909e40d040b4102d01d01c00050505140403100286656881e1008100e80c01818a807034021701035040742c840e004034501c11304600e14500321601700110a4100000075908644000306600d8082c1c41c1c446402e030f05111801e034001c1400d0106000030a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 524882643 1250 524881393 524881439
    0x90510090f0212011b020c0f01082203030b040c020a11060310030c0807081c020606010c08040b180102100b1309170304050a030f030c0e15040f1205070f120b0709 71
    0x83d41c14828540c480c4403440817a01821500117010240e02d03941c840e090202c4411080ca80481c03199a910041c2d0111010101c190070f011408443d014105940344e000602c0304201601c0901c41c404400d2410303640c2d103152200007441411020406003490815401540e403050150321448862039480e102c01c2030b5512503070803142503600804c800340f141c003604000f5041d4402140990400d40024020020b44921014007a2410083d4445010051020082c292000360034281c00c141c0d0b690301110010046031903040011409070044846140798102944940350a07184090600000c47d144000e070b00b0011f101015007190959401e900b552003ca1008014621440c400c00082050448070b04000d4001c03520301e01d2070801c0609100d00d1505040e4042c13101c21300d8400a440040020340010160029806150404080c0200103080040d608005801c0313031884600800c1560302c2c0c40d803a6425065010790b24043d500384840503a0b940c5000809250a103070340490607141640b506900d4951003450055003182c030380c0d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 524883893 1250 524882643 524882651
    0x1060f0f02190807062004030807210e0a080609190f050106030c0311040b01050a05092404050a0b0f0f0f16030c11040c0e0607030e030d0c0510090510090f021201 71
    0x10400040c0d1080d43c2c0d1a000c10070144039500792041800006e8030540c0401001c1944c003281c14810020794001d03512024034102c1c10b4502c00c2400030f9004100300c002c14501b502c1604900c0c0006442440030034050301407401000540310413549100d55043c0d501c54042c0448900c2080d05849000c03400038801c941c0558481c0d0b5203500b120b03207075080200703404d01d214519521403445c00140c041140c1e01b15048812f8114103082080c0c0310342d050800195184084814401c01490b0601d054080d1110390000b841510400c0f19038864068030743c980c801a90150300b80040520702c041003200f03140122100a030100302c000c2c00502c0e16000c5c021103d40e84a40c0c1241c821000704051010a4040212800c244100c0c06400c3d0303410491460902c03001031000141608482c050fa070000b03104000d00d84102207903004020701404035802c640403104002c0070390888040664590040c216503007206a000d000e4901031a402c50010701c800b4907a070368407030014000c1041c100c1c0c1038180f81c0c00240040c0c4a603c9000b140500d0640001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 524885143 1250 524883893 524883907
    0x41a0a06030c140c0d0c020d1725050a0b13061505130506090106030e030f190f08041104020a090915050307050103021606050a0e0f0a1a01060f0f021908 67
    0x1c0d00d0100700b108900c5500505101d59480e135507000680c070850003984d1912441c03012082c000b0500345415580c0242200301130700348030300b80c80300010010068103110441a1118808030b80780d10440302003100e00100319030448807040340814072000c04150018004042150071190301d81c2c550b8201e5901040d4100800c000e040c08218614060a20000056400206000b82e02e0010000766603041f0500031740043c1941e56440d00640641001501c20004554900c2c50f541d480c0030400b60065900801c002c0002000e591440c80110312841c82c0d01c0c02154400c000480c080903031008c00c4040d4000c641c2c40c0c070821104072400038514203180502e003110a05403084070344003818042494241700c0e403a0062814540100120b412658541c1840d22030980c21490000c1c59451361050710b00641844040d460080c480d49059002ca11004106e60441601c200a5034004080400c0c02c2d00c144c0344244160b90100d0884100000e6041c0111050200c1c0800d5106460006168902c1c100c1c007255800000c0d12240d0010031a2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 524886393 1250 524885143 524885147
    0xd020a02100f08070c0303060506040902090a08010c0507080d0902210d050c0c2e18230103020a090b0a020703150e0a1e060212040201030b011706041a0a06030c 70
    0x1c0712140c001440d00204103007040e036019186420150825040100609190040c941300340d010401a050040a007961265511001e40c060341100818074841d44040e4400126083c0511546002a005840d080d042c01302c162180e210540020381d100b80310540711151a00182e13190800c8a403c02c01d00c9034420040c88507000d0f401d02e084951030410007403080800045440c190000344604244038211405004814030181400981c64611120388005a550302d1030980c480c0c10103a0710442980e1018408400c0d95641c144002c1c1c802c0381843d0050582907140000840c3d4807075001003070001524101010266511004000941d003c0045280140c10041d414010400c0000603c40701e545124400c0c0111b0710f450941548852242e41d0003810415006842e00c0e001c500c2441c000c1032550825000c548400015000b60340b0018100d070b081340040d00c2c040040c80706600643d10030f14200c507507000909099030740209000051100304440c9070750b5043d56044c4032041d2786054050020703200755500070814441c40040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 524887643 1250 524886393 524886409
    0x6020609070806180a0c0b2101031205030612100509010b0a0308030106110f1617161a04050402030a060611070b0304060c0302071b05010815060405040e010e0d020a02 73
    0xd142910340116900700615100000c410742c101020480c1140303207889520440b8a0410400303030081604055610005010b00381c1c00152651340740c80c01444504186201112210a100340001802140c2000d1103602ca24403030340c0a50362244014100c4105442d10308603c42c504821005510407403a21403081001c541e10a0051980c000f000b5542e00c600e507400c555a40c60743c3d00050040c40100810381d03000f18bc22810400c541e02101d028401603a4100071026034049a0100c10702072410040b0090b603107600e106400003210750a15448042c0451160b0406c9003180c04ac00315181a124200c1007481302084039070700c2c0e10040d4000e044001001503850701d002d10150003031000b0001146150040403007000848888400c0b03135401944440006004298688103070024025070324013401400070070a100c40780c0c0040741415000d0321001d0300c9a058a503900151144500ea03035a10054109c901448200014101500600111458036001096002c400d1140724500300b800384506006074841c0b02c0c024258200041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 524888893 1250 524887643 524887651
    0xc0b130f05042018120a03080c0a0503060f030708030a031b020319030c022d07080c0604060c0507050d1a0105090402060405010e01090905100509090102071e031407030504060206 78
    0x20707062102d0071142890381c2c1c940c10390001280103683c0000704100341c091150124140b2800083c00794960503e10141c40d0340e640c0e41408202c4c0840c0317500f030100c1d406580e0801070f1002e01c402a0743d40c4c0d1641d564242401758100340c0e41000c039018801c0035008100860140302034004640d86540000e01159171040d03a01a0100200381c0c0c0d000e640003006110f500395800c03000390703401064070305011a098140250483c509500c88403001d40031208040d030182d928409510501c04c0030303040c108036541581ca075803c45440c3d40840030f20540c468000c00c020043d550144c00113442e1540590305690321565510301250b00f1900e4903008684500d500190080d039036003010380c40c501400d01612101c6143c90240e0100e0046c0c41140201414407a140e410b0010300e0303104482c00005025490018001c50810758110194001240590343c40740c401c03807001a180c80c0c0305200f0744130800c0c1c2281510960720240b02c81e1050202c0384181c01e50030003052601c400310302c01c4540010139041e803283c0e07100ca81d103a10f8048000e0070000058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 524890143 1250 524888893 524888899
    0x4120201120603120c14030315030d080c0a2304030321050c090909010b10050c0d0212030a24060c060b0919110d0e0a021017070503040c0b130f05 64
    0x2050001c00e4130750700f100c94495554144002c040c0020305084414842d03410040308144000010000103030504040f0303c5414000b031701100c11266030404191101002100c0031360000750140140750005106044810350074103680303440561045124002c00c1203034803031b4009501040485035662a02c094104d0a06045007031107004100c0ca0801d40c08a41c05480313254455445400f0010214000c02ca0a502503800224001c007542212182c84074003620381e802ca140c16012038001c404954424600209804403a030f82d011078542d04d50340d10b182034840184081c042e010080c0112203204a06055810804000b400142d02d841c1c0d0440c140340703030000a844102020310300610352002808800c94041c00320808901c00c0c05404580c00714000d103074074468065410f5002c0b559007412110640e03040d0100304405410b000f0b6400e0901d8285040741a5810440d100c0110b40c3e6110703180c00a80b01c03e1090b006150801c0c400c010901c4059511214000c060300041043c0c031801480c2c81080107214040c10400c00100030030303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 524891393 1250 524890143 524890151
    0x1060206100303181203090905010b18040e12030702010905010b0d02011b240203100b0a02070e0903070606093e0918010b030711070509060f03070305030412020112 72
    0x612182099100c9522000f428000c04100840c0490f000d082410080c160fa01c0e0000c402416500700240404440e10580e25207d1500c000866402203400c100e9068a205c14410351000520701e092000520300611140c009002c4c2082c031a1800d1840300c01140a803036158000f00f6041e0240c20541e0031100c2d4a40500e2082141c40300d0440140d0704845070040401c4001c03c02c04c031000c1c450811030340c500c041101c600c0341801e00c411b28000c01e403110390103540684607200f100340d103c83d01d640f5440154071400020a0150f4818042040315010407400c4580c0301c00c2d5041900d0501c07809603110000da5549421000a090312000c1580c41c00c0601c043c440001600110780700b130548821600300408e0072018514041941300040c44100d00e1b210000c4d41d070405507518913404019a07548540b00b04a420a0726124000b0302000911345190a00017480340555000920312101030700c9e2502040800c07108149440c0c0c06010f00c02001000c11002d03c05000208503001c040d0341c038110f5030300c00100010a103180003074071a454 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 524892643 1250 524891393 524891401
    0x10b1f0e04061a03190f0f050907050a03020d06021e0304060b0a0510030b01020c030a03020c09010609030b0105010806010309120f020c0102120f0906040807081609020309060705030a090b0f090601060206 89
    0x242c5030028510030340240030030b5501c2e2070320140c402c00401c0b502508001740341030841c1c040c403001c40741c1d1003100154001c4208101546440d420ba5440d41900d100c1c0301d90088058506001500e8025605484140300303010041c40d162280710310788245109020710110070310011041001b0700401d4004e603c030380e0b03404942882004e420300c1f000810410056482c50201070b568104000076074020085079090701c00040c100c1d1800784c554074000b5900d043c08102c0390701a03c014000002c640b03004040640540354412035218407a8281030044408501c01010360341095150300180b00401c2c0811242001c115844c0d03910030500008440c06498074089542039411940000c1c4a5550003094509442d04204024801552a0000000181c084c0229004101d4078050751300000385c4003c00150401c1d00e0808283c80f000c0160746c3d98219802c17400300725015982a04030500042d07400f4801c10065030700100c036280010b50401c641d2144011b02a080710580301201039042407011200c0200f180d9801800d0718802040c141c50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 524893893 1250 524892643 524892659
    0x9150303460c1202190b100e010b19050403080706090203063301090b0301081c0e060a0c020a090c031a09070c350d0b0a08070b0c010b1f0e0406 63
    0x540b00d1000303801d010541c500088014424444000060f0780d0340e900e80740101150903c54848181959065503030244182c000a00d400d030404241c0c1221044040305007011990401404011149002141080010003000c400200004003502c1044c0c01044001303400b8605106240c581440940952807a043c0400090666044070341e00d114030f00c600a1410000342100030050b110803e80c0c0c0c04c005c0703c2550120000c40c01000004040203040029015401601c01602060311030a60300c4004a41081d01080b43e0b0b501c0c1070050805290351032020304082c150951324054170044540c0c0c001c00130300007501c1d12183d400f80320a02d40001540c1004450106071410034074030251222891690003811000305698035020816850002c440d4659018810460102e18481c2c20440340d0001210442140c0340030010092401d140301088190380925000741405418240100c6041e040750226500b150340307620020710344d601d074840d40420002580000303c0f0b822a0100c40a44540316400626000307614040701004290 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 524895143 1250 524893893 524893907
    0x1305120f01110310260d08220c06081f0b040e0f06030d080a0b03010203011d1e061203071401051b0f03061c020d0803011e050915030346 60
    0xb610318100c5110007521a403080d1139860101305c0750306140213a00c038103a80a6004507565106652a41144e40f40c0c50004402244d4074100d608080d00480344a007080c45803502030b1035645d800075a1850f0000c80c615050080c003c070312220740c1100fa1550000304080002503030881c01c25403c1000c840309409035160030b00200b661881c0700d04400d0200f01e030f030402045090050351301550540e80040c0c000e40d0780390307168040b007030354112200d41400c20000302c9400038a017000030066949816038020328000c09602c3c0d0600300b02599401c48019103090004200c2400000e07a04200d420f080207108001152900d0002103803c1500c032921507800024600b08803481c4e1200c01803044951080b400c94402000d04220088120390100d40f81e002500080b00f20601414000c0070030156040725000c0407107410007101c1e01d5a19082942c54824240c0124101021501120b00c1d089074201100004d02104d040c030804001ca001d1403404001c0e401404445a011106141031b0f41c000c21580e49042080c2c44002c4101000082c110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 524896393 1250 524895143 524895149
    0x6020c12041d0c0f030c04031731090510050906100801050105131d0115020a0c030f0212151005040605030c010305090c040f0b0a291305120f01110310 66
    0x40d4542ca000200b040b0019801e8a9401d02aa110b89450b072902004030001c5901602081e2828201d00e482c90800113012003c43d0f0442d036500d030090343c408410b844000c0c069503044a42c1c200c00c0844082c0803950001d9442207500c21354401d0000a01c0d07600c0c0009210a5400c0504500e00811038800709030340d0160010030050450b28207203001680c0e04044003040801c442e40f9003040c8403c6c1007030740323112400101d1520030506882005040a4007145807041c283c3e610540302400802e05900e5100410103d102e6042000101d40040c6c00440b080088581031030400d10f011152081080c951002d1005c60300e0110303001000f81c40e09840400c2482d0829000996900d0107107410342c101a00c2d600003d440340000e000c040c20414024100b405002825100a000341c92038a4040780200400d210010740d035441c80213100c40c1c10102100502130340802004140e0150322440e447c0110645465002405d5145c50403910135001c0c140020303141c0d4405003541a800c3d81c00c0c0c8541e1011f941e1090081c8561810340041040407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 524897643 1250 524896393 524896439
    0x203030103031d060705160f05131107080c06010e0115120209030106030215180a0f0506030403020f060114090f06030d0f02070504020a0c021002010501120204022506020c1204 77
    0x3c1000300d50514024100900c00c0a030000000300f080400c01c140042c1a92010814800c00c207505c81d203504400c140303070b40a8484d643d48030300c1c500305010242e05a940004260717200e404086141421503242d003801580b02c280c1c0e80c581030303011100400c1012406942d4501412000d100041d803030041000007440c206118a1041c2c20541c0040d00306403990b025806503000f503030f010306455002e140b00440c0c08916003280c403100015800281058280d031a04030403d074180c8035180c8900354058203010a014064100500480c01d6108200045d0400041041080e000700201c0d4a109c0b1010190020b010b00200080c007610f100364003a105009442c0d4000c5001c02c120350561800c80781403c000f4208034a4000b6a501c1550054800036a241c81e0740e0744081c0202c1e030b29000713403101400446085401c07800c81ea801d1084075055010146040300500d8107800502508070308004103400c56203000c60104240c080e002c0101c61066000a80780f00d040000c0c00403044600003201040e08191800c0303191075840c6040c1c000100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 524898893 1250 524897643 524897657
    0x20f03030a050c0702030f0c0307061b030f050d1419090c06120f18110303071203050c0715050921070204110c0a0c091404031b021c05010912090303020303010303 71
    0xf210100c80c0948006540050403203800d0029108030035107644070300c18502d009014003a008071303e4601a8080202c000e0300014202e080c0321031a2011a0300c1d03a800410a01080300400484580c81c2071409800b009541e1180b0424681c149113980792801d0700b202241c1a10302d030a02d0901c4011130740461025046681c14244007404500101071500181003010105500c02c5c03400016070a031260030900d10b58a144141050700112182c24101550b07802034520040070351400c10a4006100d109421a03604070030b0b00c50300750341401503d686007100c48051655441049640350f0412001120406c80540c41d43d070f40c041201075161911038505d03114400c4403c003a0103241c4032803101c41d00600b102e04075034078040840107681c040c0c1840e140c41100780180d44290344511742030480c180641c0c0400c100c003501036a49034603003c001c0d0b1204100c202800c0e04400c401d03a030100d10741e0400038a8584500c45006a40e04ca800000384102052a00c40c0b0100c0a05d0b03188020461400018000640c001080303a0649405050040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 524900143 1250 524898893 524898901
    0x6080c03061e060c06190e03040902070503190509040f0c020c060f090a032102011406130f020d020c1b01023007060e0c030628060e010f0510020f03030a05 68
    0x20415105084541c0d030000f00000301c00900741008607841c0e0040c081d440e440b0102d03c2080d007213103090305c0510880c410380b600100010020362105074003d01d643c0d8450826241803d030b40c02c072058580c5104040d0400440c00000301d880d59841e1900c541c072411000460200011404810000d544000142c204e0340251300004400c4500080b04065451200c0010301c100c40068891130314005800d10a041d640b4282541700c100302c14180103001c2c1c000d80c03458858103c0702c2d5075114820446000d203546905080982d482000c0c1c100c00205000902070792802c400c0240e501d0795011400340c0307080e6a10b41d0380390745448448030000040ea07003c181342c8812590301180900300d0240e50a00200c078840440c0c442c0e00d248001602c2c008101042d0400b4102c0d41c068016142c0002007a020b0548580044451020b0b454100000250040184500301601b501942000890f030b074a03a00140004031007a00b0103800c200d0500d2080140340751601080b00f040038680301034054000c0d22202540d90b4000584403640880d1148001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 524901393 1250 524900143 524900179
    0x121e070e12010f02040512010524060d050705040612060b0a181d041a0402010c0201051b0a0f0224120a0e010f060609080304032012030406110706080c0306 68
    0x40c03844101c000002c00107000a0360150009502522405000c5c0c110007540011703540f0b042c0f184610850507680c41d12214160b08203102c144110000265900c08014806002411003501c81d0b0380c8200c41c1c80d00d07000da580d070074064003408550214289440040c1800c40603c5032500080540f200303102e160420f4150004084603070710040c0c0300c5400c1030342c51040d05100d29010f1080c00d14601e0140d80140742041d40c00030340001c10341075480e04841c0a40031404910034080194480e000904042c56144078203402d02d0f039030000c00e0341000d603803000039510802d640b0a080250315000d1000d50301d8080c1e6598280d900c1e000b4900d100d405000d2100c0102c58800d40c80001080c5550030b41149021100c000004c011010050280704001c02050050b400022180080070410720000070440d81500d0300700041d00c0401e0300389800d000c00f0007048481c0b075030420098000d0380b60b0707090200b029201614164640c1110b80c4846c1c0a01460b06103164080000c0054138001c3c08403443c02e0400710ba030030540580703600305490600120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 524902643 1250 524901393 524901409
    0x1003080412051e01020a080105060f0a0c05010b030a0302060f070e100315031a040b0106091202041d0d020a1e0f0b061504080c01090b0306010509090417070602121e070e 74
    0x74400b40c690310030410282030045d8000c1018003000d8454101a9032500140002c40c0200c0046181400741000408202801a00a1540f692140f0004110340500f54086800c110384604100e001d40d01c040c0030b102043c1c071208021580b10301d07a4070f4032401c64141b50b00051b1901c8040030105040c543c0c0d9201c041c4200c00040c400101458100060880c0d00c810b0000b0411210030444058401b80c0c40c0e0400454468483c0049008560650103031285582e51070b0208002003030112060034a080508070b0060b9000e00c1807025490480440d0058808660503080074400070700091100c6030445401d102c582d0000703c00c000080ea4840d04102940342a648250204142d13403444a005600c0c002c012038000f4400c0e400059003e034009080c1d03901c05003a5a1450403090303d000541e04540898018440704800b414550720141d03119004003410103074504d400c80940d509920011007560081d0300081c0c5902c0360403210801d00c6e0892040030b1040c14080d1102d10749465800094030910070000b08070b40f080c2e803076620003203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 524903893 1250 524902643 524902663
    0x60c2a03140a0c1a04050c01090305060c1309090b060a30051501030c090b010219060203070507060207052116060c12020f040e0615030103060522031106100308041205 73
    0x101586000926601c8036101203041701d0440c0d05109200c0040c101c1c2d40300d04007500071298005c0003030060b5214450304240310381240c590500d4410b080140000c00b072000e030040f00c3c903460080004203128103201080c44818107494121540a6611007030240c00034089009a081c490100122030b50800c50301e291490400d59010804104812284004418001350810344411240302000c1040b040740d00340700698558204070500500d50742101104004100107070003c55100e030940c5411890094903556141c00c82e0005081039445901c1070140201403407500e90b204100108005910303051100070a80c0840c136050840005000340d444649402d81c4e10701402009901d04540700c401e5488481c20582000725400034810f041c00c001101c0f010a0090420008645c2c6d030b550342e01d001c0c0345181e0035074450401901c400b52601d000002103810170303e04106461800c0f06002c1c03203a0754040c0c8200244030010729004001e0824070910207500c00030000100c014048408030390b0014155070541441c0c0c1415420901045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 524905143 1250 524903893 524903903
    0x151a091504020f040518010503010c0f09031e0507030807020f010504033c0614060103060810050613020f280909090812090610090b06090105070c03060c2a03140a0c 72
    0x40028400e070002c140c09040c0c60050b00204010014440cbc22605403071040c2084003c14030705501400402ca8500150f11800d0018524840010180e80c03100c0c5043c4041d4010340d601c0360041603034000c40c41d01d401101140c400900e03142e410181943c4680402503100f0924014403105020f8000c11290203184071a0710851410132125643c1c840c5c01c1c9040a811018120186990071200203400c070343c081c0c0308523000d070fa000d08000d190350800220004010880074202070743c804d004480145c43c400c0701c0e000400701810754006051711030348010804520b03501c0405442c071108500c24042c0000c3d0360b02200584c01ca414142010521209034200040035110303003805032512042500030000300741030028643e40036042c50268040301656070380200c403c9a080940450740140b040020103640c1d071242000e0a00c25014a207070040a41c1c2d242d44100403117070710300229000328090740348203808008001d5100700c40c04240d914510600760030340e8004207a03803108102111801c0b0301042ea80c80040c824044002026404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 524906393 1250 524905143 524905159
    0x301090905011e090c08060c071209050402041502210d1a0324070e0102100c051c1505120705040518070815090a0b010b0a020a151a091504020f0405 65
    0xf0303058032006059940025a0000c05000c00014034000010765240300b03403d0310400c0ca007003011325600c1c1d00840c14490905000c2014280000c5041c2e0b64500c0103000801940d009060050358642d00641000c5145181e588040700c0c00c02c0048200e8003002c01c644e600f80f455100007071607603800b4004a8041528902190701445102c994808054114000c80f031100885d080f2940c4c0d540d2490b50403502140080015801600a010140d400c9465030300301d900d031400d490800380e0a00780c0541c4280f0003e01c262031140201600c0300500a0020240201540502800c2c0c0307500321085c64444502c0d50741c0303209100d018040c82ea1800051244e1511103403a142038282d07a42903400013940e4081c01942d82d0561081413400201c0e00c00407a04010001414292150380300d00303440c03800d03807800d00e00b11641e03001030b400d030ba01354000c080c3d1400c00907244050640c0c0200104600003084031130308500e140020015800a40180c82031020311503d001c032102801e04014086402607500d07805444031001a018540c000c0c3e42010756 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 524907643 1250 524906393 524906441
    0x10e040f06031b0918030e10111f05070f090b03060105040509011403010b04050f06040c050f1b06070c0201020a200d0501050604050a061401180b031807060c020105030109090501 78
    0x203c080034101d0b4020300051003045042481ca02031a070a070280180403c0c014001c0107010304101c504550362007032030b040c84040010701e241c00714103141550321005000c200a030080140e1011503c90160006000c1c5048110000c4401c0c0c044d1490401e0b0007100303204000400001d210340c1c0324800315405400c024003900c00a50750783d0000410140701d040041e11179420000140a6030a00e80705a901c1100c0515102082e80c0341d004c203010040c804017400c1820400100665112040030100a00408050b516104c00241c5480011420150b024100b002006a0318000c4c6016030781c0020600c003280c2e041031840a8151004800d40d41d10001b0301011034102164170500c409000d01035000c42d209004c280d40c1442150f440748402e0003140d0540c061103068062020544105521034000c881e9540d01103490301102a468844a40740c3e5081241c906001c034810010009107002c0501c4914010503003400c00b60f041a40c01c0d8006061070005004034003606546407013400034403909401c04031403604000766441c20b40f05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 524908893 1250 524907643 524907683
    0x9020907020d020c1e0402160618020a0524130e090d080117030d0f090302010b3001090804030b0601020715080106082509061d060406110f1207020405010b0306010e040f0603 76
    0xe02c0b1381054480300e01d01002b207001c040401c08030388000780e03009210182403418081001803903002c801401d420310b10017001c035622160450340200900c203880011070000c60315024090070f2401009112910b5500075603829181c4c0c6810054850564220308296980318207488803d91450140c001750207181c03030074071550982904441d40300c8200709000368020701c88203401c9404e00891454417000c54001101c0d992640b0803000c1c40204661011045100106182042e621000700a4105400c180c030783c06c004c0c4050020940e01000170344020310001540904400d21048050f01000307051190310240041c490000b5581441200b1000b03440e400e41c9015003109609003001010342d0034500445000c86e820303207000441400540300c2102910401440c4501c2c007030904000311400b1106454050840c41051588480c14006021401581d41048080c540b1180b07a401044160f0f1410b1703008110a07601002400fa569034402c0c1c0e0000060380030f45010074003480310700f40e85008040c0e690001d490311103101312100100d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 524910143 1250 524908893 524908927
    0x509040f0b190e040f17030f0114091e100315140612280b0a15080c060d0c0e0306010611122a030d180c090b01021b0f060a0309020907020d020c1e0402 66
    0x81c1101000c2922a0b82b90818009100402d454400d440308162964050b075140c40741460381e00003581c001315004240e403603841810046120203050082501c40b0002c00b81c5145e8241e280341e00038402c8440304106200032142c40d031210103214541800741c8400c41a48880c40034081c0746c1d050a940007010014600d8040001401803034a4070200341c03a145403550000c0c849a0009072034520b074038014601c514000590502000404413502c2103424000000c58800741c0d0703581403100c603009084946540310340b0748500100c079003045005600711a03da0424049a0800020000d07060510300e01c0c41d0f500341d138200d444400c0501e1400741c07148410710341e030421008039007488000d400c607900607104690310b07503003180c4a900c28825900608000380c0161310000040410300780c9003000c084035120103440c400c0d1003d000c03000318210b607000b1040d0034040390f00d50b2600b40c21030500026056000c0344500c00b0705403007620b6050094880380000f103007511074900c02801c7c440040407000500070240b8010400c554603900000708480030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 524911393 1250 524910143 524910149
    0x405090711070e0108030409021b070b041e03080a0f020f100c11030304050c090a090b010603060501110d0801090207150e060f0a020a08070507030509040f0b190e040f17030f01 77
    0x240c003510b0750001c0c1540c5804003850694415101071400c042c10501101c0094101d040001602c01400c98140d28100b014490030028000b41142290345d1403c111200d0140107030881110b440904060040010590341c0060b81d80c6039005291004500180c80d1040780b40c0004405060310700d004001c942c3c400d0180a43c07010307000c01c83c6507d400e00f20421201c49540c49000841d0060019084100015054949015001c0c2d1000100f01d0008103030215841c3e03c5c0c0000030903000070001ca139594106008640c0c025001030720b0070400c0b10090903807106101c4024564031041c4182c0190b2500072a5030010000c011901036942a40c4900c20817109110321903150340c071041568901400821040031a02da003905000302c80700c07030a40b078903007004546880d1402c030382a5100000940070420140701c021400e42d9140a0783d640b150000134003082d039400314002c000002a90aa803001c2c0c1100c0000100003807043c20507480e0f400f540043e0704c1c007005101070074804034802040201c1c1144800c00401c00070803054540c14281a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 524912643 1250 524911393 524911427
    0x608010501210f02040b03031c02030f150f01030c050c030c0c041407081303090e10090f021e03040501110c0607030b0d05100c02010f0e0f0d09060912050304050907 72
    0x407a404000390b000340b4809001c0064480c950340b00c1d414000d800e298101d02c0c0441005011240380400c0750540c2c0a01c2c0b030254683d0351201d5000014402084420340704550000f00000b0785114111003980010300300440d0000c0b4a06142e190302004000340e01500a94942074090710507603a50352904d4075010340350a48042001c1c0310301d103040800207085003190100c81c8184002d0300c0d000c4058845807441142e464000070110200420020007041d40701d40f0503000b40c0510100983c2100040c01d060440f0251011000980d5100344107000e48000e8116003a1711003a1242800d441d5a540e440768201300c0d0140400300070240040c0e100007900f8800050000b085845030803d1342d030422030804240d042201c0e03d444480d02600c5584024403240317503413150303901009007a40a40000184846600c4000080d44d00182021b845034008500c0da054242040c4600403d041c2c1504e8108502810014040c00510b0759018114540c1420700552041003810800c40c2c000e0b20006101015503e00351000074048664400464a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 524913893 1250 524912643 524912669
    0x4091a040c1416111c0b070302030c2a060405070e0a050610030c0e10090612060501020a080a0302040e0f01080d0804030234030602190504030201020a060209030c040608010501 77
    0x38061142c455040c02e01100ca0001d40380040e20002084010201d03c400c1c0c4515110303641c0b1352065611150603070340d24501600d109100a4581c02c110041030030007070890052500400170844050120801c03521304201003052440c00d20403041d82a0749403860008411414800d5000340b105100000401d001202c01d01004016190b0300e26a07054250386040d100d158228900301039944a441c0250071501c9490b01c145404100001c100c0006046800d5404200d00412181c40b424840180e01c59801100314a03041342c1030201a26201c0002e40e51007180c0300160108001050b2080380303038071a404580050006410340a000e0a000103202c181c03010a00c942e110385d01c241d01e1601038450090304030920550301900a000c48019001140040f4680121806da45185000c45c6619259150046101940c0070f5a00180c4661081c038401081d40540d80f00340d01030003414802040140e90014071480c04683c03100e005602c644a440200340341000341604658054200400840c4001055100354102d07545142d1400e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 524915143 1250 524913893 524913911
    0xf0203060a120503030c07020f10050d0c08040b060603100801050a0606030c0305150603060a050a120219081c030605030d0e04060623030c04030b040b0403080708091b030304091a04 79
    0x2c06148010041041d00180300061000810201810040b030010300400310a4500000144100c091041c0f103c011803c0801c0110100815204a101c1603605060500741800d01da1a60304134018000c0c036052140000100203146070540424107402060118000e101b0b500701507101e100503120b14040c210000c0e1600c2c0c55100450300c41c1c021076001d8018002e102c1c03070a180c2c003030074840705610091603281c003c2c41000c8000340a4541c0e02080004082c2c0c01804001d05c500b5104000345288041c8180c980600c40b03803000d000010340454240c40440c5070303c3c141c0d69001c0020009030083d000c59800113a05016401802c1031181c0c014442d401e40d0703401102ccc200837441c0c66000079a030b02400104440749400c050928071010b0000c0500464000a18190440c14103039a50b49069002100f102d08448003a150000c1c04201900250792a4004e04503040c02c410515150380e030b0950300d64144c4202146200c42c42e90001980c1c60520443c0d01911766544140480741040b03040d8420240340fa18a00c1c0110f240040f04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 524916393 1250 524915143 524915159
    0x82d04030309081c050901030509010e0a0f02040b0f1c060b0907020a030201050f0c180a031205040906080615280605041e0302010c1b05060415080a1416120f0203060a 73
    0x4844844c4550703c030581400340d4900114000d260042800205640e01d08410307105580400565101a04c1401007880c01c4049105000039200044409401026051345220031940c0340f02d0109101482030b94000382c450b03580c0c20320802801140e096680c00200314400d101c441a07011a660a410703000c2d13002844035071140c1d0017804103102c040390f04069548083c480c03032170400c0381c207201001d000750b0040c40070300b0403a1030b9111007142a0368442c580000c00c0c1d000034100468061805003000800c41a009031001c2e1600310b50703c001c601d812240c02032042a4002c00c0702c03028901030048112584900c10700740001c0b41c82d0480609698014041c1903861480242d0070045882e0410b4100e0a0381e030b069403a2922600c065807444803120f002410303202c1041c10307080003041c1c80c0c4801014000400c0d40c5c2070400f401d41e05041025000d54000341242c01d04e81c2c02c2045600443c001d000a440e0080b1100e4541007481c0030b90303882120f1074200641003a050f5820000003101d40d00268000e5070042000b2900382e10680c0e0b4034140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 524917643 1250 524916393 524916433
    0x2060f0403061401210c0f090204150903050a03050c0115081e1207060905030d050a090b090109260c060a1505091e0604090206070302010504050613082d0403030908 72
    0x5083d103100c1d40d1241700b914000940d0001a405803080b0318641d40d03140c8618030304810401d00d400c1218001c3d40414100002c4041105c00d6482803950708000001b903080da1500d9845840c940405402e0060003d01903140340d000754011614040c800d000240d132151034040603a2215580b0041d500508185088403040346004204029200d5195102d103141c2082030f03a035100600090841540d890005108551044e40c0074010b00e4031841d907041001900014918041e80c0c5013034044e04c08d0b80304c0e84c50003244d00c0010324841c03281440d0421001924030b4460f00c0d4118061244076000ca5414070340500801d00c0b6680d60960055003102a20301c2081c9d100d01e032110705001c1c0060301150710048140d018070a024030350740344c1c0d2040350300400301030004507845041b5000b0905650002d101100181e65410030041070000911415800c0000018089207e055076120208240161086521440210700d1100040401506508000001d141031140c4450381c1c0e04001c0d081c0e403c24403513a079481c09546144840340b003007410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 524918893 1250 524917643 524917649
    0x30f110c030a060506061308030901020706110a0332070506060607080307050a230a090f2d12051b0d0209271b03010b030705010503060907030902060f0403061401 71
    0x206203211054480c0d1004e080050003907034005204001910169203960240d601814240e401141e880b41d5a0000914103080d5500a204100c2c007451180038000d40411032148503909490145030880780c08003466801c0b1421515210a60308065071501c800300300001810880c0d019a050328525035403501032190038030801d540141550410030001d084240950094484010b59240240c8840410320b00281c050a22025800012001140b110315103640038a04102410010090070852840e0110b86c40d880440038142040c0b5000040045005031184801c8000900c0b40060b010341c404200c1c02d02d69110482c0b0910b20991a0f0075040c18111802c000410840d1103501400c088020713640c0700700401c0d801c800740911000c001e200c0060a0004501006041d03d9600041294031050540d07108160854404035600350281e089124100460303a0000103580d03000105075840b29040d03444e014124000c06401000a602540110b00005000c50060141060f00e101c0d081c02c205003c0851040210400248 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 524920143 1250 524918893 524918899
    0x60902090904031d060a03020d0b0f010905060706180c08060106050a0801150507020d030801050a0807180e0a06022b0e0604031b050105090105070e06030705091905040207030f110c 79
    0x4000300740024400e84c954051080d108250413036018602c000101c40d036200119030000607402203410071585100384900c1e041c3c2102107585080d8442d032440081d1508542c0e00c00c8171301c030b9a00860140244001c5820035600d20400d5a0007294004842c40c0191010b11107000b400914410341c030010900d107000e0011a54900b0241e110000030380c1c43c254030141038840004030441003007c2840072400584440803140c20661283d01ca540c8658113000a100a007403240d40000034962022004205000c4c20001201d8105548030300407880c98054040315140118021000700b015200103440000d10030401121444c1c00301c2441001c01151030b15641d103054405d0505105007a82001c004180020700650388040001d10300d8013030803400d52854a5107800c4036011541c8200507516002040180740e03011480c440c1c03034481280d55a0840c102004020814003071118058011170303c0041141140304ca0501c05001401700500c259a1403440c1d29004001c600d20344d000c4004142c0000107217194100109e41000e4040002d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 524921393 1250 524920143 524920159
    0x706090807120809090708010824160c0b0c121303020c240c100f0c0c030806010207030b0403030e0d02031603141218160608010b1b070f060306090209 66
    0xe004040700030030341c4411103e91030200b00d40c00b1251076880c6454407071341c0c2a4460b001650326206000b41030000940140380d41c690101c08400003480c048000d242c2010140a038004c01c525210000e59103110b40c2c0002a1012001c00e042220943c0d0403c010042c0004030607200c074054849030104649400403117001070168101c640d80c2052410002a5a00b00300d881801340907447c0d0034800d6507001e560003801c0c0c079807c58010f4401d58480800600070b82e8038443c4006410040f40b9044040107051647c5808e0050400600c440880c805038420046400550f070440d002170060705144c5000340050041e520028040e01809000100f0030b030001c415524a2040c01c0d0360075620764095a0300700da0301252100c2c1e01d001d00300c09210407013546c889501c419100d11142826500b00c900029901840c3c1000b06581d15606140380754140082c84c0c3c8016428111107542e081c4603200c400c40000f0b41644401008168124825000002410441c3c10f00301c008075041d0342c6040000703680300d003101c00c142d1041600d1942c020900d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 524922643 1250 524921393 524921399
    0xd230a03140d111809010503150105060a0915050a1d0105041809060207030224010803070f021c0c151d0d051504050c0117090709020d02041706090706090807 69
    0x4120020104004110360000f141904407000c030685400051a0801d400c1944000d4141030504038200c5014000c1100100884401405100751075001405950701864002c20400f0040b4001d42c41d8601411100546035114004c140e03004003240c2003015030400050081111001c560007401c200080c1c2c0e0b81c181d40b061f140a0628207402c511081c0380c00700002c007542c6e031600136001c241103101401e40b141c840c0c0d0252010800d40748015424800021a25240303041e2080100701a42000007150000341c0d001c2c03000c0244000b1030000541c004000d48035105030441200e41142080603980b000402e845214801c01c0c100214074404444245010080100a0344413121072280c0c2c3c0f40000c50391911034450400c0320507484d0780f0750243c00340301c0007680d04232081d9002c0b100702c64680d80c0004002d1018011002c60300824580900c0e441d9880c0c102d44625250240d0009440f20143d2054040f42d020f0b29950a555940780005100c480e07503000c00b241d00f580742d4017944002249103441000820102c4081000820301141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 524923893 1250 524922643 524922677
    0xf0b0a051c11010216030f0c08161a161b081f090c081203070e06070f030f050d0207150b040507090303141e07020f0319200d230a03 58
    0x20048403060540c864441d28400e035608031240032024507c6812031145040c03075460a0706008600340c003c403020b03070090100711628800d8111220304452621030441c00803580b290a01030341d4405c2184482d4404a460055010b1240c0e080078154048003600c03040302104d994030401070702c5144800ba0764500c004001840c2281c010340b0340066400300d002e1401030080c01e60342e0311940d25007080c1c100031941c103500110422130195008403654942c030505a541070700c3d0004039a14064040c0320001c00409101304101454012071095040d24031895103118115543c0c6050b0034155010076000c04031407001400c18084110b2401d01d4090180229019220000302c0e0341159002da50000203860304030b00a070030920903004104007500194581c45108118540c0d504c5c020700600466041d80385140740240d11001412800700174400175000155000301c5607440d0040f0340d10554007403000500b0b0705a4040d00e48100b00042c0321002003410308181c0c2d5606004211404101e038143c0f64a45c0e006d01034080f032840c42c0704440207d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 524925143 1250 524923893 524923913
    0x222050405060f040f022107030b06072d0813181a01110c030709050f0a1505060c010209090a0c1b1a04051c02060108010e0129030a060f0b0a051c 64
    0x2440f0540c051f081000b0744003440e001e0b00305000f60440e03d41c1c1c90301c103000c11550540325428464109455052500100340c640a1a06550b00300d5001c4c0f505490303511464040e030700010070b51800d0b032100b0748a03503801c0d0741c1c02d490300b6202c401d00a02016003114035001500208030310030304d0547c0d065075207000140c501d140300641c0c0e194074007000c880b202d0207502441521a0b500344001d60180c040c1000c00261400c000340c02c2d04d000f91008107110f407118a0518800e010040b000031400450b0f400301d815640e02d81c0b0f42010903001e030240342c40c81600040c094050082d190060340055003a042e96680c6c0e00c1100d034480811034843c8403880700c090202044002c0c0c02005a0519465581c494003a01c2155414001d04950150320201041040d005800c40801809445403c1c0100d80700d6100c0359000348861a401582e081581490900139070180c160040070304000d88013400921030568022800b000100c2107040c2c1c46010307001c00390085200b1218000041414601204c514640080041c0e0301050021242e41d039007806 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 524926393 1250 524925143 524925161
    0x20a05120c0a0b130b13260f0408010507020613080f09060705062401021605100309150912030507020a060f06050a06120f0905060c0a09090222050405060f04 69
    0xa004200010022519184400740030b11420000301c0013050440c14080703481403028050a411a10310302d225004564400107401d4008041c5030b130000e404010540c0f0040e43d1284100c4958400c40100d00040e02c1c000651000b44101d2487d0244c2d0900c0d601c0070345800404041c04001010208103100c402c800d26942005010a444003a01c0140b520034540c44031450b0040441e0b65030f990201d0507881c5aa002913441084003421000e000400743c29520041d8800305192a000303190140c00b1591041200a01c00d402030b11850f60045e040000044511401c00060b00c100e03d030a0761415400f2403100812031007842000d210b0201903024100c1d00070a59600c002400c0b03c80388002c1510b80b514004505a9502c0c21040020401901c2e01031300750802c0740c00320050b96071124601c034401e481d099042010840124420303500140310241240c1d6014800402d8461582c0c86e0800740180340302082890b15102080014040c0d403102c500c58141199a4104202c20750b64204c80c19170300611180c03201e0f002414190420146 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 524927643 1250 524926393 524926417
    0x306060f030601020c1e03010b0a08071a310510080a020c0c0303030a02120c160f0302030d14010509090d021009060b041104170a20030a020a170d020a0512 68
    0x511078903200000c0815a06c0d0a42c14941c4590309240d400520707091080c10540202a0740c408011441d001085440e5801881248002c8845607a0842e4a4000b8401c64603560f8061041c0220f40891000703a0040800076071501d524246280408500b91401480c0b2062290302561010b810f0b40c0d5030b001c803074041d41081d400312a1a02c1040d6185d00240e8007400550710400c44104016160b4240d0980e03c10310400203804048010001c0002c500b0b8144000240c40c940b580240c100b140380c0300b0503d000ca103948184040e07503024a150601070805083d24662083c100d500c1155400c1a1f62519205a51140c04621180026a0004a0702c440d44101074102408190080d040012160402070208058804040d00b0098187c0001420300c205200425010307082d848040061000301c000faa904055000da0b03442d08080701c400c0c52002440b0350307000c21204c28500d6000d4116621319a1b5041010b42e461002d514215081c040e03940110581440054070941e010f800000504080c0ca1280c0840303ca03602c4540704040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 524928893 1250 524927643 524927653
    0x5030c031501180b09030c0423060d08070501061503020c0d08270d020f070b03040602070825021003110910031103070f03060b070b0a110409140f0c0306060f03060102 73
    0x2401c0d0f81c42c1c90004000340b81003080581d0300c004e0b6104260800c5451640315105074540204014440048803004101290000c40d00e101c0d6103503100028001032a1f000001d202c90800948d80d800c00c0010f402541c00c81e40300c0005808400582c8609a00341d00480c00200c01c190311100552001511440b0115040074802ca03418030364200c1c15180000300c0f55601202f04141d40702c0c015054609604005d0700342411811000340c04841d04041c0c0204035880003510180c83c2c9034020504406002810049441e00c002045079604c800f0003000096108001003c81648501841e0b45c1000a840c000d00400075140e400f0040703145010000c0c1d04001c07041d51000d0f0b007442050369a440c104843c506200045003c0c180c603803034141104142000080640c2d0990f00420039982061200600040c03c0c201540c0c5c00165071903021905010b540101244c034003440e80400189410441c211240e95052078540d4040c0781c008101c20440e9a81d0b00321459140b0040d06c030741f41c01c084100301d1881800c1000c4040e41c0c010005205540c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 524930143 1250 524928893 524928917
    0x1f1a0901180c1e180608090d0309051f0c110304050102031209010b09040305072a0b1e3f0c0c0c3109020f0402070809090f010602070605030c031501 65
    0x50f9490301200b8007240469410048010388022004007080107000610b4002c0851505054550300ca03103031007148105040d140c55442c410000140214612907400f1038418254040d00c00740e900180ca020810000801d514144204841c40701200b214152801070300194075100852106561002006120120b40d544c0c92903140d03590340da455041d6000e1400780e81c400e500d4030f0150038040d11403004084101c03050720800e40340350301003184082400304680019941c81e4960044284030800d4903620b1600d80381005001407000d2a200c117400f9084503001d200382009041d203420006900008903c00301c4e80b602580ea040005188002d410001e00d900c1080c1e0054800551030f00c40480c1004110003000d111545100c42240101c12090315641202c54080d1420300626540c1e030042011004540e41c3c050240d07800181c000c06018002c0c04940c030125016218504501e018280d0b9034084400780581320040c02203040c0003c1e60361103401928041e02c88590414656103403a9402c400750414209c2950600030303000c2e214 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 524931393 1250 524930143 524930177
    0xa0c090305300f04060f05030105090103290108160803040b07060e071706060915010906080c0f0d1407021b040c0e0301181b0602120a021f1a0901180c 66
    0x64020080c2c3d5001c820b864908242000c0e2503003250100d0102040002d200410840d5078498400781100d420901a803003910012910405002162040d0b01240d4641000000c01003400500e50070349035080d02d11060100e8071080310b01d03100e120300d00c1049001da07800d006480210380c0a90282840d0010705044402003a980c0c40c8090608900c6021901d154100001700150390400c941c0040c0c1c000060300c80c28004040317103400a0800ea8442c0500c030b0800140c0b40c00100310205240444040c2d030b06044403180c495101d10001006045070b400303500b41c52080da0740480c104900000300484512001405501100c000e07006000051200513001010030040d4012000c0c1030301c00380b040c1e010300190103091601c642c21343d041051180000354400601034130b10303d00c10007000d41c0c04162007010300d91040c8000d58a141840d022450180c05032225036400c1c07950b80e10b510550403158000c0311040c00c81d503189406041001c0812400100034800c02c00200c5413481d40c00d1040841d40d0141c06207080500700b07507100107101808 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 524932643 1250 524931393 524931397
    0x504030b010e2502150403030e19140c0307090f060906030b060f03030301060e0405090a050d0c0506061f0c02130509030d0605040c0207150c1a0a0c09030530 69
    0x802510b100c41003081c0120480181d40056031007034000c100e02d4442035002002551001826400100401c806001c2010135100c1d400014041d207003802143c0302108000402503054101e070904807440350040741e110704140d0002c03030405ca040340d00a0107000500d29005081c40901412003c4000042d42c0b840040f031644a40c0c801c41001d180a0a008e183c9440e20387e040c01003144c4130408481c825072043c0010004150700c01c0d4001c80c002000e41e40821140c403540035840ca01405c60b100140700740940c5501c100d400b64041040c01c00c050140f411603072652141d5040c0107204080b00c107860081401e5040d041d101d42c0c02000007040b100c0c4090031800500704d95007842c40484000380c51760740d141e400003d42125240c03850f02640c400391508403020801020301c9000690759103071901c00c5010031207002440b00b9485000b1080600410f0700000c501c000301c80351588130105140c081b505034680ca40307882e1001d0102440f4000401c1502d81c00001040708038043e45420440300301003820f0001c0500c0e440010340c000751000e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 524933893 1250 524932643 524932649
    0x1050603091c090302040f050f0a091415070f03090507030201050f16061e110301140a0b2101080c0d1b0902070503041d130b040303020702061215041a040c0504030b01 73
    0x1407110142d03801d45c030401003a1907000007250240d03400d02052240e103004400889410600308000001d07082d0766450102c007201c0e240031080506000301e42040041d0307041030000921810890356a986a40c0003a030081e0211108460302902d02d50143c003080c401940079000030301100c0b985d4444a0300b0600903c00340103042d6441c210860394280c603a030030719903024803030310f82d05a000300700c01c6007441f4085901c12121064001407003000c00003002d1201001054440002d144098015136856a607a074810400d146000030981c20000641c0200714000100e40c440881c000d010701e94001e00004801010b0380b1004011f2010010044150141100c0000c81807000e100030f0600c03501c10340185888034134011824002954510f41d80400d02d00b1701041054100030040c0c6450b0855204840c61031584450400318000c0c090224000d4000c1d4000801c022400b8160381401c0c85148074100c202c03041006101480243c540c102c104040316014115000103502d020b401c90911028240b07009030804c1e40e01c0e201c0004a010a034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 524935143 1250 524933893 524933897
    0x3020906071b08071502250503030f040e0105060c030a120b030307051c0f0504090504110d051605062a0a050a120206060d02010e06130f0609060e0f030601050603091c 73
    0x842c20412200c043c072951004290500d1148400c0c588218041d445549250344248601440686940b1181c0b40782c5000000d410040e00312615046e500066021513030003402100034811001000049918054088824048544005d5030a103840c4210658000c04003580f1b240e0a00d40b00d80301b400207518100068807010b80120010f00d40b000c0300c3c007101c01280d41c11440d2801006040e1141e505a04c0d0050111812200d400900041035507031428070541031030310840d07a01ea07c01c6150b02d00400340b22000689502410f03e030389059031071a13038500400070a846150442c91860600440040019503124903c1140503410400d40b04920201c2da2100d023006a2100b003203900d8007882241c80c1d01c003503040105a84c003070030580d09062800603580010340000400404a841080000f0326401d120b00c043d900c0360010416649030210082c0c4890010b4901c11242c0569000500510510b00300e0f843e0205140b03035540b0000d0054412a400c11003030089a41c4020b140311075501c1450010200c1e2400d80100f041d50702083d0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 524936393 1250 524935143 524935193
    0x5030609012f0307050a0210060603021b0d141e03040b101a0301030b070c05010603050303090c010306031e0512210c280c080d0c08090303090d0302090607 68
    0x89842076907112042c501d0001407581002d84415420b0307450407244c0007900d6040258841458000032417404d012112690007072800c04800180343d9800d5000317099100d0305500144030100301400200d03034074240c0100010000c0c400712860000408680001c0001020318880e01f5841c850140d070b400d078180d00650f001c484a1640c034080000031001288050040c2c40c620310104881c0c803840d08100954001030001030f014a007000c0220340d00501030604508803c2d03000000740550780ea01c0c10015181d8000f150030903e0741c000e0503030341030b4950300c680300340300659500c00071000c80080a814156652500c0c00c40450303039880703a891611001d44001002d0a84410704000d501e403296115507007504401030291022200a005106100c050103096103108000b40e10701801c0b02800e484101c088400109000000d012000002454000d10000b90440b1000c035656846464454489401a540c0ca10007100d51000c03075003240005018030351090b0014040c2000050405040218686038490700100940c0300503000301c81c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 524937643 1250 524936393 524936411
    0x1120b180f06061206040c0c1a04260d0f0b060f1c05040f02010c020f04060b0c0c010906050703080a020706050c03060f0402131a07321b060705070503060901 69
    0xd011041c2c2d004805030344540c00e000c8806500791924101521561103103850f40b21302d6150900c194000940d580d0040004441601000c2c0c40f075241d42000d0380c040e503c0201c40084500300318001c03004030242a111a10041c40d0030110729040004217412603600e6240c948070084001d8640e6200d010748030703510b128022140d03150004890010241d0103404444102c0382040308010214004002c648880c68081c2041e4050040a200155021f94070028260303205262890206844a460000d858105503000498010550180065840f08900d00c100740c0025000c105500c00130b80300d500180c2d042800c0c003402506000d07082e5252000d840c8110380c080c2d5160300100820044e460450540c0d010b102042e1011031130035001c5000c840304100f95020300d145003400c0000841100d9400803c0700c0342c043d00302001500324100100b41002007598494000c0b039140030b5140c12103845034007148203150000060b02e805289c0003038205210144e04814010b440c01d00030410700040ca504c0a200992054003408000108045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 524938893 1250 524937643 524937661
    0x20309072102010903020402070303140709061808070317040b190e0a080304090908090d230102190807020102160b180109020a05010509030f0a03090e01150c0201120b18 74
    0x404204180390101504407400941d80003444101500e40544000d641c84510742010745c09010b012900c11500f02d409000c00442c00d03444606042a109540e403a2074072040c41c100c102010440d03500403000e00e41c10404082001071242449410455004200c1500700f40d503694902c11240c024811800788900001003d4001903445100346604820803030b035203598541881c40f590303540c2c000e50165040c401d903501481802e21031103a050711810900140b4128880c2c005140105d4121441c0f002d901407841c41c00f40e90900c51106000303440c2c030115400c07000583c400e490082105c10b1b20002d06080c0035035500f0030000c0481c0700e40c21002d10300d040c080d45d030400090800c00c017031000711a05c2c0782076801240d160000000c0165100101c0200720782c2c0900c4c1068840e00030030000f07403c00c5009080000c0c0d44c49070300c2c1c0200400d9000750304a400c98031810010304881c1e0b604c100344101d80c0d00f085a40300004924002181c015805042204910003a250700000c100c41d00e480410740001d43d142c0c84921604d564002c200c2000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 524940143 1250 524938893 524938919
    0x410705011a01030e070501030c02071e050901060507030806010c08120f0726011202041b030c14040311210304060503010f120b1803070b0c0702130b0321040902030907 73
    0x44280390400c103441c0d208608685601c664006c90b4101038540113510041d510030803848024040322005c01e15070880c0440040d403890510b219003801160080000211640194243c03400700b50952903a00031313542c030100110381d1000488403c42d01074400340f041c140b4400c0d03000b80721841a00000302c0c1202d6802e0200300940f010343d1501c900310643d0046a81050881600030800c0d044031841d110903400040da920018002d000419241d020246541c642402030350391540200f11050440e494043c1c00e5840c000b032005651003503003c060814041010740101608010340c2c13030760300000701b0601010b501c1002d2007050b045603c40c0c0d00071000240c0110040c005c85030007001550040480080c20028100e4a544441e44214010081118064000c10340d03841030006001b150909680082607158900d030004840c032240d00698410703409040c2490941d0b11080381032007040d514000040007049852031503441d124520804c070811004008050100154601041c000f440c022140d20015003d01801e003401d04c0c07120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 524941393 1250 524940143 524940191
    0x14030c07021801260709150306050105010e0f0609040b130c0909060e0f101d01140a29040509070f020d03020313020402091c150c41070501 61
    0x280000104190004c00806880b60b001c1c2d40d113106000d40c04200c001e4140b020b2940308228103820845d00701415004102c08000f56031150204011a90701c40c0011035440c4064030304140c0003a106a695505850520003034024200000c2001c5030480480740404c0b500c10258000c0c0c10070907241d8040e542c650707401920390800b40a4610f02041040d140c04804540800c001d81482c0d0f020819501003000c0b02540c2d01c0c0e8030050000d00c1d100d90380889a80c41c0f01e0368624000d208481d0f42d403480c08020030340341c6082c0708482c0c11122518240414807000b00102c0d41c0f0002c0490000c444a101004006000e840d14000d05200b15443e84948210f0b030b40c10b02000e8240384070142c1c1d0400300740c8100100a0a0126110960100da806482c0148c540007184040b4200500c4a10010a6035032081e2001c020130044116804103c201a0800d20500688400903603c031904003000120090214228113001c03070700d021b03288043d0000b403d2820313140705803e03501c1d860b140e00c829000d84903070b51120411a03550307403e85540841 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 524942643 1250 524941393 524941429
    0x4122a080f011802101103040e06090114090114010c0237030b0403080a0e010f150506041208210106030902030114160807020c06161401020306090f0714030c0702 71
    0x20341043c0c0c080c07078850318a03d0000d2294150408880034070f1702c14040010a02400800c880d5070b1030b02e6a01ca00091a812038949100e512024000b1654800800f850740141c07a001d032082d41c0316400c115901482068083c00541008140a1103c002d6621600000c0c0203000610340303c11150040c1e9a014000e1411443d02d00f400c000280041001402c050ba01c10342c0319426140007400e60300d900b807541e005400340400450241d07080070000c0d03414959640c49050300c42408951804096660310900030307180103034412004110040902c90001c03401280081c1384801d18001e03800e450300806d0b2540c145244c820b802c01d4000030359803071140045090920400128110000c800c15032880d0003501014444a0401541c080050792004030320301c03a0080202d282d4507070008000c035865140030301c0821405a50342209031102407113840f03080c60b0064180b003124003800000c0d010500f255100c030104c011421010304410100100d90301464046541d042c061030003080f413101c80e00c0d500c456038010030550441480003000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 524943893 1250 524942643 524942651
    0x1a060a031407051e030a020d06060807090603060b091908010c2303011202060c01060801050c480a0b0708041b080613030e1309140102070804122a080f01 67
    0x15011130a4802e40c541d082518491650b00d6403118030345406409582c07083d41c0e8076820481d01069058020310f01034420102541e409e20300c4e0b0341d030308400c0f0195089071244503802003040120703241b00d091022030915100402e1200001c1155210034060855902040130400030340c050010105218084240318070302c211009145040d541489a48102091203480080c46000001800c5880344000e401c02c50003044200000c105620301103285404aa101140049500c0901b092a1072040585035141042041c0442e480354044140f15100e0355080f4040b0000e61588601845100020002104944910250758070002181068030b03002c1c04c1901c5980010842088002062102000000300c1690242c01c2031a038254507050350406840100791120001e822004040c45400800d0342c58120060a03482440c0c010000c50009209500701c1c099007100a1003410108010003d49040945803000c1500991100c5007980000d02801c07400400b2456052070769103902c004000002c010312005d0142180000280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 524945143 1250 524943893 524943907
    0xa290114090a0b0103090f140f030301030c120201050c0102030916060c030c02041107050a120e18010605070602040810140702070e0c03100e07112b031a060a03140705 73
    0xa400380d04014514042c05070f642600c010f8a81c4650072041d10183c0088201016804030f040102c1c2c40c200071070f01502a841041051485041e001080704d0489421070120722156003440030300b081070100031405070b04214040c405e98000020030310045002c0c0c0c9201000304a45403606444414001903640010f090207000100900802c3c1c000f1090220584d040b100012040c00040d5400c034507000b42c1c000540325205028501d000c10448038007040450034642c4510b00b8070080e0341c00f0083c1c20740781c8031040764400502000402c42c050041003d0807025115000140c140703621000b03081d01d450400001508020303110b400e0345001004014004d90014458030103410864240404004e8005000c1c12401181000100062071150002c400300d02402c4042566045403e007404010b03c0b01c24940700c03050103801842e42505090750b164034ac002c0388000220040062062441c0c06a0050400d040f07040d42c9480d002080d9a2240d4a843c010701e540300c00389d140000c42c180740840c880301c00d00c002800e10302441800c0201c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 524946393 1250 524945143 524945149
    0x1003050c0d0506191d0a140303160305070509041a0a060f020714060705070b0d0c02010204050f0f030f0d03020a0311090d0b04080f040b04090e1515030a290114 70
    0x8903a0007032401c15a10180c00c00c421156008000703006220003004c0b0741d400174102d00c0f44003040e4190010b010316103103480792641c0c1e00900e441c1d100965092403a44c00d050030110f2080d003e03802c42c5901c4002810802d0810105c203010031305456075844080003c40480004002500c0d000400300043c088924004034800701101c0c009e583c0d0046c5008010b803600011944200c0d80d80d5039411105c0c690360040581e96101e40d10608182c0c42d40000580d8085181044242070803d841442030700c0880c3c0d0002e244d80507105841c024049141c490006094040c0038034a00d0051a010401105003520703603580c0c005075103010f01103008040b540c0b102c80d01901040d00700125242955561441540c69411030155906902d540c500441248103040c40d00021200104002417103200c114080d00031078003408824404001c800c5402038880c86007001d111300100389840442e4400c05c202d070f0282400302004c0c0c1201d19280301d036281c5440c201c400119901c1000b00c0d110030048201c040206040c014692807091000040c401000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 524947643 1250 524946393 524946403
    0xf0206010b09131a360c0c0a111311040317040e090a0b0109020304021e0103060b03151002030c0a300201360b06010c0b1003050c0d05 59
    0x190041e1003400b007580380d00380c1d03548018039414000300e0030108440d910501c0c80a07108203046004e90310072003039400342401801000307080c0c040d114502e80010121000c0c0f0004c00260290160654045420902c0030b001014004c0150403034803802030708650840c11900c1c2c1000440c1e2031010042410508201c1c0d5032213142c501074240d4055030f51112030154201d024080e8a540350040d41d1040c00202160300c203210302c103a40070403010301c180d0083c9501d1080380e881c1d109610a030f20007500d009400c05d1030105410115125002c403944440700501d03011418075503c0102d24002d80090707401d0300441c48440e215803141e151030b40c00040d0018490025500b0310512040c0c0c40c0d2500c0e08564050410884c8600c8039249247c2c00309500ba41c1901d06007403003103c2c1510080240200380040003604000030582d0840b04100100c00380c0f980198104010b078049403856034405400e45400340c00c66060003180c0205800244084070000e225175030012944180310300e50b040561600340c0d40da03022401801c000343c00f503022620200c0c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 524948893 1250 524947643 524947649
    0xf0227010e07030209091510210c050f0a080105040b030f0a060902010e10030906060b09130b03100e06100b03060901060813060f06140a141504080105100302010f0f020601 75
    0x1851100307a0380b0404280d0180c820200610307404081d941c1041100199034406100b8250250341c502d0402108207825100f5000d1150091740413401e140c4623a0100400b85c00c0003005c0099071505034204910203801c03448542043c400000425820320041c042410180305119018404400400d01d0740c40700d0100035200d03903000001901c0c0030744503a019170035a40290740200d0104000303007041001001c0500000d009007203000b8121001403d10300c00288404070030b8240c0c0d0511000521a00e0040c102ca0703600070040c108114860b170103006021100c160b02100e44680798400c1c0301385001c0c108501d08603501400c4840650000c1800000c10310901030192915400c25040d181941004920382d01e0340c0c201c4044103850604000c5c1941d04221520000000d142c110384111061a40744950240f9403030208545810b5070300038100380c1400d10400007054078012402a182c00c0302146040c0c5820f440b1081c41e401d480d82192541c441050b4441c0c20011540d04c5030301c5540005d81071426000503071030003400a44440c2d042c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 524950143 1250 524948893 524948909
    0x11070b04080d090203030f09030c010c050d030e0c09090309150a0c02040e150412030b090108100213030c06022409060703050702030c0312010602070e010e07140708070f022701 77
    0x21844000480450340f04002d06a0020100d9031192485404541254002c000f841e019000718945410154000d00300050050b40c814040d0541e40103081044000309428a07075103250380304105003907100b91a940103283c000c3e0210b00281d07680304044000d00c800b0213800002e4046880042003030aa11583c00000c6d4040c40d5411500440c01a10f0081c01c1031900d03840462030760002d64983c060008111044d400b4015640c0541c906001d24441c68041002c0440244242d04441d0840c0780d80c05452102c590080000d001a28000c42c5031a849495003032840742e060700040c0c00f60303006a0030b620940042c1400010301020340710141c03210b45000d41100c0e441d090040c00070000e064a8001141c14139000f4025103681d14550803c0302e40f103039502c00c140440148284100d2015005114000c0780c250800101ca60503034411401c40c030296160b01c41c048407944440b03a00c0443c42c00d400d1088400180b1190010180f45014080101102005004100e905007504095450210660495003400340828400c1d504440200e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 524951393 1250 524950143 524950147
    0x70c0b0c25140105040e07030f0b120a0807050712050105040302010f0902030309040f1107050102030414012711121516091e170304060305090109030e0d030201090605070309050111070b0408 83
    0x142d4440c0140d03081b81c52040504410000410303456403101044445400c2c041c80726481200900250041c0c401040d9100e400c002c6405002c01d400740c00900c00203108500704d9035159031720100b00d0010311b8001011180c43c4d4442d4203110030705609000b83c03090030a00850401c80701e05070340d00190341c07881080002d03405141c82d001c2c802a00d2405a2040c2c19401101ca6080da490900d494014000e510444044030311a09880400d14030b01170500c1513580541a032400b00440150304003500c16198207203541200c140f541d84800382e26035110707281800d2070101c001000307102558455011608801005090f010703031301d4a60fa20501002e60203d0400200e0360904c0034411059200030b2400b00c043c259810800f540210500c00c0350080380c1c0000100100c6141c1c2d50100803e8841c900c103642620740c2480041c0004012400d00141d5152545d87c2c18000f610a0000080440c0e146d9114000e442e81120858042551380f144d003c2802001e0240310780414140c501c15103025180d07900c0040800c4040c00c050300350100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 524952643 1250 524951393 524951429
    0xc250b090a0c06021204030b1b0406021e030301051804060207020d0303141302030706030f020d0903050406020d030204080a02060a02010e01050f060118150302070312060e0103031e09051203070c0b0c25 88
    0xa461f064121100200804036525501c4100296030303044086070dc170f02c501d081d0402c0d0f03807000b5002000f079a069440090200304010f403280202e600c2d101000d031068900650810024005994034509e6805c0180f0075200030400f406c01d00140c07103001d04003d0403050307142440b95803080182d6011030103505840b43c5007800130b032040e00c9042c03940c000d01400340c0c2a10b0452402a25400b07243d00140600308a661a5084504904801600710183c6c0694420321003a907008d003889400529003c0d000d440b107405280700008402044110a909503a0107494401040f00864280503082d40d000b462059500c060030945c0c0540b80ca0311404c0030070b0b58401d43c0780c4010142d02240810406101c0c44100100e81094070007880166101c40030031a13654820b105c2100484e01680801040d0362003803041390801d0300711791a1030807200e14000500c04801c188402d00c121030b020070042240002e40102281c00941203074055292a4020307503000502e420f5508822041a6092014803c5c210040021290580e105501c5000c14840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 524953893 1250 524952643 524952661
    0x218090901060b1b0601052e0c20040c020a0506010e042307140103110901080411060409052205061501090b2803050c250b090a0c06021204030b 63
    0xc032a8001d0b00214100040c83e020f9130f600e200b80c038100c070b00b518815030309940da81c1c1040002202003020a8109141d800140311108108855a070100c040c45040007007441000c0d07917618694040f08030941400402c0310501c14504c1c1002c0c820700065030b125000400c1c44030406e440395a5103000501c074031108150350000080170407004611403d401160580e02140c80403640700f182e81c0f105068080e244401e000351192180c558401d01a800c03001c01c1d44061107192550303100045031002c01c02403080d2103580e1092020039042e101e03003000740004c21883c03c1c0000c039810031944100d0941e5540c0140184103400d00c030050003040c00421a2904030191a018912410906004ae510032100c2da100300c000b26008141c2400714190038141e0130340c070310303468611941064200c07006404544c0309a902900901d02071016008d40764100c40904480c000024200d041100385a032a44078040b41201c0006d208c0d0042ca094000f003042c0314880e103000e86000d0010301900f550400081d50540294072018000c0010203002c00d10000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 524955143 1250 524953893 524953901
    0x7060e03030606180d080708071a0c0406051b0f030a03050c210a0b09010f08190c06110a05030c03040e0907030203100f09054201060f050d02070b0f09010218090901 72
    0x151b80580c0c410380318070f000c0c146a40d441c0c00c0315030241d5540e02d034403030105801030884030a203204100c914519400c2605001045400350021103444160748152a02203240c82d0007080502d030043c42c058001d5036501301100f4000c1c00c0d224040c00d210b01001c0180441200300104000e8691510a000c011203581e0340c801c03a04074040e103800249181c001c07180c200082035074180182d85000313035005001180d60844618854020601e8641e5001e403a90039840d80038810b00344900c403440210180242181c500c80c840f512842e04503401041c1e681c02c1540001020000403484141c0e0540c07003002100505480c03469a00030035203030559200144620381c0d03034842800491501e540001c0e10307203400c10b08940b68400e0140741007070140034501213103400340c00450304581030120882d109411a8129840003104c1e03460104e00b40d5082c1c000c01000400e100040c042c91010742c1582c8090018036005001e466540d040c13080c6681ea41600152502e50729900420410300220b050f60008a9000703001d0b01c41800c143c0c1d036201c00318010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 524956393 1250 524955143 524955169
    0x50f0d050613090506010f050607020f0f0a0b031807081f0906060e092a031203060301061d0406150b2706040303020102030610080105010804061e05070507060e0303060618 75
    0x6142840a409020001407070b541a211030111f07038200c081e2103100704900c601508400a511010b54510307501503040201d82d102c0c02541c050309206926499002465064108403902511b1000310703440d6402800d01003100c2802400c004001d4845030703481038040740c1490726902c1d0705040e072034940c4045070802101e603002d90014250034426100d1030a00380c641907217882e0a10080d800500d480040300d0300f004040d4501c914a01801001802c040160508400171500010442a031555030f4440010f014015001c100c41100c0c11400d040c000c52905140c124101da8560001c00c010004502043c003007000e408049034149106100c0403150304070070100000801d8201d00700c098106a01007400010941c0540245000d080f085502800b09071580c1802c0354480b009105031400903045601050118000c2c3d800a00842c01e0101c0f464021182c48400100b40c1c0e000361108800a200040c0c0d20b018010507105210b000070740400510315604143d00011a64010b08501c2c002100c0fa4110007441551a26615140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 524957643 1250 524956393 524956429
    0x2030d02120708070503010f1809082a0106142101020c0a020f0f011e0909060b0403020108180309010e010306050316030c09020405061c0b1801090b01050f0d0506 71
    0x80d40c1006020482071000c295096000310b034540001c184007a0080c01528181c906081c0f43da000c8d10314000c50400031683c5040c139100030a9442c000030001c143c0c41d00040c84030340e844e803889031191010207075101e1020415004580403a4582a8103100c91114410548c19050084039462003007800c940c00358207030403480c81600c1d40644c40010090f0b0418400300b00d051506008031040649150101c05110325a546c000c105400110422110036402140140103e05002d0901d00380d051651100b640c20122251a08241c44062000c1010406c43da401100d80b5480305400780e41c070620030810000203a49000f100388090600c0b00e034890000c03159129600c14002400001c2c11900c0000050301040c2034501c05010035183c0540b0454040340c0d02c4058000c8800b1200094801131070500040d840c604290040c00e8013254854860104283e40e0343c40e0f01140400340c0c6c8042c60502c1c2c0b54900151213040342c1e2000078440c184074061041c0e94420708000140d070000c9003008070101c0c007130380c9080018403039081141030621 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 524958893 1250 524957643 524957647
    0x2100903030c020c031203010302090c0f04031a181e0325110109080303280f0f1a0f061e0711010206060f090414100c03151401020a1202030d02 63
    0xe15516410402c1d0640d626000c3e00d180325590028591120a2410700381c0e00440108010801414400d00a90f44000a889aa402d044441c0040030f5a94000c1d8070030f0301c1e0390a580340c0b400151140000f120b60030540103400b103181740010b461041e88801c800d000240003450808010b550b528014021101c9a80d4a0046030700c03d5860103500b51803215527090309540d160411380c9d031268035500891424050701c2c9820003d508581d5009000d80f03050410140340e04443c140c1ca01401826006401034625120032010040344100310b281010080310b16061aa100490001d04000482d465403411050400c5007540c6c0c055840310f48100000514105d0345002204a400040200520002e00c0082c000f1071003d130b0a445440e00d45030200050301000c05a5142c1c01002c2c100820000380312403a1407a9000390710401e880d070341d20b060b416140840b107042401d40e0210740c4842d08215001f00010080028110055140100f0300c403040000703540d510790341801408080c00741c0c60411894020000c1d1442040b0000307080d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 524960143 1250 524958893 524958911
    0x40204090501031b08030d05060a0b0c0a061413031b0b04030f090608010b03150102070305100e0c0618010507170301120308090d12090201090e01090b01021b0f040b010210 75
    0x1400801c000d10003aa107001c01c040002d00b1041140d601c84040310301d01c1c0020350405612000040081002074051030740100c88a5000400b070362004041c0c4041d80e50307500a002e4503107460a10900b903805200b0104e0601c40010308008540e11a1f100f41150241c0500d4016415040b5146036a95064554000341400416008101c10183e001100c0c0d04034240c0c070303520004029075038038081d181e040003130040041840c824000a00b0401d490720142310400c50500c1251520340e629201d5500305116500380b5402591510505840484d0070000c01340105020703a0b401d4505601c002c5124000101b02d4150350402400040e52400d000792102ca5524198043c5038481e92035940310b41c40f6242110001048010402d40d1001034003404003c58540d40ca2051a1150640c550300c9103103910042c80211000ca050161a11020440300460300c030a5000c0e06101400161500d0304400180c50410a42d0710b940d83d45049007000d194544401c60311000829041e036011588001040043c0d09002042d20020f209510340504c031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 524961393 1250 524960143 524960159
    0xe030a030c0c1b082812031b030605010f090e060607050a0c0e040605090a3318021f09090c050f0a020a0b100b340b010929010c03030209040204 63
    0xe4003110261005c44a840000716900c0b40d4810b40171580071310f5190360b042e145021400040b5000b490302600d00c0d002460008001c000a90780300c3c40402000080d40e42d6005005030350700f00499180102d12410486142d602e000d403200c980b00741c014402c40c081c801c045150f60810400b0015260000e600070502c4150b40e448400681d0130300011181512480c2c14a401b0694818001c02c0d00111a03410600c04042c0354041100c10f03d1078940c00c05c4203159a014000c9444018185105203e000c2c01d107003042c10704c0000e42d8010414441110307042000c10600308031405841e1504881ca81c006c030790070140b002c550300d50044c6060703c20340520310719055404800141808190b80c082001c4203064803800d42200c0b162a800c1440294100c50300403c0945030081003207889104a110341e808030b0084100740d8612140340c2d4040d518045041400454020b42e2810050003c05841d00940c400b00c58060320100310000001000d9240c90582c610f494140416070056406061186c1c040707401d04100a84195034403075644001e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 524962643 1250 524961393 524961443
    0x60807181a04050603073c030b01022401080708030f0a030b0109180f0c03020301120303051503070b03010305100b060d0b0a0314160b0c0c01080c0d11030105130e030a030c0c 76
    0x940d41e0030800c8802004410384020099200c46400c12034003001c2407c51322025402002900c20032410345c420941c0348101008040c800d000c4410340075581c0155545400400c500d404055080403015400a0103900713420b00041d402d460740880c4a00d004a003164841300103807800b42031504084800420b516400d02c060a8139042441204101c20082100410090b03085040b80002c0c080d04409000e5401c154000c80d20070340006400c10061008c0b111031054a070000303441e140d03c84c1c0c08a150b407800800104180501404007401c108030501041c800101d15030001103d80c03007004002d18809540d00e407103030390301e1300c0d1081c0141c091640101e00302c0c000006042403a0f51245c2914901140820517400450300160040503200390383c0380c40004100c03400021005440c0c0c0c0c00c0081100003640004d21998001c0080750048192480100003116503a5040c030301405034003003041688518103070520032500b9101c68008100d070f00b40896481c0c0003413440c02c0c1c2001115003482003800948000c4400340400100e03440380b44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 524963893 1250 524962643 524962667
    0x180209010e01111002090a150807080702070602031903200c01060501170a0b060c0316030e06090a090506030a0c030b092107080a032301060807181a0405060307 70
    0x226440245102001180e03848107040d0845004d40104a0a410460042d00079000d1540010038501c2c1c0e807912486d90040e8151104400c2002400610901124a400c68121604440700d44050501182050b4019649204425110701d00385504403510455520992003914002d42c40e000444c5203040c070014282d940d03005072984440c9546003a000040781c0d07002e01d0700340314031402101c02105550303030310701040c00103004c055038542d00f0072810412400c10110074001001d507a03802003107160715000a030070010403504124000a00860382000184947d61f12009004100ca180484c04103031a501c80d4082400d040c0707007140003401d280001601000308803054082340e20410500048600c0000060842c40141c8080103808640720802c00ca48004191038500404050500c1e00300820215480c00007986083c8000034194400040100140496a445080d081d005500340ca8100e005c202e15041110004196110fa800c0c05903043c20441c1c102c00b080015200101001410251246040d00000e012586205 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 524965143 1250 524963893 524963897
    0x40312090816080a02060d06150305042306040f0203010e0a0308090105090105010f061b020d060c0e03010e030d1a030d0203040602070b0f0406120e2e020909040201050d0618020901 79
    0x10191881404030110a012202490010040c0d130840c1c0e001e010291b8014000c1d0240c49450b200013048440a401044030790140b9070354002a50301e0141003000460f04107d445640710071018201108044000507056041500080c0a159680d075a20001c4d00401c0c0c81d0906120600595048005141e04043c1c804d00c100c076500001e200a60b181f001180c00c0356001d015174615042c4488051103418822401c2d2041c801e00b00c0808042460700f900080d4180900050803600641c07201c0c61080c2065200d00140300403078058000380541d074007501010391030307010700c90170700a40700c4d6104030411607001400c40c1303042c4203100542540c0d000c030f1084200035203e0f401030182c84003505c1000070011300d00049d00101d50003824080c03140c0342454201001101c2c05500007640c0314400342c481c03c0300380c003008090010580129141c0c006c2a00404154005110075a001c82202e2403144140804589521805a00c980c01942440c040d0303900c0f81e889071200300804058101444400e14242105950340c0036600400e03940d2026 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 524966393 1250 524965143 524965153
    0x902070c050d0804120c080a0f021801180c1202030c09030f0a03080103080f0d0e1b010309050607110a05070312080c070c3b01030b130b1b0403120908 66
    0x280080c000700d02e031203280040003460b0410042004120031085428401e21426900c1592583c41941c40d01e04000b42a0603104e60031030705003000c00c52820044003168000132180024080d850701c11031461481d09080c00c2c0320419204c42406507228424009038913004104031003103440e8204400c039214036402000c008c50081c4281850102010000074070680710682c140d440c808981c0c2565a513060517000340400d044501c5c0180b10100c5011058003454100c1c1c5c3c0310341d00030400c0c5d02c068841091a03540d0301564a042c1881c040040022402c041f07021980241281081c41c610200b4002540c984070200304081e05030f0042840110420140b00c070002d600070b1056941d03107060303155548101c2c41440341d45001041000d1200c420881c03000c0b02c00102015100070000d03d0240d04164041044011690340c0c510381d101c0032100184200401c45032800e800044040c046c07034002200e0f50b10503283c400089d010b00001d144041862403921000300469002e0340c0d06c04c02e01440300c1040da4001c0e0560b40a8085c0071624011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 524967643 1250 524966393 524966399
    0xf180e150a0e04170a030b03030724062409030206120723030a1a03031201090501081c030906020d0603050a02040b040b1804060213060f030f020306010512060f0a0902070c 75
    0x1401c0b1003e00460700310a40d9031064200300c2c140c940076030015804406240c0c44411700704440d68240007401c01035004070b54441149100b80c11130003941e10402100c945151030098240030101e00c40f0103003814203a0500f03c1a000401c03819064505140ca80e0003350700c06800a003012030740c078a400007130380210207070303120309a8801d216135044481c02c41d0f2030b03910021402d040c80040d145040641000401d42c2d0449260725000001002003030850307004c428400980108040100319140c0d0501c00c450041010707001a1143d02d10b0142d00340c0c1d41103041203010341095125040030060088550403502c101c900110204555a036904d4242e4030360070000c9050b4852441e000202d40030742094060000d50602c02000d40c900c03000028020082e800000e4006c4d60169424861031000004840303081c1d0103404540c4610b0031100381c1c00c80041c181c415026000705418014400d0059598001058802840000c102c19609a9440d40071480e0300c00a000280d038807d0724100c0004180b02c1560040204900811465402d035807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 524968893 1250 524967643 524967659
    0x3180303080f06130f060806154603050d14030a02070f081b2a0609010309020a03080a09091104050603061f0f09150f180e150a 56
    0x501440040c01081080c80000d00d90858061603d610020050460342c144008203001d0303007110341051a81000658409003801a103104008013640003a4054286480c41541e902151500080c00b580034035040c42c2c08520348890900d041505480c1000500070b140c400c0d0644148940d1100030b01c4243d83c0c134000c881c0300200c580c1c030501808040100c2c00c40b0340361858440f012072100a600940313050b20462140215180040e4050f4010440b08000100e41c09518100012072810400880d241c01c0180d05031042c000924104802d0f903014a4a088078030b55106e81031741c00180e015221354000294040b920513400320800c01400301070020a4007561b6070ba0344507a1101c29100455104420041c80d10100384810400c40c07511400655101c000601510070f07108030998020781e1440309004000200c1c128500380b082141d03202440c80001c040740806007100c88204000a000b00d65580f18400c1000301031031403035500640c541040720040103420b01c4661543f4010300034411240807450100d114104078900064002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 524970143 1250 524968893 524968937
    0xe28050d0f08060d031e03110f030402010905011e0c1502130f050117060d06020c070603020d1413140124090b190e060d0b09010b030606011b02010c05011409030703 72
    0x5c3d81501c0f00304508031582d007800d81450040342110200b507100c2518402c0007298002800c0341503040007989440b81454400908800f5494115034100203120700107242c9401e562041710321058041c201600d01e07052500f0210104c0040d0060118503600001e507007181303965440f0300035085402c110314901c5140e440c0c800450320030f0b6086802d00f5040060a001c117155141490130012018842c1600624001529a0180c10710005500800100b980801c0884141c4681e011b130240044d100c41c48583c65140103035880c1940e4121100180c55003e10648981442800754060600342103454050300d5161016000b140d541503c9020380340126003070201445032402d000200031995003001c41340c40103203070500c020715608000040071150702c074060801d5500071a141662403070180c9511070000c1014450380d42072516007440540881d0400c039000d8000e013110b507038400c2151140d0303a0900e0880030042c554144207000d445628034510300445003001740003c0013030000081100e0b510a03200c20b1580c034040c1c03e040780f842c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 524971393 1250 524970143 524970169
    0xf0703121104082d070e0901180f080a12020d0603110904031e050405060a092108030610031d0a0210081005060a0215040c0f08010e28050d0f0806 64
    0x1a8010101d40c031840702d000303070082202c0d40c07111841044c0b0703040c0440091500411b0703401000c0c00f1031a9400e02201140a0148042aa4010410b500c1c0302e501ca560361701d100006408090445c1c5008142c00141c64415440c1c407400f810419401d41d00d40307600451ba80018400c0d0711040b240001c10808040b01c0b800c1100c1501d100b02c5d007644440707080e61070a4111074028150800c24000b000b17001c00004c54181c0d2118040c041070a51540c4e00450700707007485c880e40c07a402e5400140201c20111071003c500014105022a41d0103080bda8007603044018651007034014201c01e0303000a11031000301c000a00c8290001807500c4059008840140c42d1a15208086d40d29041c2502d641140194844051140b420b00740010002e00302c46204aa040d42e00030303110300001460030758048404040700781d4104802e002071184140642a400300030403010010400859440d07181964070705201d003006204500340c00720b195454000e103401105458194079109801020704c00c107030700310101041114000c42e1040c200440e4407201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 524972643 1250 524971393 524971409
    0xa020d030e18060f220513060f061a13060e0604030b040f051c0f08041a090106050f010f021905010b12010f05010f06023c030d0c080601120b060f0703121104 69
    0x1071001d031058080c000d00002071001d045040310784401d0002400c60f2027254001100d204000404600b440f4234500c43e00c0c0c0003902d42000810034080604203000c0c00d0a44411522107007401801c0c101400301080e254010342e030000c0c04111259082105208603244c900002e54822001e46103104a101c82c40803050f04001241c6001945500d40c1c01803003401080041c0e0064028105101d16401e01120a0b40d1500e04581307841e983c1e51144801c0189040001d51080c2801c000d080183c880340800100a640340307290b040c2e401002d08401007040a2200c294004080b03403502400300c106d1080c0940c0000c1c06070410000d003040c001d2031b00000092040c109005002540e2103076014041c048100c0c41d007068459040000701e0f802c591440e036503004500381c1c110340c25603412154000e5512840320303408050448445680c4901071115000c10401c01d81e034002c030382c00d000c0c410034080022888440f0b0702040d81400b400b112215543c0300040d40109243c0c1100d054000240640010b0099010a010701c4055000d00c1c8030310f0038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 524973893 1250 524972643 524972689
    0x90812011a07200d050c0108060405070e0d1b0e1503010c0509012610050a0e060901030807030203070501020f0309100908090d0615060f12050403020a020d030e18060f 73
    0x80c070502541e00141201d80c01400c0421102c100207084c01c01e00c035008480c00ea0046502d001c055030015030040c0d2103501104c040081d49404c44018000104240c10390741b20307880907065242000b103660045600c0c02c3c072003031000d41520f8440e418035950a805407649051382036181c9150005180500031100c055441e655500d00b00844030006540300300d01c07005902240d49258000760b044840d00d41400b44a090440c440c2010989400280429092540c101c800c4054081c410890aa1035a0b002da0341141e9001200c90b9446560341012400e5008081d00200207500001d20351521000510156006070441e1059071031032054201d18004450901d00001c2584000780310b8054a031609407810700e0307464054800858850710f8221641401000342d00002c0c003040541d010008442c1e800a401103017080e0301d80b000c010606140e10007a50312503100400a114202c0510703c3e0003003501c25005c501c445400500740701c0c0c010300c03480c2a0440c0000c08071071245c0903c0005c103123071800780b41041541d0b0402070380c541000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 524975143 1250 524973893 524973907
    0x160302060f03060117070206150301140c1317030d0b1e19030b010305031218100f060503010e0a1509030e0d110904030e0312070b0721090812011a 64
    0x100700d80000b0b0400713051001c0c0380080d0440c1d031500009079114030300e680d000e480b1524080c0d011408170f03200f00d0300c114000c0e032500d4140120940c040c1526034011a90a079919181c95600c0072002200c185a048001ea1000c1002100c11000001019142e11128180148042454003050050001092074286196500c003241311ba0541010074030b0100c12680009032794003260700e0307445500b03100c00203a00440b0745500006e1b400c1401d40341c4014290300034040700902000d1501c040c010f01d50755a4034444000102c1c1d510900110352900c981e101c0d40c02400c1c00707030081c00000795107120b40340c40d0a01c045050782c0f00da40c94840503035400c10502c20b08401d607038152521000c603403188003480074004201c0340403507020b0400d0400110913030f02c0072880c511491003075840143e51250b8600340342c01c2000c2d4034000c4603649030a008010014011606441c0d20402a01d0903040140c0d608010302480e0f0311070741547e8012031030b004100040c4541007004016040004a511501b6640c0d0b00303001900441e804031107420480180014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 524976393 1250 524975143 524975167
    0x806010f05031f05151e0705060103170706330b04060323040c150c020d02093706050a0b1c2405030d02010b01350114010216030206 58
    0x8401814060007020f00340300d449102040700d0b5090200d808000340700c081441190301614042c1c5489694000101506110556031001c0c3c1c2c492060000811442d00041e10011514160094601d000c0c0c00c07c805100707040d1004a100da04851040c0003074640d0020561107001404090400c000303d55501c281545040e140c42000c074024050074650230b68081200c09030109040c401c1c0c0100340074a001c2c0c4d20000409182010291018088422100a02952520381ca0250780e4183c428154680c041d42c1540541d03807500b203c1a40440100f008020801c1c0540100300b000c107243c80c0f501441031f14844100b2060741c0340d00070001e940040748100004c4950411105d00c0200d083c42c1c4d641c0040300b1121000c03a0000071203814035070388082140c0c0100700d00101c3c0c00400c024034040002888494050001700043c6110310002810030909407251400001110303200d50480400c01c242c0c80344c0395074980d448007081d43c44000400c02d440040740068014400c42d10715009001c55844a6000c07258024881d524085141c444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 524977643 1250 524976393 524976421
    0x20c030a210507080f041e0b04120f050d021614030601030210050d050c0706060509061806180901050709150206010608190c02010509280b0a15090c0806010f0503 71
    0x101d001000700030b225150005040c42e001e451940c4480704c2da103484600304654499941c44140d40c010f14007882c82403c01c440041d0901b1601584e81c0151004003123501402c04c0c240c0f80d58020381c0209944a84080900040da012800070400d00e02d03605001d048591b40c44982d008813000c00340040e8103030030580c010001443c0c8042d0700e0803e52018140b690400300104108030071070714100c815511718080040c05000700541380c401e85002d800100d41c42c4d0014105107010030b10800100d10f440c11030403441c0c00803030702c00c0d51842c11035503c4800801d002c010300e140c0441118003902e0107540c00341c00302c3c2920402141081c45e081e090142030b11564020482a1310300141290707020700140c80201c4005030321080d07010482c900d0040405808c126000413465041c04100c0354030300904a11042e20540b6000015050100248900c040d81c0d0382040c0f2000c40350325140d000c14020f007900000860995603d03100080c0034401500107859181541d10303034916658402c40152460704807400c19100040382040054441298518 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 524978893 1250 524977643 524977703
    0x2c090c130c270503070608040201021c0c060b011b080405031603240b0a08031209030f0d021c050f0a050a050f0a0c020a02030106090212090118030804110907030c020c030a 75
    0x948000b20a43c0c51022a00344007160304220000b0321180100300075542c0400c115004201d010918403000e41c680200106014031840c001000c1c0d030b0b242d05603803945a201e22001a621100c3e0a41d94829400340e28042e02d05034024883d0702e0003401029058509218000300c81000c484d0010b061001400b00515031201211441c0000340d040c0340d60f0768000c90582c440c00001c0000c0c00d01580190340d108040d010740c03920342d5801040b00055a10400498010100050a5a0004190703200150302d4410b08070500c09040c1048096560031450f0008010f035000c2420312150180000320801c01483c1ca409000c10184c810485064841300908400305480700296408114400c40a10544540d0380c4180e000909407040c5601203825290003182814200d22000d200c590402006802004900d40100c03a2080740302c0800c1000e02400040c1c8001000d0041880045d55032a0006020854030300c1c05a0000d001402c40c00c501c20010710629403114164200056401710310340d00685030025440c0070100011120349124 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 524980143 1250 524978893 524978957
    0xc170304021011030412030c0614013501050703020909070f0806060721081b043006090606140904110609011106040606150c03092c090c130c 62
    0x1c0300103101d1902d11358151b41c040c8a90b407100710703d201c42d0504800707903042c041400307050141c400f004000307164055605915190140c948022899014006102d000c0960101943c255080c20104290715a050f030051564103c01c58410b80c1684400c2802c44601c660074910741c011414100105a180c0703070410140c01108d00c03541c0448040000c44c1d0010b40c1d60403145410801080b601b200340301d071803030340705110700800b0b160441d80d1803c041c50244c000140080c69030462203e0b414810b5803040b45200c2c3c200c03410883c0d0f00000140540c02540c6044002005140f0038201280c688058040c018544001d00710f006603005440c480d5030029070f200f041510390040300700130705002c3c1c1e0003015400404103014480c800ca0007000000348040c0b0780482c4c10103500c40388104000700b001b4802c5100c0000d4001003a0f40c1658500d5600001100a07846900c080a42c4200c0300d45640c1c04100800854000004152007402019100d00e08854040c080444c01e540e039803010000841c082e03001a00c0d0714289100b071200521040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 524981393 1250 524980143 524980147
    0xb0907060e15071b0302030c0411030a020327100501050a06050a030e0c0a030f021503040b070c0f020a091e020903070302011805211207020f0f030f010c0c17030402101103 75
    0x940e82c68000004540800e40b2200c0074003405c005610302800340e014a03070b005460038002c4542d108866007451000400c80e602c003d501101040030354080300c44c180f1500b9120301c0905044600d00c0c001913510740c0c0d030100c9040751034107102c0082241d00307040d0440700031a4842e48031903041c403043c2c600540207030840700c2c4d4890540c4505440c40c00f083c0c0c1d68000c001e00440c0911075426403541d0034010b1010b10b11010b1b0300c00300c482004006102c0091088581158003030300c14a00141c4001c00c52174136400c1140340400107944001c5100d0f0104504440754020b400c025000c4141c040b81d0884617428030b09074010460f55552503003040d0340410240d400398032180c0b84240c0400302c0380910307900c0d540000ea050141c4580b0350300d02e850000b4480e42c422400c000110b807244c482c3c0003c0342001000d600143c010203072444858003c5803955000d0350180c82c01c01900d0700c00e6008200034001c41e11021030090110511840649582c40d4280c20502002c1c0c48804aa0040b82c001e0f165524110b0110000d5a404d207001c13040c3c5542e4442 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 524982643 1250 524981393 524981407
    0x813210b04060e070902090a0e1003020d0303090b0a020307020105060a0303080c0a030204050a0902130b03160c0812070e21030d0b0a0e1504050c0a0906030b0f03190b0907060e15 78
    0x14000a8045d041503000140c640243c40180800481960404000c18140d00141300c000d00d000d501c00c40c201c95045810460801c618901200a00039842c8000d140c8048201480b043e81a50f40145d44100081d9008106a54842082090f2605184006000f14103102c0110f101010075100401760121a03040252529035204040340300b00b0321652109103540d0380400d010308005560541080100f11004919046003401442c0ca20100c1012605000344100c20060b04100700075641034402d66005041b0002c5240780030381c009000c41c03010b50656881a594021100d0405101d01d80b01044c0a000c0f80c0110f080071174018084005181c0c034052103911285081000650000030040700d88034819400c01000408108070030b0009944e005450444c0c4d112080c0282c600c080d51088048045404500c2d000c11200700348001304079202451040c0e26003500990310a440c2c403548290311151003034460b0310388030115078400d65140d40381d501900a0b400029401ea8120740c184c50b12a0f800002d400c89003070280d25000c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 524983893 1250 524982643 524982671
    0x80405120c1e1233011d040f0f1202071e030b0405160303020102040e0c040819150c05090f060a17060310020408010504210905060f04090204030813210b0406 69
    0x4441c80f242d56045400c000c40003200031211442c0314521310b1030340b00c400003541852000f100342e881480a146031003e445000070281300541c220280c105801141481c01c00769182401515051880c4124000d4420517a0014122808282e141807610302207d869802d0b034215030303a230812407002800039541c52003810302030000000e40800c403500035440b079000107a1300e07031903d20003034404003005000040140c0240700c00c0184d1000451046510350510401d18800e02c070354544a40d102055240181005e8a440210704003550840010000c1000c103c60203079041c00c0040801104d4428a241c60000594050240d650040c40c46500c2da007051008003500c5c403416820032114201d070020362103090705a448406010a0080044506000b0360803204224502a1140c501610150651003454001c010025071108504500c80a40e80a000c0d00e820940d17490b60b4a0030300002c9500a0048551a03d074a10300001d800900038145084507d40f019111001660300c1d100c01c04890002803094620741d031281c440c0703a4100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524985143 1250 524983893 524983903
    0xd110301020a18061b03030c0c081303020a0e04080702061c2309060126150702150f070206070305040503070b1f06020309130209030f0307080405120c1e12 68
    0xc8441c0c0d030340d00b61030388800700501190389582d120780d085c000d00c0008921040400710215201542508000c41c094001d9002260040307550f01010782455004191030394191617608046089078000c86040c03881c0c58450302100e14001003035400910b84a020400e038401800e009020b80880d034100c4c40e490100000b580001b01c140e402d00e07160880842505407025036401800441190080c005400400b03496044c13241c90f03210150070746100e62141000411a1085603020803440204a00c0c41600e0150b60500c400c002c0e41da20215080b8442c1420f00a001622444590b00958440c07145640141000d07150b800701078000341130241007591603000810000010460161846d406464801211030011460482c2ca240710403032a004801190004c12101c1c1c010b0340c5218090100400300300340180e503243c41d400080d140c0b5144000f00c2c40340c0c1c04041204400d0152601c0a80300311002910103440e20300034464515100c80401c21801d038002c0d0301a84600d00340802c0340d000982c20101602902243d03640c00350103440c03c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 524986393 1250 524985143 524985157
    0x31505190308070c1802090f010e19240507240920030f0a1a0a240810020910030f0e07080a0c05030c01080c03070e0a14090705030c04050d11030102 65
    0x184540312040090548241c00c02c0c0710320251710310441c1080c844500099410340790103a03840c10003072512445106543d51034421500e034840900da26142940d5902c10200a00300b0307007001d1844411285445900c075008004551030a03030b000150900c0388002089a0b01c036030800700320401c0d0081d55030342c14800107040c0c5000104030780080038494002034a03000406240000002c0c1c440a240c10202c1000300189403134543e6080b14084c4032400100b5520384114100518070b03900360b50004403401881549601c90080e054044d100b0030720903540305219440062060f44038011360650448401e4805e024420310a5001880080342d4400114a0020391040240380c000381e904020780079003010703483d0001c100110aa0000801d01a400b401080030b01500181c9542401004800082000000119120b214034500c4410788401001c240195071034016206560403000065030081c0381000200c0c03602e40c000d00c141e0344a804040d54035490107003408144280701943d207038101d5a046031804996080d54080c0040c14417 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 524987643 1250 524986393 524986403
    0xc0a260408060406050c040f0306020c0a0204140f0108060412050d060f0906050f0301060605070f21050703170105030d03090804090c0302070c1208192706020d03150519030807 77
    0x410300f483d062110445102904000340050104020000d51440ca03545404882e0041c80c0141c0b290340c2c1d01074042c100413000d20002d40c450f180410b08140580e403c00018020040340d01448040c0e03890340c03041a55000180c40103804072507001081c1500e284508000c01e0100d002a1000c9140755540110014042c01c4c2d41161040d0398680100303200d14203150120840b500b40450083c0700b620b142590140080c4994103002c1c00794001521181c0030720a0008203200005207011801a08111000006000b5040031000310b0003e648203445096a1120115690589100401404100c103280304140c0040001a1049480803400c0c400050b60350700c0d6100c1d45818410a8402594a540920304181c0100c0f032a0000420340c80d0920b818008a446001551440107003607002d4085404c2211f8203030303040c920f062201843e00140e0310100c032000425582d00c0b000c0fa0b45c90b400b103400750404500190156104003034550501180354004010501d010020000c80002c445221001e443d00c0e034507140c50980c483c0d0001d4607 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 524988893 1250 524987643 524987653
    0x3080114032a1201061811032d0a2705070501080702010618050405010b120304030f060605120f01050603070e0f1803030103060608101107060906180311010b060c0a260408 75
    0x861b05100d1882c1e0f407102440e0319010082c0b0b81103a0b910b490380703000240c0444406110035a0410812054180e460103d80000b0781990442c50559601c4001c2c2648c000d50800d420080541050109800141207611642c02800380061303034203200c011100401c000b854202191340340d00c8006180048000c980d0120400000046a02d1505080c00c6082d15901c00000d40550000d030311031440803401000751026a64008806c4545206504000000c0c20301c54201c2030380505803100303c04c2d1484001071041200c500c1c4034001c1c8a2a0303503071000c0684510452143c40041581140002c6442c800c010140341d01c441804088952120030309a0a4076540098004643d6207a03103000502c50440b08000c0840c0d45644504d080c4132281014107484140d000321280104440d0711807901c40208081900b00800300321199140304c12100e00d41c1001080001e8443c224503080d480c19903a0070407820444112141c2e4507800703008000000c0ca0f50781d80030400207030203150928109405d51400c002140c4400070001802403500901c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 524990143 1250 524988893 524988899
    0x1119050109020f0907080f1f0e040c05040b01020a0204020f130f0e150d0f0f0501050a0b13050708160e090a09050f0f0c0411040302190303080114032a120106 69
    0x41c000000c07103803d449412500c0810188a51019003151322041a400c00091500c0b1a20031120f04810030980d094110744008002c150880a405202d110710300910095031520303614028030086a4190708054010b030419403001c005410290004e020000702d650800b854170300e10b007440c00510200c0d0f03003002d0100c0b0080c00d0b082028084078101c1613003103c1c0165018a0340c012420010f5081c0c401c0c23105c011b10040d442802001401016200501c01c141c0001c000e010918100d40714000500c040c15010b440350710560100900342032948140c6204503d152224802510341000742c0c4062083e0500240801c040c442140b0400d464034083e090140000e100c01040c00c090314900641802994840c2d1407207644085d040071012200000d5152070a241a500020460801d40da840c800c1c4c46203400203508010104040c1d00080144440e020440f4043e55801e0500c3c0d80321005174072a0500c02c00910380c50781c031104844103403030280c6e2484500f880d10b0a1134109002e007200d010408070340b8421140720190b595100e0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 524991393 1250 524990143 524990149
    0xd0f06061706070503010f1404150b0405100503010503060c0306060d020a05030a05060319120306050a080a060c050304030c02092205010f0c1103040b090f0604090501260c01111905010902 82
    0xc1c5800c03c0c02c504105003158101b21500760100034520495000070002800604961119031241041c40200c103e25280f81b503c61f07130f114849a1042c420385000d84420041c0b152514465401d85c0d068890080c0580340e142c44400041030580c001500b030b280e121408021185c032900340c0d44010a840082c0d41c86040e00c920b405e02c0030f4011a10000c0c400750007504051507030b100c01601c00300c100f480075a00c408507021108040d84128000c252540016030411210b050104810100003000d1050034414003051040c03605100f000c48240c0000e55000340483c0d10706170541d00514100040e503a00c40d60400c40e240342003001c809142d01030291400181c0b00d0b03954a609180307201500e03014090b1b5500d06410440c1c48803840240c80c954906c41e512501c0241075002c00c00001664a0300004106a0f8005100585a07501c810805004000a120f0a40c4508210320011400c41c00312035404040514240a418420002c80c01910400804a1307256018000e0720015804202124249443c050003403000084848041c414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 524992643 1250 524991393 524991403
    0x5090702160f06020a0219090603051c1803060e031905030412021207020103050a0608060c221409040201090b0f0a020606060c06130311060403110c011d0d0f060617 72
    0x39115550805400f40a4640c00143c40e40d03103a84c0c185d4800d40d24a58640c008400d1000c981c0005014901704400003040c002c0025050b912036140c0c0c0019125070b00803c1c41030b140031140840385111560030030402c001183e155400400358400030400d8914014500e00c4241c00300c01001c000c840441e10110610051002c0a980c0c4403141800c3d0004000148286150340702a00500d00000c0c1016210f90014480001d6034100c500204020003c0360030500b012130310821280c0000643c1000300b40902a2004070446e100300c1c081c100c402d05114081110020340600000b0400100b00360b060156002002400d0b5600c48000c0000e0911a070a954540c00c000200900380100500041e00c00c01e018040382c019100d001c900181c000b00303901c0d00011010a0703454241d80d4200a0781a04295000719001c1009154018102407101061002903420014a007401034914800c210017800000d40600748401c210b09000700c0c9900c5a6004030310300140400300c0e50b1600183c443e9500844445d03421000841c03040c02003004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 524993893 1250 524992643 524992649
    0x15060c1c0807120608030f0d02071205070308133c03020715140d090f0b1504060e0f010303230408030703020c221a060304030c02010f110304050d0302070509070216 72
    0x130310039645081e544996034002e0b0386802c0c1d48001d00081c03a442c0d4440560442c3c0301c0690203050603412a4641d00082c00740c0d0403052050b0042001c203000101440d07807443c21200410382c01505000306103522802e5042c4041002103c4480d072140e402e41c0742180b0b24207500150038a10940c0144682802c1c1640041314203155010f103801d10140b510b444503150020341c282c4031000e0030038000103059070f140d0030000d400880b011405040c4050340c1c01031020000c03100300c00001305582034030140f080c00d9950a120210141c1122415000301c0810014000a0b20600c045201210519140103440c0d4070583d0f03400d601c1e803140e03200700701c031b0b0b480021030208054041c0140c9030020012600340c2c0002c281c020f150b0182134507580c42141d04c079984200510030812105d078102500380c0d000d41000c1e1a0301d0940b502805001c03c0280c20b070b02241b02a0040c3e10407600c070780c0c030300440441c44401850034540b0780003d000d803003440048102c040d0301a082c07000c034494541801091061585900610b01d603030b0403260f4103d9221a0b50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 524995143 1250 524993893 524993927
    0xe0102091c0521040503010614030a060c140c03072a06230705030307020f190605090c06070813060c1101050a0923040f0515060c1c0807 60
    0x8014019241d032821407410808460003000d110714406440c0090901d06161605180c868034020072408800006014100342c40040c0c00800c0308980b90940714008480300c0d10340d00d034550300980c80c9000041c501d0300456440105c40c00c0c28524078001d1007820701517802c519101100c0da40049000f070140700d03040d80c24900c000361610390180c84020005030903040900b14081c000034004055400c07002010801e09240348849402280c503102c1400e0310300700b5140d610a0703410381d0061040b041d00c0030b0300311701c0420501603540b20a80c014040ca172083c1e40d804003a0500801007001c5c0d000d510440032040d02c611008013041442070340f030281d4601041407154030f403d03a41d030000b0307003042a103004050000b076202c4054000d600003400c0c400d40b00c1e0f00b6038400302c861b2401034111450a20440c40c4483c04050041e21035841080120713000d100100c20758041c1c83c01c0f1b1b00c007160382c02d00f4100c0d1800031484070308003407006180d400e00107019038103e6140c80402e03902d800e8441041c000001ca81c0300800c46c000380d10204108180c0404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 524996393 1250 524995143 524995147
    0x1020c1002060708040314071a06010e060d0b030703050f0105010303090e01060f030b0d05120c0c09091009030c0503121006020f0c1219050304050a081c030b0f1f030e0102 75
    0x180c20007955000c00820110511a03540042403d03d801282901200b0880d020341075610555483c0042c0300508500c150b0115070303039540c0418455806024104400380002d00350a0070221141c1c00480030b00902e01215406008105000c00031550a000c8050062080c60020034103503d14600100020140c3e4044004062600018417640c1d80c0614041e4a072000c0c5e240100d2130240280001d0001020228003c0c50f0f8070480820000602d500005002a012540c040d80e080210f004203000c404403040f40e180e11260854062001c070001290b00809140f070081c582148008001d513103051031a13126444c00d01404055108121415030030300b8480d0041c1020348050b0804140320302e00603030394031034010780c0034828410040144800201086600500361100707220604100706402d01a440e0b600500071203009820910000c148050000b400011384070040c80501c0c0d4844040c0d034110000e140810189a2201001d00b11074019034440700021100769401c0c04615400c0e882c1c1700054201e8a485001500356401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 524997643 1250 524996393 524996419
    0x21507030e04051e0a06030c1401020307080a031e1b0e0d1709030106090e010516020a0803070e04020a02030909160906110f0303180106080102030408300a090201020c 73
    0x12112048040340030659001c12281c43e10b91100440101e4044c0c410f4050031603404004500c0d1858003d101100c3c0524108008140c8400021410268020303095025074801c0280c480001c842d0b000030702d106059480d00007008a480710f01e030701c205080d100d43c82d00042e40300c4071500304010419141d03030003081003420701d0285203840300d0120352411118000900461443c000030b04c1d070038214108844003c18010300030024207840e807440000400c51410805499840c4c0b03000074442c3c145140e003007513915041d6002072180114035681c6401d0f079030008181c403040119011081826445500280003000125005503895000050a103c10440e00510a138040c1041c500442c101c1038101c0c0162040c0c1d4a6864941d00441c1c030000020310300440c0709a030840c0c610001040080d03030000f4441d11501a010b85000b0300419a5801c0000c2c240d010079500035040107010003d18181c6041269040400450599188030f80c0e103095061240c1440c00b100c0b85101141c03252940c9046683c10300c100480d1000c100d40892540784 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 524998893 1250 524997643 524997647
    0x30c010501231009150e030d11010b06030405060f0a1107030809010c030504111003181a0c0a090501210615030f02030c0d0207020d1220011406040b06040503070f0302150703 76
    0x44a817054035480c14004c0b414003401032003140122140030703000e0100c56200c01015401040e130780d1050f00b01205d6510f0a99048068a880c00c1103c0c0100d400c04000e090750380721900341c0201700741e01504504103143c1e545108180d4140c890f026011690007a10740224a00c1c20b520361900303441c100c20340c41040524007400c020026080fa003414020410541c2c0784248001289401e4008040452015070044110a001c0080004424281c041d80c0002d0800b14040e40395000c1101b014012510044c01060600c0000d001d1075104244001c0d1000c0e2411244d80104a0340c0c2040c0700312443d81e00700d2410520141c001c040b120f0307050b00460800c0c40792414118039600d02000030821030f000710030325507200c80d40010303641d030a543d07030422920100c54106103007161001490307034041c151650b44281513124120600c440c242c0203006203d007450030503540154500d640c2d984020400280307401c107911540314030309000100e0140c50402c8100d0240c440e0345e03a401c0c0c0b25401d41c010004100601164540c80790f00401141000907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 525000000 1107 524998893 524998907
    0x90e01080105151503060d110904030909050705090d02090402240d050708093f180a0302030d08040206040504020f0307030608011517030c0105012310 66
    0x229030410500103198001360015403031000900010b1080e04010300c2ca100c2d103038030554200740c140c11403100013a082e03281560250000740307034240288500c100c284150768109925080c02030402c106000012000c01d04014001d014801600c04501151250001c084442c03000d0000f5007000d0112900da15500d800c00c070004e24400703003440007003030a9902a207905405011094060401040e50740103207040ca02500caa0b5051140000039102c04a00c255039403501807402030546c4a586240c0743c0b16a8090300c1c0084601803240032070020410040c3d40001c2c40070490845420407903020b5a560000540c2c5018a51055800ca4000502544611051401184144100d8030f04101c2951640d179024200c0b8820060000551420030040c40032180f4000420002e59444003103a240a9603050541c2c255413084c0d01078492105800e68401076076550110143c02d40c1c2040c3c1c0c00802c0c0b4617078000020711003 = true := by decide +kernel

theorem cover : BRFrame.Cov 524820143 525000000 := by
  have h0 := BRFrame.cov_init 524820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 524820143 ≤ n) (h2 : n < 525000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
