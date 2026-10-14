-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0444
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:50:56.549917+00:00
-- url     : https://prove2.me/submissions/a10904ca-8521-4452-be7c-06efefeb1b53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 79676260 ≤ n < 79856116 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 79677510 1250 79676260 79676269
    0x70e370b0a0801090e150c0c010b090105060901050c0a0804080d0909050106050a03020a022a0337030c02030d030b040b12031e0903060a0b010219050615041b021b0d02 73
    0x703041d202d6980c1e0000d509000013407403510f803801880380910381e0202d40d810080c147c007000015080b041c0c0400020f00c60302d51182e08004103502c1c240a410391052041c0410a4954851405080308000c003070100c40580c000354458140c01e81040d80400c002d0b44c082040940081e42c05076914004101102d4240115410200003a002c0d014991180c3c1c10103901180303550b0018400c216203981100141c450700c591021396111141c040c0d802d84445030203407040c4020130040f90215000d59003400702d1030a8815540340c0084c4203001c001c1c0c9494090f010400f0310710765407000d81c0d800d01903074607410303001c0d02c4c00a0100540414402a503820f40006071051780e5200b51408a60001700842d1941a40105024100007902d002d19207240900342c0040e03003521842081001e41629540b08072090340b0240c0031225204401a00021115404080103005400900104031000100200d440e20304100400110b03580c0482c0310b200c00100020a45540164880b1041c0300380e04100364a0441403140990310007903038405030340204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 79678760 1250 79677510 79677527
    0x501050a0c0804050a270c12050c131403070806060f1c0506130204060b131412010914070b041805040f050a0b0402100c03080f04060608060c090a0f030b070e370b0a 72
    0x8c050b52502c07040001e03605001742c000c503001c643c42c0502c500450764070b070642441903a42e20116107000c2d104025011400c8a40041c84038031440c0c00070a00500c2080e20000d00034550041044404420b2755080c80400080050082e107110b21000303032a205420007103004000a0f81d10b954010040c186007081800d044070207844070300302900e220110075543c64001c00c0216414107920080c1d4050b5520744000c030010010030318581c0b010518040100e5450645608500215100f140f1a1078801c0084054000415010340c0100c1d40c03185c01204236445403803050f1185030618084d01421540301204004000c21458114050802641140380803504000203540c0030706001c2d0007078100d44102240303a00003420421950080d002030840841076800e0360500c60450000c0344c104c51450742c8078500000011584d100420000341c220f98100074121002d842da420700307486032840802841d03001101031620300d01900c1421200091204150501c2e000569462a4030001c00d5541c1c001811002c8200b040d0100d1a901c051f0740e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 79680010 1250 79678760 79678787
    0x61401050f01110c060c010e0106050f010f0c05030d11070204050a0213050405060f0a06020601060e0105071505041106030c07050105060409020a0303080c0715020a0e03070501050a0c0804050a270c 86
    0x10b03c100710341c660810791034244801910b0398041400908030f40300110640103915440f003803200038045207881c0c03010030184d00c18201d2041d00050b00c202421041030f220300790040301b590155007507030700d40202c6000710002e45038454440500540001442401c5007018415281d000108220460410000710a001d1030803c107031150740c0c0300d030341c0303510128900d03a0340d80c0008103c081c0d004000740301362581d8100180d141c401c00d106840c0071070b8135900d54860f2540600f0480312003030b921421000e071071203401080b50700505000c0d0040d2000ca10482801071350713896100040d40185610000640c80301c4461420909580b0020001030041c0e04200c154001038039140d40f8503094039818140841c0c244c0d83c850300340145000c2d00002400c00b40c14000520b031480d00030b074000c244801c0c3d9036441e510b05030500700c00e16075942c2c65446254009002040000c20303a500c20b40320344c0030322841507103042e01d06079440001032080740580c0c210692111091003150010000c0c02212080000c60010a01c1400e60022014001601b03441c803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 79681260 1250 79680010 79680017
    0x90a0519020c0708060709080f0a0f0618060c02060105150c06040b1e0709140910170102040305031809091504030c06020c15010905071d060d0e060c0304061401050f01 73
    0xb60505266020700c002400b40c2008812103000f4548101d00a00803911031103400c40b180141c043d0705035401c8001c620001401d8004250109140c0307550303500001000e01503241d108007200c0f00c00303180018a80b40902c180741c210030340c018001035042c0400c11130200842c1c14948042002005076540c0d540c008140d495101d0b070007250383c055540d21140c0541400f5401461681140c48110402c0720b060303080070000303095a102041c5140da12580b4410300030305040a440707407140403828030020001c4100701105000d41d118490009410a5502d5494038516042690f5500c900c0b80400107400340d604000307620315803000d154002031041120315440c2e0b48442c000a4030140c104240348a1003020b03c2201e03011100d8116001044030707402681005003140e0a0000e02800039100d0401d4040b51082d881102c1e241d807941e02400c00c000c07921080383c00300a0964000041d0f045d9070364503201950401c1c0004c0c400148075458540300700342c3e6840e1501e4004100d40901c0e004450388100c140c018802038440c070080c103c030707200c081c01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 79682510 1250 79681260 79681267
    0x10030f03180918020d051f06080106090c02060a09141e0d030605090705090114030901020903060924190e030705010b03011b080411120a2001020a02010507030e031b090a051902 77
    0xf4060700305922011300407401f519000143c0840361459020208840340c41000700f1986444480c4901600d05103601c500c0140d00c6000803607284109640884a11407281311100c011200d0140d8182c24050000701c0c00800740e1000c0000c5010300300a000c1d4000f002158941000070038105000554035200180c402000c1000201d078140d03032640919100c8075001019006140c0340e1400c81c007035501075170060ba1910b01034010300c0d0115800002c005060f5011443d505000c00319414481940c80e20418001e00c1c0b1303540b041c0e91806110075000781e40301d8140d0a800510242d40c0e80c590b981005425143c4000d185c5d0301a81c50201040c0999080c0015104802000d140c90b501a48403414a0034078001840d11240d03200c440c4119a41b01c1c075100249600c00c0a01c41c8241c1500f220344411110490046103852a0158202e030112600640c41480181141032003030034101c0c2c0c6a480f140c040b0349823400c0488a003100d0200c0c09606203540c07a007240c00710f600451901042c4103900d0100340740350703401e4444075035140b0154022 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 79683760 1250 79682510 79682513
    0x504030b07031503110325050f030c04060807063c030b1521010308030109020903030d090c0303081f06050d060b07060f051602060c0310030f03180918020d 68
    0x203410080050032000d41c0f190109850f800d09000c416000000d042c402e00c14444c07903e02e8241a0203a8103d400c0b4000e06045006241c20300b4010280b04644420f07605000308040c50242d91703a5881504041e1820b030005108041c14801d01805142000448000310400d170440300c0c4150941900c80054a81c081c0091241c010f1111000e03000341c9000c5048aa000e44803902c240c035503008080103031180d1009442080d004040005001001200a00001e4000f050806c018000ca4003540c000b4014050003071708a034900f80c181141c11080720b0101908a96070b2030001c4013042031682c02060203402c51903803110071030300040b23500c1c01104108942c402d41c810b021004c6000640091240e101d1401800d803001025501c40b05458000c0003030406000700411246010042844c00400e0010036211988540040446442e01500004c640d00018151401c52000c80301c003000240b03190a500400c2482a1a207240e030302d51030340d03002c2541c400540001d04902c0c03801444000300c250f40d4100c3d0418507010340700038074825003d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 79685010 1250 79683760 79683767
    0x6090309010e181f06090608130206071a090c01050301060e12100f050405010c0801030506070507170409020d141e040606050604030311070803180402090f130209010315060504030b07 80
    0x3000c0e810f4045070307030782d040028015a1081d545032024001410b000710390740382c1400f540c1d00f800a00454001441c00f0001413a42104100c00360442d60004000764200600c0b80d0302c0310f0344000c80c580c0c0f0b801d03014072b144244200d4020070041c90714900d100f420503d0070356060200051a05100d540304510a4013074501c0d203c05550b0900802280e80c1004405200e00350203403c1e13031000b420042e141101c65600e06145200c5075441004814141c035400340252413180c940072801c86240c3c224000a80b440c44840b0160524041c01100910080c1a03220025841e8041c410480d401c4462203a00180a480742e6002c00c501da810014610350590b50304c054241c0c00e0348603800d09c80001c001980006410210024000c010b00d5001030741d00e4496480c2c00100c0d0000c0f42c413042c02c152070b40140c4408003901030078003010411070300c0c040e00034204906011303007208804404800024050420520f44c803005a600140d01440c0e96414015045422002c00c0899801031404400902c0ca2086d4880500a000b207800400d04d450312 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 79686260 1250 79685010 79685029
    0x415030f1407020c030c030714060f0c03031003150b060a03090602070c0803120c040e0402010f030b0d29010b03060402031e0406060f1e05103005060306090309010e 72
    0x8150720100341a2802c0328020b540c40041d6072080b4400e00c940c0e200b100d890300d400915641507a5698a0081c000b040c12824030100303411450058185440911094044900800156200c0e02480094600c003a1550500f176001d415403401703071002d143c1815102c10b4640c403082c08480110419103000510a0241d00300301c0300070300403210010207806200d1400a0b41003400000b404100f03e194108160f243c4601c4100d002c0c0344140c3c484c4240814a000000300958020456001c21581c00d040100e00311950310300085481c002868211100c0314242090496032012441110222100322806441941088046d9549020041c03d00b807045030008002034480103502c103203424685213001d6071003007410149090b5005d4625800352002c4801c1c4501c00003402c05500c462400078044869103005040e0805090002118020070307024180049009008041c50000701c1200c0004500c504070401d0402855107681a1400078060510aa01500602c0303000000030084031400e0b40242043d2083c5c50307964000c41e09148 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 79687510 1250 79686260 79686281
    0xb06090a0f06090b090c0a0e010e0105040803030a0903020d09050d060207050307231501050105030403030e01061a1801020105100905040c0e090a0210080108030403030e0409020d0516050103020415030f 88
    0x2e0514000081c0c1101c0340d0040c228840d42113410b0b13000e40e07403012544615800f03004140c0000562180001d200c550080445050700c01062421901c1c041d2200d0265145920544091908079610044141495414807801090b401c02c1d18185000900e400001824440108009081e10b0350020b4902c0c1000300c00c00464001c150f100302d00c02c02900c80c10760002108005000b102129008201d0504001e29500d1201410f0301c405843e4282141c03174548085008104265520666641c0e900001c03410900a091117500950301c4904941d81301a620b0301600030140481c0218156070401c41400b1b10000110305400c16151404000070b07451f9168206080a0500d550226401402301c00621000050200d000d40c0d26a0080da108108214100700446104500744070b0f4201503003041c441400028070030201902c81e990000c01c007151221440d00061a100700340308045440b603025101e0341c1c49110011780c0c0a0000d02c000d00302141001d140c4001d003145a100c1300302201c1055a100c00d000c01c01c0c000d03580022001c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 79688760 1250 79687510 79687541
    0x2d091a071b0f0902030403170603011d1011090303030402060f0f12180606010503150d08030a0606090807080304030b190914210a03050c160b0714070b06090a 69
    0x50949074210721100c1514007462000b15184880415034000d00c0c02207034060b0358503176516600054002c04080c140b0b100500621303410b540741c040011410070703a600d2200c400c0720700302c0c007411400110043c0710003103a0100390802c00c3c40400740b00201e401e544c0400ad681c1e02c5601a24102e0761800303014084c400b01d1081d1682d402041002090f90410b071203091000a200b40c0400020300d035003140036280666182c0b02250294001901000050303020100c00d41806400c00c1e0290150302c8860070b0780c2c4c035007070b1030380048034840c981c590740701003c0151070360000d8503078014110280030303084580c01d000a10780c4078403807804054483c0d030180c00410f44404005400080a0381a2a4100b10b441200d10303091207485040d41e5251254803d50300c03041202558036540141421241005d18a0041f400d42c0c2503014041c02030031581c415034140003c0e03421481c4200607418041c03250783c140825150400000d09905070344010b032840e02e40203004a200086c0a0b4032100d8218404442c0341c4840d81d0740340c4510300942515244035451 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 79690010 1250 79688760 79688783
    0x1c0c090513020a050f090601182606070804050307301205010b0a0905130b030607120c0e1e0429040b090603031c020d0504032d091a07 59
    0x5554604094140070307031003114a800101d07a41c0c010084803a01c95900181c3c04180c880c0425542c0d07001e1941c030a43c214155a08a5895550b408c0e100c02c0d812031420249400e1040303180f100b08044042c0314441c0c1c0044541041d0b280d509140c1c50301692400b40000041c201005015500d50303d42c480b03400d180d00111018040911003411500040a00c1e0039819800b0509007003400110f40e82d001d01d410784494800702e640d00b090240c41d1004005900032089264825075585401e040c42c1c6403800c0c016544240805e0b00c8007000d001315004d44008448003981ca00d070400401d001032005541d80d21408100a02d8080341c5950001130203000078005118004c0d0403220f2070750340000390450fa4090f001100131201c0850b4100304052103070382072000424045810707030381c5034104208440804103c040c4148001201040050034122980e0400341140d0003581c0507400304004030b8a080304500c096500d010011810454105041c2c0e0b403500c050a10041d81c021030080307055549009800c0212042540c911580150740c402c1d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 79691260 1250 79690010 79690021
    0x21809010626070c03030216020a0b03090c030a0201120b03010b1903170304020d021507060207080904050916050d080c010f0506121203010e070e1e1804021c0c0905 72
    0x7140d5250480c0c00e0404429500040e0344450758042c503071081c949511010000022a54214002d5109090041072030703403034250381c501580340d00b6100300c086c00b00054041e94a0504541036441c02103000d408a10a40c8032640100041c0d82c00001880c4000d4044c0d00030480007003200c0001e014000c860300c1d00f0380141400034a0008881950f001e0011680100d205c024099200194110240f0080320043d41200a0b51107230801824900404580000c0c143c07802c6007051240c0d5590020780e44411010744800f040402d50120301c3ca82885025005071100b401000800c109201b1030440380e40c00e01c101489404104041010f000703440342121224503111000f0031941c00c05c14001c6000744016600d1a0198070500c80c0d100c4404000104494110743c0c41c945c050540c0e05c0c0000030b22594030002d008800300803e005a414050301c9140341180844201d050000040d6041c90134031020066000499a5070500c00301030002617120b2041240d03034140c50208080b554520750403c80202c081c147d100e018014981001c102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 79692510 1250 79691260 79691267
    0x9090906061201051e1f03050703060c0203031b031b030c030403030605090906040813081606021207020f090c160506070206060607080d0509010b060d0609050604021303060218090106 80
    0x52065104440c444080b8016000c1c0c1401c0721421104a220f5400000b00c8444815552018590020080c1030601005000721107844144105510440e843c4c0e11031241070040003258004e050881c403d81c40114194030f04408003c2041152002c1144114030010103d107151104e180401d402010f1482c0055990030000d00c0554a503000f05c0f0260300082c686000800e16103055084c1d2400384c82840000c02c60b98403952a26002c0380c0c0000c840f000681c00d0788400103013091007407046208004030352124510142c94100040c1c00d080b8003c0f200c80d220b55041000d500166505485078038041e90640d64184140d44100091403a80708a111503000b820440081804003c0d000960758415140342c0e00755a02034844070700b4004d080c09944401006590309008100041d42c081d40000da101c92107000200301c411843c804122640d014901d00f0380046d803a00d0050165040900038160421015507086141c885440c8503a9000800b1307000040c803403a00055015400d004607800300c41c01c5007009001c80fa4550f5140b00c0507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 79693760 1250 79692510 79692523
    0xf08040f1b120605130308040b0a090f0f030e010504050112020f04030c0f1401020a11192706050f091f0b030a060618030c0536090f07030c0515090909 66
    0x49440506120001c0c170b90485040303050010a03410349038018640c44654695400380d00050803031103802d54a03810b030004251240314202806008101d500000c1c0000c0c10010200c81d81b100005040c840200010456640c0c04410004030b8500e0041c01610f80f64402c8100c3c14a2181e9840a45821070800d00032a034000220100002c41d5001401071480c10603401c01640c6400c0c45140250030350504030070101560521044401584254081e0001e030285c40d2000115800041c07400a1608002802c0c0e080c8080998410103004c0c0c038007102d032070501e035442500207141010000c0030540e42010360008005110302031b41440c00a0030030142c001d5120b00c0c200030903034001c085a104030400540030a41c100c24914250308940d042d00d4001501c5e01c0c4540c00c00d414003d070a29200341040340c0402e40c0c954030300541d075018184c1c080c503402000400c1c2c00e82003034002d040c98949003c281d11815004a017040002070100b90700d40b0106c0c1c070207640510342864800001c9100e40541000f03281c01000c00403c00140000200c1d40c2d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 79695010 1250 79693760 79693763
    0xa030203130f0b1903020c0d020606120c060a032f0d06060305090a0305030702160e0601021e0d120b0d15050903120109020c03040503070b04030209070f08040f1b12 72
    0x2803502940d9106010362007000584500d2004000400200500c1c10442000c1c01c1d10020a050261074a100d1005051070088c0309491600107030407020078009a45440032005c0318a101840c0107011400002002440d075105001c498824036540304466056405030000c1e002c030f814428140500410101080d00410340d00ca410a0340081d46002000320318903000b4401e050250010b200200024070301683d096400c2da02c05040202544a030340301864161034503003016005003a4409081141d8284100060b14210203040100d0400201300c021610641001640c840944080d140c2441d00034042040000200010900290010008880c0e102070042c80884040c0c2d001402d44100aa9514140c40c40d45034000e0200c40015004124010841c009094028204010804080e01e251035540c1000a140c604103030300c0b500400402207810401d502d80111500c0d8801094200720010b02c1c0484801400104000c00c0242141241051181031003110a50f05c080c45548080e0b10702415202e80c1950280301c0721010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 79696260 1250 79695010 79695037
    0x1507050a0302010b060c0a06091509051c0f02030d230702030310090608030f0d0e01060e0103030e030a030903081b07060504080f010c090317070204052707030507060c03110a030203 79
    0x19407550904100703040301d04813110765014080c0e1607600e541ea200641072501091711100d14081024200d5802c1c3c0c0714168bd180d00c1203009100c40c04039080008005840b0094010500c41030b080030740c841170340120840c0c5801300c0d200c0300000d01d0150090070189800c0d8500108108000607010051030f190000000c1d4001e8100000c0b280c0d515039151610b40c02d49901e405001c04c80c0d00f05115420036092000c025024984c00180f002c1120b010903003806003101d2480d0b000e1500882c1c0e14004000f0700d90406c10911159605a001e0304130840780340c1f0042d00c5441c06100080001d900094290b00e000180040d240716100054203540c403040d034400c0010000d0b0024015102e050003031649030444060140b00c0d0080d0420207803a40c40903540340da264141c0300c078040d84000d038290358100032500042c2d0342e52003040c0c41098010b42a20700c0110310100410b103880260322401e03c03035003c51350600100c1d03c00030368402104c00a140c1900c503c0d00600c3c00719402c03040e00880c8461880750850781c000301a00880503103000e00d1a42c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 79697510 1250 79696260 79696271
    0x20d050f060a0807170a021008010501201b061b0c03070603060e07080c070602040303081015080414010906060e0105030d050301060c03122d0e010c05030c091507050a030201 76
    0x10704204010000e4840c20b03060f580900c0042040410030b08514903030b840040142c40210304a82c01041f6010002c0425100003030440c1e005111a681000380c664401e01060001c0c3c6600c210124034507968031001c0303c0000d103501c20702c101a440b0307030b9004122400503001080c081007510b40f9118403981c501c1883e810b039100703006001002c10704074401d01c6400103c9551858444098450641c00c2e600c121000d0280070b0500030410500c4007040d594002040194841e0780c1d00302d0316203000305099006008540103030900c044075817000503005a02101d0990030680081d010881110a000d03554018100060002c1c001400c0000004030188800d0311141240d10030342c02e071071542007800c108807501d00c024010080421503440f516404280310b61100c49a508043c0340000b06440d410040c80101e8007140d440740240e41001c96400c2c1d507035889003d119100300080000740051042d400c1c001c1d00f42d00004000400c0f8400c045903941041e580c0716601c04414803100c144650303680c414100f2540340c8011480c164055030030705 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 79698760 1250 79697510 79697521
    0x10e0106110303010306090f05060403090509151311041707090c03020903190f0b010e0612030f0403020409050c060c060702070501020c0108010909060e0d05090f09060901120302030d020d050f 84
    0x107906024996000d080590b10390380c01d43d540c450042c00301100980b008503035800c40000003501000300c02e0142e4000e480303520340e0750700d09003c1008440d0020f000c0c1e086280d00a00d83c40b9562100c145000b0103840c52403000c184c0300b00041d52502280100d52140301559004107100314401c20101310241511030020702848210f150a100390203034400c040900307030140d01410b11110203101030f02c000411513100e014989038a104071b0b203c0c074008060a80000c40c0b01100d0030140004c034a0a0652414044e120001450424007401001c98807400f807403002034003468948410f0410040280300304101c5040080101c1c1e1a503080100c1d0541c4d0307802c102c41020241c8541c501c042110340c00020702c1600700c1d105a595001c80d03070810440780c02030084070100300e4000791500d4511695100510420035101c205645090711683da440c100950050b4601586018004070818041540c807904002030540f40c14404048218980e80780880c9103104a0310150308041c400b15002c81888615040580684004503c40b100c6841e00f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 79700010 1250 79698760 79698767
    0x20a030209031b0901060f020c0306041a07030606080a0c09080703082a030f0f070c0e070906030e0a06021b0714130e061602071703030915040507051306050d0b010e0106 74
    0x151008950312136050801040340724800c100d8022008203520542c2d65040401c408240380c503800f42c1d0b0071150040080c07003140c1e05030590315520703030b03c121185010300c0310368a02540907003041800b81a9110458455001c01c03c02405004040f0080040ca4100c5403555a242407130f07000398000c030a840d100b100e00d080b8030560403840d042100ba030312002c01c00510314161101c0c0c0c4a1034968401103100c0705201e8148401ca0105a409444100030011840420070504c0d00b85c0005140801ca41c210606161502c89121301c1c0ba1400901c1032403a640c4180c00580d94140d08583c2e80036544183d084d40301c14800e040c404941c102080f05503510720b0100b41c0300b00405180c006064410786203030700c0c40940d266000c1c100160540000359803100d85c44041b4011348880b10f4644d4140a540802205494005d41c000024443c01c154100700c01841c5004600c050101810295a000d840b94841d00c10144913002411000f1400d20b80c1d41d00880c000c0a004080300c90845080ca07211503000424031515181080707110002940300d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 79701260 1250 79700010 79700053
    0x3061a0d050708161409060d0203010c020705030c032404030c0b0114010311030c070b0a060504020705030c0f0a150c090b031608070905010509060c030403020d0507080c15030109020d0f020a03020903 87
    0x1110895000041d05c00000d0160303400c40100b0041d4000901244034001da01c003803007a6580704009078090a08036080c8414985402c800007130650003a070002c01c407444291040e000c0c1f24541005aa003151070750f00c403420200c030344845441002d0401411403000194000300c00f600c0e4603460500b80c80c00c0c400000c42c1d00314031413607000c00c4440c06403011080180740d00081000000d284d02040314040007a12a4581d00410101e810400c42101c0345d500c00102d801d44044108440c07030203490800010005248541e40d1400150200399040314450348640681030514000c040d50350140c0b000c5010300303403a071505804410425044940800c00701c0c200c00017103124584030326480c100351003041c0c40e0f05140402c10402e002a81c0d10140141e80940030a003c0400180c0c3c5d0a00002d280d980260000c0a44608049089081000c101c04803440340128040b010000b122040a0ba411141024001a250388110010f0342c0a00f00d8032108107100c0c4d20000303400e031074141c240c0e000d0b0910302c00a604035503031546c00b600750745a03648 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 79702510 1250 79701260 79701269
    0x3010608010512100e0a020108060409080a110a02040c0c02040507020705100e040605031905060f270a0221010f0506030c040504170d0b1e0a03061a0d05070816 70
    0x400c020014000d60504910a01c1c903500402c049030003103003001101d00203c480501e02110a41c10503100f00042d50303807080c08250040b90469082000c41c04a540303040c0540300705c10005d0b0074170440c07038880301e46107400b88580b1094503005042440f124080c410010807000980104032303c11468a008185080c2c400280e0701d059440c0940540412161824180c0340901103000d015403107600c40c038010900351800d000c2031041880c4402c1ca81c14004c0c040c500076091040c002c088140e075815030001c12415852002c3c107000030700600407801c0740ca0616800b80f80c1c00d0540fa07920107904001001090130505901a01803011036110700000c0000301070b0442d40d1030545905840e0f00350306a02c0140c4214141c50305a214a1f006403159880d00402c030380c00e160941e5550082014046444d5848188200b81c1c1450741000a031030ec600d441c0a0446d0002c03c000922048036800040d1074a6a04e4024a104003002000507010200041c046030304035510385000307641c49080e070049240e28011076129801a800c51040c030710945 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 79703760 1250 79702510 79702517
    0x110304030c0305030c04033002241302030a110103180203060408030c090a030c080d05120a0903020f03121005060f07080a0509040e0c040507050c0703030323090708060c030106 77
    0x441c0c0e50703141110141c10182c06003514210404c4000000749143e103102c2010241d045920030380382d840c1d80e24020a10264943c0b2019504400d41c000b0003003a800f80c200718900c03000c499880080d07d40000c1204288a20540250507104000102c003d2104203040d0b8000006c00341da043c01341c41501c41c074011050f4000031380290143c1c03000006c00e000520000c00f440c0e00440580b0800d080070400400600d103100c0b10b42c015113403000b004105000032503003801400011012781c1446441c18110003070107100707060000c09048030b85a80d1103070041050f100303015048003502203508803501c403c40b2641c0341210402c2940e0030700c41007001c040c000910341018030540d0194243c01940346d092010030344a4100305d0f0b01003074010040150030400402c080e0359a215608030381a8000c000c00030342004800f8001200c00c0a0048000d0140900002040360340000d81041541c3e4186030200b014000c2000050312a415441000b24500e0701208000035039500140b414125116001150900d071140100d00140e07100a0040c076000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 79705010 1250 79703760 79703777
    0x60f030d0f030509010216080301060801090516050705010603080a030b1305011d090f16081b0a0605070501060b0408010213061e1b0c03080a0207091415012304030611030403 76
    0x10709000f03500c80b541c8816000c002519003420395007200040100040c0c00c0b1100380c408401031110503401000b082c054240004208800d051416560a681075101000c000300000095202c003000000e410039030003940c1c0000001d8407021060340250150035150440390045c00d10781d0031885c0c10b00e414004c09040300c40352004110f0941c284101410000001070091740346e840b80c101800e40000040014407088060041a041c0d01801c010130b50342840459101004000d1048143c0d140e03541c0c488108604036600f40c00c05954071005864202d02522047e8020310031a10046000106584190000d0081421004c0140640358680500b03482da010041c10b0004c007850b0749810542544d0003418000a0802204400700811000d0358130b40400000c40c1e0411205001c000c24246120f40c4c040050310302600007404240b01c48941c0c0d05415080f2000100780341440c49404480c0d00c1d19902034510411080c10a04404080c80c21a241c10802a84103100488003146031000140e40000060700f07403801580e05030380d560103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 79706260 1250 79705010 79705037
    0xa03150506030105010c2d0309080a1101080a1103090307050606061206040504150c020c0f011106041205070c0603150e06090a0903050f04030303050405060c0c030406080901060504020a0503060f030d 87
    0x100a40242000c0342c10b0207c201d405092881032038905682500d441c81061a0000240790040544c44503501600c04c80d032020b07082c0c900107050240605244c0d00207203444181541d4649402c40034129802040c0c094000c00020700c050598084028131106008001b140c441d40c54041c00d0201c14819100652407000900700441e40074038040d0890f64001e030042d4108100034a81250010441d1107081b6a40e015a0208010810500b0009205041c00409003803a200f011303481943c0507220740000308000c14032281042c3d503400d01ca000f601943e04480e0080801130190f61501006401021409203d9482007250b40d400103010100722102072007400040d011780b0b0306031a07960703440f806442c115904405002003440341d03501c0701c0f10007001307070005600950300410300f802c0c90f0a08505084003d0005404458204210419000001300302c1d8115146480c19444a0303442014135401061540c01541d482400000c0c01499030364804082c40c0109022100c54000d58200401c01d90349086150006000c6a0500e4040c01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 79707510 1250 79706260 79706267
    0x141e1909060917010f0c0e0906010302090d0303051b12010602060109090305040e040c09050c0901030f020a1e111b01030b0d02090a0c030603050703050d0f02030301140d061d030a0315050603010501 86
    0x161040f07103100003284440c503170706400c401e07100c14440000006504001d00211498800f03a040d40103807082c01c0c218a8074603041c0110381450550391000d0241510341d000300f0303154603000d054100d020002c03103c0f4588440d03520303aa040680300c080c410303800144541d000206105510388038556565030316464017464145024140100307540000c00aa82480b08000005010304260082c94843e0300d00580352a41d440a140c009000c0700c2d0512290680107105112099140350880c0c000340f1401101d5a1510703001c8000e0004071840410403203403050900400d090030b140c82d164241c400b0013004090b2410300016080c1018801c21000c0c20744060f521141140100e0f026004035440023a00602a20340403c1003626500c40b6483c0030840e60007250a584150409004141c0c400f04001802c0d509102840c510b52409100f4030b520401080110301c1641c499803040b080007000d074003031002e1754020741c11808a400e04401c26610790704580d80a0000c241041500070300282c0000c076403030554200410322270a6908120046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 79708760 1250 79707510 79707539
    0x603041b0e07170c09030105040309050a060c020d06020f07050f0a031d130b0307050a0e070201140c0306100512040501051504142a1201090f020903030a141e19090609 73
    0x1043c014000f001705034180d0b1428002c40c0c1c407407406030326540d41d502e107050240078480300d250307129038104045c0c00c00c000d005139154111500d00304d0f0852005070710740540d407030020014440d501c00140a445154190340c034450000c03d84580183c000d4413211042c407160103501a500000c200f80f958000658911b5030090221a849400d01480c00380c21602181c5c0c565000c146c0c0c0c24029080b0070142c81c2078108100066909000d01d10000d0138020380c582e441d080c0707040340c2d10540c08081e1425201d44c04d040004118644941d0030b84190204a1000008604050170614001c01c0c00350b4400360140c410500d00d50a40c1051300500907085801d0a0340d05840d51060320421b449074605401a0000544408141d81e450a0700e020b061440303a07000307481e006035140c40004c004941c203c20a5842d820b0062120318a035039400300a0f6070b00c0d0036850030a441c011551403030b1040c0c140302c1c4100303500d5016103103000041959515000303084045502c200800d841242243c09070f905119a1003010300103851414107008410910001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 79710010 1250 79708760 79708771
    0x141e010804020d0302010e1222060c110415090e0f030f04061d031203100801110f0d0603081309110909010315022104020112050403050306010c0c03020603041b0e0717 73
    0x40d044440707007111070070072451411450030348e500451000308610521500e1f0103003c48503655038011500c1e024000e01004807540000d4410074540d4020151900d55400000024440c4550f004000c4e4841c2048002000700d280a071040d84903000710b0390b0882c03070004121000309440c600c2260500d490008102c0f01030300e00c8000e80800300d03019002c05806840802c00f50840c8224551034070f40b030b847c2082e42d030380c944140c42e030244d50140e042030740b000484a002c1003215000c0011104242c0e5a88018152002030004c5500c01010ba240c00034981d1801c044d0142280150b6006410038080314032402c0d414201130240c00c440c140e00807015001000082d56207040040c550b0642d031005410300240c2c44119410031041c000312044203036010104801c6680c454501b07105544081406c21031810191801001070100504031818456410080800c0c00041003507130005680c0242441d40e6490b040c500340d032101200c1240480c036807120701000701d030b07200314007000902c255084d659400044ea80850380480b881c0b0040e01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 79711260 1250 79710010 79710013
    0x609070f0b09060403050a060903080907050d0809030f070b0c0120041403150a0605011106070906051e0c0d03050f1b030402040e060405070312050a050306100509030601141e010804020d0302 83
    0xc004002a000c7c0304608019014000004e000c2c2002d00300904a110300911404483d080403809010550b101c0d41c07503000305900120041c0d16501024042441e180c1820102c59091190301c0000038100640c074010054914204000e02c44240e02440760084004021801d0000c18020301041c4901011060700e108289801001c0703904050010501d000c1c0d80c1016941a0301264403102c0602c11540c00c01048107200b000d00000300700d94641418020724030b60720790244500b00032000604103021600e40502400419640300d05558034410084860342d1070501340312801c0400d04003800100f08125014005204019504805141079004e203014151540700800490b881a03480c055868081c0b4104001c500c202d2190300141071807421030904030440d1085a0001041000800c0704586032580181900e030402030540304405a007180b103d060703e15025118245070548103c00000032121144040704060590a07140c01c0342030224403c4000003a844031108502140e2080040303030041c101800f9081c0400e001c0c0c070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 79712510 1250 79711260 79711267
    0xe030f0a0302040f140301050609060f010c0c080106060206010e07020a02030d050a05070b0106030518010b01170603010e03130315020f0906090a09060b070201020114060306131e0309080609070f0b0906 88
    0x40c130341200d501031604011004580c40001c108142401d118083d00894121600b80051070407100107120a51107a5496040150065030a8208000f0440d40345c003a00c0020b0084c8031103a113842d0004c0da2102c00f4814110300780c18490105244034004100443c0c0391340c01402a022030083c3d22000c0e121603201d5048041000000c000400c040b88600d60030701d000c3c0405a030041180d08001e1004111203000110030704840c1d140a04600281c0e820034050b14041c115200a03010598030880024014408003903401007602001943c070440407104100002944d10030596284070303840c0e1461110881c000c0381d41e6501600410481c1581c6171030840040c1801c010002c0c0160149a00d60361883e0540311180c0c841d41600c40080752001c115a028000d098140361255142c4a030ba07c0c1040001c0d82d02d0030b02410000c0340d070f032010090070280200054001502e1281d0700c10390b142d6445d24600180350174894402c4041074000d0101007400c0040c08540fa1088404041b0620101404c203000180680c4c000c1c41c02590058080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 79713760 1250 79712510 79712519
    0x18010b0c0a0206190f030b06160f0b01080d0f021204051302090a0e15061201030f02010207091109010f021902041a040906060f0f080a1506031a15040e030f0a030204 72
    0x280c0003044403001d4103d0010184c44104009803040d1801112081890b082800004450f2100b20aa0700d45011040280801c0180e0741404d401c60b295000c000380654840c00000b00f901c01c4005480c503200da80175602c1c0310160250705400c90320f810342c080808400480411081080c1d2910304800b03001d480310624018a01300345500025075105040c0e00c514403c108680401602010307004854001b00c009803413a41c50500ba441c4018003070a414007005100106018250f415a40300b0000c803800340100e49410862900c1d18200d9840a03001100180d0003d42a9041214003500c00b1880c0a43d104183c075241034560b01560070003024243c004003400b5082c0140f910f0808594580c020001042c0c042c0f0301c0051018104081d42c1400c00e04c541100c15a110b42010411083c0c8001030041c25058004000b800c002c5615a0450042d014981c80a06000d0400341d1f80c03100080504c0d00d06014000c3c0208910300701100009000540d40302d0510f800641d041485400c1c8440070306e000411080c01140340c0145401d854 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 79715010 1250 79713760 79713769
    0x406051b0705150a0c020a02190e0103060504111e090703020d0609020c070e0103020607030804020d2a1a1210090c051801050f040504201803070518010b0c0a02 70
    0x1020040d500b683c0048544a09044440d00003030300550301160501101403000b00107035840c211420700a002c0c6060340d0820603d61507600800015081d03e194a047c0d9503560300344103000d04415501a16094002c9a02070458a80140c0c05421190403070500d0b590110540700304240c01400900d0041855000c1103411500c0400340b040502420102100603215414040807920f03154240d08490b00c0400e100005102507560001607880003a814984014203581340d10200b0b480d00c0058000030f0215050400e0b44bc0001b5036001c1141d41141030310000030036151f440c5080082c14a401810f1002c2e44420414141d50301080048240d03c0840d04101c821255512940c0304c080300c4e03441c01d0740d4000030300104640012000b030f01000340100b0700c24600300c0d040081c140c0303100342540300d03d11a6510460303a4143d0803400105d040400a0000c3c509846652258000c010301102000c122440d6032081c0201113020499203012100314a280410300c145100b0f80c0c0c28120002100e50054200074003900c11340c503121005a45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 79716260 1250 79715010 79715017
    0x2208070302160807060801080609070b0a0311030c1c06061d0307210b010609080606040209010215040b100902070f080304020d050304030501020406080c071a0705090a030606030308070c0b0406051b 86
    0xf4000001c040c0c10b45402ca00a021180c180c0141c2c0c503582000c024402000d00014418003500d1038180e034255160f242c0c0200f58010009184802141b20000c0200308559040c507024015551002c410207100e10b040c0c0140074202d0324640180404108001c01c0c1540b58400450030400072940a81210045510760038840546120182000302c80c046400f038170404c00030308000841c018641424603202460500258640f1030364001d02860040b035004c5140d0070300368400c00441101304254410103086081c01d0802041548088804a18051403000c00081e500c91a03c00c452821303070070407800686030034107a8a4000d503600140c803e80e030205c00944200302049040c00188001e510920005a907546080c0707020303141107002000c41c5a1080280210300c041031203562003504034582040170b41301560701c0510546103406002c910a070062007805001c42080074a034800030a03a03001e42c844034469540c4009c01c599020280c07400a1810440f10f011170006001504080c1d001100d28600c1014044001d17a280b40640 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 79717510 1250 79716260 79716269
    0x1106010b030417040e0112061103070207080c0d0807060207050a08030a02030403030501050906030606040c180603020d06050a0b070f050304030204020c0105060a0b310902070c0e220807030216 84
    0x2903000003070004009104501c0b6010503401451070741000d25105030340485803414440d00b0300003120140030004010751640080c00804140b21010b440f070404500007940c900203405610780728400c980020034070b45400d10301346c0041a8003a0f07095240068541c0c5490194020a1049403e8814545000c00107200031000d103100c0c1840440068480c0350508004040d80e40c113074411030113030604c0028020940c4011602541c482806d58000c01c3c0c034524010201c485403640054000c2c012810b84010403466030640040c0842a0041010305c081600c4104101c400103082c407649818600401070700001618003e100f221483c0280d05403410075940c1e802060983c2d01001c00f68040ea5034030400c00c80e0030300c0c0c0900c00c4005002d02c0d483c070318105155014140180403408410842504403a40c8200c0100c1a02448101a00c1042429500c030703180d40c038140a003e030081c0500a09000d0b00341c0010424131490a005065038a6014488401c00d91501c988106a210441c04d074218028800e050006000480707850000b807 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 79718760 1250 79717510 79717529
    0xb0324030304170a03030f020a080f0613050903040512070506040614071a01080613080a110a0f080c071509090b0310060b0a12020c03091215071205060414011401110601 74
    0x144917440c1c000c0031201029030110b0740034414020300384030640c40b28409600c502c054080c40752035120007000402c00c1101003c840203003820001080804c60000c0090001c44500790f851989a05585102d25220038440c0a2150031070028481040303150b10550001009100003044940351135aa034551504824240444444968060b07004000e041010010070703a000e4240900b01c82c27505440e944400c1c407485202c008100f00b00c0182e900e00201d41082c0488818580e1100c0350161440d200d10384001185c00006502443d809104c20008400e544801c24424421055440310744a40c20316200300700038003a00900300c3d014842d1580003004407645116a070081c00d01c0300302140e10382040c007000400c280306160081a2140c0180b10000c0341140020a4504464007203606042c500580d82d0400d00d48403c0f0913076409aa1000310a20080a81040706204981807c44060010b65140028001503d4082802d801501202c1004000007040c0381551038180034140741803c0e40203e500340300d9107050b2083c0c1050b01c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 79720010 1250 79718760 79718773
    0x2010c0c0b090a080114010b03180303041a0106080403050a030504030306090c0c050f0c01090302060d18080d110301030302060a051f031406010e060d300201090c0b032403030417 78
    0x11440c01c3d801410042c04218001c3c45614145115099508018403e4402c0c0401c0031000c110100e4428010100501140c0700300c075107074502400c1540e4400343c1d0341c0550003510f20031000450568861501c0e0b500c9180c1603261b25242906402c1c048000b420010130550400d60f4510b170210701003100707006006645906aa510724803104508146040011081603040c160303010744503d0307903266004100c80c400c50790100c5030f481d00d4210f0700c0900b030054601010700c0320301d100c000d06080301000b00c403074040d2880744c031228000c110507002020300c14000e00c030a0001801581c80040000e140c407059800c01035108411030080341b00c914655005204100d000e41080781c034450841d03c54900603208010b094010b01c2006507a203d942008030206000380c50007032000d0001c48402e1030f000341d0b00036000c522440c18010302e00030713150b000307011070000380200182c91044807080218200003648405440560b40580c81000c00c070742401c044000c400785694498118240c06000a0200003428004600062040e03507828000e001c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 79721260 1250 79720010 79720027
    0x1810030b0f0709060206061c02060409050c1306090302010e10030b0a08150609011202010c030201090c03080322030f0e130501170d0c0c030201030b0d02030607030e012f0702010c0c0b 80
    0x40f0381410f4200074210740c1301c0c004000140c1e03a2885002c0c000d80c901c154180440a150001c6441072185e40c22201450f42060203000c0c0c4102000002c0400c4001d01d2003458003552501401c0350390740420f00c00a400101c0402d140b075010319003d100c0303081c04e406c203040010780c8016220106908041076884280c071a00180c040110034030711150070903031000c0c0031110b811481d810030100b2113112000d004068108000400ca03d010036000b58043d56020390858154038000e80d0704d260864055104644a040011004003083c000c0001e0040c12502968552210658407002003404c440400d845d207101540141491080c02d580685403160324042d003084c005071164a000c4459a61401100035842c90420a03250600804100c2c4004550b0076298240390101e55407080c000040c001c03455200002e581809904140041c1c00e030503500c00809048040000e00490000c4409100304903458030012204060410281d250300b20100000c062951050412a02c03991054580c0e180880c4130350040c40c3c460700000760401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 79722510 1250 79721260 79721267
    0x60601020f0f0d050a02030d050408040302040c0e01090902030a021204050303060f100903170706020a020a0b13080414032a030705040504030f030911130b0a080a021810030b0f07 78
    0x1c0744800c24024a5060540600c076651030f0510300c5070300c04102d00400c958030840d10134003c0b80c04d071900c800000e00417810f2506207060aa40103200892259103016110300380e0300d0080206245401c4d0584030101d4503403505030130310043d6000420643d000b541c01c10001030b241000e2207441c2e0050b8000c00080d40c6915110041c40002c110007203840d4800d4407210441c031039003580664400142d03540030324201000606001c42d81e103c5c6c00f880350002d080f54008195080020340c002200c05005000b04890301941c6c460f502590704082c0845c0c00980b020100300000d10504c210000000610719001d0304850007a041c54a200c80701e0000c510481c103080303440c07108951041ca000c1180101130441120b04100a00305590043c100d0700481c0c0400050544600c03811003031210b555440070b04100007030070b88488480e011a258004111003044944902c0604001081442c00000c41604840e4041c00781c159007514482046d80d140e0000345552400400d1341004400540c040d5552802801c60003400b0300d00f03007040c2c02c018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 79723760 1250 79722510 79722523
    0x501050601050405150702030712050a0309090510090203060607023606010c29180115060f050f09060f040303030b0f010207050d020301150b0405180705090402030a09021206060102 79
    0x1281040820300050116554062800100c80385c1594410399524140c0b02090034122030398440840104e2051440050100c003040c07844079944a5503418103104d0321200c0c0d80c030880754283d40450b0750030b10405040c0064011580155001a0000c100c0c6081c18819400143c0d80766051042d13a81000c0d201100c060b0101300320204000f4200b14040c0c2003201e117060030000f48120400000074101c10003010241650440ca8401d1801109004c13001160603d464014642e4883e16001300900c0c661a05010444080c801c0c803065082e50b0721951900c0c10061028401c4034250451b040d00780c83c09408010b801119650310000f02440b5407208091234031586541800740c01c031100c03001d4503070140225a0510007942c1e8046150416078000b01d0794900e1741c120341c0c00400e00418144444801c1c0308031161000c260038203240042c2046035011a8101c99855501c0400da840300d20607030300309001c11400d01c048001c51502e9009554041070082c0d00080300c80c559000600e20000c01202014590401c200784915543d040c0301c0c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 79725010 1250 79723760 79723771
    0xf220801061a0d0f0f0507090e01032112060905010f05060903100e0102070501050f0105030c0d05030d05060f0301050a140105060a0e0d060608060106020d1205010806040f020a1203050304050105 85
    0x1c2100620304000b40c00c1c1d11100303100300075a0140000d860554010568001c100c6100301038010040b8031510304d5490010003040ea215004a003003030b6000500580340d40b04d0300c3d05070b9620000b05a00ba820080300506403140c4580306000b1301c101020005030510341d6200314401010103400225065140809a079107000c01c58201e107000383c40400042d011501c2c00038a41c0455170660b640015400071400c10b443c021300078000300030314035424503003405400c80f42c0b82844ca0507103004400f42c1c1d090300c200780c080200441003920020501d80042c0302400700c0c900c981d40720951111001e40101c002c101c01c00700290856804460181685640c0d0250985c089005009036001d4842528007a00e031042da11400342ca0030200b01c0d402c170721404c1d66403000020030207582c20140003400000e00315242941c444030060340329001c0c0407450000034684420002c2d0440d040c05901d040302e0001d000b51030a07443d50380352210b15144a2006030b82041140000042d48907000905a100c603001c4d0349c64544900340b0745040741c25203001404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 79726260 1250 79725010 79725013
    0x1110c010501290a08040201020c120a05060606072310061d07050c070302090c040302040518060604020403200d05031305010915091806030203030a17070903170c030f2208 75
    0x254994035040306030844c1daa5000078240348005580d0ba100407494586000da5460b040f20f140360f00b080120500080d4400c14511450594003141e03180000c0c861a40240540540305000c101d810034041c074110b1401d901d002c0340d01c4082e1074207045404140c40a4480a070310000001c461080241d1000f08078461480c0c100e44680381441c50112040c500980d604410300020740b083d5501c002241002803a14110383c0110341c0580140240e2a0160b500d801a11145501c040d46014840000e1001e1400303100300d80036203501c81c40c240042440c552450000b500944486508007002131910030100d0030402c0a084280c0b00c000100c0f40c00d5051100061480b10294002d0845030000c04030312922540011052096075001a414030045604802500103480203074806500340c00f000039036a400b25030010b000710811803100b0103c40f454540920803130b901206444064540b0200380c03c07200d0040600300017000d0102d19034084a0625110445542107a84079074141c05c414250101c8011188084808102c000c0038070f80b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 79727510 1250 79726260 79726319
    0xf070b06010c020102030315040605031203060a090b090a090f0204051503101b032003070305070e0d0f031107050301060b03040c080d0504050402070c09020a0327030c0b0901110c010501 81
    0x43c0042c1d0380340400340030f007080c070100418050344d983c69940c0808010100181102c040b4140c0f041400420303802562003500410400102044030b15044c020314080c040003524540343c56499454220082c5111070085402caa24800c02d2030242ea076502440c0d014423031006e011460b000c20340c2d08061401150805003d802810316412400f0415505400b000e40811400e012030100c0c1c401c00785550006e00051410b00e81240403041c40200703036140d48240d1140c01c0c56103c02174021114800c0200c240036521008120850728004a000607108604d40607940e003109088841c65511000000c0c00c0d24205d400c4801420000720801081c0090041728600030449103010b0440d40403c041c004000b449a400b90500a03600040c1d02001c0052800056005051104045458465081f40180984052413081c0003550b40c0800f1f0b00160500310443d04074040d49a142d0a1211542d82d450752120400200010b030300f5541d0f034240030303440c4500034010985082510f00004040d81007000600500d00b80c4c92410241c50401d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 79728760 1250 79727510 79727513
    0x5041406030705120304140102120304080309010507031107111c03020606040f0204050109031e0605010b070c1403031b0a02030706020f01060914180f010e0109110625080c030f070b06010c 82
    0x2000306d40540d0318054650440ba640000143d2801007100c0415154000020802c0140620500070750301500341c010086c8195111110b00b10240c0380000c01c1c0a603e003000308403410004600d07020000ca210700242280070a04030046141d034040552840c04d40241e00700404102c1240f0b01849608a0002401001c50030203007440d00007014095580070013007110602c150040606680300a0740b0b101d07244d0046040c0020341c1c40b070b000c0e400d154011804c11540c40e03928200201d11101c800d0b8240d07181c220301600130f505041182450003000da0741050180454015446990301507107040c4803c4004d095103400800181c00321101c1682120b880d41d00c10101e191900011038080207488000d40d81008071041d40b15000340c030082d1280d00304400c0c0c0e464207032603610300741e1410b508030419040140014068201380d0001c1a000c0140803a40c40340d01048207540121088040782201c80000040040c0c1c01811254140450358519518507030045a90900070390010801030108040411402d9000c00300b8a48419000102d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 79730010 1250 79728760 79728763
    0xf010b0d0b0103200603010306060518040803150a1701060302011e0507030c03200606040e010203010803070204150f0f030c060c0b0705030703090803100609080718020904060504140603070512 84
    0x40c00010320104900c4240e4000b4892000000f0209000810291b900d5940b8034100340204400c0c82207901445418910401600c00780c00100d00c100e40240131a45155500864003241030046c0241c0d1764484500d01003c01c5200e4401074040034a07000a00006031141140005042212401d02d05009594003400c81c074105544407050300c000c146c0c942400c4400c800315103010744041e180100d090b0709542202040c1c42041b140000e0160040c1c106503010000003411006440c20703403000f4020740b004c5510800c001001401c20b40e02080c0f074075a029456003c0c0b07940303c105503a00000a540304c41001071440c4030510900018050130b0004080a040616806c401541c5402074404020710780f0050000120005031042d0003600040c004a40c03268500382d03245481010b440c642c05290250f000002d04009001c140c00400140020a60b010040c114040300b02c20162134000c3d6000c0b541e07054005071504e0300002e6580321402200fa844007500044444c03440c0000c1414a07115083d40203522840450181d40100c080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 79731260 1250 79730010 79730033
    0x307050705060901050903010f05010303030c0504050901030b0405150901060302010e040203040b070c0c0b0a181d0406020315090a0b042f07020a0806040807030212042d170f010b0d 79
    0x400340c40c469251051440181c81758001c0e030403019099401c00300c0c502c802c00a03a5001303a0507640719440c20032061552880445040c011030048a1b00003030b2160040c804a2045151140d100344107100302c5460344002a002c040a81d41645c8084150f174541005008640c0c114006103684401501c0460440c6880c2d210300c08954406044403081c06840d14148052104200010004e809003a07201035427860000001821120700300e0700d46c00e001c03a00c0718002c20102c0180c040308940c012030061001158640740c4820000b5440644590300c00005440d883c881d0703403100347c0249e01c642d18008001400015440030300040e2103904030b494114103201035005d1907000700c1140b230b002d0032045280e0041e101d110520205509019030f800148261044004020401c814040141240c500c01d03401e644110700800914a07080c06070303000da1064106000c241007408000703d0748441015000901e0f10258964030b0b4408100d00c0141c801c3d4a0b45078000f0800701c0800c450900850404040549a107500340310a46c030303407007140035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 79732510 1250 79731260 79731269
    0x30115301208060102010b0307060e091308040521011409010518030322150e07060e01020a020d030e100908070506040f0e0408121003060b0f091605070c030c1703070507 74
    0x1000030110343d05034801d600801b84540c01800302c0e800280c442201a0868107103941262003421080002801d01004444108005500298141c180341c205000c20001c0e0400d41ca02c280710607800a984d0003035803001d0184003025800e182c080c24040c2010340910b030039140c0003082c0c801c2c43d90003141c10340403c10001080701d6100c540300030b0320b16210000c0303206201170ba4810f00002d00700d030300c1031600c00d035408505500c14088981031004880103269039140607105400001d013000c0c0982c01100c501c902600303000401c0210304d0b05c68907001105507510760010b101000401d502100280d941c03881803107869801c1050101074541100c0040c01d1902d855411202030480d030003000601c2c14450003050801148ea07080e00c40850212809414034981882000050b40070f0b4401a184681000302e01c46540c1070511740b1064406024100310484d945100c05c5200168016240300c0c1084010016900400e0b00224404d01840c8078541e0700c40e88500d03102048101c0b601c1700c40381140742c0e04100300400000b01e0008135082140d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 79733760 1250 79732510 79732517
    0xf0e0f04021012021c060501030c0216140d0204050702010510090902060304061d0304080d0909050c070f0305041a19090b0703030f15060305092a0f0301153012 70
    0xf52200d030b0000103802481110300c0f510502680c1454141ca1075000b0300c05484007070380c0c101b2451400440c02c0307030b545142c0c19044c144186108810f000d5a651010001c001002c00303440388002c0c0c10558040313800c803582292103030010b1f50346105101004103164405001450100400d0068503142d4000607000d210181005005642c0c03821941410404881d16081c032080d04019281c030703190783d85035036502c030030102100c100000d41c446004100469548a4940280350800445c1c2c10480c0f9541c0312101c10350304000035001c0c08800d1100244e84034100410303068092080715502c1c2c5030244140307032030101c010404c01e00c0f050042d50351043c80b42c5c01140c0155202c1a4051402081010803118140002c05030b4a6500c0083c4074010004501c5941540180c2d004000d02400c4411050302c0d2020030340c0c00200c066004481442d4418110303058a40f148840056030402800016650844102c1c01e10f40c400b1607019102c4464031101c0902c00c00c0c040203450241003504140410b01401c180d461700901101100d020003030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 79735010 1250 79733760 79733777
    0x10020c070503011817030c03060d02030c090a06080609060402010203190c0506040303020415081506090114031513020a08070f110706080a0c05090a27060f0e0f040210 73
    0x1100041040d0350007008060020004440020348201d03450750511016251202100c80344000036800d5000c49110f4900030386d81c10b0458503041300700301c01c0e000e490318223036494480c0c42c1c52085641e17140540c0902450a62100058051500401c542065402411010079400c00010403000d80d80100032200158400b103050412042d034004281c0d0f44494002000e40107210300c800304810103805038001c000341c803e40310300e481210140c0c040c21900c07a50300311080c0d00e20040006018800b070500c003001c0e0240c40014144403942122102c8800307003075002100c20720f000a215100c00b02035401d0110048081c2ca542070401d514001e24140e01034480003001d4028010465000f031703e82140c0740b00c0d0031550a000f030b900c0165042a070759003e00400c520000d4816801d031610700348090081c41d008008507011010060001450a8a45002241c0ca611040c0c0b26030410b2222a0850351644081c1c0b2071003010b0601c6100c0c800c852401c090780e0340110714005208031058a045014000503075205800410746074581e240c00c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 79736260 1250 79735010 79735027
    0x8180102041a0c07030821010806091510051903020a0b030f06060a03091208061f27030503040612050a06050607061d010e060114010305011a0309030f040b13080f1002 73
    0x1400d681e6505c00781c1441004503410b1041610b0042c58500d02c42d00000da40581c1c1d80f501d4280c0d46502c07042c0d03010340c4654045194500300c00541940c07668030070400c030079408295580b200403502d144404c2100a501e0b4a18038424021450206030501c0074091500d0690700f1490701203208403401202a01580c8240804280310207041e21a0b0004c2c4a910340c0042c0541e0303003618401c0c010b4915003040d691540324411400b01440d01c1e0072003100f07000c0c0da0040c0303640326140c40c8903461411b2241183c0c0d0f1002e40000d08000300200100e203080000f4402400155103000404501040301012100c007d0161a20703a414408204410f641d41c80560780090342000c0c0000c2c0030200901d441d000b40c45402ca91003055401c041c1504d8040b40c0110342d490413641c100c41d5001c1c218008a004508840d403d000b0a2089400010414659090540a1640002c50301d084903e0030f20a80d03002c0205d0b03002a40701c20307044800026801021906180610000d04061008005e4000440551a281e40c1d101c0440d249090380841d8440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 79737510 1250 79736260 79736263
    0xe030c0d030b13140f01060f0509060d0605030f03030702010b03061501120b090a0c0305090c0619020a020406030809010e010c1218150504080d0804052e0c08180102041a0c 75
    0x246000c00c822000c00101e12005820102d91808890b03102c41705d90300900014400d8000c0c1c26000c19041c0d9503403076618003018a020425903420100c20110001d036102000702c0c0f5601d02b04901031043c4030f400f00540d203070314111100900b541c0d0001d44440c0643c000034184031459554003414058a00309080007089005201800350051140240c1c956111000d030341401800c1380c465000d20444045641d0900080c0d90302d035a080c0e900c40c0108000c0d5000001040400c0301e0070382c039401c64215403503284185c50f2092016000941681e1481c1c205891400000429403000d6800032751700128140d00382444c002c0c60f81c668880300081010410300c101402420b034100c071444040c4440c2c2c1005450303036441010052040c08402020380e00140105840e9210b01502654800e01a920303a034442d5511100030700c0e600d100060b448060101c0d403614a0035194001c20b0001e2896502d01950000081c1c95407045043e15040e900c914034018040041ca030a40d00c1044144480100042000324580d06210340c9a0350700a25105607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 79738760 1250 79737510 79737529
    0x305120a030b0d1202070b1204080901140d06260a060f0207080d0606080c040b04140103020c010f0902011404031a0702070806040c0608060f030a060b04061211040e030c0d030b 77
    0x40e6440b110f60142a020000b59100300b00a25009078200c80b403460f25205a8901c5110b6200803450700400c01d0000f50000384410f00070a2505010300d00440248000c110000c0f15801c80049c200c2e0703144c1c98100a01c102e5000c5d480d05880c03244001040d140401185414585a91100801411050f03d98101d00c03c2c00c1325039011070b07112036070240801b0354414a20700103038003d00d69401880c0000e61b601002c243d4051f000310544041d15a5040000d14003403a0060b110703c540711801419060680901403450034050a100d2200d03103031903503107000c90f0158061000602c000b1040f4120b01da0b07035205102c1400890380032a50040b814504480395000c40d21410300681c1707884295030040101b84601000c000401880510314821a1019140c0f378807203440341802c101c41c00c8200d4081075003552040b503104010402c190014030484501501c00282c4646a528001c2800c0c0d8604050780e81014110078841d15050074880d0041ca03a140f0400b6505100711001e60a84610150301d00700201501c540c1c0e104210b40d10500003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 79740010 1250 79738760 79738781
    0x1a040b0703030b1504060801090c02071d0712020f070302072c04050f0a0c140a030f060906090204020d06180504050c010f1e0f0f1404091505030304030308060a0f0305120a03 76
    0x11540c170396543c0d43c001061074009004101465091001e0100c0707440c00044e005041c0e0311f02e0014003041c10707440140c8802c0101c00510b0312040001c12040c910086d00244002c0030880c1d200366000750b8410721803c02078603050b9140d10004100d00e00c880314090380d40c00c2611400d1031429804c01c0c00183d85460070300314079200c04498510f01500800040354108110340314903404489148503107101841350801003012082a5204c0a403c4800c600518000112254000e0b091948030b0040040d60380340e1078010800700e1300041071258140da503440d814850311190714103000300034400040030302c682d140c40d41c0ca06460f16038018a035410320101c8040000028001c0c150062038111881a03824580c040d507400a280d41403481100c07021035070006105c42e00d14032030720000d0b46024800300c12034a014902070031000100240c8400d44074445144c9404226560140028401503000c0d82d0380c00c2060426000b0040e001c00142d204070f40607031160004000003500032031000d02140c220340c45503845121080701036010349108000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 79741260 1250 79740010 79740049
    0x70e24041707030c080309030a03080c07061104081504021003020322030e0f01020a03210f0203010f0e010f060903060b120d020d022103040f02010c0c0f1a040b0703030b 74
    0x21251000c5000160030000c40b401503910480072540c44060766260302c1404607d41d015003002c15041c0110b800f900145400803c050602c0d40b80c520192114021076100803501403c0081c006820080d41404005800707820720240c06207826820240d0008420141075014201030540100001e42664840300482008429241e288a40d6100912b0b0041070455520500741c810805400d420565500c0000c1e406100d6031300d82c80b0310551078950440041c50038024480c8807811926554989134200e21030015500901d032408043c040e480c18003022402080c0140c00101010600f884208841039014066500303c98004200003120080140800c4400306922443c40080c812803d101041641c000303900c0300f9044c0f5680c25140a224034040f40450001801c582c49642c03c001c1c4049000704640780d540c118120310504140c0141182640c03803403001000346c0c0c024020082e122038100142058100005c4820b0340b600d4810b45400d05101941c0301e40e0040c2d40002d07082665403404100d00780c403552107241c4011514035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 79742510 1250 79741260 79741289
    0x70206040e060102100b03030d200c03090a05010309020907080709030215090108090601060c080c0a120206070e060316110c09160e0307030c0e04080d050a020a0305070e2404 76
    0x441030200d000042d07401c54018031604002d40d588080e40d00c144045440c000703010b1403a00201ea0304000c0584400c1c0041c2c40135000c135042d41114200c0f5100140380503071103c40616215242c910400150b200c0980c031883c1030504004c2d0420050382c13a0300e2810340c001c8450500c83c0198503540c00864200065400094106900000317401400c0c115401601010000745c0c0c590005a5666424a454000c28811b03140418907030010000040c0e11280900143e845540c116115201030ba02c130703010504010201d080140e0408000d111080303510005020100200381c4036149142001e003940c4120518100172a4100142110011060f00e800d10031100029001814a050b81c10207203040084903040000400110341c0c40644d2943c82d040c04980c1c1804c60750440380c4840740301e282050303070180d09600420031280408101b180070507108951007803d004c0c2c41c181400580b00e8003031100150883d07401a00c22014002c1c0c914200c0c00c29038504920710340d810401c40c102c0d100c88a213080c03001d1040c007031600084010100301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 79743760 1250 79742510 79742519
    0x7180801090f1b0302031b04020d021201050a08030c07090e0a1203020a0e09040b070305090313030b010e011d07050a0507020607080c151302100905030d03050a05010801110d0b01030207020604 84
    0xd844842c259009500001507202000d210f6804040b2902c070080d019045803100d03107280c42103056107048044010b00007502d0300da03800b14054101e07400f02103c0070240385080014809400c1032102c12005d086510300541c0f426004030000c130b5448000d442030071040f43d1611800780e10b9060900081140c55840a0202c4100301048000740182d00300c0300000c00014196071044038076140c8520494040c0f50070851040007034507000b50890180800a124014070b22080001d484095101c2c0081c600440c0220b024500c00c2d41442c031107606900c010780c00b10400202001000c1801a0070001c441c0e045985424050b558400c007543c05d60b41c81c010f00c04040e50002c4003064140a020014004088a0301c0c7c810035642400c03100ca80d101842d01d401d44e040c02e6804220319071207006042c080200060325802c1d0902201c0076940c0c00000385170450514250001980b14018000b4900c0c150103a00d02400342074000740000c0d84a00300d02a0305000301054110482e4503201c2100843c0d0107941198540d6030050550703070761141c0b503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 79745010 1250 79743760 79743773
    0x50408030d0f0e0d080c070606050a06031418060f0601090803040608060a0f06020d030f021b010c020c030c0d0b1e13050c030a030504090b030c100309031403010e0718080109 76
    0x184529585242882e2034001440c5011542c101e03d00744d039031a01e0800781c94a00f4182500d803c5118100c8503c0d0741c644004c40d1a6849040b050010082a603001c00e03c1d40304000c04101141e80501a9900e0b01c80780046840c0200000c0f81d002d51064001c0074030b01c0c0d60380d620001281c07841403d9000c80c1031400001030200d0540e44c448035403480351134140c41d080c40c03850781c1d184281e8108000c1d10810380143c100038002d1340c0b00303071082d0413156807010399540140c1002c41c0440b40c80704140002c41e12480750b0795604032105200303405000120300174000320040d001c400382502c00b00300340100d0900020012031002e0001600001c10140c80c4021141381d01002c3c0082c0342c03401211410328080e42c0244d038284a42c01641c80580b030300003440181190306a0310b00c0d007054a4100c003080540702401c0312580c140a5040309030b05913110f98001c60301d43c21035076802040c000c1040c03c02070521902c1e2604148003c000f0030051000c1600e0402c0150001035a00c1d00007421407010f69118000d181c41e80002c4072950a281550051001c2c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 79746260 1250 79745010 79745021
    0x21120411130203011e080312010b0f0d0c05030402130c0e06160501091217090c150c0a060209102d111002030f090a1109070201060e04080301080601051203090d0201050408030d 77
    0x9104041401361b8503543d07007560303e00580800c03100b04000d8400600101003000054001204e1044805080404490100302594007040203103002400210412003945840342245c850701032005030030052440c2d0b000c070043c900223021540c60b0289100040084124003500500e40647e074108000b00041946403800d0302ea0100e1051200300050300d0f07500741d0100135019501513801400308400410000b10f555003440354181030344613050b281007000d010040c00300c0030900060700707444d03c11080141d03200b00364001c00c8412040fa600401c2004018111210810742103051550f40640f442d2403201c264072107800840d08800007041400080c01407500740030412000b90061801510b481003010860b81e50b48481c2c5a948c00031807805882c0300c1e04c030034441511b82400303041d07240c0080d81840080b54a544504883c4207900c4151403c0b9801d49000004004600d400d003c424050300040390701084400012000c5d65407070042c083c415126401c3d01c110181168080c1049030000e080703141c1580c0e21a42000110001840c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 79747510 1250 79746260 79746299
    0x40602010b1207030f080408100605041109130f06151119150507110a030e031005061f05041a0c0607081b030a020702030106082112041113020301 64
    0x60901c140100a03151a015900c110034910006000f2140f440e00d072403402c040141c0d01500d400c44200400310304100d0074001810802403011000c0341492034402070200701e810103020080a1001408920000e0769004408201d03007001301008108046254003800c002e0049a1002d00401195158089420380000d014554420801c080d1207185030303003240c1d00344d4194001e41c005010014141150300c01c91030702d030321241c0c00c000300f85450aa68080c0a4030b580c940122540c098001c41c03407500c42c1034840c1c50100803943d9501171181c814425410072001158400c1c0700e100913803044003a0403945100282c85a42518010b081d55a10288200100d4100c91519400003031030440d6030040400180150b406612514050554042c1c0c0008400c4801ea84100079000a080160259001c1000c0000341c1e030240504805400e2200250000d500c0b5100040c0c2000003070352103521075280c10301054074083e01210481d50300c180c0000d8803035220216580019000509950300d21141840400003180c2000780e40d1804280c031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 79748760 1250 79747510 79747513
    0xc05030904051f0504090c0e041a0712110c0307080c01090b040b040605070206040314071a0703060e010812040e040618050303090c0603060a14031203090105070327021909060b040602 80
    0x84c0c0700d0742484180d8216480281030b05800c03003410030112040329449544140a80b00b0381020724600c1d040b00c5035102003500c58100184502e0fa01d010161400c0c880d12440070310300010507250000e5502255140e014060010f02406404151119211f6080d00821040303903000403c56654030305881d20950300c2d0020340703058403454030741400107115500004a40b4095900342c2c40318101150b1400c0c0103815580001c90444040742c210b950010382c0c502c00414540540020b03113022a2281c201104840300000c16849482c869215101c44a032601e1210101c0b01600c5e00c90410b50f0099507076040400240000c407245080320524002c1a200b80b04011000d14064492041900ea0a04074481040a2400240c6209501c400f40c0c0c4001c01c0900ca0a84d140c0392440e4000d029a0803884100706a028280c10880340544107035111020000e40c41d0b8984903041c0028054030b072347d00d84a03503030000c4448121210030f0024010200240e21500c88035110124030b0082850203414040c141d2510000d43c00354201d40300d100c025 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 79750010 1250 79748760 79748821
    0xd02010510061b110d02090f06030f070e0406021803060907080706030606050d0905011b081501090312030507050c0304120204050604050c07030e010c06050a0e0f120a0c0503090405 79
    0x500380b081507000404814034151040058080d01c0300c45103140304100107036018100c0205e00d001a1a0790b140184101d129624002c298903040082c5414141c4a82011085800c030307200610003000b8200c4d0003600180c112800607101c0d000c4010002c0a607801100d40c5926100300c00412004910020301c141c00c0c0c402080135282483c0e035501382601500c41c5c0303004a0780403c0042c4400c6902817426405508454050030004c00c050440d488400008910440048000b03004c105c01c110050b40000d5040340b64a8007840c021480701e2451f1100140541d02071a00410542c9807400700c2e041038404d1068558012514041e85e90744c541c0e414207080c074000c042030124041ca0403c1c00203001881d161044610035404089410314151080e541103c45c164259990f40c18091412141404504a0321459200301c0c0030400020722610755200180c03070315141e01d00c01d500c140d1107081000305070723181c503010790302c1c50300301402c004160151320300d41036040d4010380400942052402041202402114180c030219410740300310108c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 79751260 1250 79750010 79750019
    0x1e110a090216150609020a080103050105011d0c0318060901060303030e070305030901050c03040902490b0111010c0207050109060c0803010b0708120406020c0c1207060e01110d02010510 81
    0x90b0300462000490a03034070720040da80070070302c095075480c0e100c11141e80c0041d8054550104070201d81100d5011340000d050300c401401000b0342445114050807c01e8a21601e640050703000d142c10310001000341c22013460100c082404244d40071616031554040905a50b00e510b800320040b4002e0800740701c1540000e003400504011218041400d4058036084006145020211401035599038003000003030000303210801000452010f503101816544e0706c0748207980d8100080303001c1000d105211801000200d40000301082c882d42c0d402d4034482024050800100f4042100c40042c0c42590043d00040302c2d0b94240414100f1141e03000c51241d040d5007090700c80380c00781a1195011214800789400c01840c940040006210800468028001142c070650076a45040c01c0001050324403181070300d0480c0e600d5000314188200031003d026203c001c40080c0c9a000851540102c0d083d91010b19209090502c0b4445d00d0014903030b481089482101c2d52403604a8016000c80e407802070082070b08498441010110460205 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 79752510 1250 79751260 79751279
    0x9040c120f050105030705042d061a03060a0302150706090501200408030a080c071406070e04020909241807090504091a0601020313140411090a09091e110a 68
    0x28140d40d0090000c259103800c07c07052100030299403031070711551072100c01010200200e000311210200c50460b004030749c2d11300d008000302103000400f409640c2554184100070b51038903030718010310490b43c040310508421600c0c0c88601c0c0d0140f05800d0058905070502d4040c0040c82015044802c4500107444080030a0381a180c4d01403150080b8003503d000c40c0c02c1084400041403140314000e0b080040ca0290518200c40750b6a9280788217200340b09000300e40c0000003080903464120341c50b00d012040c10b94013075103080030100002d455000f0062043c65a0454012115225078101500c00550704010f44141e501402c8030352006071010040751400700203019800b0210703003400d080c0104041e4617807154404441072200425140d24000040c90305045200600c1400706502003040b0310001003142500038411205c20500f0722060380c00c0d00070208851201000100c0d21502c8040c080300869129280000303a51002d03140c8140f080d40060082c0c2020080148140c0c01d105150751030311481582154917078000c1d0342e2030f4600c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 79753760 1250 79752510 79752521
    0x804050c090702031602031e16080c030718140f0a060501030213360e19170d0b100e09090c100f12020f03042a05130209040c120f 57
    0x101d005130020700020b42e408200070440760440348010180c400344411203003035480660784110054010752140c903030841d000d8140c28450028048181c06440114030304004660340e100d50b842034000a61501c42d417131003041540e0340070400f000d1000440d01c4090400b0b4518900340e00007a51680c900c7ca14004000807035600a2089580d0803d40c0040800914500984082008a100d00b00c0c61900d60401515503140040700580200101d6510001541c0002c01100c5140003203402140203008919081c100118001c0c0440701801c000342040b0950340c03145400800050007600881b5600100c1001242030b900d0380252404004590a40b01080c42d581c400f03004c595a480e1402d856500840f50a50f01044103100307120a05261000b404d095070960a1018190104c3e401031050116041012081c00308101940702070700742030118070004d0407101030303019a030800c2d82e841d911a180c070500080c46240b500403180d1301503941c0048000c0040001e0011204003404c0341107004c1c80104082c2c40d1172040300180d9290302c200c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 79755010 1250 79753760 79753771
    0x30c02070608062b12050406020705030a0b010b0901020304080304030501020702095407050306070921020d060f0507030501050409030203031807030c031a0115050a230403030804050c09 81
    0x940314141403807a814510030750000c0c40720660102c0300501e00302084644100303c2140249a1b1030baa5613a02d40f000090510280340c000501c40e0708a03a000718081034004c0d81b241d05580f040715510340c0e55404040140e00e140310395840410b40d0f010114000080c4007065002d080054029a01100ca035614060307142c0e4140c01d0904007103e80b0b03800d00c480c441240000160010f084150341c52181500b050598135802c40e2030f0a040090700c0741d0200c0418000da0909102242d0002c46074100100180d05000181c003400c140222500442c540c224040c2040d580c135079818019803038214401b041103040303115422019000458000c00403c2c04d20000185c0d604040c8240310256030954099421500c032025070051341034000700815081c1c40b840d4404400318010380701c8140150b2051807441541d40070090203881541050344010340d505c040c2c4101c1d442c01d07a00002219004c3c41940382608041c10741a0134000c588009070200074064002060100805410460907400f5601403002c0343c06000440c8100100103030f04690 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 79756260 1250 79755010 79755019
    0x1302120a1109040f200a09020423011d0105040306020c0f0c03070506070b04140616350402010c081c1109060708030a0b040f1e0b010e0607030207090c030c0207060806 73
    0x5902c0b0101e00384503954000c68045c41c280122071080e8174002414964035800c110308a40d0b00060400ca000c180c4903c0586021440084914805091001a02610801624240714868680c40f100d090784100100c4010303541c4070104540b01d608a502050741d0f01c03c44000d40e049846503a4030b004841c500029880100e402c01000e0514020a980e00c56540c0880584200d45414200c110f401c0c2c145002c0c041036101b8400350810740c265034800c40c001000501d144603024044d0311004907032400017070600ca540c504c5c04100c00c1c0300001034559200494440080000c060724818011500782512041c0110310142e0060003142404580035607450b000c1c9500c151464558003141c00c0145200040b004409540c0c480b20300d07240001e03024a81404901522048601e00d40d005a0718440c40310200200e0045040303900c2900420030030042c6d02000600078540303040e4a14414100032984c030040600c01c00004015220070340c400c0c002003001d4200a40039004400d01030015014401011072064816030189205410052 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 79757510 1250 79756260 79756283
    0x3060906060901090c02031c0510060302040305070e07050702030709050610050c0d08040c1701020d0e0a151802040614030106290d110a080103050105150102151302120a110904 77
    0x341030b078010007241c175100d019400140004505100c01c0c007035402d52100200408640703851710f062000314007000d50b0806401d05105000c2400407800003e0301e001500e6210341c174428213491b203000030769050090b01e030008d5042c421103c1c0850001c4480d0069130041c00142c442c26041d58088206507020700603070b082c5c5051540100c4c0e121445074820780185030050b008900c032a24598454280c1980d000c001d214039a070584d00000e1200c144030f200d104e4241c7c1900b5901c00f40070342c44903070b6403442078240c4035a660300d408580303400e40940015407003011000055801030080081c50303a9010713800e158942c0800160300c43d510b4480002000c41da0030700b04541d841c19002021088104003031282499800941c85000340c0ca40d26013054003550140c0c00100000c65580e1104041c0758994030b0101c1c00c1d41c1000b0502d6124502119000e40166000140d8072070308070018002038801e0b500e94500601001c10f599010f0350000301c4c1071032001c10000204030480d4440c0500a0703080e000c1c040d01c081c400c03600c40030740d0014105643d19 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 79758760 1250 79757510 79757519
    0x4060c022e1508070e0615160303090305160c1805250201061703030402030709020f090409080717180a030b061e0a0b090910050604051c0510060503060906060901 71
    0x80d40320301069404003030b46088454484000d01c0c6040419001180c2c0f010b802018049549010744031280f282d64848a0742d0300d012014640c040740e6a00e100c00c010249a00c42248000705409072094891140c03903810a2030f80c070079070b60400c41c8040416202da44daa22403040800818501103028580c4a034802c1103604542010011001c951145015034a0b0115541c07880041000c01d80c00380488a40d4a69400440e10f900307041c0101410514954095044184100b000c07103030300440d1b2810384605807821600021542014101382e1100e2140d0400101000058068600e20780c4260002c0d1035864100c075400f06481d000c1405020307566004c0c0c0800381c503800d01c51000404130715002904400c01205410015084444100885c20b0310289800c81c07013a084003c00c0c6c1f0400b5003442003015031b10845011000801a1510021032072901c5907004003070141c0f4850043e04a009182948404456408012070340e21008401c0703504001d0005002d07a501c2402141c020520001c00064054041d02d001072104445034a030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 79760010 1250 79758760 79758853
    0xf0e06090a0905010203040b01150f0207050d0203010f0e01020a1b050309040c0318081e0426191b0801020307140a03092108060105030714091804060c02 67
    0x70018507100351512500000a1000e0025500940c4603218102c02941070a600071000381c0c1000d490300800072940b030b043c040300e80d00180c1e01c0c00701c91099421b800030a4050001c40d01512201c03194580481c2094085000c00505600a0a18003540d0f0740d0000018850b81540b6048040d080b8050840c1c0d0090002c200140703080d60200001602609000400491070140380c010b40c190414140c44031a00498050340c0c2c154503811020262100001c09840d183c102804649031100c5000510700d942882c0e0310004842c0301c2000400c1e0085480006041d4280c201d142028222003405009038003044004000034020313005000344c074000c00464032101046144e1000c01d1000d5000920313140100358480b030119000c179040030030306014100d940c048540d828103614000340c40c00101600d0b060402000300204a8415070006201c0900ba41400c2d03115500c40d0040000b903e40099901224240c041c144240020171109502c02d55103071404d90207850207010034020408080304000c4407a03146000c13032000003490310720303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 79761260 1250 79760010 79760029
    0x10303080c160c0501080601232a01060504060e01080613020a09020a030f0c0c0503030103080c10020f071103030306060726030709031109100e0901330f0e06 69
    0x1a0200c40d05202d5148071148030380329106016144421200001d10407542d0100c2101e90002013800c050004805d13a08041c8404000d905110840d20b40103e841e0f0841440c0c0000c09001c421401c1d0b10b1400e00845203550390080400b441854461460100d000402144103a00a4104c0b10180050b01540d5034804a28941100982040380d010010f240003244019192000c2d1440b032150341c0c0e001401600340351414049809841c0d5500501940902040c001080001240d042d650712044407600c03905001030141c684628003c0070040c603030001c10030300940003140c800313807100e10b01071052400503030f8840c0140341d00c91005036402030b082042000324402207900400d01034280604003030f0f010500c85040912268542081c0c40c0d120000b240040300b0428000d40e40003402280004032181203540c00c044200b072031070800314801c0e4102001d16400141c541442948024820703440071001041c180d245092842c003420308120148002040c0110101e0700c8215010795105803002d20140d800e454035010b082100140c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 79762510 1250 79761260 79761271
    0xa020d0e10050313030e10030204030c0902030114060703030b0a0b0d051e0105011b02040c230f0d05040618081b010207050a08070f060f020403171303021c0b040506070806060c0601030308 82
    0x180046410b41c680c0b034441841c241800f075984c0058074ad500b1440c01390541027443d803240100754010f1006100c051031491070483d043c84202c90680d40e07200301c1d10302a405030100100c1e07107502031201070b00041c0d171000b030702d00078141d02106020410203035803105d042c0d050480b00d2400d40d04100414900520840d40504500d003100382e14460203000c4090283e0009080d80c8200f407030b010005950404121400c8500e0681c040350400710810141001d00d407101c11580c3c2d00595000d0b103229070300e4801090034814154000c260f2804001d484118401c8181407030282c561007604030303c0344020100508201c50740b062090300c1e1003541c00009040343d103825840b40b07a4290000391040d59205016054200000d00b01e10403247d103007060141c0561030b07600c0e5091044900c01d048100c1c400d04041003058200c5407904c10059406d0301d40c1101e0310f1310104486180707618a90003072076004105055103002e01003408000508948034044036a50458a540c814040c860b141c0641c02803295a540060014000039004400850703001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 79763760 1250 79762510 79762517
    0x170606031009050c090103110f0a03020f040e1e06010215010302040f1d0f190b0a0504030306050402120103110102031903050c130303030e0114100b0c0c060a020d0e1005031303 77
    0x40d5129900b01c4111503040d2000300c43c3c18800a00c0c010f484d40c040c0640c180d00c2c9a40444a820071502d981006202c0c4140691441010341c002240f502c05510001a14060302511112080524109003411081104c0351180c1000c505002d0009043d980f00007120b1648201c2020384ca40141d18550074030026123119004c058204c2d4846044804d09980c1904480d034903c40710700100081c81610040a09140704039006e08440f101c42101030001c580e0300c24805800c540071400004503a5600c0c202280100f01c82c3e045540c0c0240002407400600c4403025820341620300030f400c00101070444100690f5a480b4442e03651403410040741c5014803c9000c3e40c40702368010310900311240380c088644034044103094580c00c210f01107666484143d5a52000748a0600309100c807402e1100d40e802c00f10098028060180b2412207018000a21041100410300401c0b150f000042c14007519080c5c60340c80a500c5481407a555000100f082e00608010301d0222840154411030b511540d180d501e8861501d035107a10700c80b1058050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 79765010 1250 79763760 79763791
    0x3030e0102071a161e1101061a22030506040b1509130b070903030905040b06040b07050708100c0f082203020105220803061011010204030305180117060603 68
    0x465442c200d5a0154440d14290a403180742900c168202001c014440c01c007049544074601620120407005650324909608000c1b80b08050201414090550360f0090301c00b149406140c070070401c2d20003016000741046101e120040d00100d081ca5060a0740358030019002d54488404140490b58507042680c022080050451013003007030704040b406102c0c094905802c20790a1039101d5080c002d6284030250895918078019005034a5a02e0051154000c5d0103520300c581e684000000c03240e5103000480d070050280c9180706899080c2030804a46418861090746901d0091100c02889070703440340702e207010703c00d1140c03100401001408002c032000580107104100c614225840c00455803084020000d04520070341c008140c6180c10304409190305810803044070840300744a400000203900b00e003505c0c2c0c4000b09660081c18040540390480307250005404410007944009004000e00d50711000814055401580741000f10780344800445440c15008540e8450300342d20404039115142010082d9084918030480700c55 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 79766260 1250 79765010 79765013
    0xf080f03161403190905010e010905040e01140a02090114040605180103020f0c010605031b0102070b0c0307020a08030d15030209040201031d070905100602070303080c031f0303080a0e0102030c0703030e010207 91
    0x5542e0101d42d0f0380414816920004c90300c10382c08400c0708081c000a00e000c0040940c0341002030041107050058a04c00c0e45c0381c80724054005025400002850105a254029400c0c0309001c1002544171626850008110852503590000070034115001c4441c10340c0d41a2400b442036034030350210b4801d8510241055000c21069070440400c0c4090000c3c85000b000003d5490320344802c140c50301c01501d0404a00414403907800310260b0300421080304403091000040da66106080c2d1541c2940301d07a6800075404071404601282601000019158440041e5010031140075005458608090316200080d0302040130b400160040d403080e00280051408101401c049010a000842c1003510700c2d0001d8420942d1681042070300c0c0d14900460b4020300d81d038000340110714203580340144505d000400d0100340000000c08900d00203e02030045282c0606050b520405c80d03101d18008012131801d07184240f0081c00c000315000591818421680a5480c0410491411724141d400760050000008074a15a56007880400c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 79767510 1250 79766260 79766263
    0x30513061107330501050f0d05120c07060201050901050415020703020a080d1406060c030301120309091b12060602030d0b0109150801030b07020a0b0103020d02130c05040f080f031614 80
    0x4008a03aa0486a001d40002c0410058142c409000f101d04003400e080040040d500e40e2000b40703004010070348000d040000a418200d00d4818440120a110b000c000350f000741070300020600034180c5010703034000c2c0210340b80e40c460242640d50a030390252494019001180481c0c10981c000c101c03680c404e0040c4c900d01105034544207000d401072407499140540380d120510038510726181959010b04200c1c1e0302414a500c8030342e03c030364030b020501500002da611a0503010038103001d4801c0000030081d0b144d00340016241c07440034241144060384c011001c548a00d0088405002070b028100550f540e44d0f0095040000d4400d104d0b0180c40d0700c82c00f035414801c8441020850401140300c1c00942c201235100c6c1f550350b501d185016014000020500000c54006e21070140c00a05c034484900d0440b078040b40c88440e070b000c0a000040e003114842101540007031500003820510ba0700304010b00100c4518000f17540c12181d9481c040c60702c500c50101b0069854200300141224400784e5405245511b000e041800510046a002103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 79768760 1250 79767510 79767533
    0xa170a0f0b010206150d02031c0207030605161202160f05010b09060108090a02010302030a0b031005010e0c1e0d290a0b09010f0c03030b100c12030513061107 69
    0x4092603110400d1240280240c014460341e040207200804003460700044525406144581d180d10611400380314006569041001c00c4071000071085118403a40301e08400395030390560748800c03a180360500c400500440d040402c0c0c41c260b065a5103808413000784940fa84170003540070182c0c44603010560701501c0c001c507603d00c003d503032001e115034000940341d2501e801b0004845401003a041c100270903802041001a408079992890940c2801c0142e100d8841e04c4140001c2c0102c1a81300341c142c03107802e105000403401900302e01d0403190315800c1c241c0c05880e082003060007481001c8801849010b6107100c3c85c69601088000e00400114100c001210f80715401c6400c1c003001814445542800045500b11217403804582900040180e001c040346440386500001e40b8040c0b000840f2424007401e80d90076424076000317401440c0300f540010a001140380b00c419000c0c10081e00c1060544080c0305c218200000c0300e00a110700c0b4000d07c44840c4c2c40450310056519140948865000744281207018420040081c0300000328 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 79770010 1250 79768760 79768771
    0x110f07030609050f120a0e0102010b090906040c14031e0f03040b0a0315030c0e04020f03010e0709050f010303090509070c05070605030106030e06010f06050706110408010b030709090302060604020a17 87
    0x2c030724100c2030f0a00902d00701440e0b01048040d00010160060a00380724126061040d00c0d0500e01c0d03499402c000140e0041c10702e0021305800803106401c1000010005c80d4803031040e0310440ca904122510743d58400e074954260b02c1c201d6055403100340500c04488400c0001d64080070200100c0d12400600081c2900b560050f6011b41907000000c258980e00f55094014006080c21001301040040d00d15100d00405802038420701500c00d07150000700d015912019840c0d09000406402808441d0310002400c2d030321813092240d4001c4625002c00714064155640d0114103e80d0980e4403154014209002c000c0701340700103042c1c0024050314194440c00920107001400051209031203540d02ca40c5801005402e83e4021900c0d0001038003d10014000200ca0711811400d5030602d00e0241c0c0c5480b12803600900801c4030b000036010a1901040008010505400c51344082c1c90540941d140940d031100d00f501528404040140903801034000648203040c29805407003640000c0c5002d242ea9990000600844401900c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 79771260 1250 79770010 79770023
    0x6071e11010206090307050703080d0e1b0a060c1a0702160f050a05060a27050306040602130518010902090406151106150306041506081203010807060504030b07110f0703 74
    0x304010540c0c040c41807607404040c0700041c6140007400d40c0c403035883d6121400014108440030440c000f110407030b81d002c030b401440d19104840d01801c0e0b406c0c25070892881fa0341014403542e01d0b032030702040320392080982c0b1142c291310607103103900d07820030080301031039001e00034885c1003140b0600211101200d031041801d030041604107410311049090000b400155480740d0003c90007100300700b080b80c0c10207901480c0e20080f01c1030050b1051921441845440e50042240e11aa0345442804140014401254014189144012040e4039181e60b61024070482110700d00c15144440c4450b00100305e00c40300c0760000c0100c80c03001040019500d440700010300c2c00050000149000441007902c2e0300e2940002c020303098000d240d01011040c031885000c00680c1e035280c02800240b892842d081d00d860001c034240c02c020042c1000030156540301d910800001d50380d070800d101d980d0700c501c0ba1305000113003240100221002d40340c0140104849a941d90019a04040b410b40f02d40c1042c41485001c0b48075940a00c081e0020314030950 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 79772510 1250 79771260 79771283
    0x80a14120108010506010804080717041509091508030f090a090c050a0315150e12070e0709050109050607030503040c051507060f060b04030320030f0901030510030305040506071e 78
    0x100b05800c4540042410b030503c418501440042411081607403d4036901040c3c0e4000d510400603281d125001d01d03400201d55620800340303102c2681c1c02100202c01e5a10b0400d0400c400003000550035a0b000d40c522620009420800661300d055154000070643d0031000341402c8000c40d900e13002c0c1300c101d50341d03100d10a00260020500801559041c010020510208010904101d08020142819288682903d018404640c0c115111a102c028002c500724000c0e41c15100442d6030b5079041c15040c0c1c0c0071115070300090b0201c1c402140c070b98001c8080340290380d0054512824080503a40079a201d520150069400c0110020001340c0c0c0c3d0b03660b10351152640c0c4030803003981e2502828604402941c3c0030b500000b800c0c80c140003060100e825480c0542d002c43e601407903d001c0c031448581d215010f040c1940e8804036030340000200c40810f8a400c5c801440c0c6a0001e0f6400c00860b5070b03101004594503082c0c0001000110304000402061810f9405000268041c03002800210000581c141c40c05034142801c55003001c004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 79773760 1250 79772510 79772519
    0x2030f07060915060806150d02040203150307060f021b0316032402070203061303180b03041205090f0105090414011d060d0515070311030f04140712080a141201 70
    0x583c1004060324001d002405030b90705000d000c0e6280c0d00300a10b141d0f004d41a031020b207415983c0b941e600e0800d694010340b0455890400098404142c000030501902070303c680c0c240021a00d200340307490b070520841540506a0400030920113101180561141e643c1031294007020b0b0442a41c0c2e001c000010b5114000201e0701c0c00c41d04c01c0801c41c1e0708200b1900d410a80c4144a01d0f000350700c01003000d0350b00c2510346c40948007e11a40c41c09550003010071500c6210742403443d0f0040b4402c1c0300c0300d00850143e03010b44082150044004412104ca00c6200c0c0a207070004100c1761031700260350080c0301620380e010f80140003203040c042e400700032034001c03100742d000e80711540325022004c1d80d12802ea00c180360008000e940450081c40300d52038895460f02c00041c00713020764448600182250b07200354041c0e04102518015030b5620704010801c40c12000c0c0075101503172860019410000410701c001400740441d520303d6107203042c54805032122205508136201c44028460303041003400c02c10400400824444010161121165060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 79775010 1250 79773760 79773773
    0x60c070504050c0405190f090603030c08070314040801050f0604021810030f18061d06070c0602040e150406080606150f0904060b040618061215080d020d0201140402010c1202030f070609 81
    0x80c8e0384240e030654035105043c004a6030016202c550075420440d080d54802c26440d04840551101c440c01c10105804a0080ba08030019004280100d00040c01d2419548508040000328400e0803480c4c0064103407207010170101d05011400300d040740b000d42000100300c02c150f101d44054840c410500d400074450340ea0807104010f400d2182d00040a05400c003519070000d000e45280da10800503000c18240030071541c0c80030800901b601101d004d40100104a107039410700c0d458100e0405090080144154104000401d1100b0002103561242e10014004c410f610541c4c00401c0081d407206007016502441040b600a003925103000d00c500410000c800b403551245030200003404a0b10f400c28010703003602ca203007080041c40d03400314100c207602910400010342d0654801440552110941c4084494050b4a050342c0100f500492032000b94003654000303200b8400e1110540e0540502202c0090104541400f0007020440c6404c00c4041c1601c00e00440b4517100620308080d0b6543c000210484007541c03544040000c0055 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 79776260 1250 79775010 79775039
    0x1507020d080a02030408031306020408031222080409020705030903070b190201020301050d0305250602090a0f0302030307060506011107030506180c031c03110417010b060c070504050c040519 83
    0x801ca011410341c10702c0d586d2071b04107210150060100300a500d4222061001950454004003004421a0354074000c2c092841c030b101c0c070b040380c80e00304404d08405185007002c0c002c24020143c3d9401840c180c58981440b1802c070094108640640c0d65100a1100307108a071410050240a840060206511440b60382c0c1d00315035074595030004608590051004103d80e4850307070024180d890380f5003485510b5894568540040c140c0c400c1901d02040c00e084114002d006d2117038001e00c0300800c01d895000d101a11200820ba03070240520000750158810050782c0041103240d8401600f0001c14507040c690385403110300b00b62500380c1c5900207071942d8110a042c00343d410406260340d10b00001110182031856101d40c00680c803400050344404990184003880050540320340e00032810f4180e003080140e20340761162003240e0304040011300e040240d860404052245d29000056a20b000d45420080041c00d00303001c1404094000501101950542400045810764851944182a46019200d43d401c246402940290f884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 79777510 1250 79776260 79776271
    0x9010e010b0d0c05091b0d150602010b090604020d0204080a05010212060a080613030e10020708060f061c02130c03020a0e0604060207140604051c0c050105090d030e01021507020d08 79
    0xd4408400c000740d201c858040c1144e0742140c2d003048954600180312198510002803060001d0001002030410150307a0050548000301410040825217030340c0241c0c02c851490221503804000c0d240001c0407407500d0b4008012081c9410340250600340d407084075a2410745007003004c80d00c2c0e035008100b0b003003030034402c0d60b0040e84500204c1f00c000c0d04c05c1c03405052030b4540c3c902402490030500204415000d142c003a408800e80d110780600700c64044800f880c80203458240c113005120080c041c100200e4100c04500c41c00341d000300001001082506c0713807014900ca00b030a500c107080f608000240c29035035401e0120700c0f50035030840c80c5460240e81c84401d2030b03006048001d0306c03007441d214640500060048650006070201902c071002e096a104d0000480010340301d0043e98803e9502040c0d0048250016100c81c00e4405514884c06000120300c0d280c0d401903840d40103558050360850b002c03c1c2544040b0344900d900d0840c142c0e06005844117002c2c0c540e103081400108031002c0c00549c0c4070340444040598445009941310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 79778760 1250 79777510 79777519
    0xe0a1401050105030429010f0608090606010207050d030c08160b18100c030603020d1211121608120408090102070603140f0c1c06060f030b0102060c0f09030609010e010b 74
    0x56040400280c4180400f170030240c401c00d411444c24599204e510141804020014550115980c0d07070800c9892150b164007400000032044400318403014000980c050044405130090600749040c0818007120000e405d500ba410805145804001b0418410040054030303058074081030f01010f030f400c152001c414050101144100034141e0034604110101c0c3c0391821441c01140800d542100710012006003590390406235001c010380030f40404000c00319813113452218080d1075145c00b4650b6082e0b9507451700300202007001c1d822001c215019202110349c00c0030700c40610032042d0310b04000480412018240003183c0448600d48002014201c6d50f030100503407070040c8854a001c0c000d10b04c1d041c50b0700792117100203401c000f00c00402a010500c0085e2038410b440c100c60160455a541a050030080c8014001a228480116801130f0008c0b10042c868000c1448007001a0002e001c41c2d20340340390303119090f40078030003944564909200b84901035906008840c0201403402c00450b00c0c44aa4400da821a170305068101d204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 79780010 1250 79778760 79778801
    0x50d0b030a0b061c060203090d0905100905040903031d0a020f0409030905060a091d011a0304050303040b09100e0c09070306030c0308090402250b331206010e0a 70
    0x54508441c0b2603114009540c4030128500a00540043c80c681e02002003050b0b0001c010054408000503041a207000b01d644c840d540d160f43d0b0028000c101d6418a0f00500103402c1400c203100c50f05254122184540c80380c500000d0380c1c60040c55102e9005004082a4095084280d084c0258a07164205900304001110100243c0a0740d81e0003406018403446014040d45002c030301b4a101c02d01512a1074000c20340452004c0a114035800d41032444407007401001e80402203002035044801c20b44084c0d1341b103284d2200080d4995202e030340b030303820303d0410080848000344500034120300e140038207004a5980d04580c100400040358500108400010001e2418003003610302082000442d1201c0100300031260005107581e6981d10030808100030340704102030011440c01182400080c1c10040412500590090011002c0f81d210001c1044031042c035002400c0d03001007180b40307484614510404e000c940742c50007442c2d1444444500182070030b04c00241d0000703196048600401a05405600480041400c9260604d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 79781260 1250 79780010 79780013
    0x16120608030307090f050a03031d03070e040b070207030807060e070302120307030207080105060d02090c0906071a0f092802090f1b0901050f030703090209011401030e010501121101090b0a050d0b030a 87
    0x4481e401444080c04100c1c078ac082c448688a0002c540303001c1100d000c1e046e152180e0700c0b14100030070300700150380403145002c7c0b0000040383c0c60700c0881c106090f203500c00851450944140c4441016041003030010200e40078035040000142d075042000001040250090b5486040c141000f0342040d01a81c080f0005904140400030990340d0358808503426a0b04a6456000303464800c1c0680c8180600c1d9081c0f5040100081e00c07505101c40e254021215002c49000c100860f075520704209203071403098440c98819441007103515102581600b40001c042421448041031003031580001d400c4480540d0b45a40c40f640000520010f80600d0301311515400a41010924091110000034060310500f000d4107441c20740480411820b81c8250400c0745400d0300281380c1c0c02156151601c540c0b92009444511f804203140600c3c001c92064103020300c0d030403903650221052601d80c154480c180c8500d942540d5030b0410bc505000410310040c4100605003401d074641c1ca294a42d40c819084500710754240c03019071305c03c4c0d011000100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 79782510 1250 79781260 79781269
    0x30516030506031005041502031003021e0a090c020a1514070c170a091805070306060311030c0307050903030d060305100e060612010b030703050a0b0a020a050316120608030307090f05 80
    0x20392000c07501c80029842d503031401d10043c0b051f081026401d14500000c14405a02c030315401100030307240210b8030f0400301d000034100c035901d000d10120386541014842208209101c5d80d40d000301d08005060040d62101401d6070780b10086042240c40c0c000081ea50740c503a40c2c04079a000b8011a07404045400d2a684400b42901c94038103408101c104040b0006002640d41d0300c0fa442090742000a08800307042c10141010b003c41c48014103001c4a407580020b24040c00011403034071902400c00700c003181c0801c040c0765403a1051035901c203904c003d101c0c90a04c1001c100b020607603101080240b40000c0c1603174000a242d030840c6081400d2100001d5045802400c1c81074140c210b40002c51059088102100d03040c04001d64000f440b4094005018078503410f00a801c0000144403001c51100702042c41003d59149a580e03016004007240507407190a00000c80a000068a480c41c8020900b103428207414040b18030100c01c01e442c2c05541058001c0c8203503801c04014071942c240c0260f01040542101d07007421091a04090225 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 79783760 1250 79782510 79782523
    0x20a050d05040512070605090c0604060e040902030a0b010806010f0e060604090b01140d020a1412010b0a180609030605070c0201020d0509130606030e0708070303080403051b0d03051603050603 84
    0xd0003255544001c542004002c01001050304042d04580c0e4841c00c0314107105c4000c1400302c03a560601d000f0030303107541141d00d044000c44003669100d1721107500c400c200e03005100040100c42012601481105100720104044011070f0f4020802440244440c1d030411080340350080c9140c0c421001001000c0601060b42c0e60302040d02c0945003c0740002981e206823000480d00c2c03c40b8410030300101440090500e0314084580c000700480c0b00c4503252034640020505002c4002d00c1202c4da00b145e0000b0190042c441c0010031801011000c2a500d00b07250200c80c609030661124100c0d612603400305842c0c82c000c000b040002d01a540d8801c5060805246440f00f03500044d4a44000424440030050002000c908941d1002000d9118070f66a074410040e598680001400421070440151401d03ca42d10340020810f10000e040c1064903030650f076502c5151a10b41d811341d82a00a003016203289120806803010310756080014030f5410015650206090406e02e00382e2411903040004401018140000c02c00f0f2510005020b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 79785010 1250 79783760 79783777
    0x6030609040206091e040c020a05060a0c020a24050f1003020906040e01020c010501140a0b04060311040e04060915180b04050309093c04020f030102040b070b0103060f020a05 76
    0x40000c16607031031001506500ca140d46995012032007a41005520100d540b4849081d482a5400c2204e00c4d0103076000d0f40e0f50b100b5180000c0c555800200000d100b54140e030001d29042c100b80c011030318000120395404000e01d48400c019031075200301d4035120511003100d0007030703580000444882c191542440000301d40c0c94a10b03400041c0c000c1d415007004c0b600d81e07291a4880741b56441000d0003151204c400300312080c007a10081c8100b03940061035080d1200d02e8030b09480040212130441904a280a262150a40160050481c1d00b01c220806110000304130b514064102e01c601d114120000d1210420701d4a180d45030043c2c045826658903018060a049020355201c9044c0c50308529420703aa0fa40d80c2c035166186205140016070840001ca040c0110101c50f04140051782c0c46803c8c0c208110300007004030040c0e001e40d010850f80120700d11000304016040003114083c2c0204083c0015203006d84800c2120130075400200c0456003d9030040040040c042d65101d03204100403041c5040d841c019048800400b41d001d082e48 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 79786260 1250 79785010 79785019
    0x527031005070203042321061f030609051c09050d060513020409120f020606100507020310020a050a1701030503040302090c0702040903080403030f051b0d0212130201120605060306 79
    0x8140c102e030080064038010000352000510400780580c044103003003c190060f0b0b0041810941003c0341903080c0d07400c9407040700c0c0000146415030301c40c0c000f02010850b10134400c1d40c4004841010020030180c0c0950400a4001e100401155030804190800f4a84154981003085006c000c06d21069803880365400c0a16086200410300d5116006554640914548001d60151400c8044810003040c030050740ca002c9403944488542c015480b20a03030300c0301c40444a0742d5010949004040360389020f0406007074954000340c219034265912203043c1c0e049a10005520f00440c1011500c202c51035404809c40c1001603c44e04c0d48117040d49142e886c25601d010311300000348280051400640f1100c01001910754081c2c00078800d000382440d600b0054002d2506071402d600107800d080d20403001c8409400f4403409607051070380750601d21100705590710301e54111420000c3c02075000c22510700d00b160382c0150b8078043e40e13500c00700e803191040034030003d00b1540081901c1c4d2400e508000c010803940d0340f20002e5a41c13010003610b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 79787510 1250 79786260 79786271
    0x40f050a0f121e2001090b160c0804120809030714030d090e0a0e10020a030b0906100c080306010509030a0507050406080d020c04021305030a061a011103180a0e010605270310 76
    0x142c0c4410242079400300003c5d62a04403400f0a11580000d002d000b5144c803028409a004030000840c0c0100801d00e02a0030717004100402c2200c03000c6100f0300003549003d18481c900b44111100061b0400c0c20759400300d48070f00104141100c403031a05008504000e4054280a0811481c004e00e644102000030040f009855452000714441c442c141300503001807440c20001c40d43c0e000c0812020b001450210030303441c0185007042c0040da05003040c580d1158080700e00e48400c3c003c1181e0340e64040050340020800c60400505101c1c006064400b0003038040740c1f42c03141d406030000300d09140c28030045566a5100c10007035404003089200c1303030340c011500008814050f07070050303603c02403241440000f4105034084c941503c0389218840900c11385030305c42035640f0307044446882d038808901c00440ea1035100100001c00c5030001c04c2442004a82c1038502841800060b05054046030b48054420101c00268006404280001030900c8984081c0464846d50100c603210062421002004a640c0e1003c40a404510640d204c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 79788760 1250 79787510 79787537
    0xb090f01080d1d041a06030711061003031706060c0307150b01020109030f230415020d030501212303070302190b01060c05010b120d0e04050f040b040f050a0f121e 71
    0x100c0c0f6131621705005004503540e8200300000500c000d4901c00c0d4040503002d2040450066a201e428840850743c0551321490300800488407003205807400740035958403490030010700002c00c0091015020842c054200310000740b041c001c81409130391400303d00300d0459260401e1900082e40140740c0082a140b0b510340182100185000e0305074420000a01007129000401c0000b6102c11800685d030b2081c05550030f8070010300c40800240d003540c0003800b440030802c201c078143c4004c1d00404000c001c501402108404541211504140d00290002c0300403000c4d500006860300503d501044030001400c0320034000850703581d5903158484050010300500003080140b529a41c10b200003504848415180240b01603c2c402c400b1054541d601c481844520220744807000c0025070745494810603204155034020703a666980d541d03071a008003810080c001c94010403070f060400b010410030860115503510a5100311111001030130000b04d00d07c00300000008000a040561145407020740c20040116203900700303004e0101e0b10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 79790010 1250 79788760 79788791
    0x1512090102071505041202011b03111e12010e010602060a020702030a0605010611071403100b0d05030a030b1503071718060c0a0806010801030f080d0b090f01080d1d04 73
    0x41e6000988500c0b041043c11280040d6035101c1401030b48203005154200c4000b0760107a00362559103840c1c92440c0d895091000d000781c040d8011610116026048504c0c1054003150b01003400ba2000110315001400301c1c000c0350b030015260030782d070140c0720b449440010b940c5032010007075442600404103448a80c011a9a00031500c04120303041c24650300000071300c9a9078640000815501c0181b0142d0901d01c0b5044000400c082c03001c480e50002c10380540030304091240001000c000c1c01850116580000c000b00200000c5801800032b0206080036542c0490b2065600c002c00c56810407045590414038000c005001d0755039080f1141c0320003103e01c0840d1540b6030340e40355000c20416540c10710f20300c3d0601440d8100b00000c4656001060b00142585608050b0344032200111000102404010301450110520401040d600d00203402d8810250001041e540010b00210b40142c43c240c40300480c4001c8000140446482440341c550140301d9440c007481078903030949810044019090860f8002c507500e0f0041b6503203404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 79791260 1250 79790010 79790017
    0xc03110a020606030c011706090c12101a03071211090402071104051005010c0f1b0801090606090b0a1208090d080c01200426010608070509061512090102 67
    0x1218106a0329403035650310103521000304488541c4240106448644c00b90300601d80c4100895100c3c8050340e60b96619001c0c82010f103000361004403c03a0080c80074494102e0320b60941c0340300790380782c1600d80c0ba001c5c41d10184001505840e208201e840c0000d0040014039640044c0c1c3c04004c00b24940041010041003400031024460156280c0e0840c1c00080c41c907080c0490802000401d420a4404004940c1c2c0c4a21080d510940c4c0c2c0100c6000507020403131400442c1211010310a480c1c000c0030044803001780b5207c5140f00419580c082c0c10241d45915001091111502c100c40003408080424001c060b080e00000d00355520030b0180b03160514143c41c1c648c050140034015980d502170080c02e4231000140904105402d40c1008100a01a601f0414402c40d0b03070000c0c8c05d807031449540c01408035042c10b00b8210710085290041c0800d074682d404041280444103000d0060030020a045030103010020b06090a1044410009040e28042c02c400e561150b15019060300321081c5001015416640362a02d1014501a12 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 79792510 1250 79791260 79791281
    0x4020a03050d020c0a080601320d030801090c0201110a0f11060a020301170304081e01090203250906050307050d0c03080d06051309020d02150403050303041b08031201090c03 76
    0x410b111075807a09580020b104900000c003181e401c0ca40b10b42d0b4942d21940c44009005866018950407007401c001c2d46060111404c000840100b5180c522180003c03858041c1c82c821b0036000941020300400003a410780c410b07002800716a10081c488e610b26000b040c1000e1003840c004000b00100380e56800710440c800d020207000381412030196801410881d409902a4100380950030595403909040c00c81c00000104440483d02c0410140c480d04040c134181d030025400c00d9841f200c031035480b4516280140d07824011820504026241e00d2002d142c48101c110b0303980300581241140915103442402141d1340012004201c0e0401c5544031030f4050f5a251411001180d81e1008103500404a080144802690007600c00c0e6001aa00481c0c03400a940328035003034402980d806500b03d28041a48400f6051404d845400e8984090080e86000c2e6255141840c6500840d030959800e42401030070300c908180300c1034100040c100080118201000030340403c00082041c030502040c07999031580040ca180c000c2d08410b079a40d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 79793760 1250 79792510 79792513
    0x8010608060103120203070b06090a0f0207030314100b09090a0e030a02030715180f061b020f070611101802120d020106170d08040615080a11010503010e060904020a0305 74
    0x55584002103a5503000a0200b151380c03002120110160510002c282da00c01d6030429002c00154844400b031110b07001025103101905031704d8074803146008600b4001003012900c071341d5001803c0d28060881110410f0b0140030007143d90f20240003000104900010b80d11003820441e0560310640b00c0c010103500404903990b00500c075000c0410310f84490f90300030000e040000e004e02c40200c40c034560039100500b101c1100d50b141001402d4000c0b09000b00700104108022144038070000103410b0850440c0c540c4241c0702c1194a070060340600c00c4201d6908082c403480d4001c1105044c100c4030316219045a40d140c085103441e40601c0d65030b0b0094100c4030403103906031043c0c26401603c0840000e0f0700c070702129110440b00078004003642c01d1880000d00c03948001d0040f501c60386040041c07c1d020300105001c43c2c0e101c40103401070360034503220881c80d08061404400400102001d01c014602e0011034500101d0811a5815281c10f0060a00040004220094003503a000c1022151a04541d6680c4001400c0c483d00b5000607120703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 79795010 1250 79793760 79793771
    0xd05010c11070b0307080703021e0d0b0f0405060102030901050a2109062a03090206041d0609070503040b0103030e12010603081c0b0a050409030516050d0e0102030304200105040801 79
    0x1500d4024000e0322104100c107040c0e94000c2d407120040c088a01c0291607003000a203500c000500b4861007603014046e0003034028115180c5005560401d0055040608001c0c491a55454115101d140c00d0820380030701c0c1e8007a43c0500091800d030b80040e40b64082e1503145414032400060700e203400743c4601080c000b95520b4800c003421440104402000418807100c0031a209403406400c1050105181c00910f0381c5405443c00c000006007500003140a464800c0c0100d8120341c05100200301281c90300100032071060b0189a001d40d5203060744c104006448040c0c00201030080c204188404112100c0c070140c1500e41600303000c6030b0025a04042034034808020400d2490303520b0600c000c4100b0450350001c0144030f4403091114454003540e40c0c03013030881d04410105079218040c42402c04c0b160609800c444c0c0114040d08000d0304000e540310000b8910803c401c0c013103030550001924541526040488009101000c0c80107604501d011360350844228101c0301841f40c8201c05804003400e9070303c0f80b000c82d805004010000c0c0302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 79796260 1250 79795010 79795031
    0xd050303040b070f0c020a030602130e04050102070606060503010315051003020d050c01030e03090315070e030f0102030a0c0509130b0402190804050f010c0801091a040c020d080f100501030b0d0501 86
    0x4000c802030f6180f100182e507503040c0c20b07000351140020300250350300208800c0e5814030755550301d0004e6208070a03006060070441c90001c0c018040100c081c0c8194080e00000da550201e500e421811103000b44c004105100c0188010300200300724400280c0410103013100000d40c1e0311161082c03524410540d0009500841c0d03d4500e2080100101d01c66003880000e0300c1c2406505942d1b1103058981c09011b0103190107a2205000056050b25000320b56008040703424064410345c10180806c3c18000e5800201c0c1c807036900081400381012042c416000143c01d1491714904150301480003510001c00d905c0030b00c488940340c01e03004155607902c0d411910030140100200e483d0010003180a008000c0448081c0d0303041c01030440046ca51101030051310240d42c1c082c1d6620300700b0f0b07081c0b103e14030091030001508070300c030b00315000d0036915912540b040b590350007910b4005040080a0a0b8018140342e001404419402c03131070350a101d440200c451104050342da09003030101e8900e0350b110208906050904001d0815800c0018250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 79797510 1250 79796260 79796273
    0x11011107031e020607050702040515090f071404030206070204020c16090b0102010608010b030c2202030c0405100207050102101e020706020418020a020c09040213060602011b08060a050f0d05030304 86
    0x301c0c01150100b088400707054016041e40c40d514120390050101d0801c00c201001890a644640d038807030340d00c00c200d900c280a51000304210720021148107121303d0300d590030302410540200d03440707140c0b014103000c030380c034050542e800b1030200d028203100240281c0c3c0100301c1407107480050007c442c54811700010507078003da40c3c0c3c01d100094420600c44501551800e0008650000c0600035007a150703c0140080180740c1070b01081c06000004071811341c28800400e81d81e45c0b100c080303a00045014079506401c907038480d8103200c100407003510344400c0c0c1000d540c003c10b000c021990f00403442e07900110710540c0024031946284242c240001b040038003149020710000381d600400c400c40d40944142c46100002e0100c03044a404a5022403280c04500005a0b00450008001745005040075500ca803002e01000c1180c000d14001c0d8080d03545980003100980d44a030010500e0843c1c07440d00c0040303410715250a401d181884004a80810700e24043d180c0030310b00c5003420313807803c0c1c40350401d4501050b84001280e58900e090300303251 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 79798760 1250 79797510 79797527
    0x504060f110111090f04111905300c0c06010603020a03060503030c0609071d0a020702060702030a121202040f051005040e0403030c08010506090f1e0a0e04050f070f061101110703 78
    0x1a110385481c1148140d1818248900f0711207c8074101030501d80350000d160580030380070f05902581000030411020f19089070000009a0f07510f40e195140343d0300440035245a0030708800a0017400346410900030303c4403000380001c605044407250700f00161780d13071a080000c4010381300350b400040e0580b1000460b6400c281001505a00c03842d01101a1105241c88001400111900610140100f030f99607010801025941d070081c602944000c00080c0303054001d9000c01d0400b41d40380c4c1c043e180c0c55401d41d2a14602500708254125402e5024002c41c5001d040000c941c107406170030f00515005244011034444c01c01d0044007101d002e00310070a2024021325003460000d02800005000303a002942e0300740001514105201aa811440010880d000503820601440100c100e03071080300e072803e00c0b5848005501d840d0400c050016154a54a01c510380c0340c50f040484c0740270001d10400c01c050b4080c1d281004451010301c0d2600c02c2d11600d1411040b14464608824090401548882c0b201d11000456004054200451 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 79800010 1250 79798760 79798777
    0xb061504030302070e070f05070803090106051c0c06030e07230904140c0d020a0501052a0705031203010e04020d050f010f06090b03010614040b040e0319090806070504060f110111 78
    0x1085e542d40e40c14400c81d80c0e4000041240046081440883c0c0010000780203540d11401040001640c10b5440e0000340d090b12039180100e50381c51000c001d12003401120084003001d0030aa080500140e11800c0800c1c0c2d90b00030b1391041e4160710a500c40c6410054000045500c1d18541c005c15407200c500306030030301c100a0702c0d0344a4a0400da214141c0c01691508000105a4243da00100301160882c500b20055946500c42c55000b4000c04111340305801d801c402444074040c1000a000038510607080509262030001103140c1c0c00341e10502440100606440b101d4070701d0303001c3d82c181e4041c0d81d410058602280781224100201c0d1702c55092802c5001e1001050340010121a407a00b024071050300480141400c071041070103404101c000440c0c1da0101414250800b91201101400c00104840070508103800c40d0040c1c00e85603183d003000303505211a954001c028501528048015019500304940060120b119620440081c0420407103440c0e81e19000742110050040036400030b0001031404520805154009401c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 79801260 1250 79800010 79800029
    0x6050405070509010f0e0c0a05070516060e040e0703020621070e010806010807080a051b070501050a1b0815060706050702060609011a180415030f0b070512040b06150403030207 77
    0x4c10b170006030300f818121135003100e5850441e1100342c41c000b4144c4c4200c03020001d200307003088010001041003007182500e40c0c8281c100b45c10903041c40c40081100104020080c462401d000e03140d4950350700803400c07601700d9a04642e03495803020401c500c2d440780d010301c00e18062002c5040c020860400d4102144c00400c00c402d80e50000305588000065440010030307603514001400340000210519001c2d48540c0c1c0140313401120949503076094403913004545c000003085801384d46690074400341c85024020440580812003124803510f407031480040901c2d00c004d101001102101c0007403001c68444808072200b040e0000310038401c2c1c0c600b000c0702035641c0c50181e44050151540d0400003510f00d03000401d0000004441902c00d24240c0007440030b40c924101c02c96a103138000d9542000191410340c1c1d0100c5001180b00e2140c3c08c5101c01c1d1410036241c500002003007001403050400034001091030703101580340d006500c509032a540d0740f965808201d58003492492030201c88400103001c01415000501081212001c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 79802510 1250 79801260 79801279
    0x60a031d0703030f0804080a08330306010909020904080a05041a0723190203030c0616020d0c02060409090c031203020913090215210a0c0e0a03110f030307060504050705 74
    0x100855404000303c4011f40074010a01611940300d11802c5d203c1d410803881c1c1c1c5540d5001080200914160040ba07240d03424075035040c140709529003018001e460062401400400103500c183d004142540700040000703118a00c002441a4664040c0c000d54000e841d0030300d0249045461a0780089003540700742001c2d180d1040d287d1051001100c41070905c0c00c404285000b420510f1195902035481022030f080c100d80c140028401c80c81100d80c1000207511410180013680383d00042c00d400641895a00f508250130400321442e44009030700e6200448088400c06140000c40c0c0e05c01d42003400b14280c03960801406000c4480340090940da040d00681240d50003291031310340d900106c0f0381107421200d5505000350007803160100d031150902c0d444c0241010490703500054403019171222001070207650890b8408425503841040803810369002200c081e54080c240d5034500d165085803550307a40001c0c02c00c2c0c02c030700c6001c00703c09810307640e2002d00a40d00c4580d48a9824000350070589010f0313031104410f0042601802c1c3d140c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 79803760 1250 79802510 79802537
    0x160606030f0510111611030607030501180212150102011d16120b0a020906071a071d09061c050114090c0a0e04080702120a06060306050c040b0405060a031d070303 71
    0xd2040e00800300c1c2d028007480c81c1800490b031917109000d80082c29074008002c2c00c0141c03030f640c50902816107d407209a0b030005281d81041c0c0c0c8800c1c02450a05035910440c4180401c0c420000d01d400f01603000841103c202c00002c080d000102d0140104c84103210140703521140d0102c0900001a1907040007040d408503001d80c580b111000b9030b1840181a015002c204220041100201298010407280300c0107401140703001c0032074980343c200010700c8020901c2006140104040d407907001d10307466072004040c02c0070000f26035031200180707aa9001801c6148a000840c11600400340c00400240700258000001d0040d101c242c42c0e030f141020f01c1181d4440350b501581c516036085240c0800e011040d207031040780d4100c542d00c590300d42000b260460003080760003031a4408082c108010810414092510464020480350705500c3c100c01a100054400f00114205000611242c403d40098405a800940301c1d681c03078500c01102240500360b10304da0841c05488072415060704000206190040d6800313901c03505404140d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 79805010 1250 79803760 79803793
    0x2a020c01030b011805090601110706020307020910120b0a0f0c030501030c0f060c03050f0d0f05061f020706081009020c0a030338120607020f0601080d0c08160606030f05 74
    0x200094812080c1c000a0140043d2920301911b0b40c20040616003080000181c03601c03549880340c907800c050702586c00031944408501c5d250754101d034010104802e03108906d2810f81c0d000040048294010140410307000011040c01040d031080b41c80d200001010300410410390006802003d080c00156005401e006c40410524902c1480f04101d44840c1c2d210000c8060310348003180e07150424800070f42c80d007a0030445400703103400b14003942940700130f0510001a181001d804001035440c086503180510718550207000c00d4a9004110103041380c0c1d480c104099259500c2017610700c3e1860301d80000103d5840860100302c0d48a00080c074070110b51103910100401c0703421342c181e940302c090001440d40c4001103010400c0314406000310358030800c81c1d016040f504444c0c0502c1265041c00340884009005030b10006503440002030400c10f40b401064210081c000c0f00076603440080284020b003c01510400e000154010b504004203034170300304c00f0340003401042419284c1ca00748404e02c1e0101c0c800e030380038840c4041c5104100c61 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 79806260 1250 79805010 79805027
    0xd150f0c120207030203030601050a03020d060f0603180b0601030b01020a02100c02100305060906040902030a0b0103110a0b16030302031b03041a0f07120c140f0304031704080702042a020c01030b01 86
    0x30190010760859523040c1c01140c4503800364002d4030415800780b20f0083c081d20640036420140c07140465500e480303030900038010304035141000001c0416091031408008201010b54490b0480b90a01e070100e05105407500503454000d00303c10082d000100e00f081c1e8a0a20f5102041e1050b0343e100300e451080141c2600d00c2201031300d0303007a070b4115400700b080800328a4910b001d1340161025803018041c0d402c48081074881d12a0008240d1094500c0400300d5440d1401c0d1800f0303507051001d002805645130501100302d480c03c0401085150007000d060340080410340070138448000d9a0b08000300502c0b20351b646418a003252480403000001050b080c000004940c80920300b000c9184204807030340c0c43c52048003011181e0405008410300003c1881300c00442041074074213100c010448180c0d4000c3c50742c0d890401e4500103125079055881030030f004074030300c0922001800c00d80c2140c500c0e98041384c4c0491062465031007940721035105a000140709045441e808461a00450001d4400000362420440c00361400c1c0103443c441d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 79807510 1250 79806260 79806263
    0x405060106120908030f0103021c0308040f0c0302031e060a0504120f090803160209010e01050d0f1e12020c03070f1e08030406050c0d030b0d020d150f0c120207 70
    0x1040040144410361040080301c0a074412404086400301068403145415172040c0c0c0e00354030000e20301c0e0052056050000c1c0e80480c07114030010700b8002000c07a80b8002d0000074041c10040445480c0048802440800080780014580050607114080940a00f2003e58003079021030020b86d00407280041e148480310300c1440d1103290403603081c151280244c0300403170311140d0b0003940c03400b80320200c0008074807194104040e004034a00c0346d02c0741c1f420342902c0c0100101e00c0c1e0141c0c043e103074035082d02c0010300072511422221034030660b01c294071400b00300003840d0034242c641500e088011180d0380c00b540401803010350021b1540311012074098900c0240c100c8185600c400490140031070520340c100c01000541003540442c00007484080e4a22505910340c4e406508690195005500040020901208482c800c0c0400c01d14166141000c020300700310000401c0300810800c0f030291085403806c840400f408a144240ca002e08200711007040001582e28068006281c030300c4082002403d00208000550030510840d40500d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 79808760 1250 79807510 79807513
    0x7080d1112060a14010e1305090304030204050c16031101020d020304110f04060302010f0518060c0d0f0206010303020a02040207050a0204050103050d020c030c13092f040b01051207030c0903150504020f090405 91
    0x300c2c400c07001911901541c6c0d40c0e071608a1500307103840543e1b10181c443c56000b00c179100e000e1903507070b465401048252140075050134602e50080004508034081e400e910100d0aa050030201c050304480c01c1070500900030f80b005600b05500000c104400c101c10f20b014900d4040e800ca60502070030302101c052104a500c14000240480d94500c24400008d00502c003070056000840d210a00452444000c00c00c1c50b0405a000c0d44980e100007540502d49030000d0400c1e0f0074000300c1c40182150344c5507883c003c0d03681c07914100c0030307010310350008120003405802e111401d545c0f80c02610030f000030f50750b0b0300d800c80d5503c283c504440f0050140c07010095162801240518076242e00820110f800752031410b410005054084085030361850000450b8030600810692041d0a040c402c21080c4d01c661503000c0c80b040e01e426030003043c100041040f41401e03060122110130b400103070070314001030300d00581602503071043c01642000e0b0060744e0f008001c04000c0804e0304079510488c0309a5100001400c2d4200b40030b00c40a096600402c0c031b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 79810010 1250 79808760 79808789
    0x100f1203020d080a020706060b0d051b0306041508010c170a0207030509040b0a12031106070507200102160909061109030304031217070806010906020f100207080d1112060a 75
    0x7401d2107070743c10380d0704a030380035000525140490380c400e011907009605c507002e102d0b0081030303d0390610b0661140d0340c1d211480040700c1c40340b0305041d0401c0710035100040c4440e2045684195221038142c0d01c0c03803c0405071200314003c010b1410300100c050102407200301c1180e903c000030b02c002030350b00c00c09000b614070f601da05031111030070901490200000750081254240d040a1002c030f0015410140e0144540703160700030b840c2c081290501c08030740b60070484010051390502804100010000314100e01000e140e10380d141c1e008a0000c0e800004074180500350345010005040000003142840d180c0c0e12851016219002c02c1162002da00c0c6505042c2c020001c0c5941d158105100410114400a01e100c07850809460031440c180e184c9038440b4a45031098440303600150fa00c0c410454035580142c0c81d00040e100500003041400b04c00029150f50310052400c0c22841a000f1810314100001c020640d108031180300e130705001c1183c03c1c01c0400c400390001c030582170500c102c000c0451070070b0410548505c19103048850703c0780b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 79811260 1250 79810010 79810033
    0x10501060509030703140a050706051c0501060806191e0f090c050f0a0e0d060b120c0306070f090b030702010509071403060105091801050a020a1403160807090e100f120302 75
    0xc0c0c410780d5811b40c2c56000c1d04000c500020001d00101015002540300c46483c1c1e601000c50000038110351840600d0145047c005101c0e02d40c001c071545502500407546c442d0b540d1130019000c80c5e03042150703011014542d510407030381070b40040c184201010b85840b680300e400b405a40303051080940b0849420900481c1e400c01020000d42c4010005001503101420400f10541d00c0754040344010f541600140ea4813590b0320000001031070891448021490044018614139500d0700000303031907c0f0068000c100344031044042c0b803a80c50250700214010710f94104015102e142081000e4080c2c1401c0302d10f01050f0080060204a04102105046c4440c41c05001010303160300700014020800406482c0c108001585009040714a00902803d445070403410b03801360312519900000303130912840340c0102c200b0320000d06c04c014080d40700c00d0751007800c46401d00e00201d50351a40c15082e901800d0035045591804502c600300b02c4004110042c00007140d0305150f150100d80e50303c03145800e517180180700080c010781280c00c2c0d460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 79812510 1250 79811260 79811273
    0x1404120f0c08040b0703090b07060f0501080a110906030708031b0f0d0c060b060c0d12050606070b04150b0a0e040210051c050402012106031502030c0418090b010611010501060509030703 81
    0xd0000d211f0305100000545803050b51904d500000002ca8031140c88000b051f051500a0207880c0c0100300d1200184948a01c03955207140c0c1c000600e41840c01446c612000800c2d565007001120003c012010540b641c03441001d18090001c1d08007001d1120714414042d194840c1c2c0d800007908128180c05984600581015a03a614040c0c00300034030300c60380103105100b10808000b0501c80b02c02c0210b45520317022030030700d249030042081e5036005002601c20f0106003c5e00000c40c1a51000070740c0940d10100311040100003522440c0200310103682e058202500c4040030500016002419000b607000721040003d2051070388081303072284150304040c0482000d500100c03070a103140d600002d4020f0f2050410b0400031550107010710501c0c480801c2da18031152110020014003658401d002c04410800005519515000445400e01d101c0c2c0d11495507060b86140701000085141d6005405071039004000403074030b5a4984004114000400b200100c039440d040000821a00039400c80b54000e40181c041d090f80e600d1600c421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 79813760 1250 79812510 79812517
    0x3023a0906060e091f0209030a060e070b1306080f0c070f0327060e04020a0906120603050604030804020906010c1e05010f02040603020c0f07060503130203011404120f0c08040b 77
    0x1c4070000d4407a10045021144541000d1051395150001c0812140b8801d41c401801c061200c401002c03803040040f0308180c1c50201e000d1003059006203000c2501903074a01503038034011845d8060700c6c0188000c100149101d0300c0b852a1801c03912141c0e07400c030480d2154030f40801d03020020354124640c460308000c1c3ca00001d801002401c44c25029082c4540340141200da0382c220115903840745c0700c078106070400a0003100e8200008011001041c1c400f182013410340500903000c00d0003802003400340100b051000103480e180d0381041c0065940030b001d48429007421700e809490064181c1c0c0c00c83c811740c088030000710254468041c0000450300640304002208001000800200842c0c0090f20195260310316418400361600050005243c07940d8016694800f82c1480d5003018283d45a0030915040f0403000c2043d01c0e07000701900c0e0069984945949402c03600d1000038010200c010642d0031400340541000305009060140d50740c0f071032070743e1613849507101ea0b05401c8a005400010080442c9810301080c4002503049016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 79815010 1250 79813760 79813763
    0x2090109031401090b040c150516080f0d090b0601080f041220070e2203080f060103060312090501080109180b06030712050a020123090d150c03023a09 66
    0x91802c0d454860005da48400c65013950402103101040040360f4400320750020121103403805509081441010761010003509201918440d00440d00d2040282c03541c040314244001000c00304103040080c502a406880110b4801e404910102c0c0041d28240310f5200c400e03c550342c4044d0b040f50004103607806440c5c221740320600980529440c19100c0c4101000c01808001e003846503201e1310545030002035101c800c1c0100e01a10141003030141d40e500020303000034845030480003814015a080c0d407103100481c02481103900c040c084003898100e640340aa040000d00003510004c1c1e036441816030703e03540800251040e000140d001d13103030742002000104019110f040d410410090540346026500c400c090621345040b14150740c290000f840844c115a046201702c502004e00b030b000106440c404500d012650301400000078014104400e02c407042101c00d810114014032070304070402400514580c001c000390059125106100d80045a000d01c1c83c0403008098807807101c410b000c0e1002c1c400e80c02d100c405050f03464070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 79816260 1250 79815010 79815013
    0x908030d050c0f07060905010e0a020a06140f040b0a110f0a030309060b190602011a010c020105030601031d010f290613031a060405060103090c15020c03101e020901090314 75
    0x1c807041c0c80d200303100140135050060f136010402801604140d402c454050100c1a0150b205100c07c0005031168200281212024180381e1a2000540100b07071840c420700c21807200d05000020081aa034140f170000d0890440745a4a4061a44000010550f1b48141034203003040caa1007519060300086c4a82c00101c00f5a01c91070000c50380d1540c120104103650440d030044031180070380c004188042c5509100d1001c1828025403000040c003036110010740000710058020b410014004002185640250004908506004203032564110b10603402402068900403038100c00b0704200303c11608110000b00811071003c09090408100025001c0107080d5104030800e0f40d01d40da88001c004085194243d0f80c0300504401c80d14030b149480d14404000444074002d080301c1c1414940380035000400c000b144540169991140d1110440300f80c034074280d1400c122442030690600c02c65407110005021600035200010100030f503045442e0f9260490004d034080c075141d40e80000c42c0d0748000c202140f000e588601c0803422200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 79817510 1250 79816260 79816267
    0x650010b1e0a0c020312070206041208090307060e0f03070e0f1e04050105010608060405130314070209270601150309030302071a010f060207030f020d021f0c0507060908030d050c 78
    0x48071540182c0112034828089801c1c06000f03415801d044c046102d40c10040019240780c0580795001a01500480c020109600e400340c518000b08400c1104580c5855001003c4403000e03607072603c00070141d0081c4120700e8003421401328000c0311804c0c0060880c059a8400740b14a41c65651440a8111820000c0034018514142c8501e0096182c000d440701d80220300910012406604100c800340c0380b1207000d031655001354685400c00c041c00b04400303161100c00c1c0e41441c046203031103222507229000c0e001d400c00195104d01c0e0343c018060b0460450029030080c036504905504c1404440c000192101824401c18140c20322890b20117a1591095221003010340c400c0c20014201442c175180c15a0344010002d0111840c40240d00500c170022103201008010001c510084c0105404e654a0340c60018050000078003034121081e0020842da10703410071460107038402e050548102c41040c001007443c0007103641030325640110746001c100140310300851026282c50500a529200044140100038440144500c1c607501e001d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 79818760 1250 79817510 79817557
    0x709030c080304081216020d0213060803070b07050a0f0e0a0b0d020c0708060601050a050c01020d2306010c030915020c090114011106010608010308070650010b 70
    0x14200107040184029501c07241007a144a01d088143e0700c5c070800380401403002803411407510031030700b007201e0f415540510084124804a0155030b624160164494182480802c0042000019200c020b014404240b115101c4043c1030750307540f2131140448001517451021081c0300780070341c25103203100300081c04c00d81c80c0b00c0e41c0b00e504c50b01d04e8101640c050380160700003c41011580b03080140c14007401340d01002d0082414500006002d6124030b40d030000501c9000300303480c84240001e41c192824100d914a00b40b18500c5030a01c0c000d4a80c1d8024410340c036020451000c0340d401e51050807154140d0340c0c1030321001102e50a284618503224040d040300c030110b1045129400094880c1c2801500a1000d0820b8400010746c41d00090a400c1d558001d407602039120200400040d5401501141120b8114417455a102070a04101d0054010109050b04091088218412100116048110340d22901c001c280f1580c400844840c102c40003511454213016588006100110036140101060351502032940010030300b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 79820010 1250 79818760 79818773
    0xd140705100e0f060c0a0e1503010f030213021305010e0409050d11070614040311010203040806071205010e070c080d09170a0306080a030f030906020d020d050604060501020a0f0605070903 82
    0x1100076600a6030344403403035200b40741e004020300e14282d01c0c81005001c2c246003944004200e8001c49424000308140c11050501e10345685902c0c0c0d94541c420003400d9529a12040c0b900242800c91008070301403450260035091041852081c0c402a030348031201d9407501c0f40b819004440748100c1030880b41d8010360300d9082d4000207604001d01170f90026540ca0345903020b02501c41c00da00b0030b02a0750088042c02100c411076400603801d0b00448080d13030791060703040c0c240358075140040b89140100e4124039540d11500302403013015900a0344009100846100030320640c2c1e00ca040f032030799440044d1006004110b0000e00e04000641c1d180180c9202140040001600301c0c00ba190010784c400365a29002002200207440b101269149c0240400f40100d01d004190700390507030390000d15103801204500b08140d41e07403640c50304001c0c05404448904c030450100303545aa03101408640200019a08980b14a2608a0018455002081e024001d07a0088054140c0c050903440710300c0134100c01060041005449840400082e54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 79821260 1250 79820010 79820023
    0x60f1b0b040201110d0807030506010315030209040602070503031302030d1d0d05240411030f0d05070602090d240c0e0f030102040308160b070e0a03061a04020c010c120506030d140705 80
    0xd2565046c3c0305040c00000941222005482ca504141c00c3c0890f070043c2380380c04003150084a41c1640e5045459513541000740c000d020740c1000403ea0b0200005006406800c4051408018000c13000e6801240020000340c07801c0ca94094041e42da0314060400140e2480c015514043da58010003d89800581c0c640e40d81c0d00100406140014200480702072105005d2b0b1903d6505281400350b00905600c035950513801da8880c11000c800c1c0070824006070503c01c020080d019503030011006090001c0140540c540f0300146005910400280c400c1006203c0481015000307208400350541c903503840303800e03102043c803a040019000c3c10380c00d5902000004002042c50004100c007000303035040410503901070720746040f06210103010201084a240d010012540d114000d00003200d602c110700040c0e070300100c001012020810b9005540c040e101045030040c1c4c882c103400c01c40f051081ca5442e0400760695191000440781c00f9944150141c0c4020725842d20f07240900100c5910343c280380000c030f04240e1140c0d2003510300803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 79822510 1250 79821260 79821283
    0x9020a020d0e0303030c12220309080609070e130c050a1e0801060810020309150f090d0206010f0504050402010903140a110d030c110a03020307030606060f1b0b04020111 74
    0x20301c10045144a01d5001c002202d503088200c02541c41c600740080c0c0d03140720f130103010140c0c16814a010042141600d055510300106500045450350000e00d5090107010100d46106410047c01442c000403030504010442c0420780340036054090031a01c0e10044245444010341c8121100440c006001c43d240d03aa40038500c00070b01940c00c40c01e009090b0300030311103003000265201c10000ea052100510440501280340c1c004074045180058690b42c5001784c5070f10380f412181c54039010400482c01d02c10100030903a8490301c03ca4070002100d68084003441c04a950340801d1245d007207001c040318001d124a19203500819003183c014909107801d03e403252104200d00d11f07407810403541a4051000542040031a101c3c01209030701c02c555801c02200346031000782c120841814000c00c1300d02403444003109981c80503800d401454008c2e003204d100c0e61300c81c5003c0008000d68060503020888548449580620450b07880d46103c0c0000e4040300015a10780c0c5482c00d000f00030700201e052140c1b9685071092071034104139084001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 79823760 1250 79822510 79822513
    0x1c0207020301110f1213060c17060a052413120308011508062b0b011a030105010c0b251205061906050702030f0102071b050603010e01061809020a02 65
    0x11811441010300315030300d12001c194407800901030541200045000e90740c017800a807814100b15640c604909603003030040130004101c1032801c0d5807003007d1903110201d8044503030715080d125029101c0c01e04020001e41c4502c101d40d842145900c82e81c02015903c0c0050381d881440800071402d203420010481c0c01860140c1000b40c950a070000800281944403810600501d10308410217825a044030004204c10001005140142400c01045e030000e11481321003a1081d00500403018442d04900c2d101c01400000e07c0f4015031400006159a20342d04801d048a0403248141c50f5020b584100d44d441c0009182c00412800d55202e04005031000402c009000200080c40f031b9603110002d040340b81000381181ca01a1086001c1e800c000820729504040c82c5001c000d07640f4a0806548a001502c00030b440e25580d10384000284d40041080f00800a0600a410406130700300c550806442d100c9080c0b1160340402d204001600c513101c0010400f081c024a200c030303108018810384154846e21421501c1c10b980c030121084006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 79825010 1250 79823760 79823767
    0x3051b0607020d02160b0301061803020405180c0906010c020d030c0804151b171c020f030105030601090b01020c1e0307080d030b010302040b0316090305070e07110c03150c1c02 77
    0x103607606215a010400c3c0700e105c80300407241800504491070205019007001c1c45504100c000e182e10a03440d184004590040c4244010b1402c1900450b004a40c0304c0d50b00010b00c036044001095107005a105031040d581039542e024602c41c82e03003c21207901d004600c15014000c44050b1800424800340091018002c540c00b6540340700d01e00d0000030b0040d0714003450701d400303451982121000145888500da5041e40c9070181191188049110141030800800d81410f160b840000c01e4bd9007021800040c5040342e808805031250740c3c1c3d0304d03050902507600d038100450042c2c001c081c0341c402034a01414040c40285c1e40d060408003041008011900e850041e8019000d1a4441150311030720503414059a04021000c0c6402c2d402d091415105003524040a0320341444c605815090301a840d2090401200854101e02100c100c21faa48042450760031301a6898400160840c103081114a0000388403504000080e00070712100c40c50400a4801003801762000d038050b0820405001d00f2294003500a840b20350461005a4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 79826260 1250 79825010 79825033
    0x1d15040209060c060705030421080f0a06080f0a0620190c0605040501050411060702090406050c13060e030721030e2107080d08041a0a020f0703030f050109020f0703051b060702 77
    0x100c41c0360903401200060241c0c100801959018000036045080c124640c0e50318cca45001100190085070400c0b04140b0410228a03c0380e00c0010300c8041003030145100300400003109404d4581000f02c0b01c4080c1e4080000c00c2518030032400540c4220000140341b802d02c0201071941d5a003010307500d054034142c50682d114000d101c14401c155101c0807000408030b801a152084650100e00b4041000300090f000984d11030008864a40007021110020318078021403130083c2c4c40c0e4002074403004915400c98080c3c4103185001c624414040390000c0042c8551100e01510308882d60129501e400621040b900318a00714002d0b01104150003040c1a04124031019103d104d040c0b001081c649044183d200d003c02c6040c0d02070102080c04500503003095500044d00a1565031480c0114001c0d11402c10404001c1400042090034190f0540c0554121107059000f413100341d1360f0b045440c003a030168040780074401c0001c00003100002d002d04020709005210320724030f90200e0200700c103a90512804560840160b0841c003200f10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 79827510 1250 79826260 79826273
    0xf020c010b09060d140a0f0b0109050a02160209040501090606080c01080a14070825030518010b01020709090c0305030409020307020f0d0905010e0301241d15040209060c0607050304 79
    0x824800050390b00303a4403481c2c101e000030a15100311002a0082035201c2000b451340c0710510440c40201e80084007506214060320f002a94000c0c240302e18004180b80002140130115035008482e51245041c405c500c0c02d40c05a020040c01c080c018204407400d641e01c00c007440004d10180641390092550b040642010001c10001400b0a4002044e14501a2805c4602207a044000c000e06070000d03a07910704220903a40c0c050300489442520740c1c0090310340c03032400c0c400c0000680c190005845010240488481300c084111801d0903a903401e00f810780560005542032100000316800110307102d0080f5110340a09607a9164241164000d030417170303840076400200b0002510f804101200441107a00c004112704140b0071401001100c95004050421240180340d940c240c0c0c00350410b07a8114162070b10795000202050b46140409072a03c03c203000070000042a4070054101c20a540c8124010220740010030a001c1c1000002c0d800140354a50114042c405400320550030000ea80c0314900310380765281c1e41e040c05d05019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 79828760 1250 79827510 79827521
    0x709050c09041521200d0b090601090608150c03070212160c0b040b0f09010509060c0106082509020307030204030b04050303040b06090103020f10091a03040c0602010b090103030c05100f020c01 84
    0x1050b2042e004051303c8001090080d10094003201c0e005403042104014002882c400440f11024001c1c0341088248201144041400c504840c009007082128507a50708940d0b440c1c5104030040f4003450030040000b4001c1c0b04c5a40110b0b800a0745105803124804810a00b041e02d401940400007807941003441c560820444d001540003030140240300f070342030928111050b811361103503111111310724002140416031640141c06480c401040100401c1e202c040700803846000309028403c1c02101e01c0380110503400800004c6071450b001010000156826080c84402000385d8005401402019402c00c000000310301c1041c4514080d82c480c502071680c0e410681001c44468402031301c41841001450010401a594002170030908034041d03511241c0502003820540b044501d5030300580d80c03100b4204403200165501c00045101d01d105c1c0b034160710b500c0d031202000c0f0700700d9050015090308030030401c2c010710100740900f040c1c02040e03116804555000b540700c51038500307455001c00c2000c171184e00428106642c0b0340c2070181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 79830010 1250 79828760 79828799
    0x8100203090f0304270212040503070b0f07090504240b0a0809010c080a0923030706050c0703020a0f08130603060504180506010603150f030b040b1005030709050c090415 74
    0x11070500707081881c03002150300301c01700a4114078041c000b11813020f580c980596884500700c400780c81103032134030f41802e0340c90390301402c01110045c48600c0000c2c0c1c0d11b019010228042e2505d50390b4401aa0f003090203110003031101020080200c520340c40c41200c0a1501101c002c05091039100302ca0310749a524001414080000e440e404559041c00d5050700f1083e440a6481e0340b0100c410030120b004e40403414500c05103070100c0d81d000451800340074544851000040205130880c81198100403907034400300d00300c1203802903043c000c0050301f1403842030300480d5004403c004124001c400d1a494200d036648100b10510f032681c46800801d480c0c1000b00a01d02d054410303166088000c11003140802290b50300e01307884000500030f071002d00d5581c00340340c43d0641005071454050105660443c421503141e0428840d80101168101c0e1504200c60008507069402420203084903400780081040c1400c0200c2000944401800011608400d100f01441c0342e4880c00340c0ad4034103406c54443c200d1035050110601c14011203005c2c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 79831260 1250 79830010 79830013
    0xc04031b0612020d0f151401090806040b06150a09030c0605031009150305060408040911040b0f0702011106041101020706030b0a030609031e030225050307030309020a08100203090f 79
    0x2001c210303031500400d41a560381c030107450040c0e0781c403a854031036030003020741e400e840118500d014030300c054200024103e6802d0301d00100700c08550a5004004407080041402100aa03030407400200d40001c1d8401032190b080383c00148107401e00f804811020905800141c48100090a4000c0c108140410074400344060045490701610b545000fa1114800c0882071064454040e60b841c02c1c505001c1c0440e004502440c3d0040c140c40450900303050400e080c1c0c01c24001d5403820b91510b00b0b9140013000031002c6030115021a0440c509014042901d0304250f000020b00b41d051210443c61040c14200c01e11007070313110f14407078650b90080d12551400240b030450981c0100e000d0500d00900c0c4802613544050a80840b80c1c062008103c568141c542282e00c1303000d00e80e044500390400003070001595010303000ba01c4000958038030601d84140c4052040f006460380b0f100500316820801c503080110740700f0742082c40c3c550700207091a407000d9550003141740760454500803864069408410f12502c56420b00c9801c01c034026500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 79832510 1250 79831260 79831313
    0x12020603090325121d1905030109030e0a09090201091401090306050103050d11010506011d0d0c0803071b03030c08130806011202040f0b030304180f050c040e16050306040c0201060803030c0403 84
    0xc1c085d42c00c011040c2d4030f8074484c20340340c0600781d4642000111500074041c081c00900290240d0f15000e8017800d2142e140740e10440100c0c10100b070201045c41603140a94050303413504101072034945249600010080710a04200b00188040045500c50003120b000358403070300c02803000c01c841e00130040016900a5951285034104406d00c120380ea0700003408074891042032030941c0c4140d4628000740c00e101d51401d004080d043c400c2d40010300b6003c01b00141049a00444080d09018144202140c01c1040c43c00b004020800c0308a15001180d40c58014010142c41201140119074a400c4241c1c41c00009074499100880961818011410917001e6455440c143c02e20130301c007064102d00003d8a90203980980c40035000604c40c80e03400c034082a04214034802c5000010455402c0660181030030b50b0041c003a00300c1180c80340001c02c1500c203005010300d0480030191f0302d65007141c8070031041102803d06e0480d040115034980c47d01040400080c80154000c082c030b80809a81c41d451403400f80d222400c20480c01186a0880 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 79833760 1250 79832510 79832537
    0x408151609050f060a020f060a05010602160f06030504080d1b0e0a050f0f010210060605040302010f1110020f040812070b09120f1e0d06030b010f1202060309032512 72
    0x50f000001040000c032401915040402001c1b8030b8001c2c03502c102000c0d44250407e00801d02015403005050342c216034240c07101d2410701131051000040074402c01a0180168004000c994480d51041d500640b05002151424071462124415602d004130101c6150090041d0703c40c00740d4016559000445058401c280c0035407074440051444551044218000e496400c0c040b031150b03209000b0601c1001d000c80c0100f1030252203103002407468005010407404034900da07400c100854020912043c0d400d29101c010000042500c0c2240b000c3e400070080782e01c000009001c0401c01c000c080c00000c40713488045440700d0701d918450511058214000d00020003a402068034481d0300c054920441e080b02105228041d550240883c500c4075030210103402100740d400128040190300e240350850400c41c3e028107807200f29a62150041880180207100d0000107100b02603054005091141c007a503032003440b030f4003640d040990f05500d0b485090a0034581e054126040d85aa0003001014445007455110a1801d0a610400e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 79835010 1250 79833760 79833769
    0x50c15071b05120304030504030203030d02030a0b060702031902120d050309010f06080d0e1503070305070f0206060a05090c0d05070504080d18030b3d05060c03120c040815160905 78
    0x40f1040d1110f0309001000605241c00740301150025035010782200d58407024242c444001350001c0c0c501c030031814140030741c00082d45001401d40340da240c0c0090141800c4204248207410398144400c040360440031103068440d0585052203581c5e041d8149807a0a9640d14014000c1c5003168a4010060f00300d510f850400d00240ba40010181401c2d4040e04000844284080018100c13018003460044501c80000030481169816001180582002d4540300e04504800d0410790702c40340119070003500109d40c00000c016618044020a0300a100203e14502d4840c1356118030042c2c807011159000816400141003241c22010403066620040b545041100301c8101080b510080c112884003405070004800400d1121792541904404062150745610440d224000440380c042103924100c4e503a840b40840c001000c1c20030100310b40c1e00410100142d450300c400d041110800500c090302110410030f082c8004201c0d08010860b1456425150000b00094900708100b00ca05d6016003000c90304000a0782d03410025601d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 79836260 1250 79835010 79835023
    0x4060906020d14091c26040c0512060103030e0f0f03010905210c0703030509010509040c08010504060603051b0a140c01090c0b090f0402090105070618111005031303050c15071b05 78
    0xb00e440d064810006c1c052020300e40b21021680710a4490040c0244810031181c2c4082404542080d6040300c100002c16000681b614400d1101a001c5014014040c80e00e1400c05620784401c1d1008080c0755840d10100e01081c03c5030802c4104503400e500566180710522444009020b80e180072500e0140f0b009480b840c40c0e43c07031708424030000b428020085130a4107241e00940a658090401520401180700000b00c000d001c142e0a104d80c80c0100d02d002400309402c0c1c885e0260b103101d5070503401030054881c8a85980d00c00d80d4005030410082180600d03000500b2107003034000300b20000c115400031451344680d00303103914400c0301030f0303c0301c12008000c22100402d51a020030740684410100c40040c0c0b22551900162468032403820003c0410740750900f00b0940b50301143c0484480750083c6291400c00000c2003d010002c80e11016890101d40b0510005146111440c81450010b02c00e1800c07038280100044903501e844072800c480c0e000100c82504211a09512444013001d150700044040b81c500b01d030b81c03209130300c520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 79837510 1250 79836260 79836313
    0xf030705070b030a060b0d06030314070201020a021e030f0607031406030a0b090c0a080714030303010b070f0201030603060228080c0a0302030903090d030203030a1415010804060906020d1409 83
    0x42c010000515106541d40510014001d081803155901751840300100104454001107001c82c0411002803e02030310003041d6411598182c005020008a54080207144040c009481102d404c0c003044480c40342d1424054043d000c05000018127041c2407a031009010350f403015039020f1000e0f5805c0304100702560001601040c3c1c5400c00101100b58a800010a04104e21614215003180010f000001c81200000e00082100c1050000701035500034801059105e110a100312920300000f4414500407600c00d100105520b481410001413559403586c2c2e02c000e0703800c241d8440382071403110703e40c241d441c9203080c11008084480b860800303140d1801c540d428615004a10841b410541e0100000e2241c201c100300302c40640d071009002c08640c541030b140c000d640c0c1e8411200159440e0504c040b00e0f1b080b80ca81d00103140208040e18255071816400701c011070b000c2000500070b40d94240c540d004070010500071b01c01000b031a296648041024050842c02000300d0f072000e0440b040b02d911409240b00e0402c2d1005031241c540d0f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 79838760 1250 79837510 79837529
    0x2009070309031e0f08010905060102031e0d05040605010306050601030b060d02090103060f080109050706030207020307030303090f0212030c010b06070b0a05060d060e0d0806041b030b0105070f050a03020f03070507 93
    0x4007030b0400b12044100e5204a070500b4045000000c0107035003000b482c4007011081d66482c1c04aa0702c590905054420983d4910301503482440410041c0f040404e606c2002c0400000103800d08401c071070300000703850080d102903a01c00c0c1c2e40e2005105100c0903004e450352000382070906001c0300f02c0c4900401e2480c410141125200d0707034049500d4569a120f50840701c0241002410034100c291984c110718028460600121032500c101c0700d002403501d01034000c0d01c5a241c0c0050180504a19685040d00500300101e03046901d0f801100c003135001691200b01500414448000840d101e0000c00b218a0031510320a07445845110309112820020312030004081e070028040c6808a00c9880780d40124582c00c0984100801960800400c0504540c0c0061041c1c01240d46a9400381c0980301c04003440704603401d0100e4034166260818a403510903001e600841c0300d0407018941036152034140e46824104525041e01120580c00030080c40040c035038100b00c3c0000ca030884002640c036021680d920b03a940c49400d4403500000c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 79840010 1250 79838760 79838771
    0x9020a170a020901080609071505030105061b0a030e0a090b0609060c0a0203061312050a05030414160f0503071e14040f020a0807022a090a06050a0605030420090703 72
    0xc40003404070040031035000d00124040d503110a003d580750941100c0042041c8520280061040401d0262206036140f94030352901d16424a41031100303543c4010286407107800092250351014804100c102c4007035000b56501700181035841c0030082104c0ca20b41c4984001c0c0c0c1011b040301e00e540d589108070f8584e914210780007580ca03040484510304044a80c80040d5042c0540d40c10840003038181007804219900ca4100310045100310310302030320b9900414a00000241007030000500295810020806039800703001114600d204680c42c119a8101d43e4005140c01c00d104681081541410004280600140030504111110002a0580c641110710410070701081040500005840b03d0740428554001c1d007000b9542d501042c04090041c0b14140e455600601ca81100f101e0681e4a4216180408d0300541c0c0801c1e84003101c1040040c0000007034012107149a4a440016a03982e607a40e14100400290f1212504c918090900c0e400074125200d0384c0c0b40d1f60705083e08080b007a54420300d1196000c80c0904002a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 79841260 1250 79840010 79840049
    0x1020a1209060905150117030a0c030302130308030c0d0e07050f090705040b030a020403230606040e0c060703020c010212070f0b07031e0e010c03150303210f09031209020a 75
    0xf40c551040060840c2c00b400940e0900d00c600105034034140c0307007441d03500703011608402c1e59145e80e88107200702a0002540800c4503030000740711342c0041064101819900015a84948600e40310344d1040c0c40c0e00c00c1c10a00040e607001c0c04212030190301d81c10080780010380212441c22003c60080107010001502c14000c2500103459103020707400b40e80103002c801022a480380341006da80360007075105000030b8424008075006443c00010182d808040300f41008054070150305e41c4401d00001e40800704482c445130150301482d1955880b820040d00009020f54000d00d40c4110b0070001a0810300b0300381a09000c0700081091001040709807069601840d440700ba003031803961301c10504070000c0c00300c0c290600302c4d011400d56450394204150070850142d001000204032903c1804001d60850303d801000c501c400f00e0140081010074002d007841d2801c0e00d03155040880c10400a00b02104446d8200400d040c0d1a0b03031180e185090542c40308450302c0e0020304000c1000300c14030980005041001c06c0c4180c0030190b60500103c503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 79842510 1250 79841260 79841273
    0x2071707030602220f14040902130c140c07060f0503010b120604060302062206030603110609040902090109051f0303120e030910021e060f04030c0c0e090c0405070201020a1209 77
    0x4085550600391094039072141c02e0080101d25501c0b5104540002d9010641c081c40c00d4410720380c010354000c10078035008862b00b030290041c0032400c2120040c00301e030404180d050382145004025119240c07010381541400d1080107040802001e007910104807003840103000301c44008084800d03190380c01c0d1081c4000c8d620704002030068201604000c1d0003000208880214007401c00403007031701c460b0320084020f0f4541c656104030101c842c24800509581c504a441ca403090420800400f280d0401a00c049148580741e004905a10b800b81d001c100419a600308001e42000c4045d030030800c485402c0400045c09141d910b0040c06a0140c1c0d0451840e15603801402c3c1101000700103e821007070003d4103110007100200b10194403200041281e0040300c10a06001c03a2402000c42da143c800c0540e549440a25283c40c0c6044480c075820b0002152083c180403000305040c040d45541512038031980c0c000300f03500d18001040c007080d80c902404e078409585c010b02040c80d05540020f0020320604600e000050b05944504165 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 79843760 1250 79842510 79842547
    0x2030f03040203160602060a0c0201020a020703030513050622210212101a030f01060b070b0c0408030403080316080403140c01090c0f0503120304021c1a010801020a02071707030602 79
    0x1003a81500044c00041003034001c64168440c0c11020030402ca4030034a201c0c141c0c01e030710400441400503002000d0600000e4001c0002e82103180c05c1c1c411820856441d00d000c070b4025400b0f004402c64403a281d030318003c200d55050b200300000c1d1003e00201001c10244016116403484103140c001e200c1c51460080841c410700c00c000120b0b04030107042c400e1018040312664226000e0b19001050700a000b080c00d400b105a805000c0c50301210200455580742403041d4807001c80b0303803402030002c10800f842048006010344080010308051400703682c40130b60340e05000c0a284c01031300c4810f062100b03000700c3c401000003190b0805007200e100d041d590b0300f03640d80c2d40d4451501401800040030092010740315080214400a0f0440101c2c01d8a00641c04c03200360365003008022003580000c48000398040b44554405001a0300c4884a028807441104003203916281c8604c1e00034140001d80044416030760108405208aa04000d400002d08501000c8007543d0252541c180e103c1c401c070700010381401d80001d101c961001c1e82d207218 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 79845010 1250 79843760 79843783
    0x90a021b0127060e0a060e010e06060d11060c150a0b0904020d03030b040902040911031204080c2101020a0309061b0e06091801080604060f0c0e040b010221040f0f0602030f03040203 79
    0xc0c5c5010700c2e00780c60f1078402841000a01e4582c3e61070800a401d03c030310f000492501030000200780d8a41619603588107000304070b8400e20303180c1189080c80505000c41c81000604a43d11007201c2143c1c841c038105440c0400c071440003250794402d9002c24103000c090380f00e000791042590741602c0d0104041051602090160a001000a4103c0d00e04142c16051040403c0e6000e4551000c1341915a10303017411904440c140600c0c01941e0340c580006e00419a0780ca00743c241c2e141c10700050b10080c024000081c66140c2280c00c0340f0f501001003030300c8444010800c03000e8441c4a00e80c1300700b0b001d03c4040340202c8400170f00d20320100140340d0042d40c00040030251640e61000d0145041580c6070034a9596842e0b44000f620380340300b560b08440050038100340c4000c90b0009c0c010100c141d200e0f950340901b1150784d4010400905100f20342a410360042503411503554090700d208840200101c44295503440c58a40e07403022840c40390340720038510042c4000610501d580403084406001010b038405840e6140ea00000c0d080100141a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 79846260 1250 79845010 79845013
    0x8060607021021020306090108010203190b0a030212031e1806071b06020a0b060301020403120813060f02040612050402060403080c15160f020105010503060105010f0e090a021b0127060e 81
    0x520090070660015407089409a6103580682d276642841420b078081681d500001c01e0450034031240960490744680e0715010000d14440b840d46e665004540c000ca07448110354081c0d000020910155a03004c1f60703402e03400781e644001c1c903e81b03885a042c0458981c110700307501e44200b00000b103c405018001c120402d13007551030109000c0061796454003035622544920100c0b00c5480703040011308545418403e60701169044403250081042100d4111619a0001e00540c4a0301c010548400851254030400c2c80c0050600401030751a414203a015081c4801288003940307907805e04040100503100c04081c0c070200c0b6030000c035440c4c4405540d80c00c24206440044d200e10154250f0040000c0a68143c280c02c0d641000c036100c41440e9903200800728242c0d01c090169035050350205004115a504c10a00094103580515000346610805000a921424240ca00340c1c80940c001c10080e5032015880220b02e030840b1182e008012174081c00300303a8154200c00540d14480400b0180300c01d024024150440e4045116140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 79847510 1250 79846260 79846307
    0x60301140307170c19030c05010c0f0b09300f03040203190804090b180c032e051f0207060e0f06030f010801061401020a020d230303070f080606070210 66
    0x207034181d41300c0001261074400c02d04569891194241e03c81c250f019260000c1000e011103061100554040340c01c41c408035094002c0310b0f00319020410170070242d4042c4096002030880f202031850080070b2401100e41003582c004081c0f07416409003040100b01c812a4124042c03580d182c0d6074070700000e800d14212400c0e152425050074003010420083d0002070040d611303203030010489a01d240d802e001c240d2007a0040050f070301e992480401c0410420001035940305070102c3c4000030700c0300c010381d294410311120034008001c0109600c0a2100b07150848611540480e52903c80010500c9080008d50f140901d20a00042c81420603000038141c456200c280442c0c5006001c0725500e043c0701454401c042c80912030060750707511308040880c050000920342c0c018080164000c1590000603001c01031003140c004001c03517110508080d6021900c19002403980104000006182c503071400f1803010740050901d40950f801c000c500d0b82000140d13981c0d60300b1b40d407401d03405a4200e100d40e07e0142054400c1003500303d90380800040c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 79848760 1250 79847510 79847549
    0x9040201091e060917190606050d1a090313120219141008190f0e010603030c14060403090303030207050c09090d1710050603070314070c030e030606060301140307 71
    0x460b20341d41100e1282c2e80301050a0394903058040c503800e042c0740c111041d402003c407400454414680c40c815041c050f020010310a5a14070000b16005a440400c0360060390015040904010080d809640414184095413030200b100d40c440d45016094010149403440c000285015501e43e00321800005901209002110744ca410405841410f05072001e480b460340f0081c00d6451501c6601428060111002c08016031054034840c0790242542009408219580d00040409003000b401900c1c0154044d44030320350108143e003814010151250300080041d4809001d00000070b40c081c0a0000320790f01480c0050725041d15103045410511281075041d88111100140044084d0100340411b0105840d1901d03c00081b140c00006040f00c070480710000702e00100c100800c4035080c484015a0301c00340c240303130000300c1008051408142140686512000840752480d40c002c06030420900a0310840441c0100f6031440c0070710006d110ba220500900c1c8542c000d202065041d038400700246d034083c244215030758201c511031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 79850010 1250 79848760 79848809
    0x161d0603101e030b0705070516060f080a06030c030206030c1204050d11010e030313050a05190b1302100f14030c07120c0f0206070c05090a05010611031201050904020109 74
    0x164090b40c00d6403208450311100e026440c410303440450b035000e85024002d5441c0310090303500341c002d104240c440f4024151081d211101e000e580f0405880540c90f10f0300c000d101240010004907008240141c0706150402c2440450401030251040720344c1125140d50b00da441a40c48940c2c0e002e083d00d0307183d03600c00000502081000201d98041600581c0c0e1b0303a1400020340810407807c1c0e5808008001d0982c0041020840c2111031481c0d003000c2a0040c0f00302c4803582050741c0c43c9403410001c80700c03454411092501580030407030021111600034803c0c0b0450161540f49e80c0028059224501010040c000c003440d10081c824047d450308903c2c0c0f1a4103240640380e14008024620b00d80c400c8404980d0110840001e0200e1401803055800458110b280d903c00c04404d903080c00040d80c00784000f50345e0750211400000d41940d903a6010b40c4034101c944404a07180d4035010b009090400e41c0e50107159103410500c8034141d01c0340003139180707411500215114071668070380f400142c58220303a03030b00074030b1401c2d816541c080548181c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 79851260 1250 79850010 79850041
    0x6021504030c060e1f06050d02100504030503041806060306030302060a09050c0a03030c110319140c0406090c02100606050d0f0e0d1e0e090103080912030a17010b03161d0603 76
    0x12500361798600c40c3e0a041601c2e040701d0180c0603155100317040c9000c803000741c00c0906112139065010304102c0c0c81c003601d0340c071030303a244d13800c16030000000315006a031321200c2050a02408c0010682810180011400d643d40652078150050040c8881980ca480d00c6040c80010040030060110140ca004600c3c0d4803420300401c150007039030080d10140382101003001103082c00140c0d10001c031018020202e102d040340d990411005c1c080146121548600c0000820990b290320608000384036404000039115501c140290a0920034071003500e0f0076182c40e0301005056001404c5805600b0b040100041e21614070000b48002d10803079481c140c06105240c8603403017031b5801c0b22a070400c1324070182c5c4621464641003404c840c00885442040d800c0113001004100080b03032503000d04520080148135114401503010143e285d500841418000900d075140000900202ea694003030141c0120110940b0b1450030817080d0040d903c0700c42070301c410450002c011610200358402200c00407400103041599900b84584600020103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 79852510 1250 79851260 79851283
    0x305190e061903150305030307081503010c08060415180209040e010f09231c0c020d03030501091109030a02060702190306020d0608190b1009051008061006021504030c060e 75
    0x2071903c202040030140484c2500e04881c1e01c00700079440c6585010b000c45800310b015040b54070918240d83d01c404103a4083c0203543c60124560b907180500d260440410094520000750700481c01c0942c40b0600c4000e000c3d0074501803542c2e501d040913a0701c1c459800494010020b290403409194640b901034080100300b9042304129a0080302c1c203902e41c140000c1400c0c804582941d031601c803544041c004000c241d4240107010308140603800d0602d50200d141d0041000c0c9003410b10100c0001390344500600c0040102d03c1a03120030101c6050480c1040d100101003070b078804030728502a100359408607503c411990b0301ca619620350b1064120425800f80c0d20310307001c0003a4100410f01d00d07003242007541c013145003240080d46980c00d0781646543d0070002c680ea19411002e84003d0003a03289084611000309604020307000d038600682c0b0201034241e036145021401401d0180142002c83c0f61101460200f04156000032001d440040380000d49043c5d40301d928098804400c88100104040c2c02c1003c0046c2908021a0b01ca0852 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 79853760 1250 79852510 79852517
    0x5060a0c0611190f08010501120204030f05010c090807120206030a06080a05030c1506060712050d0c0207170601030b07110304051005070201020d050f0d050910060e0415090305190e0619 81
    0x1220f6040b03090741c00c80c010140c0a000942d0610040041e58801d45c0c011003000c1101e00c0040ca000e0712500d40003404080c600c020f641da40c0d115203107090000d0f0300c80c807014020010039001d03002a600740752140700c44000b4408003a10828020000c101e030300780180d028800400c1e0103012101e030500107203030554480e000608440c05602400b404220b100d408000242e2040000a0081e0b02c1d180c1c580e6914007050307800c5258101009030034002e640b881101d42c400e01c00144226001032640614081d400414001b5224200325650469401000011002803a41d40c11002d00c0c1412449807002401251450145a100950092881c2c2c0c4000c0091f42000042414034001c0c0d0a8918049041000355040d11030480703030343c0c20700d0410401e03110009025400340360403807404000e4810f03060075072200c40c09494140d00a980c0b92000d42007030200708580103e007480c0c1c03a1003101041c40114060b803030140890040000c0c4141e02110130140c00c00c07542c42030080c22605000184580e4544496459490f030094210200c0c0010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 79855010 1250 79853760 79853797
    0x703060b0405090601051e04060e12280f0f0305030a0b0d1e05070504090528020306060f0d020a09050108070603090503030403050f0d02030a1b1805060a0c0611 70
    0x4608001220240c540c040c0c003051594584d000110380c1540005000030441c41a0072450401c04808001000100030558904e030008510314100a4080059417111041345e00561403901c060f144000109150f1502c28845024100346c2d040a02c00c1c6000f030540206007842c11540d043c10543c01c00050f500409034501d0802c03000700312030280820b0b01d0600d00042c140003806020044170303d030030f00c445420305846802030301c03001c541d144082000e45108480444558120700c1d0408181c5010300c03004807802055800c0c010013900150040390700c610029003200d024104a696904042d02c03403c40f0203100d585d01400c0c3c0b801036999103c07407074002e000038040e01189005c2ca00001131000c1c402c0c09041116a040009103244d1b4075142e400740c0d00c03940f1080030741c2a03120b4144585083d600662000d5031042d04603030000b00f650010110301c1d411021010f4800b1041c001208040804800000380070400e130b6000b920340c5542d0f103038154400c2e500904090701c01010f160800c903400c1c1c00401800e01500540c082102104070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 79856116 1106 79855010 79855019
    0x20c010501180b0105071104050705090603040506150303042d0b0403030f02010c11150403210905100e0d080705040e0115080f010506040902030402040e01090b070306 73
    0x1030050080348040488042e4014000c002c3c41c01d10380305103441082c0c2c1c2c500312a28040c0004a014070740c1c900000342450301071000c440c54904000c4c4090780ba4a8986803040c0c3d41c40c1304440840064000c0b402207542420004280c2c0c00740c6400f0502220303c01003d042900c1c030007118803020a04c40f8802000000c4614401000f480614001d944511824a514102a003514144084041003118110390009004c9002c070300348a01841c00201d50015444509003203a52405580c1504c02d03158a481c504e02040c1540c3d4420102d6030300c070708251500d605a00c6040e00498410700d10014094018070981510b00d4844c41d09640d00c0400c60404a0078140c03541203c03041030101340c210304a8580040e0002600c0380d00000d150358460b92141081009604280c00300303129001c1c51040d04840e43c0c000c000301c1c0c00c540c0e0b160071141081d50030320020003c284031406d040390b0241003922090b01003031801c103000c02c = true := by decide +kernel

theorem cover : BRFrame.Cov 79676260 79856116 := by
  have h0 := BRFrame.cov_init 79676260
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79676260 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 79676260 ≤ n) (h2 : n < 79856116) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
