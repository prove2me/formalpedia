-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4964
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:18:19.38898+00:00
-- url     : https://prove2.me/submissions/a5bb77a3-5afb-41ef-91a9-57168b7045bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 892625899 ≤ n < 892805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 892627149 1250 892625899 892625911
    0x6211b0a030b01050735090f101803150b010809060f2d060307080115140a2d21020405040c0807062607080a0237081509010b03 56
    0x300610141020400b40321592038555648000c1900074211a203e06032001d003000f0203a0906c400c11b201c12242d03600d41c140c00c2c41c2840e03c1a01e03408142403007108281c5554100042d042a0007101403408020890881405030840c01744490034442107048000544a01c40304a4408640d50312840000d001280c125020a812044002e240718456100348000c00c61003001032402c8103142180d07810321649050810810008200b4a4000c0100f10001c04203442d20030514811001d40c00ca44094107407886c3d50b216058001480c285070000840419400b0450b841541c030350b520840c860005d00005840c43e00c500302c4942200440401494101e8651700b08001464041c1080c0c030400005031000c62143c00403c1444050492a19000300c2000c50130b10340c1e58900c4100c0d1500340f80040c10707014080040e801c00901ca070424052040562180b10b2a2103220101f140f00395807200300d644240301454100c2401301d40640e8419107170b82c3d21025a40e05180c6000c50050880116004501a0010409600404041d5401c21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 892628399 1250 892627149 892627157
    0x90609060f42030f041505070c0b090c0a05060d0204050a030b04020a09141b070614010512010605090703230903041404090c0303050c030906211b0a030b01 68
    0x2100c0004110b251542c50009012039560040482001d072140210240081c1c041d1010404032800c020412510701010345405144071004021408000c1d600c5680f00c2e444408000403c040c0ca0000e00c018003140e0420400e48030322140340e000c12141f85000c2000c8080a00181c81c1d00c514a18080a019407170703001d00c040b9075001e40d090001103080e41c0c0303140414000b58000c6e43e0360780090134580100809540198803a0079401e1170038040030b85130000b03240c08540c00140004030a41c010140e6a8250035031046980042c0210710b0030052000114106071200e0680f00181c2d1005e1101e010101514200ca4140c0640b690000505001581302413003608004d80082c584c2040314064402d0428100e0f25001c284c60300c4101d03400205041c070030844030f84000e11200c00c3c115402d0001000e291103d9004040314040601000740016504a07040b000300700b11295801c0141030709907070700c480b000c550030842101c01e40408403c0d99180400c82e007101c520130f5800340c4104240701d6071904142040550041c030140101074144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 892629649 1250 892628399 892628419
    0xc0e10051803010608030901030509070f1a0d021b010608030703050306060708190302090103050f0114310e0105010501091a0309070e040503032e09020c01020c0d05040e0604090209060906 82
    0xc2c2d2828041c4c4c2c03000f081c00100641d262613000c00054140d400080060a255001040410080318440048022101035000c8214810700b102c50200c02c0b0700c9021410090b0500002e0074821903d403c0d1060021241101c008101c82a1108046522407150500c00b0300055024004078019140107170003088c03441c1c4200c070001c1c85c140042c0d900c941d0300d82042441d0130200c0e6000c1014442940c15020303166100c0c81c6003000040544c1002e400c1c0d074407100c03100c14050196410030300070364455400c91050301e00e01c4410350072900c0c2074005481440c068200800c0d05041c9500300000099035500802c220000d440c200a00c1110198207000d032407a058100a1400303080d445a20400035407011403046482c00f49005001440d40e0303103007079140090b618861100e40304492680421901c69210603a0140054403810000541d071441d000088078003a000b4400099002e02070740c550b208032190000000e10032100700103040b83e001d554800c200720849600070300c040c0d00881c181c00003030b03401e01d45101641da22140040c012105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 892630899 1250 892629649 892629697
    0x108092104080601060801030605090c0a12020d14070602010e01060b0f0a090302100309050d14030a020706060e011e080303061806011b110f123708040501030c0e1005 73
    0x140c18001e911176804644000300600c2440228052207134003001710401015981e1038032000c140c0441c940e100340745240c0c0450f15200210358803644200034403a04881c2d01c0801280448403540c0b9641c06100e00000741d843c00044051980e0103010300c4044540c00003e01d403c09100c540c0c214025071225040c81c08100c1010780100040e554441e5941880d8110390300081c21203028138086140600552500301808130444c0200064445542160341c071241c15540581c41e600207103001005000c143d000304000040240021820108403201315007054480209018019980d089143c0c59100555a5903003055a0402e14071420074030b4504141c12510614090754030410103041030404007442207048820621700341c440101440d051985c18808501101c01c5110868050301d02c0f0742d1040c00e03085800386141405071514100c012600281c050710903402031000b660300039181c0264960300034000c0c5404a807500701c0c84180c0c948104010355140c00c1c0900b031408c0f1651182e400342e40725082a0216884088040781c0303103007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 892632149 1250 892630899 892630903
    0x306030507171606050415111e0a02130203060102070e092a0303160210020d0804020913080d0b01030c050705210c0d09030501051b0a030c120504110f010809210408 72
    0xc1c5215610241c40c0e0342080c410340d14a00c01f9110745010050f14031421810201e0214007600c1c01c4819465046044441d103a24a0a0000a8a000e0b6103c1510040001c00003402d1300254480c0c00240e090f00e10301c0740c6680e03140c01080030940740030b19158410100d0f101c44058800059010803030b081e00c8001100c800c04002481e5600441c5603c02201d064500d00c8110305100440310340f4044103001412150b03014540003030201000030b101a01c10545100420324203658084140302d0700b0707001a140380c2e81e44e20a00d0b16202070f248140020780000d103032540e04400d10307210b08144d0702401e80c40409046041c07000340f22100c60541840390340c0185002003107052444a4200302003c2d100c2c1550b140d059070030b495424541e00311500140701c00500c1c003c034504482e880a8135006c41e24990481e00700020581c0b00d80604881070104c00500c4200503142205000c00d00c010722401480c0c1801c11141c140401c4081c6004440c501416103011040f54852014040240d100100aa450258808601381400d0b550390100f4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 892633399 1250 892632149 892632193
    0x30313141c03030c170117060c03160302180a0f030506010e0f0403030e01151d060625110a0306050613090305090f0d02060d0b100504030213050a0213090c0f030603050717 75
    0x140c10340922061071f40603040240000b41d403184003005142d0461503e21600b519000c0104258410141e00003520010486922880054000054003a80d40f507034032428210b4a1145900040c1e50500c180000010000c0c2c20b01e003460310941c40002e880444d600e9968081c0c0182030b80702c1109040755210304001000d1048c004803c0002d04000c0704000a904950003048042c0d280505103a02480b4100288500145500300c846003204041c4025510302c40541072075006070011951950380b0a400c41d07000020f00000e0341000b402038030126001e244016041c07071a64100c5d100a40010081002404502000e00e0b010902d0602c44401402100c01c00c101d50740095803680c008401c515085a403040420301d103050084152419105e0360400c00d18090458000030481c241c074881e02d102060325100040c00c401d403940c0640e0458041c0340103600c01c458650482401520710341d0740030000116611030300c4a000d4804d02610040342e4200c4050140340d8100b0051180c221001038070191544501551110b01c2c03500c0b85444 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 892634649 1250 892633399 892633409
    0x70209040605060103140f0c07053301053a080f03010e0105030619110702040213060e010512040f30020607030905060f07020705030313141c03030c1701 67
    0x180ca03c1c3c10ba00240c100d60030704280001e080d48076410000544a0082d000ba080481114400c2d1202e55600d8071916100e00c82c10f0002065150f91a0000c028103015004862650b5200a1440742c1e038a0310144410140d002125030943c41c03000810206540e01700311000308098082c20510790001554488901d5a44031140c1d2010030000000104284407040000b5405031004038080e000908182f4010300086002c10301c0007d03680d5548400394a0790841804440c0c00f0b03540504150f403075032130b55158075091384201e105110220780e0406840403a90f119008480035005035901c12059610365894000411800e604100c1c4c0b03c04c42c82280324440c030080c0484c289145161103441d40c1c2c100041d10001c0c00c1880191620090506002121001400c089180356001c0d5820b40d00407120b50f40d41c3d070100e15096140e4842d0303800d4000095585801c07031003074a0f0303007081e59101699140301c1e10381c03501400680115292607400741c0755420075406c0001e00c44d401c0311121810354039107055032483c280031907031024200b80c2c05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 892635899 1250 892634649 892634651
    0x4120201180803040b010501020a0b0a05060a050a170606010f0f0c06090204021207020d0f1b0c05060a0e091501050f0f0426010b011805122d0f0705030c040906020702090406 76
    0x4220401c41758039802d034003505007807015080c1018240c2d18240e400700090521111107440b84c1c0001c5560316040000001407030300601c3c0c5d00810f41d9501060149407a2881b503402c0364000c0780c001804650017200a40400e010990350121445c2680c6400c0324062150701084804e1521540b0139005a07a83c0d0025007600d10802e0300c801e445060144010b0706d441c0d800d48280d001c1c461084050514540c00042c1c6507010004a00e140c0300403001840c01134100c0f59682c0005038405d802044444000794810400200600c09403045400c1b925681c207280e1100003201080b81c000340c01005100711030740201024220711001c2924141c245a111541c5025096030003003400304001148440d414001824012038200b580d081c03c1500a44041e10058050b809190149a008050101e038102500d01d00704502900c0c2ea80d007a82010181d22562140f0361011840e100c05102c504c80c2203001d2003441ca000c60410101c440c024020840d5000c8982800054040d09005032202035003803010101584958034110321562050304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 892637149 1250 892635899 892635901
    0x509010206130309091a12010b01020111072006070f0302060f010909020f0f12030d0917030106020d031a1e09090111121518061003021204120201180803 67
    0x91605100510000c201c1d004002c40002090300718180e281035841d4002d000c1100d480254072189202c3d002640a600300344a001c00304a041d10661181d041d94000342d009014040441c20709488a00a8210182c10b0420701e0409100d090560940c10f2401e410150803130b400d140441e1207062803116015030039405a04203408001c0d02000101c1954003600588608001600040c1c0104e5810040e20340b0190080c401c0602108903907491224216444e8103220890b0703903408034502075101070035040d03008a0368400148441c1c800c031126802581d0503581158001e00c8030311143c103011405414550141206261110340324002034030349000080541d03103406011428200c103038051210001005240e01d020307925003e42d0340f9004100c88112100e0702c203101c4003000700341c80c2c43c8550001129841c120650100c05c3d0901d50313241000554003d4460310040760003201c0340c814260140e090f0710441c240d41c03c5c03440c200400a400185a40e002454084581c400058101540d901c00c41c08407c155009842140d03001c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 892638399 1250 892637149 892637167
    0x180d0803070206010611191506120c06080609040f0c0b0a020313080f0706030908210f0901090b010608131e020f03010c0507030c0501020c0a150507020a0c060f03020d060605 76
    0x1242c1401041d10341b82841036000d410440e5078980c0b500c101c5418001d481c1c55840030500888003200d0162a90000d01007002c582e9580f0b808404a2646001320342c05074400000288060080485510820f00a8041c5c078455071a40d0b240006512850750032520840c0458000c030701c132596200500900e0207103800441c0e642c80c40c10015801351032241d024100d1503101c003151603403d000104400045506034100890004818540000070303000d0030012003408040105010310300000c41044600a01040751800455114560380c20700b030b146405409000e0310007078001001040d110b82d601c60360105480708071401640740d99646004054003410b421400300c1e054240c07041513150200030b20719a850100c0c02003107641e8441d80d01070554024901c0140600850303003240e0302400341c00c3d01120f0b03c03656680b040c0c8006864520305001020005030504079a01d240100240490340000381000c403940d04810822072a92404104403002d401881d030380c03810141c0030301038028012501d0042c00042c189a8944503180d1a0103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 892639649 1250 892638399 892638403
    0x90c131e051c080f16080c1f090b151c03020f15160e01210606030f02030402091501020c0a0806070f05040e040221150103210e06180d08030702 63
    0x68102c1c068031038000940741e0001d00d50104442018141c280305a80740c2c0c0403207040c0550174180b013901401a07030740007038100d000480c0820781422000140c1f154640c01503440c0c840f00204c507a0080e0080120382c1075804a0240b07000d41d90240e14402004119076403081d6800221407800051205c11400359000408070b030841c502c00d104007203030070b080b55603025001d24012110710b59140c4d81e6841fa40070710456800c2c01f61103912864036400c00036480e140e900240040026020001d201500c40c03040045d00d00000f1702030324662802244c1c0104e400903e6246980c0341e6051100b64106100300c518107604c10092034100c113403600e0361540020814a4094612880c10712030207002c04103028504010420100070900954003078104881d0400e0701a652401d144041c0000c481d1105040182203c480c4940d05000d6418521410001d045c0c82c4200c0412205182c0007103400c2c181003015203084040746441102030701e1030074464080c0c8a501c0c0c4000880301c0c0c00b2000310200302c07168510340d410798400c0720020404c4030107030701 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 892640899 1250 892639649 892639669
    0x20d092306151e0a030506070503070206062205060a08070f0e09030301060f0c081201090f060e07200a020d08071208040b0a0e072301020c0906090c131e05 68
    0xc00111000d03800790b4000101d034404000110794203480c480f0440f59490301c400203140041c40c0d10000706c4905080c5a013000e030540e00104c030785600501c21a0001070b0b8606000102c68081e0f041e45032242110800070604401401000b000603030408410940080c1c1d01030308105000081000e006c2243c100350402d034558414803401420341c0d119500402c01005450381c001e0021000d81c04c68036146040d500c081c504151148600001e11110440500c0003042260682c0e000c00e00e004a80d0a04100c501d075903400c030800b4580119040004034a4031301c0e0200b082900408105c161071000001d5808503015540040d9443c20004000d54005101268410402203944007541403607516091003902d52900d80d070f814815082c01408082081d442d8024022200400c11000c1c014024240400302e00b07060000b030440308100b80261060062107910880d041505104d00b00b58003030000900031101c1640c83c08002c0445500070743c0c1c504180507650304001003074820f9000105407612000880d02c0520b21f0701042104d6840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 892642149 1250 892640899 892640911
    0x90605040905150702120a0f110a0510020d0e06010e182b050706060b1e09030703170c030a0801090501050f0d02100c14010903110f0d03020d092306 65
    0x724100d00400442c0c400a0301e2100f040c1d6103249050b407135403440012410007a0b940010020404049211100c103504080c5150760326020b581d039001090309203090550380d0880d42c2009400754201c04100403040d0860740007000020020070021444000380404039143c800243d201c1e90740002810140702c24550014260017145101c00d000f48a60104034007034400802e1801e05000c1ca04949501041107a40142c054400c0d15402160801c010382d80d502103c0310f20352002c003c070b124a90f1400310b1a03241c3e031004000d40c3e0b2440710280c0100040c604590b540b814007060542d56001c20101401203d0220741d0400c0200800980341d0b031078542a51401c08110261030068104034418400c0180740c6285484020721040242d030101c0d0035491a04124600351212154142c025103201e10400402030ba83d101508044000d6111303a8030048404007041559444a008008500d80c0c0c1d0003019603842e01c0c6200c0e4010380a0301d81c2010340029040220380c4c41383c10004018950b9044962094665691850140180369201e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 892643399 1250 892642149 892642151
    0x201150305060c03041104050a0b040b0103230a060f14030c041b0804060213030605090c01081618050405150111060c070f060e010905150601050f070b2e09060504 71
    0x5003103554064442c6001804540320101c00b000080900c844211500030b0458090700410a504104980801511034030003581e024605104522599510034030400200503400410a450314405c45140880038101400d0040c20545944000c038602a0b940e210000820441c40b00d0512440710340141424814016000c6109504d0003580e449501c21b000044007480c0d0781c915084415540d5480d10400a00684000e1103260031044804000c0200340d620860141d9001030403a0400180750b00111088001114a41d8506115a0400f00f4003401500c0d41c841038000101c01c00506a10350740810100c0e43c04554010307031a440007041d5015560807040c90440b80b141000544054038020407280c0c514858800c00030700346849005020148107440d4002e02c4000581002840074925074209030303640300404c130000200e180d01400810350a600540455901048007005a424402c10703071900106560300400c031400615060781c1d10000105900c80c0c0c6400d00855803000001c8608004203103084070b0403500700d54012 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 892644649 1250 892643399 892643441
    0x28020f01020f0307050a0207150201060e18070614041a0405120c0109061d090103080403021e030a0308091504030203130e04080711031609090b0a140f1e0405010c0201 73
    0xb101910741240d0340a00d403030500320707628200803008925001040d480f0252852181c2d900703a01d225410340180d8116000d12014943d25200e501c081c000d5594501c04003204c9a004000400984e4055004005c43c1c20b29076402d903082540e00c6c07000481a05c0003006210b66042c1c002810710261a005070300a00070720480f401084000c150b070300080c00b0750101d40510414019a081c00c01c80480703450001191691010740012060b580d03d10b000c4e0181d400c06d0004901c240f20480710385040790050030781c4002e0300b00c00030020418014240c5081c0d03003110004e8038a45550088051301c2d0142d05115a0b1140118440d6004503555180104008141c0ca042c0d0003091000c241032003444081000d110660b8421900b04405549441d0814006072900c0d00800140101956010000400d007065030700c48040103019040c0283c00d542e80c01d0394072044503200841d510880490300b0210303011051000c0303c980c1c05010024040710340d850b03403034440d42918011503040704c5581d1501d0300c144160341d0a0240c020f0030042c41d00e1074001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 892645899 1250 892644649 892644667
    0x207050a0b1008032d0a02030f1b030318011512080c150a02040302010306061403130206040801141609060203030121080d0504020108010b090a060806030328020f0102 73
    0x110101a040074207101041408111a50105007040004143c89030880c0c2c0e65643e90080d11640c11005030344100500032034404804070240107000c481084016a000d14030709043e40200c4081500008410100c2080610300d400074100200010740c01803e007100c280c5800d01c5103422850075104144004203020400780700800c82c44a07411060f0400796401f4510648980e070668629103411041500b01240d1060b542c180996601580d0050042d43d0003a80c06011240c1c0300d441c140d0300c9074615022000e030034004100243c3d03445000200161041d02c0205107512382aa5001d2072401d68250013451802001603005000358500c06200c954044090b41c10101d003101d1808070042e4803408144a144801c0c3c012084001e0700341e0741019452405544192039a80711031000e01078400400c01154100d000c0740700300c400440c04440c180706842103450000d1140c000c4a0400400311007555010380f40503010b10003841220444480c4076143c0001000642c02c1640c0c1c00904540203250426031101140706920410446031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 892647149 1250 892645899 892645903
    0x17100f0608040c0819110d05010c09090f0b060409090c0308030a0e012307230d0632040f110d0b09160512040206071704050102370309030f060b13020705 67
    0xf110300e8128001204006d81c0700007180036400c0e1036000410035440c080305980910b03000740f548016915040f504102d04000c04141c00304807174445681030f0340b00c442400b041042161641011700c4591042a01400341503aa03030301c4e000d041e00107980020360a901c964039042c4000d42440b4880700b00c100c1c43c0c285427411898a240148a030000f034411000c10202c002e00c0d02d200040a007110b081045403503202a510310756a0103800013080d0ba4040d2140c0e01e113000100440c249140f44043c091512409600451060b8000c2044010011102c82c001101c1e04c40752002d180c0d20224000d04a600c41211010400b807000804000104200030240510040a00d5032005001c1d80322080d114000108c1070800c84c580c40703e0000039094000d681c80102440590300f0101c1d001210b44028208503102078085031b00000307a08041544500614411040e1121030010180182914244402000e40230f07003004500e1700d4a176201d22001001241c01522030716283d080c4105141452844d0030600a003496045040014582e5095 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 892648399 1250 892647149 892647193
    0x1090e0606031018091a06130507020c0a08010603031b0b01091104050d030c0605070207030f1203020c101a120d0305190603030c050705040501030317100f0608040c08 73
    0x507001d1a40480016408010b110b03c0c10007409148008800c0c81c0156031a0401600c2c0b68641100d071000c0507210130881503004c140b9140202001050400e0904503000c0040043c0740007000901140b160407041d014544402c505480500000e40000c11036500710b040142062000e07000c1c10102070481031005001c2240804401d0540f01d40c60000300b420b000b00c0250001a000b90b80141c3d42c06050348201c00109a04207070f04074a0b90348505014001c60b41c401c68141d0700c03121315110103400109142e0312100055480782d03810ba070441031820010700300142c1c240ca242c902038a0f02400d8007190368400b012082d10380700c440481494881201c1407107428040d945801d4035207028694943c14551a44049004010b1906104501c0e060b00c0701c00300811a620b0134028550300242c1c809941d02e00412001203102d00741800390038142e07a015110030003602c40c003110664450100821102d0f43d034064840202c2c07610380c080c1000d00101003d654210150502e406c207016940c202c0e82c4040313402c2c0d000218004800501864013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 892649649 1250 892648399 892648411
    0x1020601060f12020d1e0c050f091c05030d181502070303110f04090f0207120804050c031501050f01020d1e030b10020607020d0203030f220510061401090e 68
    0x101541c0e501c41d9409840003d1000f8028042e42c0c004900e6038102406540154051801b0300300610707112010799005801c50b0080025040014810030401014200000c000d00400901520a00c900003804c40398042c01c0664050441c1c82da040090128038600c00307405202000440d607800100d0b012003a0343d513a5004002c00c55809045500400e24409160081d070110400d5400214080d580351030110a10489512500942c25100d190400c2e0400f20382d99403095503071250b809160310122000100b810b40d0a82030040c801c9545208400c015551518184a070180010111020b0810355050600b0441c026080c115528115071285161843d482e80c410044c03903001d002d1f802d5a100300290318500710060150314600c5504000c5080000700034581c0000c1c0c0c54400c40140d401d6a41c421100e06080b6100c5c801650740210700340350301020855002d0303130310108619a4030240b034240d106030050791b820381413030007401e404001030f691003008000c40c0e20f42004098400b142482c100300c44508000014080d501d000d854 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 892650899 1250 892649649 892649657
    0x1060c020907021009150c1701030204020304021f02070303140901020618070909050606040b06070c14010c050f0615270703020705300c1b0103060f0e01150504050102060106 76
    0x810301c900c1c024420303000501355100050100010900f0710f02180800103d50003030071494801507d080390720070840c0d24500030740c0f400000b006910750b808000180d0809801640e004545031080c000c480945454000e0844440e000f82110030b295003405030042101c410304100420003040b016107161fa001c140302d503015030291442c0301002401c40c080d62809580d134024101282c50a9010800e2200000305a4071450301101c040c000300301c404040c0a801d0090b01d400403c203c0d080c5100303000d154412040305034005010f24164204100070740b922460424108400030b195004807007840340800410140745c01001040e113101007111010190500c5083c402118000302400c040701041c42688290116002130741c018088401c850b0b207081a4040300c001810900c90f003140541c6a0403540000c0c002030352141701c00c40019245205141c510082c41c1142c0c2c80083d030426a0b1041d021844806074401e5070060320404080c03004540c186401303500c4440152481005006003072000308038507a400200707079042d0396991030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 892652149 1250 892650899 892650901
    0x203070303200a0201060330080a140c2a0a0314121806150607120315180e011a01210501180c0f021e0a0c0e040b0f01060c0209 56
    0x1c886190040d80c036040c070840b040001403404102d43c0c150001d0007035074000e488180c200a462002045150700f00200e00300d9031204500b0010300c40b40a801c0484e486030340c00c040410707661044410700311802422034846001903130204040190224514842c0892601000403004001c0c00005059880161110060400480790381d1894400d181c02c0555100740081a14030302d1500705803048610901c030100c1040c074284120f1000034482c4031581c2c02c184031f9030320141805103410501c1c1c440041c4000e03003c0e6000c05060b00e4940c0941902554010440180386a8600160300e845020605d002e03198043d9095045a04080e044040e51070310815604c1104000d081c0741c9001e5402c14804401030100d0045c035901d13245008000981e0303198801000703100c0045800704000d5080c429000341d07101e1040240b0a40168800c010710980058070601028803560dc5070102c8040a4035592051031501c2c898100c0c20700705425800703100c1000b0301800c05a420184440103403210b5810004014008040d481e4041e2095481c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 892653399 1250 892652149 892652171
    0x613032102220e18070803030901020c06091501061215031515031104021606020301030b04290705030717010b090a0e070c0b04020d021903021306182412050105070503070203070303 79
    0xa05d00104032100642e034072850710b030082c64004e40041100741118001d080008440105c0481c049880454100b0340c00325a9007440000c40b900240030303400d103030500d0f919027440c0d546105180000004500c0ba490100d01e0414001d42e02c4142c034216204c640c032445114105100107185c1d025900300d02c450603600180c84142d94044030b000103008010107407809100000200501c9005900346108a0051410010940588158a40c0c234a1403aa4400c010b801d80c001041d075080c80743d0010f603000b01c1645031100d402c2c0030102c581c50070103c00703070f0256001d0100040e880b0301d141000c80e01c2100810303456030104864a40054050003c02c0c4d01c105c010510051180003804550301c00c084c0c20346280c1c001e0080b41c51240e505003080050b5a4034001a441782c0034105c00c00d103000d1040e000c1da4ac02e46190007081100d607a0301c0f241c1c002c090a400f403c8403594005a00c0c010300c400c5400c21740e01c0028a04c0c800326845052075800c01d40d0858002400c241d042140400410822540000c02c4a5245505103000101d443e051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 892654649 1250 892653399 892653403
    0x9180209060301180605060f0714252d091509050c0c120301050a0315061502031806090901212108180613032102220e18 53
    0x840304250300880110011401403030090102d1414030320803800b004215200c904021903400b80742d44006440c1760400c00800018004181e80d00c410b20070b0b40485031080080301c100f081015100000020458203150700f0085140c401c41c860610602038640c2c40420361030907a04070152181e500408000320788030000d6000e00403da0201a006161281d001c00c11400c288030078400750b5004503a441c015100b09008000515034440480b812240000c00200c056031840c2e0350300d440b0880008024604542d16500028111151002040c003030040360301842d912041e030b104507507603000e480076403500502c42409500e409442d0211002d065a419048078400f4007000b100c1002d000300515401000f0681d65624000204a40d03a010b160702c140a40f40c030700260b540d040e811002101c181c1528a00d560261011881102d03030418001039080c003900d00541c00300c41000c1805116a500751180740001d500050003c44448054071007120400f0240043e14600d15140d885c03c81d04201a014005441800380e60708411700c41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 892655899 1250 892654649 892654657
    0x7140c0304080304150e040b0f040902040e0d030b03160e0c07080706060b0406090503120304170c06040f171c020f0706060e1602070b27030a0b010602070f06091802 72
    0x800b01203e41e115207903680c090300b8480940725540400e0818400089624060250444445001d414041e00310403d01c1004082c08121a05a07041644c1c0c01c400800c1441c28440011100e003182c8011600340c403010300345468407a80080c91040f8840d40982440b10080c0d44100c0d03a00500f0a010003070b203a4205040c45102032149444c0100030a2401c0300006001030320710050022650300391506580d466451060544400c1600e4001194000403c0000d000500b84a256406038503155507403030500a003204102d00d4a441903e043c0d8008501c440c40008100d0308508684a410241c04450305000d890842c000c81c44081250101120b0340100d1a0f000010b1914240c411658100c1814014140c0d10900038041003000d07503498091510a402c0c0c6040c1d01d0000410f241240c0f9106441c6150108280500f04280d14079031072100d401c9080c01d42a04030340d80c104403d0b01074034011890303051030b03514112019240c02c03001e030702c1040001c2c2030301070400c5155000030310141250241c49148100d08005150b03030b40280b013 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 892657149 1250 892655899 892655909
    0x31e10050c0405040507020705031002040501270b0d0e06160e0904030315090b030c03010506090411062a070e0105060f0319050408130501050306090a09030e030321010e07140c0304 79
    0x4038120070450007c0d40042c1600440d54243c042c0c031400d50400c1c043d40f060317218500a250201701160548065000d4200e0a5080925035034500048075440791584201584001d12100d07207141c0b6850a1885240180030083c0c112202040320044400d0b403500241005828200249c411a1584001000d05001750099188800d02c2e4103100140c5480307502c490028444810918040c0c499011498042d00341403181c01d00130b02004100140a40d135075500c018134150001003281e0060300c03e100045d031450296041c1c10241800103003c00011058281d884d18210304e071b90040d4000540d42c001080716455041c12070340c600c407100d1b42c03403a0b80b603691076280f01d10003a4a2010174500f914100401040c07158a001401d004480c2c0758203500c1041c0d0780c000440700d42c0015110070b031780410003902042142040703600c505c0213a442410300c080c061096100007411a040005016000700c141c40c2d00101c10401003140c1c60250043d140b2030091420302520003004010310070f100048440c400650015002c038204181d0f00100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 892658399 1250 892657149 892657151
    0x220207060e030a180b0a2001020c1b010e10080c0f04080f0f06070f02070b0c0f1e010c021f200c010606120b01120c05040e09070302031e10050c040504 66
    0x101489402040101c0740c2c0c2141140c14161200440c1c1c100000c0d04690801015546000d1410300e031f0030242d030103440c2d40c0540089642d402c0003082d00350003041c80b5a08000d164000c60307900b500e03c41c0f8009415034682c404024412034410203540c0c841030304003100399042041e030401251150b0301c04003d0b030b000e4400c0342c10000d4944102e1500806010300040c41840310300030700080d21107586807040c0030b4031010307000611400583c1003250248500500355010700001c49000342241c07007505000000754100131845004a00b00080c074596145100c03824000c24036003a9003031004290451103200e1000070385007142580000300d611010b41100381c01076032890034a458030300156203a0b502000c03007246000300034503c1020003084240c1e440d000c00e46168030a0f82c00011040e1110495801c4840101c001403560300c1211007808814000429140034a105543c03248003580c000b46049402c6004051424100904c1151490400c400250b00303a000403a15030701601f070044011869803504d4070045068026074000341d03041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 892659649 1250 892658399 892658407
    0x10150306150348090507090603150e010311060c030a020f06060d0510050a0f020406020a0b0a15030b06040902090f27120c0f03070f05010b220207060e03 67
    0xa0050000703258201c0b80309401c001c0b090500400b6198800c54800680c031054414140300030352040340b15000e52000d581481031050010340715003104d402c440b41503c0a13000608002d00622100c0e8251281c2c1c0103aa0305083e003502d9044c5080501c2207181c005020082581c5180381c042010742d210b410641c0d24014230642079a4407054219002581c07960341c1e5021080c41d200701c01c0031907403d080034041c45030081c0e000b4020704220200103075403401410025041c51021541c1c3d1218486100c100e00c003400c003a0289a0181c00d140000d4200a202d080d0040c205140c07403131920102070084004858048101d90303011042610700d032350b9600020f0041407060f50182d04220385034104082c0d22500341b040c40c442c00b0703419440c180440289440b400050100e1190704101c0d8010b04048680d480004040c0645040e071604451110809081e10390841e044000211200080781c00290200724007030188007240c003402d40d5a081c03c10711003c4039441703000c03411403007071046a0f00180403414010190003c034828000d06040305e0352 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 892660899 1250 892659649 892659671
    0x9060903010906092a03031e02070509133c030504091d0f2107050c0a080a0b0702010506031506010e0d051e0102070c05091f0f0504050a0e10150306 65
    0x40081d0303008420404000317a1000d10026000240c0304040d030f0340551300d500c40340c504c45d4040c00d07081060140510940c0b1450344005aa41d880700c940a118440b005820410341c4c0d00e0303103402d151880b0302c081c5031942207545451811100c11310b0035030300c03c030b200c1c103039941220000250909407190b101c0c0e6006821010b0825100690007500e03600da100e9442c00c0201241c3c440d04681c000c0940301e882c14600400c0c8241d41e00c07898000b00b400000580125401b0320b0548850007000000212a000e55a0103264640c019819210502806905059200d00a40000c2c0300350300e08200000d403502d800190a0800152801c04104140d2040c011203608031b0024100d815051000d0400c0b035901c4071103124100004440c108800c1d1340e00810f00175104a16405910f00099505040800400300c0d00102840740000701c0c200c01415500a00090030000d0070300e0703040300840c24102800e00003900d00040c000502d19080c0bc0d0030403220070340080c48c0c0c4962000460300103015840c1071450b00403080d55a2002d1300b024101b03580881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 892662149 1250 892660899 892660913
    0x20d05070e100501020a03020c04150b04080115050a030308010b310f0803250f0f060507030506150a0f050918010806130206040905060d06051e0a110906090301090609 73
    0x80111058100b00c400c03195698012652100300100040060b008444420024213007900a8140e00da030b5851008001ca8844807446090741007544200c1c2e10382e44402c0703c0c0c50500002802580070741400d4030754420280c1503444c090a180418420310040c940001500200b400441010400d02c01031000c0d1302d9101803440d42da10240d1202c60080d07500800f03040e540010031450002c00c44040040c07561400d102d1b17001704603140000250035002034600300d12042082000480d01901801014803613000054613040c0480c004044983c0200040c3c0916003582d001e0400c5655201a210f1002c443c0c54141110900c00404031994010303140f0f25138100e1150b00001810344501c007180f505990001048420b542d407030245490801c02d003070364041c4d00120308010522041900e0381046a12200c0a0649011780c4e920f0b0383c8070011114100d4000c7c903d00e004814008103d40202c003200d030030401c951001d100700c0e061040d40c0300b010312400391120310600000861884545080d000080d80300e030041000c111a60b01420002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 892663399 1250 892662149 892662151
    0x1090210050c06010f060f12090206031f1a0702101119140a0201090e1519060e030a020f010e190807060908160306050a0e16140603041e020d05070e 65
    0x16040f40244400819131054103d00903040340c9440d9181200303450010400c1e691040c039810440003042d1144c41140241c0c8a410056024100b4507266480c2d41c4c100200c102422841d036008140803d0040100c2c55a107600d4000ba5503240349c045078025a18076140e1000d6030800009080c01c051402114003524035051441400810f483c0516100060300959141d85511100740d20360003800700d104400240001012042d545900c428110a444100c00403000000c05014a0700e84000d604c0141000c180f101d942e1000c501c060421040e0010440e0300350b1a03002803032460340d2070091410020000c202c0c000a43d84c0c004213103d004100481d42c031040340c80300038842d100c441f6801450081740800303a0000b20140006582c485030348040b00c480e464113007142d50b02805840e01800c003106003620360100c50024030f01806040741016280302515003841c50f0121481000e1454800248641c100340300300b20100e45080421131641540701d0303140201220910000c0c080d442c040174042c0091090403000b03e852048440c4039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 892664649 1250 892663399 892663417
    0x1120f0f020a0207090615050f0c0a05010603120315090f060b031306140f04030e010e03010e07060311040503191707061509050405032703010e100e012703020109021005 74
    0x10ba0110303511760b05550b09451980c0700d007520802840d0407041c1140c1c841c0020b4090224803440c2c11740b0300b14080308068034007c0041c509840c00e96481c2800c0082240d65440e00c03c402c1c0705400c2c1801680c84103a40051800001e2044041550311035280c4005040258000c2014040340c80e10305440c2d0401e6201000301744201d6404503480d074a0080c0209189a803a040c1620a81e004010a660741c3e070307281e070226440b03024a240c4905001010046210f150740a01507845801907100013810341c9850114018151000c2551003d0b5121040005100a40b00403804a030352841264401c0c1c4802c900e8a0020320103e6000103403401108042000320801c0529004105c0740d0410003c800c2c0590f882e47e5030041103030000c1d900140035034802c01507224031400840c8060304002c01a02d03c1da540001e4000864251001d24164212603048a4440315812800d4030507260f00701c007418020000016040c80043c03d08038110b51000f040841c05d000c10701014402d41181205503030152079241018010300e0003901070342107103200d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 892665899 1250 892664649 892664653
    0xc1e0509100305180c2b150203090105060a050a03080f120405060702071d13050c090c09090c0702060717040504020a0807021c02060105060903240412050703050901120f0f020a02 78
    0x402c6801c400915155503405c01003981241c0000010070442c030310b05040075440800c18401d00728000c40d41031000c22500c0d1405c502d026999160441009003100c0d8010042481001000d0091006882d21a119810f07030358803080c03048d591050700407058890301070395281081040b0020b04020403c080440c0380c038050b1909800300c5031801d031980e02651008e046040400760703130448400001d90300c148443c290b241a6020310140c407c190045030208642c003034210750f200da103c040002d0800721418440c03d034950042005483e0b9003880059400034034113224046029010b090013402258603656500106c900811000300215a40d50f07010801a250318801c9840d0740241c0688103030000c01d10701810b03890352217045035400760450f40c0c00c0c101048000d4110f121880d4251140440c03e80c1241403071006880c1140c5207010b1000c40d45003a1070440c10042c240301e0032804000092004d03400181d000410b8a140e14400d0030f0090a8650103040a001001010704100c030960910031001c1501c0d03003c0d402064407a9043c0d007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 892667149 1250 892665899 892665931
    0x90b10050306151605010516020f030403050d08100915030614161d0402030f010305160e132a030b1503120304020a12050309030d030c1e0509100305 65
    0x80e00e0900044030201d80010712500030300101c103110710050068100c00750040c0d40c0b06149855250850f00115280d0402c043c44c58580500c1503010400c401207120709200131850141165109901d071140e00260009000141000c40e002224204003840941005d0f6420003030303103101e008141c00341141403001355a201d00e009603090420a01021042c4130f41020301182d2030510790408100c1e40308028204005549811a03107464107992035000442c01075850b4141c081c1c00354114105203003403800100a1020f6018030400c10421083c945001603480442c2088412040c801e60920184002d071b1003440c90240e44045940400581c000c00300380c82070300d000d60301001e450755034a00300300051342e00d8240c8280d0550044502c10b80489104000310340c49440074103451196981c640b1004041206e620003100c02c0c1c0c0004c07881481c40c1c2010003000290300d22a1900b84013840004001508104181454035214404401e000103000e01801c22210740d000c020340b100c00031201e00000180200001c0c0d501c07294594a0300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 892668399 1250 892667149 892667179
    0x7111201051b03130f021c060b030124060e031524010e0d060504140706021c091d040501060f2c04050607121404060b01180605031306020405030601090b 67
    0x40c2ca20580402c0041c110450b0940c817865881020000e040341d01c4041c01650342503507069481c400c1050740c42040c1c0840d0460140c810907080d603004811078040c81c040004030340949001907805504031541414007815402510006ca400e02c050303a00d6234980c2c03400c290705000703120842c134001d10403d09014800d03819403501c2c10011a189000f14030210761014540040b100800d06031360195070000c0c40351000400c90000211420b0030803c40c0d40c045005600005900542c0207010b07406942425200e181442d040c0342011610b0301c20707401e0446113150800c0b030030001808012095000001800035100300c541e40c00c1c0c0d244155950244100c00442d01e502080c0040c400440800c0081400340b030348180a0002559840b204480900c1119006420300d0784640d20070f04901c004541c130b01d01590240e0000b081b560340143c0050601140c00c82c4c072100c56510454100708555014003aa034101009000ca46140e091504050020703019a030402a8035010b034a00000340005240c1c082424071100780c0c0c020900f03018407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 892669649 1250 892668399 892668451
    0xc040c0f080708060907031109190305100b0307030f060209090420010206221e0b010e0c090306010e0711011b081e070509010504270b0a1a0711120105 66
    0x1518550380006610006c21707502c5d4005d80086450100d183c001c2c07410b0a03000000210000b045840c001509203000d0300a20502c58240000c2d4281881c0711024803100c8940c801203a66264140f00181400364042000000c0003041d80440d161070f10001d01c001411308042c01d029807424060709210581130201300000d6119400411300307a12804407404445a0384254000596080d08261000c9605040f900d200c10388200b01425000c0c0b945000d400d20a80640c181802032031441c8000e0300300740f80c880f42400340c00d8a40c1d80c000340b0039054680d07665030322002d03840d8414160340c1c441c402c4100c00a59400e0204c0c150f030400a034045030760801c4c0c65640c2c40881d6110814030161850805080c416200c20b000c001442c2e01c0c0c021402001d8000b4189004c515143e916640303403189c03a078081c40b503100c1e5840440720459640070902070365000303041c01c8802e23880043c5041450401c0e41103a00120000b0b20300803d04005000054450607414403014004240041100900e24000c0c482110443c01c1c504590ae6109241404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 892670899 1250 892669649 892669651
    0x603150507032004090b0607020607052802030c190512030304110f150a0c06020d0504020406213005030708070906081f08010f0c090b03270c040c0f080708 68
    0x50f51078007460700b420585024050b1080d00115600318070308005550040e10b9020060124a0040010304a000c813400c0c441c4884903803129000380455514055140981d40201d4500f0940e01d0407501760000d00040c1902e100c000e00b80d80c1c480c2c0da1200622940c3d4a10000c0840151310030b91052030070000e0303e43c5010410915a00020f0303c540c000c01c4402030184049110001800b0514450400c0d030010704080c0e4510060780d001e04000701c0e1781c5441d2000c0c0411820540078180c06001d04101c140c800d4178060104010610110b84007910031400d0040003104056414160140c110460034050807181e003405020f0007a0780160346801c001400c103400154214810500001070355415a2103254079160000d403090382401c042488500ca090700c050001b4841400d03c110000c0c0c032039450010641e2160000040c0c80b0103400d511003c2020420400c205180c000c460001d121110640b10003038020200002c480d26010302c0c0144a45c1040c50a5910b01c0e003150070460011300f4146554410b00c0d02c2e900d800d8110796200c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 892672149 1250 892670899 892670951
    0x18050d02101d06040210020c04050a0b0f030105150127090212091605210d09181b030908191e050a210e060a06080616050a05030a060315050703 63
    0x2125002c907006144c00401101c5a1801d0f1045641310f00c548e20001b012284140c0d07810b003c0a50b00e049641c00e41c2403265840b00414402c0300200030030302c0c20b01069911307400060140303410004119896940701500080080140706d1014078628041d0325400210025400000451100c40c644c2000500710880048e407107084680c04d03040c184e2400e00d00800c1c030442d5110081300d880d4190700303001d4a001c540f07010000604880401d90b80c101101707203000b40702e860b8442c00644c0506814100000300c0740b1003070315000d0381c1c0d00b011642c41c0001c0c44a12600b0002828023404400300d204065442070141c816900031400c41e00b0041e540c10701c0d004072171165802e8400b071090741807040120f154000c20712401c4102c0203a111102c00601000b2a51600d1000c0c0c2e182002e5080b0390540b80250788150500622030100071413613000c4403030200505200b00c1d4020280c0580100c1c0100c0707040040c00000609031491a410240081d50302c450802c0c810300c41580c54034060704003120444000392030403d1142c0c00c40c00104402d03003c0d103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 892673399 1250 892672149 892672153
    0xc0c061d12070f03031508010203071718120304020a031b050307140d02040902030709090f0c08010e03040b030703020405090108030901030b01020c180405210703080906010e070318050d02101d 84
    0x20f5030f03a40e05a024040031942a10303c05400a00082c8241080c00214442e01c42d650b944940e0909994a007800e0820181c07000d900850001ea002c08a260005400c45507101c1c2e00c12460b4a0303035684c3c4000385450f08aa0401402c5110402140800d0b1040c21303604016100e0840c02c1d616440d0b214604040483ca100510030f0b84907070482c0401c000340c00c1c40da200c6114240090144c4502c161a1051a410340310091021600404002094020b00120214800140a11600902068443e07018040c0c0e64011030003040d40c054000400700d00d50f00e000c3d41c100e030000e000c003030003c003015a5964000e9803a40c0090804902290170103907400c02540c4049448101204020300660a214031030208061030040280100c071075216640680f545144608040b90048483c00c014580d140c0c1545001024540060803d05007030b40008014401c1d0104100c5642d40500186400580003282c4150138000a0100d1070141040c0911820344000b143e01092940d52220841c60501400300b1600940b8410000565506515 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 892674649 1250 892673399 892673423
    0xb070c060804050c03031623064210171b0d1104081608100b240d0b030f070911281209150c0c061d1207 46
    0x881c010400340d500140241c084844a03c00940400c2c510391104a00d03603120310b45030b03840000b0000c4c084000c5406144031040c18180210031221580e0b42e68001d0001c0c2c000340e502c20788144c02c400640803485131070051402e40e903540750700a88040d50750b468003003261801549204001d02a040c02286068201d0014480c95071040d0786980c0724141390500601501d01c01d042c01c001ca841403405c1802841030400d103440d00e0079510f0b45803000092a09981c1400c04500011140c4104038128001c5030035480407018000100b079915203a40000e0000181c0303041c07107201c05030f0710030741c2c1a4201540018041c004c1c0c200d070342001340802034001c050340c600b4100e84850565208020034450030440b50405038800c5141856681880e900e100c0c0c00e43c848451004800001c201101d00903542a403299500d240c40010b00401c00c080d032401c2e00c2d0064040358007017040c91243d85440c40d20034175503c500f00c4411419007041b000c1003140c9140c03120382100c0003000381840c4244180100101140001000c5030070280e44a1008903403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 892675899 1250 892674649 892674659
    0xb01080115050403050f01061514030604150819140a02090a0f1508031206150318100f0213060207050342061302180904020301090f0b07090b070c 64
    0x201000a00c224002c01205000010026008004178401548460000700b0210f0420b05001040c400780c864400c100086000041000d201e80b4080300c0d040001941c01082090b07194100740484200c40d0b11600161040b40300c80014604241c9c02d00d01c20920460b101c41e40c0e046107000b210755400d11098069805203904000c0b404c004e685921170080381000003404541c542103840000381a41d419480303404c40c3e8000050080500004000c0d2607408207003141d0000492511000c0c1805900004142c10203500303101e82d2005c8841e4041211120b101c2c1159001c0c00803400d41c005600103900031700340c1c0e03c04044040c807000c0b410600100c1c5000c1500c0c07025004106942c044400f64900c0c440009400181c000a48800c1c0e20042e107200c10407450f0b03500c41e402e0344046d040413814030102818004018101c0340c418441c03071002c12003140c0c1a410b0030780100d40e185103e803642c0c0000307401040c071201c000b040c2c40300c000e00301070030044c034000c41c00d00c5a6143d0f10f030424920303998a1181114803070a88020008038032001c0c1401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 892677149 1250 892675899 892675919
    0x1406100608180613030f0207120615081603020f0301110a180e04030f0e15220e1609090207230f0703032307050606040b1f050406120b010801 62
    0x1030300c03815642600721401030b0520020b007445001e80f4000040b2905801c000181364002c0c2900108080740d200801200e49021640f034090021920000c05150b10762100c2261005540f080c800a486072100307aa002c8294000c00c0071901d102351104030f0060034019071181d054074044c03041e42600c200801070030b40303849101a0300305d0360a0003101e40802da90101c840c0200e15200d2007160544290f1203600c90008560b500103025004c14001140d1501c41d0300c903500c1c032549030b41440c2d040e601c40008508510000c4000c01c500400d43c40260740000c041008100104182c0c482d0350009030540c40515102c00a000e07807540030803000e910843d00003400120040c404080c81019001859034121890070130380305c07031140441c50281071034103580c41038001550901c030403241480031442c07112035003241c80841740c0b9150403999826110324000f014913101c4c9640e8800e00001d5110401c0414040104540c00e1018400d620340140880e0030134055100050804002d00000317856a1040c40301b03d400503100d03004540e18203640f40d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 892678399 1250 892677149 892677151
    0x60307030e0a06021206011b0201090303050a020f190b06010c0f0206030c0c0114010807080f10020d06080a0b0403020105010603020408031207050904060f0314010c05180613121406100608 82
    0x4214420702280902142044c805042c05c11441c0181000e41e04218000414004400060081d01c00c03012088000507a00200b1070800c4982c1414841e451f9a200e240990410041c2903000751280101400b04210742c4105098002e841e200d11000112510396070011128034258080040941401c414168050b1804902940e0710203804011035280070f00b1444414203492080d90403c00036000300d001400300e10424085000680ba50a0081c4410341315035a00c42d41d28608800351031207156001030001070f0b9001d26040080500200c904039109021140b03800020044101c1d42500154a4030001040355440384c02110100c0340d440000f5814800c900c840e86010070f2010301004244001000510a55260b5001e1030340142480c0100d01203580c550b00305164500032030300b1040c25691402810340b4941380c1050030366407286182c0b802a15100c0034a000300b5090b103e65941000c6401c20b8902c00503121822840d10b101162003070000d040401a003000065841006450406000c5080c100a02c41e0a00ca078001c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 892679649 1250 892678399 892678421
    0x1060915050f1c021c110f090f060c100608060705071b0302090910181a0907030204020403300203040b0f040909080a110f150c070605010602010e1002030606030703 72
    0x5407404140d01c080340f00391a50594a11485500450350381c000c80000d0000fa030070405042800e0101c4000b814030301c000f03441140701c0e41c1c1b003004010500c40300c141c50303407082903c000d00098801581e0310010008035039250070040d400c20745141007020101d4510b41c00300f000c50080000d80c43d4a81001210b640e14100c01e450640310030403c010300c000000240c1e0701c0c0300d000c9004849890241c541884072600035002c1d078215401e180355046681000c4000940360002e0440c0454a4070a40115615590101400d01c0126407010350720a0000c200403050045405200d8101ea100c8941c0c141e41161a803038849080c4100c2541c08096041072204103d0028080001d2500f00203808010b45081d031240540011100c1c010002c3d04c800101240300008940c00803100c81b141c02e110f00041019000c40402075650798608840e0384091000321012402c4141070900382d4800390f0380004203000e1507840702c400034000d11244000f2085482030340d4001c81414000d1088a0140d503015158903e15528403006501800c501e070702d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 892680899 1250 892679649 892679677
    0xc0d051011040609080304031e05100516080603061e06010e060414030d0503010b16020607150c0e0d0803130302030f030109090c05090610121d060604050106091505 72
    0x104000d0340244255032102114115698441c0d0400364000d081c2500d80d008040341d0340c4104002d0002ca1911600601900e0310925842c180c524189030039401d02003a519200c4046092a00380400d40c004d0a0740000c4d94081a078942602c1c0e0b8514040503a00d5100f95404100741526013a40351034003801c01c0999a0110b07040c10035400007a600404102241d101d82c7c0800c0052500030032848c0c052409000e5443e641d400e0b0302e0410700f10b5040c502551118070034200386d10148003550040b07408540b6040242c603203140e00f02c05031041c80c1c1e0101015a018045043c514800a100004c0c980114030b450310072103a205801110b014210391320440028a6011810b105a05610050111001d24401c030310086010b4071101c080031500c3d403443d19001d0792892140d00701c281320344041c100300501c944400c0c428005201080c98100718000d481c20216005100325190548196841d5401408070280042c0b4680a0507003a2010000c81e81d950900b1204029180180c0c40805030700f0200c1d0311b400344248068004505035040d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 892682149 1250 892680899 892680913
    0xe0108040623040c0e010503070e1504020f0c15150f0f030d050a0e04020403020d060c0c06021801020c040203150d061116200114130902040b0306120a050c0d05 70
    0x444415210a000c1100002c201410204010025512040300c010138880c0c544492950610001a4480100c1d00031b03003114141c030400040b48101074403805100f410740644110342e20080600500d09503401360901000d0f07031280c4580c5070f95081c1d1102c42c0310301c180c00141c00542c462410500f0410811039036010f099102a421070f002000d9034052004d2a10f40c1c00c582c5641e07a07110791014010380b01440300080d8600c51031040c0020409038882c90100d000855215070300041ca03081400d0300b13403418006024041c080707510114011480200842515150b1607090302259200c41145040106a1004480300e4034440c0120381d808115040c0013002d081114031500740450304002c4203200921581141c00001c8050302c1491a81042c00300e02c80410011041c5140d41a00c0d0080803000600760780040300200203107501c000f50f22079000c4008c18000d0060060113030190b541d1a039580306a03e06402c03c3d1401e07071040d09001d120030007110300000c11046165101d80600510785c4400c0400c040c44050410175503c902950b8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 892683399 1250 892682149 892682171
    0x3110a080906070602041e1d0112080d0219081902031017120c07030b0601180506090d05060c030f0c03040c03021e19060f110601050f0a03051501030b06040504030e01080406 76
    0x700100003000c3d030151029007e03130720f04408448040c032008207030507000c1821401440750344581070356168520741007081c85956201d1554058000d11401c2a1186201b051411a640340b42d4000101030140b0900c0d4002c04402c2504c00e01e01003240710035152842104580794080002c0c08030009041246c0d4984400e0340c64002458885c00c88582c0003c0d1040030070b403c10801801045003e00c1d8907504000701786440002e8040200c002580c50380903001e00c9209150100d4400700a9682051800030716038010169241c80c2000d400c0400d06400a840d01402d0747c036250300081e2641810400c0d030748110307000a510351741e2910716008e00c425201c8580301d0060900c480d590220203903d0340c440c8001c525510b00d4a001145140400041c603012000340c64100b0080320540d0f403c2e14050024415055030000c8404885203200d000001d5860f03401c80e44010318138081d81c007200214800389810241228000d8401034060b540380010002124070490300100460281d140040c801d511a1000661080c441c40000403003810503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 892684649 1250 892683399 892683419
    0x50703062d120f150219230408150a020f03040b040f02120a02150405030c010e03030c1606090b1204140133080c0d08030a1b030903110a08090607060204 67
    0x91842528400522400d070410402c070703900341011513118a0011030805040140d07822281d8900e10810b401c01034a40050320340010f01c1483e092a60252110ba95075580e92065101c3e00c80d4414030000081039083d100090054a40c1e008813040120340240702891980c584c1d54801b10b00401520036552030007000308800042e2910715241400c50001801060030113000c0c410452031003122507000e020802c0078481085161400610404d43d10001d027000c904040004010a00d140110941e4100b60b00c121002100801d110482e07040595449903181c0c0c10058456101c41210301c10149428920070042d0000350105648103044024507001d88004140103818452042d4803440c504000c1403580d50070300041820805c00c000c200c008001c9200036128050090b000030342040b00d440030203840c409000002030106021540010900100810510700118003480020002c001040301200868024003242480c002c0000340800c003290300014803403415050505100d00ca8001e064100c62054080c000071a81c0390007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 892685899 1250 892684649 892684679
    0xf0a0209180a05120306090a0e0715030e030a03090c0e07050a0509061306051c05062815020c01031a0906040b060d181b0806070f0e06120a050703062d 66
    0x1500c1d20381921780c24400f0403c604003c0c00780c0508502850040c900ca0010004203081c011a003d41ca1214a44803102c002036029200d00e48055040303001c000780603401942c1541c040c02d505409121802a01070720382d40d107000c404005a800c040804d0b002c1c000200240e2207040240703040c0320094141402c00c42c80764505111902c1980110000c00d0012441860004580e428030030750148a51b018801c0c5e0030b14001013116040142050302d10806080300300c640780c560807107481c2d0050110010102100025010080d10344480e1005940020309181c1c0d6a041910714000d038801000700180302c1400f68403143c0c1084014542208050382119050103c3d810603820f40c4075800403400492034102040c00307286000711000c1c00d5044d21004a841351031051111000003e501507022000c1c0c04e0203044607101042c00e903140c7c01c0c809162940114000b80000e550070341c00b00c28900620855805004544804406405071135071030103062200140903046110707440c0812040071647da851041c441030aa110100400c00c0301d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 892687149 1250 892685899 892685923
    0xe190806070915050711041a060a0f14041d0727031703010f09050603190f123b1207080c0901061407051018050f0a0209180a05 56
    0x5980502082003582810040035540944e2600c14034101a41c0c1d14043c84a5400d500315004aa9601000b1074841c00039180402480d0b00501c01510f400c1d0400b402810411100203120004100c00141e03054044135005a03000c0d9915a210a01000d070301c19015072541c08000e25403010041101c19440c0d04260b4940b444c004400384038030942c107007402e604183c0c49401c002d5051442c0302e1420001003002440c040d440300241e40f0700e00c402140503210503000a203000781d07010702024013003102c0005004100c8203100548465201c2c800141c00c05031523141c292141c007025804001d5400740c545030907224416002c1d00b8810000c0c00e0f0700d0001242d0882000c19002c9050440446880e0f1040c1030520414030100440ba6045e90304407100f861940c140740300140921804a51010004004110081048400c2c809030304007109000d0100040300748102140f41500c15940c00b51071358083d0784803440c880ea802080b00e0a0b21500501407007059101d0780c0084417410642503089146001c0c0c0100c2c1c0d40003940a00400440710 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 892688399 1250 892687149 892687157
    0x108040b012112020a11060f0a0503090a020a1805060301060303050415050706180b010e070516050c0907050d0b041802010c030207150c1203200c0102120109050106090e04030e19080607 81
    0x1441c51501001c40e418103014941304010911202403d01c08d2401121001c400c0c278501a40c0300d4071480c850914151380c0c0c1074000d5010560f403102042005802c80200d1404980d2282800191a43c00a050890302c803404003600003001000148226200c404280350009600d1034024601000f54a035901114042800460b501000c1015041409040307102e86024161030703200040c46091804010f80709120b40e5048008810203103d2910902805200030801000c3c0030f0540c80903490000001041584401c02030320342c0398a800c09010b41c604051046420100440a50000c20481c940041d2410004104100c00b14030903818081245039001609030072020719611001040b241c945803c804400d04001058101441d00350a241041640c4a00d052500d5011230310381e5031801603401440c0a0f01c00d105003256503440078800049d0464081e40943e0407680c8a07502d090000d0740700d20300c2909485041d1070160006100249074401858145400e20030415444910b6120f00d94a00000d4102282211410003003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 892689649 1250 892688399 892688413
    0x10090504140609030a0f081b0a080103020a0f0b04030f1e06050406050a0e101104050409081b060622060302090406020901080115140d0603020d120e0108040b01211202 73
    0x2640c0200070050b0403c0c6040051814402a08001024580d0300303415103080004500100720710816402c1d076082141c840e2403480f07907181c24148003e40042070a200403802540400da0020f040c0e403403000e00d02d05480f6085025460540f45450380501929011400d88040700f803030040403810140004031080203445000046010b240c6410468100e0710700034040307200b80c0d0401324907510b014004954101909000e080010300c0342d940c002c0c0001d0b980a1600711a4001d850100c101051210b1400982562241d095030300c5420301403848540c0e1100d800ba40c40a410030700c0c000038502521b40c1c10030703c040148591000020819030701e030000303840740d0010b85082e600320b0360006101102c0c2d41d01c8903081c0d02610964403000d00c44d03040c9a00040110b20940c66911041501140c50080c000c6e030361300058010740d0010816401c14603c0d003001c0d03903206000108180800c03c500c0350803103194003d00d02d0170b114a805c5603154034580c1c6808070a40400e2203400e02244030403001c00314040003461000c9201e100d480c1981c010003071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 892690899 1250 892689649 892689683
    0x7020330010e010303080a110d18021012110901090312050c070603020c0c010e030c0d0609120302132403021c110a030b0301020c0613030903050703060218100207060810090504 77
    0x200000980b0b100381003414090588e090807020421036100380052580002c094540060b0800003080580c070095010800700c002c03640d01d990094041c90103401282e0108480c08440e8104d0501d031052591160200c1c0b200001000031600c1401c01d441c0c1a41d41d0308245e482c14101250301030412205820110209034041424294606e0800070070308111002e00b007511000d412540029a40d2000e04141440f8910366409841001060f03048040c4941e03219101c0e510080e18640e015010750083c1c1c0600344000341480001624208091404126000e061184034520040003c00c40103548416040b1080320420008070308205c450b84104d508a01c0c005070890348403028580b00506071b40854550030310070313801400141d15000c001b2034020341016001c0b000510484561509440212191340040c0c1140280c1c0400018032640341c0003459901c86d00c1040d82c000074070b001c003003010201d081c0c5240401640500000e1040700e0003031100981090344890f0a180003907582c0402c200751041140c040b101141105a200c0d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 892692149 1250 892690899 892690907
    0xb1e04080109031418040f021201140111070b09010503310201080903040b221a0406022803110106090e071a03040b150117130c0602010507020330010e010303 69
    0x65a1380308480b42c24a0000c602d03849035005500c00400510490b41d524000d9030941d0703d50b0413100e21045003550034020b0341e902ca0000c004a50000d040c07d01150030f0480c10300d1600c401180c4030f82555210300c0c0b02d82c20301d0080340c011100c907000204080e00d10f0200a4062103c4184222040481d0070b0018101c6020307041ca10004012003005010055150f000384021b124000d01c1c00c0640c2e0703a0908401841e05048503843e90103840000d9507100c096040c0309107541c00d01408071440180260b41860b021104402c4514111240092207044e411b0071401c011150240041d1090520740d0080000b04000f00c1c0550700c5402c02002c4880440c5420102c0d40048820440064040200c001001c8006100b030f0a500c0d0980b64000440801840c44030f1451025220780d20607802003015600c0e0325200600c540c9649880b140d600c0c160415000705807028a241e0000061542c81401031a104815030b6029506116940700d4440ca000e803a0541103a04500c0c100f0a40044444811034a000348001d500c01d4070310707500d1410302030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 892693399 1250 892692149 892692167
    0x601093503030123040f061205010e0309090f0703090503040b070506090607090501080415060b0903061807330203030f1014010e120601060e0f010c0c0b1e0408010903 73
    0x4045400901c01085841000034014000d5000302d144041d1307841c1560001001000c8141c603013081c4500c0d00d600450031a4a00c0d4000500c01c0c81040204050048220f085659005d0129802e0f401408000010701d950a00a81a41c001ea181d04010500729a140d48441c115045a0804420603402041d52000d000b404c02c54141c001c0c0000300901054102000028403181250285030f040c49480e001007001c008044020405140c14400200b2010791990118030403640403a2040b4800d22988001c1110000081780d04054004558010b281152401e140a004170404141d40b00b9200e10500e0300c101d0b4255100e190789000441c0f80c1c007556591800039030b04a90400041d0030841443d03280e04080c4032185110a0845e0504001d003000c1d0301030101080011104581885400164001c1c00000a40e5035009608075907141d9044941c11064070f04400111042104940c4c0545001175142042142c00707441d50040c01c6403403200104070b5000340c01c0c902511503039106a000301441ea660b00300e4002490392000e01e507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 892694649 1250 892693399 892693499
    0x1418150108161e090c021603050c0103110a080f100e0a140f01030f03080604020d0c0e0102010605010c11040b01020a020303071103070b070b0f190906060e0903041a03060109 76
    0x24940350358401c220f503402c0350843c0c0990450181e403000c41641603402040390034402e044d42502030305c0e61900c0c0e1401c6c50300e61f10712590351800b1a082c42c0041c20090301c00c0f01641c0480710300b82c1e02c0e01400c0e52074014441800c072001c1c3c01b0041c600248500443c81b0007045441e03500c10b9086081c00300f000e104022180a102c0780051103850b000074442c00520000340002401d8880c942c251074106a6074a0302f00004009100300c40da0000001e00d0155401030a6820104640b03882030709070020821656a03c006494500903101c005140c0980421014402e241551050075941410302c111500080154042455584010010b9803504407950708100c261808002c1074002c0d00c0d0716080642080d0040d03035440340d215806048440091110400156940420a0504014454400180400c40d0300c0d040100081c0210300a006954020780300040c1d505400000300c8080b1070340700301880204051820807101c240c10142c0903504006040c2c4001440c680c555240701c0c150346104090a80600d2071009504e044d010900e05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 892695899 1250 892694649 892694669
    0x2180f01020c0319060b060c010507031401050f0402030c0f130f1a070f03020a0b0115120c02030702060d0b030304062a02010207050f0a09021219141815010816 70
    0x90300207a07107010030b07000d02110004c0c1180072100000c0c0b9011000e40302074408a03070041800300d4080400e0605400072070041c030316914204100103110342ea09002910034010241c001440d2902010107041c0307607004561007070a0205241c01c2400200040b44942e101215081411190310401d01c00c91003281104001880b0130510310040d42c6060101c244d40e8018900060a411900c58141040c18024007a039850746900a039900710310368440a20701c00c0388800c401c403440001c56914204144003c144243e1600c0c1c007441c5c00075400c100e03295080100c01c1d0700c0310b0b00c0b04401c113803183d8103081591420406840640015100c0342a02104040440c404002c1e0064541580b42a010700030050f0360007158000658805840d8944d90700154004203d000074543d0120080c10b20004802030115014030206000d8103183e440c070b650108902e1301040030f54500001c3c0c1d1082040c082c1c0815042c00025114802c841c00600c1500d124003100c81c42e1541440c1c0992040307181e03822404090503102d0301014120054124201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 892697149 1250 892695899 892695913
    0xe060a0c0c0f02011b260309061b070c030c0e06011d040c0302070c0e04020307051008010506030a0e030d050f01050a03030e0d020a05030601030309081c020a0f1502180f0102 76
    0x4000c180e10302400c4042d0003007800b1180b1100b035900c43e4191402d22981c11001d1107959059280554400c5030002000183c4036480d000510850b440000f26130190303000c0e500904d03168640748001e02c3e89500071801c1c48020001007001000255009001d80d0044d4051144074010600c0c103402d007035040200422003410004038804441c0c1e4041c24000441004c0010b0f82c001544240400044c1c00920900c4400f405024101c01d0015000101c0c0007c603100c2d41c03099056500300384c0c6d6002848500c0034801030010202e2001c0d401885182090000346074000406040490307440c4808001c541035900245407451401d840c1c0082001c02c4c03003a45245401002d09940d60891a495500c004003d5404214030904c02c2c00c03040003803001d40d40c40d1740c0102c0140c040281035034400d50b035030700d030240c03410050b0300c914000750258840c071904428003803008030703203902964000d8560058160794601711006858401c4880001345001511004a50320107042201c27148200c03c410115010300b003203070340c0c4003090000d411944010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 892698399 1250 892697149 892697171
    0x3120a1e1e110a0c022209050c0f0310230f0708160c0f0c1e1409220203100f0b030115031a042402090f0a0e1311060a02010e060a 57
    0xa02140d80346280d44c03425401c450810b00c00250403d4032082c107481081302a005281c0c51580c943e02c501c0b0843d108008079600c0a0741c070b100b4071030b68170030052600c2e40c5500040300c00741e40c880d805e0300060340d0100310207004403108064040f0b075200444140ca110104485800400440d00d40261006401042001c0b0300740740e44544d410014000020f210000300709007406000041007041102108010313091035600c1c45100d0031240385074046586140326060714404569594809801c0c200c2000d4000e40503441c220800180c0c005240700e00070a810381c100d070144a0403804203279080440c414440503501d001408506402c00d2410103095804000010070804868001000003500c114010201510303c00e0740040c03190381d9030900c8426600c592002c200c0d140b503070740303166442d0608a6009000d81001154481502e406100911915221358090454112088008100110f45150000705094030420701300980707501901c041409074000e0020780025039140e14130f002000304240310495010300008010080030f03202d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 892699649 1250 892698399 892698431
    0x61107032307090219020610081207020118060905031e030a0807090306020703020c04060902310f030507031415010303050a0309020415080c1203120a1e1e 68
    0x200d10084203000640d491003403044028082c00000b002800000c54440c403070030030710012051104554100600924002a01c0706009048643c20340d0035034001808a8420703c10109242c3e070200070240c0c18084a140d00b0450990b808040b4800b9095550310042424948002c0c9483c044007094054206017003003c3e0751030010030000035924960314600e0032034865140c1501c281c1f10b14010b600301400007400012a0030034560006154081500c0640301004103540e00c882190490150340024580b4451000c200c18210f140c04441c0e21500d40454030b10078003140c0e00c0c100c061481c58070303034011070b019049400708000340300b80d681c007134540d40084802404030003d05556000c0080d005000040a002c00031500102041c440d80c0280c2029a001e0000c001298418400d00b0001102d48a207a88a1068400010160901c101130f907540300000802982085543c691b110348150005006d40081a40c80c215048a04000f01900c01003601038400003414003413291048880700d01d2080324440090905a20780c00740690 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 892700899 1250 892699649 892699673
    0x4050a09050105160804021c050f070e070507030206070c020604170604110d0b010303050313080d0504050c03010c1d030102160f05060123010309240b04062310020304051003050106110703 82
    0x811260700070700316801464230031201c803510300142107841004035481850500050101c01d81e541c1d010b10b00b03c5941e60050071075442c801c11f2401801a00807401140466001300f1104041500c02040707139080544820055181d280700066034141a0300000c18001480303040e0034000480003045e55031010707514041e25411030006045c84000c1c108a80000000d0001080080c2041190b600334802a42c4101481604000c1c000030346060340c0c00d001d03031294410980740502c110380405155440e070781e40e042d14130a8074000207848034103615010354003005a00d044c44049801c0c0b030211441000c3c00082041d0500380b0901d05401600700229030b21501104024a120003c0d070f040d400b59003440d000c6604103107403424000602c1040700d84450340c404a880d503400c15040b900200c1c54140c0c181c50810842ea5a04881c0032007650740c0c41c10500210503042c441c145414a00d810211603c0b00740116890709540d1004501d4858108221500107966200103000c40d0380d200c41e00507078105a8200800440c1e046480740c07064075030703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 892702149 1250 892700899 892700903
    0x915020403020a05151204110325090c030204031403040611030421050c100f0f140318160902030a050f150f0a080f0708060c0309120304060b04050a09050105160804 72
    0x80080c41030031201c007603204540700400709886c0e00015060501e8000700f000b10000c1050321238004e42c9060301102d14042c003004a2410b9003500d0b0003040f0301d040d0381c44000b030180c0384c2c12908041c0c0070440840410388026000e0107200d0f0100046956510f4400000c00c007002d501d40700c16103500208004c011111032070951207144510040c1541540c00685440c40c54403407000304968100c0c030f010080780211900113181410700c004030713260500d00e550484022212801c0005110b602c2100500103d981c83c401090a80c0d00514124200c1c4d005812210408003400c1e0320b50300100311250004100076002925011b003c5d00a882503984d40c840e81000a01443d4030203802007414081c443c101d000f20807a660304580e1200900c982400c1d01d08140c6500d0031540c86101d03034064003101c4d20078030380481c401141c103004880c03040b21070901414000c00754007480d022580c8082d009980a0f900c442503001550348510070140250421a40041c01a4442c0b60a500f5180010a00b0004268920360b5150b55a00500b205078041d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 892703399 1250 892702149 892702159
    0x30c030904150e191d0d020616020a0f02030a0804090b0a050a0b1c060b0a080612060702030d021c050108031206011d04050a0f0203090a03030e0303010f091d01020a030915020403020a05 81
    0xc954003141001007061608450607a400f03850340505c07405002c5940d0000022a030709440b002c0c0d44091200c00071440d40e03036030500140d100d400410f003c1400e810048008510080c10b91b00300c006540c03240700c5a07400540040c00a07a07a1a09582c0051070500e0400c0c000384010355000c1c0e84549042c00020b803c1c01244081812288040d0300c21440c0304155001c10050280484040c1e110030071003100506c403220407103030940a950442048940c007603000030b440f846861254015890200103141d140080e402c41c03040c101e122440e00c05070401d540c080d401101d028002042c020f5460303500310800d056201303001800c00c50512080001010400038540946420801c060303801062949406c4034410003030a0390000300a01602c0032040c800c010720003083c0c800c481c85c001c0c3d03002e1050384042175046403a48403e215603e0350040303030001089108083e800601185204000c403101c0603142031921400c1ea0b000e111200000b942d101c500e01c1c1001602c1041c203a03202100b403011800d080c210340c003007403401c4030f90b014040c455 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 892704649 1250 892703399 892703431
    0x90316080f0a03090902090f041112060307050d120309050106060c020321041211041a031002030106050304020904020f0910180204120803101206020a17100e06060408030c030904150e 80
    0x507490700700c801d04223054054010803040582500403182500071a480e0308424203031201081c454030340010702030140c0c1d0000785155000580ca81ea08a0468407080011091603203814003640400c1f0b0a1103508010803a0b912101d610f545944109420610040400400881c00c0b000c404945103a60060b1002e8030802c08030780b100c42e00c2c40d082c2071840028200c5816070003410300c203604211003101c2c0841034070214140c049800c8100809404000c2e40002d01074400016014000200545498003003590440d001814071407a0a00134808500e5894003112461400c00c00d0705820005010f80c590010754217012540c00f141094184080c41825000d01d51003d401d5000c04800f040b10082007011000081169801e205080c000c91304d02040a908104001004210f4184540c9211140c034803074680704548148908107903e0900143c4c102e022000b40045400803020321000c075440b001000246500c084010086440c1d1101c00c00300000c0d118550b0702d110501c861300c002001640f502c0600e96030032089803002c0d8604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 892705899 1250 892704649 892704667
    0x3050f0906041b0f0f15090e070804020a0305060412080108070f120503040e0709030b0109140a0c032306150f0304032d030b1009120204090503090316080f0a03090902 73
    0x3d04801d94100340021a40000b00198038100340c04060304031a12400e084401c50100312059400a43c41e2042246082c03250b00042d00051140281d203920900c01082440000d849440e01458032070225012140c9e50700c01d1580592040e0403804160045c60100000c10401d420a5460311288041b48600c1c84104402860881005002e2055401404285280003000d10342030100034503401940c0310503075150a81d0740000c141110503008036000c4459404615009480e552200c5005202d000c1c2220205a50b0760044460303103640701440b81c034615241c4041c0b503080c20030380300708580c40f090030740c200500700001c2250304c41002c003003801e136036100b901b5081c0708914403200d81440340000c0e4880080103514402e98500e65000d9010b500000444105458240c2d04000003502600e0840f254090108a8400000c905005241c65000035924620801c00da82c10010600080391510b0700c41d210000403030030403580500c0000d104000c030b281c148d20301e500144040a120b0310082e0010304680100066a900000d0b2102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 892707149 1250 892705899 892705943
    0xb0f031c0e0303041e030b0a200a02010f0203010929180405070f12060506010903020f0d030516060c1e17090f061f090b18100308070b040303050f090604 67
    0x1002c0c5d0035181040c46401c5071401c80c00c2ca107030f400221080300303921012901441c1c0300e229100b120803448004002c110b420741c0c01312449812508140d0110340d250313100d0328207203107845c00a14004e000b441400b10b1054100c91004035001d00d40f0700001c001e103103034695030300c40c0da50340c00307070f580060030812130303c00110b45542c140301f820621180c10001210f82031400c0000c42401130b5131380701903003806072008000d1038542c4001103403480314a20000c0e6110301c0200401c1a04d1811a040b24002803181c20a2450b015021460070300c60340800c3d9041d580d05079500f24440e2000d4200c40c0081d1040b48003a68040c0c559055480500a616031000d0b1000400540c00002c188501c06c0021030b0503001e902c0101d480d01c2c5810f03a6407030282c98600e460104d60048840700080e600f5103900a0321032255008013a5003202d2920043c40c0415100200301000707080307a140c0c00001013101c50005107034803809001d01b003040346003608000d016214045e01005c800d00c451801c00100560218046400c07591140c41e030ba1410075410003180c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 892708399 1250 892707149 892707157
    0xb0306030706050f0d0b1302030106080609070e15341403030f130201140705010b15040303051b031303060e0c01110c010c081b0c27070e03120403060b0f031c0e0303 72
    0x1f90f90302d44000f00125000b03801c009a58414102210312094507543e4000c200c3d0310f45114903105400152008401005e0204440a400c1c01108911508000004401c00e900300740000400b00c82101c007140c00500a0181040700405207403030f401d00951031410110500600c01500030b01800710781c02c17440940011684106681c20002a5045180d81c6400781428914020001d0a074014440c0109070b0090050340343c40c109660840b909502c0303c0d814404000c000d61507010b500000c02d05d550208201509203500100c5e900c10243d402654005180c603041c0d07904c1880c020700c140d12141440b1000c854810010400243c0416040e000cac0380206c0511428030f0306c03205e0b9002e004034a0005824202c0d1603101e6003c0014218102642294030310307500c0600005020800742c0e00d02d440302d001c0175000001810b5600810380100c0301d10015046038000b2620325084c58054120343c00440e507941d1102182121403515481c11030032150b048002c0c01101e0001040012102ca55510701d500b400000c4020741d280b65030600560b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 892709649 1250 892708399 892708429
    0x12150306050c0d1406010c1b1523090a060e012a020406120f031419050a02010c111c0e030a0b07020d11070509090a06060b0306030706050f0d0b 63
    0x80c0301c9802c04000d8008140c1106208040301c5160000058440134202c2c1503501801068580502c000e9503038541c61203400310783e582183e51310f03200c41d4000307070542e0f9a884601c01400c1580d1070008070641d000041300c0c2480c15440001c3c0d07070f030300501000045990301c0020300201c460030b003440301c002e41c5d414005070f0700c65410042d803455103940c400580c4450890030603400c0450788200c401b00000c64950740000c840d07556564024004e000110708150019000d4510b204201700044c031043e04140300382c81c0303480407603414000001c001107000c641c401e142c98090042451744a43c43c1481720b0940543e502325640c4041d4408078800c0c0440f54001001600d000c0e044104440d0703c090160b4499040030b080c00040d59000740d1b840360052245460b11050140300c1c404103245806280b0182040d1407a0408010310300f40c020780f02c07180c18000c04100f20300040803403040b00010a80703044801d860b441c000c420141482036550000d41801400c02403891103000d940c040720200005484002003007081c0c00045640d0024403081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 892710899 1250 892709649 892709651
    0x607020a0210211a0f090f04260a230307020d030f020d0e0304050a0e0112110f091303090614040b0d1104060e0a090606021005090316150606030b0112150306 69
    0x130b4014800350794010000b400b40603500701102400040601152004c2102c9040c00a0500404103000818403a60310701c13050b0359080c90320070069075100d003a01c943d444903241b200801d18840f0440303815281c4400c0c000d60030091224050461424182c042c0d19114600700040c10580e1724202e901e01060503a05807180c0901c5400c0400500e0300600795185c0d40e50ac035014861060314071180000d1464100c41c0024103940900b201e54082c128566244034401c00f13200c0f285071b44070304012070000d450340712580c46510808564454107003000c1c0c03d0501a110342807940016041020480a606051180b07030100c2c0c0031034406003c441e41d210300a610f000c3c024030120a6180182c580024001141c0b98031564100046100b00c402001041e0795003085021a0503500c501000768126005404040066512803a0320958000030340c2e01e42031000c840803031074516986085601004210b001c0b12840b006201d4a03026280a0408000745030504001800024102103403551043d2210b44409501d9540d41402008560002c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 892712149 1250 892710899 892710911
    0x6070c0c080a080408010b0402091f020c1302090f0108070c14120c07060936060b0a030e0c0405090606120304030c090501170a030e131503140607020a021021 69
    0x20300015644d210b8401c0f12030a60030180203004a280a01c01c542c08541d0041c10503241e000101905280344281030381070404c0d8021015054250303220101884201d85001400594440111080085400d10f0480da2810042e1500c100014950440300d41100182c00006c400c0c1042c140d99002854001c00403a040c23142140400c4440c00b0480000d051010340c8c4440d201d0203501e90312140310241c19404c10f50086190010712021223801454102011030a11480301c0100341079131078201080d0aa800708148500196448141090488051140c0c1c030b00031a04075011302403402c103a10b0082d501c81c1c0243c045c1c1e01c00c0320003d000c01604c01c000c100b00d07801160701c01451000c2a50302d1038041c0007403c1c240b0a10154904c4071000d1041c069011500e84200b0381e02d2707112a1048a114020b00c110701c1d82070100b91600d90394804c14041a2089134003081c00451040420b00c4132a0511049281090400740060055502110b0241c1c016580c00301541940d62240c80c200403440820307810f1a1019140c5d0450b810300a00d410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 892713399 1250 892712149 892712153
    0xa1e0807050a1a1b03070e0f0d210e0a0603110c070f030c0e2505041703040603060b0f0301090203040c0e040311011b0801140f06120103020a140306070c0c080a 70
    0x502e190841c6004440d0480c41c1d0f60b24591080d09840c003101c585440d0400c20400510380c2030007041c8140c0c1081f00901010324048285000c904a0a0740c580c05507410041502c1d10340c0d012a2051406a0713207400d03460040006456240420030748050390042d8000d06407100d403000d08000401003a150100000b0007240c03083c1e640d6404e240440c414501096032140720384003020810ba074041600d10b0089645188584c0012903020f1350040f0350100307160500801008100010b9000c4540f0311b401d40c0c1841d000081c42c1d0740c2d03140c00f402030121202c82c2d02011280c0390a200c074100185e0000162411a000b00c82c026aa0740d543c2c0c40d100c1480c0049802c0302e146001030105110605620210308040d41020b14000c2285642200450102c1e010604400c0d0010301c2e52801440481300158020300290300c0504001245d20f404000200309401c42c40369140c01007005001001036142c2030307807040000c00006030f07a003030b0702c4010401013500c90710010104001d214003808214100114061008000c0c0041000c0d5000b000d0a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 892714649 1250 892713399 892713413
    0x90a0b0112030306050d020d020108070210021308103e0c030c0607030218060d02040806010e0a0c05030105060f070f05030a0e0102010b09280e0d120c020a1e0807050a 73
    0x41c1c00c1a80000d2a10030b010945040000304104030b90340090146140038560b500449007c60300500322021401a42645241c440309030000c0c1206142110405842c281000c0b4030a00d4841100c0d0760500c49814074041507209018010b440030007000d280b51030103181c40e000014064005a03840040017101c80024a41c4158030080301404026140c1025540d454a415034101d00760300581d60342c060041c0c0e21481c3c141141c9050401041100751480025040a82d210300290815800340d00c20801c680310007041041005241c40354280801250503d24119410304009c52102d010b0b036100310a2031040081c5400138040c0e201d140c2000c80764400104c84d514540000002c00414826034a41e0256003041b003004964500228400c4c81b03450398035896030410514400c6e0a00e10084c20f460020155554545512402002d110090103140c044c2c80e1204003600341c86240c0c1c11600d2240d0700400715000254000002a90031071102070035010240340c02905c00c074a041c010840c0c410400000d1907449851110b404011030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 892715899 1250 892714649 892714679
    0x20f0d050609070311030601050d090203031813050c040e0403051315091712220b070b1e06010f050f1206100c0512160203101d0c0303070803090a0b01 66
    0x5950b070103050345802c0350035410751742c1c1e02c02c3c5410180c000303000041c02c1e544948040c00e481444080c01088504064000c2810356105490040c041500c071080d032481824a404030030b40c2c24824144c10851481d1010044580b0301682c0280b042d809400404902811300c1902504c4107061002580c44a080c2e41e24070500f503540c401035007a80494078403000002c007070084d11010b80441b030100c0058807944500511018560740b01e1a460030181c00d041d05205c01504899400301c000c1c0401401d10303a0307a903115091640c01030034010f0a0501e0500c110110358103841e034000b0b003d07812840a09000c1c002040081d4180e50034050f680f0800d0040d0008181102880d1291442901980080c8e0301c0868101000804881c0800c0e100c0020349943e000801e25260041d40e0002000003400000107480401203560020b82441107002040184030749038248800c11000040380030b03d0800e41000180202c0c40048003103922802607010250400c1c00c0400058013596083c0b01025015505c8100140d0701e6031179158481200c0c170 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 892717149 1250 892715899 892715911
    0x90321060f0b130513110406022107030e120f120721020304230a060f1d100c050f062706100308070c05040e030403020301150e19020f0d05 61
    0x10301c500014858038010101d03004144030840288241c0c0c100340c240002459030707280f02a80c0755034845200c01e100070a1000303000540035a078007529400341d5040c100006d010200144180408003013007010006501f100c08501c00c980c050f91200480d0100785001810032034821852070ba07a0241036000030403071310480e00070a0b400d4400d9000300680c030b4040c42c403c1030502d501c0c2c0422000d40e00412040c0554920012045010f41c0b200720117007004d4841501142400786d03d0f0340503801050785140700c0d40c1210741001c20828282400540b4601107602c820001d400c1300c1d258022801031080910002050100c00c0c05101d15102c980d10441c0c01909101c103200d01002c01c0c1040c0c441c002004a03100300c1401c500426014041c1e080d80007609000c0d41181c458800075130160f50304403003104a007200001c6a44170b50103040c01c400d0740301340030710340320351442c0149400d54440525428079400d00c800180701c0d041c401000d041c2c03c14074a11110b80c1c03e2500004245c000c3c890307200340104082021404004240741d070382003584510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 892718399 1250 892717149 892717169
    0xc080f150d052d01050f180c0d0b0423031801030e060907050109080c0105030406020a02030d2d0902100302070c0e0a02041518150903020409080c120307050304020409032106 76
    0xd4103424900305c1c3c0742a2000e0f003041d4503290100c0c400428000c0c01c411802c0411083c0d58140c80054002080a0801b8004507056441c3c0020030003880000c1105441c06141c0e1400c80c841d814485219640300d01c222444650503d086040404c0e1903403090340b264510200600441e074060511040080e5a4091032041a001466504c0c010a000030086800000b400d0b040c1c50340c0d41181c03a1a03441c9030103908a0103040c01188003e1104e030b47c882d07805004050700d80c262282405c14014114031191022504c3e111000e03130286c180f010110068445000200b881448c900c0c0045e2182c4903450950704c100380c15444118110301c0713007061040c803a585030b004104031128801e4014847d08403c1c41543d0030718840c011400b1500b015401003013480010104032488540900d001614207880e40d001030102c03814a10292404d01002c01c22100e003110401061083d601c04045031411480d005000424512004000a02481c1c8601400d4101801040303420581c0c006102510140152000450003d2069100d101114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 892719649 1250 892718399 892718473
    0x3050a1a0601051303030804020d050d03050103290a090203030415051c0e190305091003020c0f07032001050f12070212090604030b061302040e01030302010c080f150d05 74
    0x140d0b00840c02c48002078504600d04e0b222901d991001c0c4c40c05140200180e800400c100c002000107401404019456091510300187d43d504500b4101407182c965403102c01c200c4066160010301811846845138040503070f2101003042d98291000c0b9003540150341c040010003600103184104281c10034050035014409210307032100301c2c040c2c201c080141c0302e5105078814181c10881540711500d56101084207810b0003030614514045800c00860882510840c0c5903000030381c08980c91114050500c1030b40c0f10000440010f1030214150b13251a6540c10300781403402502200840c4075a040c0e405102941d5140d91200012501e0b1039050301e286500c400d046030600c1c010301502c0c800007400342c3e03d50242c42d1401406414103080500310360b100b03113200320007410503584255003200189810440780028009071104040c3d40c10710754903618019003541e680781e040b04103001c2007400300284c0010680403994000c0c0e002d41401245403000001c43c4041c13150390300150082c040d44c2283c00c0f10407620341c0302100ca40d031801740d920340c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 892720899 1250 892719649 892719661
    0xd1e02070e191404031e0e04091407152705011107050d0f1101080708151503040507031202030a0f0e21010e0c030c0f0d230c01080702010e0d05031003050a1a 69
    0x6c9150403401903000b0522005000407103040603480300000a00c00c164020b483c1d149c2402d01440c1c032003103601170090002c403880300420241e841820040b0503d925090015010b0300c0d4000864516a240a801c0c100308002c1c104001d00c0ce000c100100041401800c803040b040300303070304000060104a000030388120307042c1050440254458040340e8822403843d668034845444208242051190507040c05500003031880107400c0d120585401103000314858002003040c14990b00c0c140a0030f42d0010355182c29034000344407840c90030750401c0b254114072940d8540316200c83c00c110b0000b40c198048285400d91460b07000340c131000100c0e055200182d014aa03000316800e582e00d034020141d450130416001c54101c0c41d120001c120794100041c40e11234041c8600c1807010034403804d00800e00340400034030b6050070079401501d18841550308000030940043d6180b00a02101400c460815904d4840c555a80704010001000401c8034420b602d11802955000d8180d4528402c5410020707034080007003003440f40c804101c401280c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 892722149 1250 892720899 892720937
    0x32526010603060b13030611040305060108060a140408090d08220609120201170903070b04060603020a061724060403050105060a0b0909010324020403050d1e02070e19140403 76
    0x182e407811600a4940c1c21b030550352064003401c10340e8001581ea4000b0f01c40800014002c0c06101e003e030406e0001460381d860080c44801c01c0d192801ca07403071089030346481480007040ea08400c0720020308041d03405443c40c0d070851034011107500c10042c0c1c00007600302454a2500609440b10400704503100c50f03031080c800945410315200401135626000b4085441606803215440d02c4a030000e90000841060301d082550f01d844502e80440c0440c2d045a500795189014401c40c98400c21500243c0354510b0310805d4030340c007442481e0500102501c0c2d00503500004c05c07821958080c00a40c1c050482d030103004c46460b15a02e18089010b0319043c2c0b04e0034403c242c854408908100054140d5907095801410310115920755290f10710350b421422280070284401030406201c50b4881e000800003507101300014603039010410340040c07621410f00a83c50401c982c406000c2d0400d0341c0050070006440b4a10241440764490903080b068540c5000b403150300240c2001c050840c1d400d2401030042c8540d0007525400d00c200100074800c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 892723399 1250 892722149 892722157
    0x307051e090a29030111030c070c0e0c0307080a091202010f0501050402030c12131b0302090906060604171005010f151b0b1f0b090411032526010603060b 67
    0xd90065591154030071008403d2a1402c007010190000801c02c0342091035500c02d9108031000050501c0c001482c1040110044004c8010641070340319607498141055a2030161002420f004104450703500032402001081e03120309425070303105040c1070aa945160000c0c0c060490300401d02503a5250070300002e02410903008032031180092030580e43c50202194848440550094200e5040c03241c00000742c0300090040740040d501405025041254070320b14030420010381401030487c03001d0b82000b020300030961115030540d000d070f85402881b401301800d0180c4080c070744499641010310703240c100000015112005c501640c1550386811004141c840c0051007512410010344038131148a04490044002c940801d902a410045035200e0b004816a400458040c69001d40c00202182c10002009082c503c0c05206044060403406480ca007149414405800c000030307080204504800c1840700060311520610654040d044981500e00c0300e10045400030103840401d000d9000824540603001c0b80c0000608251 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 892724649 1250 892723399 892723421
    0x309041b02010f091112070905071e2c1201021218030c0d36060e01090b03040b0a090f1a010e09030a200d030f0501050a03050a0609020307051e090a 65
    0x2108110b09504c00c1c04400100035506c08034034041c03201d0101303802d40140640c03401040603590f01c488428074110380c040c224248119110a0011030381030004010811b003403046034494000d41c1d4043c0303c16030a003c19521050540301c0c845952000528099851035542d0b00d9004001da0600409010100e0503141d5883c0705820030081560f10200340f528081d44140f0103034041603562151f001029070501c18801e11058040919200d20180e03000c20311100364401d2103e04004e50901c0e050b21543c0c6000a64041440081d2010300000402d00000300c003076140f0703000030803820307400900c550042816090602403031348040c01020381401c4034400003c2c407400750500c681c0105081000382d450b0100101c1c0c00e4607140d00d0407881d4148545469100100c1950501065001c3c0c102b07a02d001c0b510705000925601102c8050300294460010040c4c2030012a20026880703000c280c2c0704400240e00c44240c00000c2c0340016030b912003540080383c609061019400901445580c400640f920391880d02c903484160140c84000b48a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 892725899 1250 892724649 892724663
    0x5070b06151204050c0a081b03070f170c0d150e0127050a0b0a0c0e0301110304030f0302160804080c0414060f1206012c0402010e01030209030309041b02010f09 70
    0x50550340002c0321900288500101c904140400b0042400b10070680d110607816000761050011003500f62040c03e1083c03c2c220080c000d014144202c4410f140b10500842000f003126100a030301c1c690041208000700b4000401441442c96949401003a2113000e8109000e024206103c08810100500809080d035a1103c241a6070552021000c485080015403d48491059088010105840381c074080d018071002840444c1320448942c0240c900384003071010368042d0707240602103040c000c14402130780e80141e410329098014801e00c0c031040b801380c0100d80b42c480100e06071045600410031500020012124074a0903070341640080d0301000200d131071035082c90700c0c180503550010b4010b10700595048031540005190104050b0104075844c036140c1c09802c00c00340d2101c3e50341e1685100220384101400c8540c100c040081c81d1800d680001d00c2c01043c000124149031300424a1840f030396090096401555015200304000005644002801d12100580102651030150030f1001d80d1520b0241060326a00a14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 892727149 1250 892725899 892725907
    0x1509060e01180b0409060203090d09050d0b0c041e1a0313060c0c151401171f020c0115090e2a030f06090d02011a030c040c0212070305070b0615 63
    0x25001029500758450b410300594031900d426040c0d0302d130b12925070340718040e810040e02c0b454070701c81881c50035100d14003c5c401d00031940000c00480c0e03608043d24641581c404a41c124a0305c8004015209001d42d030099403c94040a45030a181e0700031a504208880c40100640040048c0901c1c4d442a44803d0399040078801c040480080801d11540005404c2012031a1016004007141c407800e50f40d03030440010040741a200c02407001568a034043c40750140490655070f4490000010845a03503040380c0c0d906125221002011194030007099040d2450030b5000381c001c0c440302e480f00d07440203441519030180004030f5141c1040c0c0c031310b030520010b03200040b07658000b0043c00b445d80414044c580c46990800131541446100e41305065040207128007401504c0540051104800d44100030b42500c9445407104024040e010b071440c00307542d0000d012030070f410f01514002205c00020008904000482110210700342000030381204041c0d005004003201e0303024010614650311080b0400c044042d504140e80c0e01200180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 892728399 1250 892727149 892727159
    0xb09060904050c09060c1f0203090304061812050d080702010608030403170c0f0604060b030d0f0f0c0506090f1005060306040b0910140a0f110d0c03060b0d1509060e01 73
    0x603201940207900c1025080c01c0404c22000107100350300100c40b400e0550031120301c0302d5240504c0f20740682c0102c00c0507400e6045242c510040c80c2e40e8021403013808100001607401d052511300040f032410140450415021911b8500d0802c0c0c0c0d41e42c051191407000140a40001600d5035206104040a41d80c8210255244c6480c54a0300300780020745642c8141d0a500c10010215050420080c0d44141c25481009e4400c030f2500d420144211140041401c0c0281c001251411100790b11881c00398600707040d8100072920b070b41070050031546250a020700424500c81e220a00c901d01e0300010350048201c0100301250583c801e822401c2e4292102035500580644c8080b01080000d080c50751001d40c4040f45004440001030740c06003540689980c84020300521844005024001c00c00340030314030f450003c0c140103201d4019081340c5204039119000c0904903182d80c1d03c1c1a8084680310b40c208900074000c4c40075407030b184c048104007600140140107100801e030110328800030303240e1000d000b00011581c400c101800682e20704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 892729649 1250 892728399 892728401
    0x323060915060c01020a09030327060518030115050a170601090902011101060303051206030d0903030305060a1e0e100e1b0f180a05030f062422060b09060904 69
    0x10841c06510040500550034031040910140c100081560707914800c06186080c007508404548400304502019110400e0850712000320a03030482c1c5c1103207040d6640b03c4001120442c8001c0090f64198154213059401c119013500e40b1042054070012188400c007103584488103852039003041403211068210340010800303d0701c00d0f0702c4800c1d180d006050251003544440100d40c00c50701d40350803c0700818004281002c1d80b941c481350701584000180c005040c0c10550000103080c81c030350762000504040c0c5480c0003a08940360f44503054000c20480103c001540d040c0303820b035828100d140c080d0400d00f002c039100240005c00320645a8040b02c1007081150025102e0361101c1d001078990100351007000d00104040e00d4080d040320010540f0001d088817840494101c0c00c101310301c1c5010360340030701d100c0d50003110216030110001c01c03000d0700120001010038801c0d00b1501202c2d100780c88331003007030307449000c0a0702030031101d01c002e010300b104100d01403040244c0ca03101d40c4110403d0243e050b6940c1c00001c1403050301428101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 892730899 1250 892729649 892729681
    0x30a020f0d050607021015060c02090a020f070303140c0910080702120409020706060b0c0706110109080a020a0c0e04080904020c10020f280c260a03230609 68
    0x7800c5050400c4003a2a2603203444001c2c0d441100592101600828504007403003400413540046c10f841c240070f032400c40002c1000d418410b0185c4140804000320f1080c8240c0e80c100c60203844110226500c40005060140041a070346e2a5809200310040000c0d1800e0000c10445283c0710b401000da5200c07190a15048482c1d03d0300400c0030055201d9420444088036030003001e000100501200503948087c14600361050301c5a56006011140c01402821128000420000190b40140c44c040c403501a601c1407150240c1410440500000c6000540c0b02080c1d03408030302000c081d40a01c075000040c40d568500d01c6038406040f038000e8400442840305409500d0240c0040c030341c0104110484040300e0038240003404a070702c8090810a40b6400242c07400039400000d071403a08802d80042c85480d04a07410102400b1405c100000a00215800c200c030f004121000d44010f030754580c10b404558448070650400740040040c251034070000b80c07a0303051501114100100c124429000a0441c4240da140c0c0c414204d202e000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 892732149 1250 892730899 892730929
    0x60e24121f0e0a0e1b1f0f030b04110d0203010f140303040e0a09171b0102270d06050c030a1d0c0427150c0507030e0f04180507090b0f030a02 62
    0x904c0381c00d41405428200182940b4801504d01c82e5442905441000032001d8588036101903116449810071402d03400c0016164005a5400c020032200d8000c000200200a80400380d000341c500030038070000e90039a50340554142d0b5107000c1c0705198030f52103030740c0007411444c507201559042d40304010030720802d0765164841c1e0f00810f030040003061b52052540c0d40484009061051a00204045501050390181000c00d0b042504100300852400885d003908842c070070310311101c491165200032500103041d11a02201050f103a00700408001d44c3c100039046010131f1b801605c802d5084c0e8109100b0042084c1e039110078081001c043e0004211103400038042c40054280001926042d03c418490449418644207100c041144074a6401c2e8001d00031102410488003490804d00404c0781c1400500c002a030041c010000d1240d04a41905040441310009001f030140c80c6a44660360303002805104c01c0250006800d01500c007115000c0c40003203118420f00c000c14100fa8022641903100c0356051000d4246501040e022107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 892733399 1250 892732149 892732151
    0x1716030c120804080d080406051602060c1b12070c050f0f010305190606030209030d020601030506071103090406170d0e150904092f0a0f060e24121f0e0a 67
    0x43d5034000132810500c605100c540401c1204042100b04102441010740c001c29182800e80100c005a000039910500108840c52521000650f52540c29075040001001020541114490580f20542491540005904981c1d072304141002161a150540d1035075248a0080c01050700400100e00440c040e010260200c411010510f44614005440d801048068841380e20056501c000200a041c50720b160b88551000311341000c00144005503010900b01d4106002d45000020b014504914600b14880c1c040c2440d40145011310004a0040c00b003c0c00b184c480e900000d4980c650308414056130028500c183c50781c1c6c440e0320109003c0c0c004008101070091280040c000241003240b42e030f1034000c03203403141c0050300c6810070200510300c1c892424031003048118815220a10b0703103460b01c0c0062140e00110300881c000e00415204c1b01d005611142445c1c0b0340031359114421480e1814030344045c2001d44c4080e4454441c60100d0000824400c000d981084802900700c9160082c03901e032075134580324454054003541c074407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 892734649 1250 892733399 892733407
    0xe0601030b011206290a0503010312050909190f0b0a09180221061005030604020d1e0309090e0102031e04031b0b01060801120201020a030f0e0603011716030c1208 71
    0x192a480c0b03d00303006040011100e03105c3c000c03410341e140551000d000a0126040c010440300140c59413003805d4a045a0340403031002440d16662000761894041c50314131540080c50355003003024030800d1898141105c04405000c0200e204c9001500d003d64407610032003600100c00d13001c1040060f100740d008096040b0a000e02140308005540011507a40350a00d07a2002101050701c1410074440c140300d642e4004584001100034103191070301080c1c45100007407020303102e03007007031075000c0700388000d4002801030685250302075040d4500514024061500038083e200340a4608040000840014804c1760f001d0480c807001d68049042d4040c3ca0341c1d060200801c110700f0403e0141c0134999120414034000040ca118408100280d81002d0009021000c164403c00011080501110241c1d80208540086580510309115540f8a004c0151055061403407426000a000000050201289080c0f45400f00c038040c00d40301a944c05040440320481c1502016215101100007003150941002c6140980c62180d2006410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 892735899 1250 892734649 892734677
    0x1602010f020c01020403030f1d060d0e0a050a060c0309050703060f200d150e0f0709051215131a060f0604060e030c042f1b150702010203010e0601030b01 67
    0x507030b0004241040c1903034003ca03090007019000300c0583c070204198604182a030302d001c0900c20441034071a140f00e001d20b400140c421070341c01e100c0c4c00c2020700410f0403084900d8030060745000342d540c10340c50906540c11032a0140301d00340309200c0c0c0901100a600f000c0204032190a64940f40001c01d114000e200d040c5542c4c41105140a800c04d00c2d1002680c84118101e4032400000205826113a4809940703228100c4400103208443d0351091854210002c4c282d0b5140340c1d038030241c003640c61104981206901080d03911414004890000d01308552000a0480c1103071503c512100f0201c0c01c9651000034901c0980ca881d69650b4a0800522644803000400c14102c00f001c000200701c0d103038080d811003c00101d048040e0320441c14200803c98000c2c0095504021401e03622032000e90b41a28024458000c00071440e4a00300350410b482070f100162000410400050400da40b502d66500c95000c100c40c2400e1000c1c0020f14041c010b10940b4100d40c0c1c0140030441c25516200118020866101018107210491b000381a07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 892737149 1250 892735899 892735901
    0xc05121b0a0f0f061d010504154104030302060606180d1a1015030c03020405120c01020d1704020d020319060e120405060a0c02061b03070308130201081602010f 70
    0xb00800402841e10b90031810548002c0c152540c4038a00203103051000c8009072580d901500720760842d003411918116030400322a0445041000c00b0110190480181d40307040c65014828054902c0c062a000880003422854101080c038000c2c1e00c4045c01603000580002d00c1414228010b003002c4a111401c000c81c42c4c091000901440c0700c1c071405480103400c819120740d480c84291480da410100980111034040d240c074071020301d403540e082420010507403648030f005c0d103050207a01501c0240200038408100c08601e0400d4507900c2102ca00c000d4018070519008003442800f0308001010f07200e4511a0100d10303950368082c030010300c0c00c600341240c05104d0140b4151403444540b2483c1030b594429000400c540e0448501c080c90000500300d03072080302d6010417003040035a8481040740e0b000d05550605008290150000032650301807083d000d1100d0a91402c4005045004401040000c1c440d03250114180c4602c1d0365060000c3c15184000d010448200114039410607550f4007142e11714561002003044182001144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 892738399 1250 892737149 892737179
    0x9030d051501030c08090d0f03110d1b0c15020717130e010503070e0417070f03020105090d0503191d0115050901060807091505071406040c05121b0a 65
    0x600d003031044001d0a540d82d0500503240c80c1152844e110889041880301561a822079440d10014001e6545c4007405003801382e0025421103500c1e00072280c40311084615500a044a0101501d61414040006503160b01440c14041000e0f0094807110880d1108840d00d0300a510444c030944d80c1d1072043d04251708092100f0018010806400c900342000d62610030005860700c0103801103403180c1c00415040c01940400411560b00903004480444102c035031441c1d000302c611400c0000b511a04617400340c102495015044a801488030f0030494860b18654001112140411340e0080483d031036000800c4030b504031503000045103200610350f180c5030754441c544090071a018500f04201c84400e0090801c0586440c030542c90043c606800d00c00064600349800909496803401800340014200000c859110f200b02d066504680d8011030321044452550301d081d5840b10200d400301e0310702005030f0300806e050809412104034070000800409400a0031003200c1c040704030142c50307184c00140b4a240050800340c2c0401d54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 892739649 1250 892738399 892738411
    0x9091c1b020a09020d0b0f0d1511130e0105040903050a0509150c150604020c06040323072f0604050621071e03060f0302060d020714030a0e09010b0a0809030d05 70
    0x59071407070240c0b42e4105a806c014200c503c0344044400c032856944074510f5801106600603441c0190701d80790801c1c08001c243c0e00701c4583c16844041800e00c0810300603103903078068031100d11034448e81e41c2c0c0c0d8004020036118011001800524248980425a0b0244000c1d00348820000d04002d001c1d034460721003a55a4204000c203001c00d80c411088200f03444e290f6078030300e80c00210537681589840b01c00701046030b5640010384010200042d4001801c0c445000070344100c00704520121156071031600e4106801211542c64012010520038015816580c5010450041c0490090030050a1074a45020418240c20035120062b200290101d84c00120019060382c0d441040030703494002240b582c4440701000100c2d03a0054509140c40c140e800d0110509031035440044a50441e080c540d01c10060b075280019004490004043c0401070440f074580310b401202030070301ea40c016641d022143c3c1d450000c1090f00e2000b0710941c050440b08014203140c0c1e502c205120743d03010744990708480c60b106106000900b1244200c1d04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 892740899 1250 892739649 892739651
    0x20a080f090d050706030621120504030f213b030708030c06130b01141305090d0e060414040f02041a0405011202030c031602190b0609091c1b020a09 65
    0x1040c4011768151140f540904400d1648c07000c4400c5200200031820100741002d04201c1c40304400105a1384030318100d50180d03a10600303078403200c1315034035091217606d0900c0c0170780100c010381e04107110966128003000300301c0c003020100f043c401034100f00420760200903c652800381126100301502c00c64a003008400018043c1500a50740c480d1807654030350401a004c1c0c20000c03010b011200c220701240c82d0200c860b0548404c2c042d868188000c800008041101944462076075900304010400c0401c0c0108402403054a2070b200d01150000e11400c10a0078419070080115240c0d04445800013400c0c15404004258845400140b0703140d207c400040301c500149103400d03c0301c1d50000b41800340d9640701c0b640c071b116038495a20640c02c2d4140b01441d414103000041c02e550301b60b1200b00c00509610300c200543d620a000d103080000f0402d405081c04440e211003240c009010703034489008245029000640140c02001e0074a101d600d0b4030380c0d64030032980d0780b07038058009583d94480d03018000581d0307074544040001c0840300c0d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 892742149 1250 892740899 892740913
    0x10050315040606120510051f120203070b0903100b060403050a23010204050f010309030c02090109061703040302100804050307050d091809050303011a0c01020309030a1e020a080f090d05 81
    0xa04501aa10b40d078200f04a48444603131000009480001c1010001d80f0003d0b001c00c0940c0d821740c4d002180710810f41100b5010281a10000309407a04a14174007425000760243c2d160710340c503065a50414400d2850701d58041d4410220010450304c3e560098543c060000d0005103820740c5c98640f286000303105407054500c0189141c2c1c01c02c82c0d0206600000051072000000e50600f450840000d47c8068200451411705450317000c141d0805118440c824100d0741d006004100c1c95840303919410090039a0b005014150850b118500050540003058504803036006181502c181c43c10b14040300e03d42d01c00790044840348424070009000482c28045039140a140b9511f2142c024504050205c0784001c142803061618900130f03654000c0740703010045038155030444200441a4a6480c1072181c103120320441070b0110f51003c81440844030012009200c444280c0d51841140c2c0d180e02ca034010000904513070030000d80c1c011542000000c42d505c0182c14000d0700305031000d0400195001180d030840c090202282d440c3c00981c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 892743399 1250 892742149 892742153
    0x130b0306070e091b070f11011202043c061d040c1715030f010501050906090c1e070b0405100509390303040b0715050f0f1005031504 58
    0x100003948001a03240100104400b000400d1009001030a6608441464201e2002140c114011103030690b500051003415030340642414007401204044050010792080303141030002c64113000b035034103032001e000141c0c25140c0046150402c00e03c407400300d11101d046690302c405c0c0c000039030000d810080c44c198503105c0240d13851155281488a220894511607481c1085001c00507034088406032030400781c01c0a001c0035841e904000d402c1c46170410502175040c825605507800038201074021604031101070b100d402c1552602000c0100041c01241c940c560b003401802580008040004c0800c01854440c000b5407030540c854039540c60b089412501941e40340c3c4450b080c0c071480d11291294a80c0401c03030101500c2261848406501e0300d031060030700750200c4c415441c800451014030035601001c101005003100d40d102c0d80c17101d8042030b907080030b1000e0701c600c0c048100d910b214207141e004003485400340c6c0d140156250b5882110740072040c00541401c000e0500b1400c081120303101040701e00754541e9942c4001d03005103881c4c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 892744649 1250 892743399 892743403
    0x30501050703020a0834030b03010b010221070f0c03030302090f032107140d0f0e01050a0822050303010602010f05100f05090a02090d08040302010f02061b0711130b03 73
    0x40e1a0380201071041000c0d00313409501030344568100040c0c41011404100000d28040320b044290b040004803481d620702d0b050802d4140e48104002c00341a80240700060f400d074010ba07100c040d80e00c0ca5560300801c1404070070303140c01f5103001805428442c220b99490090f07152140a6201151f4208902081d030021380c81529260070f1040111404048004001c240c1402e243c0a02505a109540c0310300e14021942908200480c0300310394414080504039070902d900000002c15007a0030210800c00f03d224204902010352040d0704642c1580354503298030740551190000c030b8041050311400d850040c0e00c400d6207500007500900086000305002c2d800406c0d1a02001d41c40c100311240503103d04c01000e0170740020041d159041c4c00f164200c50007280e0301d50183d03458100060181c0700c0c01c954554070052100c6110200320701080a04107907030007030340d0b00204004500410f070f0380c80c0001e58260300801255070510040f002180000c0c94600e224120103603150181002082d581e1140c05c1030000d8054451200700298101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 892745899 1250 892744649 892744651
    0x1104030b0f180a1203050a0e1f0f2f04080705060a03090516060e03030c100b0604350d0e13020c060f090f030f2205060307030903021603170d060b040f03050105 70
    0x407c04010200341c5820139680e546058000801c805000c400d0740790290000d030300103105203100c200e0038050b0101c001e0b440042c0300d18010a0710b038510040f94142c80c0700e501420582d0151001040244004c0e0304103405c0100c2e9030400302c4041d00301511740c085800082d40511800c4030602e01607030140040703400d00074050000c001c9060124000c0e8028070044070401c000280d500d180060030100024400904d101052041c42250824580d015520b52030340083e5811304160101d0481d00d540010b0071741c0c54045501e07198829802c50304001005008801518605400c50b070200300e056070401481c18008034400341c01c00d10210380220075007002904210081d8803c0c080a01145a00e00107035191048414480350302d402040301d80303c03090185007150102500c05503560b40140c1302c004c00c0c10b03072a40b41c040f000801038a081302048006002c4d6035840450b03d5151100d84d4180ca070710910a02c00d01582070343c0055540c100d868910310503511180001449585c400007400500301c118590f044240c114204103095480c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 892747149 1250 892745899 892745911
    0x60102010207030c0f0f050712150501060e0f0301290f0105040602060406050c12040503032707030305180d0c08160e0114040605040c0f02011104030b0f180a120305 72
    0x1004200c2c4a0000760b00c00c6100c0422580045842078024050810079140d015942004107684505c5401144c441c0740d0f07031742d9000c0300d52141c0c00208080010750f181c0010788000b07100756000700fa0000e100071001d141000c0c010300d14004c00ba000045101140460400040f04481c49900074035031030624000740d082045d54100e0f0a2820300346246070074548034000356103d80c0144040d002d90764800203c3c4440a200342180d44200c04807240902c142010308016480341d0050741e14000c420030203c1c60351519103840113090070503c107000151100500e51b4501303070b40560106d00800b416141c40c00303a225641d070350740344020b0301140103503044600c240c02c21803900d10b08200c0a046a00b484009101000071000b022402e60546210400301c92445000401003000351a454100070b902c00d0030203402038102c56021080400540103a802030202d1010404103070003503c52400060b229080800000303482401c4220155006405031340303110a16160305042078109401c49104948000c00180401d003251b41c94051550001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 892748399 1250 892747149 892747151
    0xa09020312040f060c17040b1c0c08010636080d0e0604090c0c05070b03190e0d03020c0708070e0106030501140d1401110d0209040e0604030c0209100510080f06010201 73
    0x16060070710b0148001440d21130803007040481034540041107101610b0a4080021a00c526261502c0384040781c0250032001d495400740407014003000d107006442c0502051100c1d652104040c0d40d091890481f0310180002600445540c9845010350424a8801310348000d6954805841d0007030900c0c01031420a0800c0c1c900300100021071703900040c0d0f80d43c0e207c102c800312850060000743d04007200d44181c0304d402e400c02e0090520b010b00c0780e0020307020f80007500451245a4a640c80d0040b1490881600c044030030b10340502032250301c03074810211207500a5008240d1440d620080b21541552416480e103090b20581240410000d2507004210054040c000d40c0c0c05440c400041e50f44090520b008030705900c50003003000c1d000300e000e211900f156400a500c104100240d640c201a9501d60003040c1601940c040d08585d406039140c0411207007800008610305018a51599034400070003016002c2040030400904034503400f0403074041c00030380da56a036607500302484802d4840d480a440c01e8100400c0301d5200500c05415a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 892749649 1250 892748399 892748407
    0x16080d0c14180d02010311030f07090801180803061f0e0a050a141509030a201507080d0f0e0c0a0605031315020d0e031201090b0a0621050a09020312 65
    0x61414450040000003580c2d43c003c10300160004a02400e2100414001c080002045c8190303c5a01e4000912442e26a1230300140c0c5540c41c3e00c858221102084000b40d00b40a02000c0b90009809900640d0454801170401180c0201c8045075120b0148100a24010500d01082008075007450300e9410010401190036948403840c2103142854000a014143c0c851040141201450a01c800c140c03039050b2005812038460085915002030b105000c0c0d00403000c00090000e1a4441d80740007803404291030900b03188507090641c260b440500c10b41140c107a41c040c0035103c0c2c5020b0880c40c50303882106801420203005006002404040c4500340b4101d400043c01c10800300b08010040c0a4200050306c603030343c04805d82c0d241c0010507019000170701a04e07600d04a00c41c103011441c02012000000340c80300755400480c841480c0d984c1d190711411160139030292034112003004010040540650818107610145501c2030f000e0100321066001110001c90b842040165501191030075070404000389041c81061100092070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 892750899 1250 892749649 892749667
    0x60609060b07080a090312230a0c0210020c0405040308040b070806010f0e210703050f0c0d0b07021905030a0905041104121401060608060f04020a0e040216080d0c14 72
    0x2042c440d880740501810000941c0c913100c00e11a031214401160080c01c1c11414640c1070703c0081480310721300d403000060003607030039074005e4408a00102c0d6180d0000b07483d04e080c0301c01c0c150b0074401300402035411300040d0301800541d42d50701d4a4500405109074800e6540e1100c0e0314241c45c1c810075907072000d01413408220b01c01007006000c0c2d070000101482a091410280c1c000d005900015000e2071140c2800341035044c03c0032804544c95000a802c50a072841841980c0b040b01b0300c10341e200d40c0c034028903000725400980c696074600803441c182285c81d0032802e18415500341807082c50324800408403986080720581d000003020091590320a480c00042c0008036070600c0190700e00301001c0598010780c041d40e0300640801c001001041107003141d0070b02102a04009000c0d2035512000a41000403c58001d40504020b200c58040d0b8034142c401c441d070724402c1e5110100707240304c2c60060000941204d100e811a100740b85080c18042049040a00464128490046500410b07490010f0072a2a0481e142106001c144800c0344 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 892752149 1250 892750899 892750919
    0x405030901031a360703020a1b11011d042c2e0f05070e13140a0507020712050a021e060d0f061a07020f01030b212b0906020319210c0503010306060906 66
    0x1d11200246014a03100700d002c04033a151082c1c2203081540a841d0400c100040003c024129402061146008082600801119072030301d400640071107502c1e603410710009070340c030302d6442d944811050030b40000341d1350a001c55142c04440d003c0d01c548006c02d001d80188031003460805011124280f40c41c500344180c218413130b221b80e44048003802e410b12440e2138a0006000a100b08842c4004208034000540d070840740781005a00d40b8190501039005840e20004440010303036000500c00f000d071001d024240b40c0440080e44030010710704040d20a082d16180d140000c1d010003034480d8458502c1035031481e9540c0c0c5a4a20420089010740c0d242c3e80e040c035050030308140f03039552120740414008180c2404880c0101540203550708007550750036995070740303044c0901c10404140c000398064109181500d50106907a1540310590344c0340124a002d01c490750443c013154100c0751065035200081104500707480d44410325400c0e608140c5601d500d900000030804130040050080c14001da800404044400308000e07070a045000c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 892753399 1250 892752149 892752173
    0x30e0706050f0c0601060909061d04021002010b090c0a03060e07140304030309020a030b0106021515010c0c05030f0d02100b091512060405030901031a360703020a1b 72
    0x10080c01030100e82c0b1050320384010b085407050440841078a04960f110319020789030815602843e90000e28100c2c002c941407640b0251203080c20103000c80c1000c655215401c018030105c00e4005402155207400503040c041e102c3c0d544490040000052441d110b840300e0500404582c03455010320322405441c410300c41400d410a0b45460080c204111141e40ca5540b03060980c0030789040e5000035000801e165000080c000482c84681c1690030395401e4520721854024194801642a034800b01d500c801c00001e002d240d8000c03120038046034401c840080c1c001d9910310000341046020b80c144441a0816040e045280e90f05100403101161180d10801c511894680401c04000f00145000221200c02c2005c4826564125007005085030500c221081494103190454983d0420303480e080c080303410300000f166500490501c60704400c0300034055891801c42c58400d1450421b03c6e00070101c0c40d1040000301c0c21001c050800892007a4001d480251b03595641c00700062900e4160b2440741e040b0a50410a28000741903100c8803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 892754649 1250 892753399 892753409
    0xc01020a020f0d03110a0609203016050301111303110a3f05060a0f02130e0610050705100b0a1d0f1e07050a0c0c0b19030e07 55
    0x100740f0f00086280075101075505401444181c828181e15008106140d040b8039007d81c030583c03c207018103e280d580e194511030440111a84001002160303001400c0c41071102c10740c0284800240c122003144511303627081c4011550215012079101506000d00c0c242405028169154103115901c0e0203007500f80120b40d68110300008044000d082e04d0f000b026078400c9080c9024201c0340001440610100b1040e000c1d01d01d2810400a588141040032040740b2090749090138080d80040261500f956411181c030000d2640040d004603c513801d226403441017504091002c0a00018410702c0e140c7d003040c1040040d00c102c5001c80404105080000d1400504e010401e601c1c00342c90700e1004a01009600700240030300e1125001003007071b00c40044480b0074a4880902c81405401c800040c1c1407551181020340c2c21004d92900380c0842e40240c40b0120381c035684268018030403401e03549084041414681c0e11302410f58403551002c0081007000c5101c9003c249901d9590101c5801c034181001615a010401601c8208900c54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 892755899 1250 892754649 892754659
    0xc0c0803190b06030108030d0b040b01020a140a0f1217040c060e0a08032224180f0e07020c100801060e0103020c0d08040507090207021e0f0a080f0c01020a020f 70
    0x75001014041d0041e40062070300400c015240d41e15031a003181c0d0381d0000c0400107030481c20b018069009080c6840341803003401040c0d024000c1c031580381d114072138144c041c0980340b003841c032411521001040d0020001d111140c410701c5a14902d0502500041c441040030f01c01c3c0882004c45400d000c0000e9580103240200e88140c00d050041882c4e03100062841600c0d0b50040c40b1500000035007540c0c40740c2c2c1094500294120b1000b900b407660b06c0d11401200d444061403034002d10207507840b0800002e4083c0b190b03a502000c01b4021910021f44503a000000740e11075600840071103441d0702c24880b410380c0502c20010407010590b2403400610145400404054041c490301003844625600c0550b5644283c0485100c0d40400c0d044030f00707040342a140141003660855094a85001c3c2d24404135928895000301c0c1d442a40080815004d610101c802d0219400e2110b0b40e1365001440d0408101c460712420000300003014948043c0050301e00c1890128180a0840d00d00f0f4119006221b100c00160348180e9480d545010a440c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 892757149 1250 892755899 892755931
    0x50105011209080913051e0615090d0c091e140613151502060702070b04090b0a05030a060b130908030118090b0c0316080606030703150f0909060c0c0803 67
    0x10016198410b00c04c03095088410160001c207254416004640a04542e60a00b0034201254001c144da0701c406641c2e031980801ca2014180c0001460720142803031800092030321040c0f41b000e940c0d495801d405580b000c9402e603100c00c44081c4240c120841948185280c00080c0f100f959200000c0101013001400103104002c1e070300182004a440350300c44140c1462202036151501d031201104c60200814912180041c4104800143c0007440840c070b80c0d0440710b00c0640da40c1820305000100000d88074042c0c500350000d010440004495404000b1004410300441f400219544c000e0244201200103d40d00c4000c5800d1507640d000081341c1404507070450340f207488044031513180c4c041c4a01c00f902c04501e0142c8031400d0402801408070402c4011401703000d01c80c2030402860740191040d6420401160b485922900030310000d46118000e80110310341e84a0302c00840f04084d1190071a0482005d55001300c40110b58404116041205610800364a04a03a0030043c8c040d412039522400d01d8070004251440e2541c0f141d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 892758399 1250 892757149 892757153
    0x9010b0706090305160507140609030a0f0512070308070e04060f05010c0f080406020f01051f0b0a0207090c020304051206060a12050c090708090606010e01020709020c030d020c030c0f01050105011209 87
    0x21306880700000540060010412141002d5030740d1401c43c014041400f004550016940c5803100031540300100c050040e0808030b00d1a100c400c51074424500c2501d80d4000c06004d0f4030000782c80c4006145451203500c9150307031405c1098000f03100c0f15400074072900079403410600b4840e84c2c400315420011610f00340781000034030305a03103407000301c81403030490040403154080380102c0d403143c01080303000c00e05445074004c0050755940b86042c0351480b43d03800d407600808052801071140b060440010070707034146280102d403001d59032000b08600321007507101000d0040c2c0003c10140701d0313071621090094000d0300a9008010702c1c00c0c440c0000317154030103d1054807000c680c503500e488200300c01031000f02c0f207400000b0b0811200e850000c502500022040742c1c0c1103118020755001585541c0940c08003901f005040c7c1c001d05d041410301807014025070118518000345d01c4203020303881a4207501c1c0020010101400c0c05551103400f840c6101d843d012215185000d44d9042100500059070300c000d0101e80140c49510100320004a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 892759649 1250 892758399 892758407
    0xb010f02100c0207180203012d0302040902040e0601080609073005120316090b07050606010f02030c011a031219050a030204121a09010b061204020406050d120201050609010b07060903 80
    0x41c3c2c5c0000c08503c444200c00c1c03600c100541c0514100c42d007044900d07981d0b01030740488e1031803031400402501c105502c0800078809800c0962054035803602c0500700240400e101241d030f42c60518241e100b10519481281006030040e0240074540c001c040d603c20a1507000343c10000a01035440001c6444003c42c18420200300384201000321406614007940b19a5036400c016065030100c811810951021032481040000c40f80010000c070360700190002d020300800c4c3c8400004417102c123624035410b41144414844d0b061300140a100c1d901c00e20004a03082100c0d00000300506090818800c1c4440506c0e805100301826500c19101c42885c0f0051441d2003075a031001810b00350001e0040e50880240606551607041c10041e2031000d070b56040780b105040010503591050002d0a0303445640400760418000d01400d1480d40051610380d4001e480140040365035038407a000329441621000e02034500c8604c0481d0b040e0415020f1088070341005017691080c02541c100324020754140319840000302596503e00019051500c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 892760899 1250 892759649 892759663
    0x3090305070204052e151d04050606250b0c0405090f0a2a030609020405010c0f020a0801020c06100510080c0318030a0509180411240a050a030b010f02100c02 69
    0x45203010014100505171780c5520304034021200d00b0352260f031640001c07500a44451800b42401c001d5011803a41c2d0905003c090034002e0100f0341c000350284480c42c10207481954031000003040800c1c80d041c1540a08040d0040c8030007820415180004102c280701507190404900c0c3e01040440b01d50600341c803980038400042c050025090f800d002e004808802014081e450003000c10b00d2641c0034041c42d41c59a00c1d0b402280300764030400d804a0381d41a4007100240f84030340c200d451240010007021005603a610a1803c2e80c1c807158601400d60041c0341040b185020b0090320001414044d141241c04d54400c48003d048640e001c0c11464407498040f00107003510340303100b64600403000000147c0361a030100110240c80c6800422216211398007900502c811039440d1044988526040340d1140b609003001d0052103840358900180c60031020800c0300030007802204500a04403142c00b503455680e910310403100102142c40c030402c0207040110501c56503040c0d560005072490745144806002501d0148940c0076071030400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 892762149 1250 892760899 892760941
    0x15090603180105102607120201020f160f0e070e040209040f0c0809071d0105011419050301031104020a14031509090d0e0901320909010905010c0309030507020405 71
    0x82040200108002045444001c03201c0d6150300e07400c200400707070b80f0b0100101d8100e10205c0a602c140010400e24007850050402280180190362040b403840091500300150744185106100081c6820000c203441d010840d40180b0b000e5094400d18148500300a000400c0007440505c141d8011030302c400c803503079103034401d26041c050800c041116682560004d041242c0840381e01c21b280c02910000100d62091000c082414020640c01d051607030700300380042d01c0300048030003a511002c105101c003540b522000d4081030034102d007648485407250324524110b11030100e00794110b80601e005200d00b00000c0d80186e40b0784580750329902019140c4d5500d071202074216070b0a240491740721161505020074803001040e03140e1409110390368040e501c01c1c00c1c7d0620250800c28401e01158103504820900c0c0445840c030070790640c0006006070804051000005942c03484243c80d60161030755507890f1002001024460100d850005003418002c80401e510041d080c0d000d1400042d02450f240c01c000341d040201e80410000d014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 892763399 1250 892762149 892762151
    0x403030b06030907050102010f2f04180b10050a05090f041e02030405010c0926010612030f0206060306060607020603100510050c060717010603020c07081b0a05150906031801 76
    0x1c940303499084d030354080301d11034540594078080401600d050a13000d035103a58461455441e2070007100c102801000d07440135041d141100c2c818007004c250002603210308a0b0340b5812041c00b15211155604002c0051500e07860315007841804c000c4094501c0d003001c107a81507150200c0d40e03041d1040000700420080c00408489485201800e0300034488468258040c50060340560001c10280310450301c03da480c0d1419000c2c45007000368102c2c280d0345002d0030940f140c0c0044005000030503840da4904111440c1e0180744021000700e14402d04000a2a82c10419264080c030304400400407403c110003ca6402d10940001074080d10000001a1541003680c0e161030080401810f41000305000041c0284183c12044030340100d405080302180304948207030b034001039212195060601c41d9203424401e078000c2d802071803080824010041c0000700390105210300540050014842e01e4003121800030050415459017005200340011490518208154821b541100d0000d56000380d598446c10805000c1d902500c104210035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 892764649 1250 892763399 892763401
    0x2e030314180a1e080a02060319021e071401060e0a021305030a350306091e2d0c0a080405160305010903030f09150507170f1611030d050403030b0603 65
    0x31500a40c00c4400d600201035010f9a860300c43c3c01d80b90f21800b030317200003035800342c404d10200d0900b00c0d8402e07400310765422010740149031003910408100c28400f403c4401010b43e1002c207180c0305200400f502c0b000184680c100800c200c1d03080c41c2120a203000d014100e41281075010410360103540c2581d2010000d040d00404544418200d490960903145d902c04c0c141204900e02013590303020322400c241c0d41e06104441e00c0c4090075130340e03820103004080800034007900c1c0503010141034111481c1001f003242d000d80600c0140b407022100301c0c0000030031110720000080b401c50a120030001d2500c014000c1d102c05501600d412416500c039414014a030200000d09500805011000042046015441280d405203e17813404c2c80100b404a80300c2e401c03070701414800751061222600340084c125099202c1e40d4001014140700d1000020340007000c019642c211102600740003210300740034030b50000010034130388070100b0f2400d402104400c022954480c014004003900d01e60310744000c1001c05010b07420060031004054105600d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 892765899 1250 892764649 892764659
    0x30418020c1b18090d020c1c0209060a0914090f0d021c0519111501420207090b0303090d03210c080402042004050d02060702092e030314180a 62
    0x7074001d05c40c0b2002c0584540104140c1d5030070204c01ca4100c90766502101c072842981c54007071040781480105440d0344441400340c045a1485a817003041c079043d844120180c11450b00e090700c54034203903a15482c0d010940c80b510003240c096500007441c17070140201031240404200340365000d803103030f0148070403203001c0740205201461560f603c100c070340060410140c00c81d21340d0780c601c4540c0076080c0420700440c204801c402d40380900311098041440001009201503844882c0f5461104c415a1030b9800b80034011f0300b050208100a5040b8001e0794940e01d021005186800c004c6400980805a400b00080034040304c2c5e818420701c0c0ba5103116014040703021100510243c010030f4001000c0c00342c00c03181244a6494142c14150003580e200810940c1d0f134503017828515290410081042d465112041260704c030604001040060312080c1c201e0340194140c031070740740900c48258103c079070000391544140300104a8000400100354085841c5a402e03400c0550316a495101c090980d0b14402040d2000e50018031800d40015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 892767149 1250 892765899 892765903
    0x330070b0c0706060f060e060c0f010c1d09070c0210030e1006170604080405040905030d06151b0302030a0c050c0d080a260c16050f030418020c1b1809 66
    0x2e455109003c10848503840f541202c0d00034260b40204800a082a070001103d82440d43c0104554240b00f42110219028070170070303c3c01c0d51100d2680744006241c14510090b802c280140c2540420412500440c1c20701d0641d10003040200b072908003078131401b0100f10032b2440c2d034082e0340004042c920398000e5440a60050401402625146c4105030181c0c01c0112380c9424100042080e034010380e8170081648c9041d1501c02040049c00b07401030141e4240c00108079603480c0e1120340c4243c1b002007074504180b1100c1d40d101000581403c0308089103105c07175000a45080b00281d07020085540685039410700d9035904005040031464064180c11403500140d4605090092210031006016000f1486c0d68020001d40980038881601c2440b0301a0103448980d500420006038010010700b102c2502552198500310703180d11418a000c010b481c403017401d03800000301070080c01c0144100003941d038490303a025460242c0d01010a56600124544004084110440c5012596441e84000c0e52009035038600c10760390400e0703e2519 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 892768399 1250 892767149 892767157
    0x2d050f150a0506090414031605150c070c09050a0e2b0f09031104090203030f0301050a0501032a02030c03040608060a2c190c02030304060501050330070b0c 68
    0x804503218040000d0040c6405024040c843d07800070f440c02066131902d507968030508580c2c502006c2e041c04280101000955801d0078104050300500041a4510200c5140100c03c0300c054010410244100311410102c1c0c00c0451002c219140300720000b595603101c051000c01051310800c1c0301c405001b000d0f01000010800d840980d1101303000031003004412804002030340c2c001c07c40314101c008981d4000082000c5000c0c50b0452012010103403001c00d150361554002419540b1000307440c480007102200600041c10562a00c50280c031003030908129051681028600c0c6039505400090901090721446400920a0055800a140190840303403901c0d155600a00304050448100c0d02440c617201d8001006281d0100c0040c90780c3e03c1254a805e5918812500f20040760004c00c0000c102000c00c3c21010809128840c4044079041c65015507264142442d01c007041d41c4040c1d10280c800e90142d102c0203010500180c05111071242a1001419020807a85802150081030b0000d40705c56030340e4040082c060341e980b00070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 892769649 1250 892768399 892768423
    0x81b06160303142d130b0f01030b0714040b18040f0204050103110a0e1212030a0b010305241c06020703030203190203041707050a05010f0c0315032d050f 67
    0x1003956913920f0080e075083d444a08103924000b00c00302204030069105000d051304544606040d0224503015111000c1d07288080e5204201000d044c001081403140c4400381d01e4208105281500e001402480380e8034680c05180102d03090a03c00180c6412122805610042c254502a10071b014940c000c0032920001e4009102e03140c046820103004103280c44c941822120b2030070071526150710703118008003404180150310429020368032480c481129041d88010256100305840180407c030007207860001006e0b540c0180010100c209000004e81e0701c01900c0460540140c015100155024040a035902c2170910100000d48220f2000524006060b8550015403060500354988004402e020203500308074441250b0207032030000100c048040f03d101440c000c11030b81d80520300701c0700c06241c55141d9600312040009898142c1e65a4407a02d1000f5130180034602c9200400406d004d4860320b55110302020185110200e680101c000c02c5001e5000710f550303040e44529412038210703803c07801d802e80055501c41d00c0c030084d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 892770899 1250 892769649 892769681
    0xe010312200105012304060b0717211506030403080a020c070941060108061503131401020408060612210304110405090a020118120308060a0e01081b06160303 69
    0x4110700354149401444121401b048ea07051030a4250380f24030f0401000e1002c0411030b0003080000c8904406040710882c00080c452108180398104408914106c01c0d400c691180500c100b80b00b00008280c000f03458581c003030240e88002d80d4400307032200f01a007807130700d00e400001f0b00a1501d052069101244c501c2135045076403412800c082a41c0440e10300320514000986042c40c41d04003800155694821028541c00c49406010101c2c46400c03901030300b4413900200c2d4104410540007601d0414008103145100c2c5903d507550003145042d007017400701a00c41e034005008034014002424440a0f030300040100c4c05038001012112103840d100300c3c91985061b03005440680c0c110308482d1002080d8074080c8207450090020000a1003201c04590046d1003641103181e41c0000e6030090100010013100807a49166498401e44c0d442c200b924000c1c007000a101d1482e0070a00c82c14038010014041c0c2c1d140002e1842c500d4444040742d04217118004009801d52040c1c0b81d0840c144000045c40c00b0401d60190410208202c01c444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 892772149 1250 892770899 892770959
    0x3110a0503251205090a030222050708091b0609060f030a050105031209010807090312090305151b03090a051e0114160c0606051203090a0e01031220010501 68
    0x1c8445a6800b1010080c02030030b41482d08440707650041c8001c0010f4400503110b040001c2d966000985400e901786009209118591242c0e4084111441950303840440c9081540307150606110302c41d82c03016030b4004061314101d032624505c0180e82e0382c1e05aa00807000107200b03aa0300c41d122080101c281d003044e100107080608000002c10a844c0c00f15580103c0b040d03580382103007044011401110410170160411090040c402004004103046d11500e4041101c2a12003003040362a51500500c3d004045003031411f004440018010101c00c03900382d0b04446082000200e0b280c5e00c41c50101c40c04c0c0301c00914020500d110b404c400340800d107900c20351812070f146880d00070018801c64042c00ca1220b04102c0e104100320048586400880c0d01072107030380248034060100000d020b600c80010440145c6402028940ba620120700d200f10740c41c0c04035001e0050220106444400d51460740c402019441d2600c0d404107001c0101d071030302180d844c0344005005000e0390350b000b4041d5594407460f581035411305110f5100c014219034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 892773399 1250 892772149 892772197
    0xf030c03180b03071b020d03030b03070b04050616031b110f041b08070302070f0b2a3f010501110309010e060904150e0a0f0614040903110a0503 63
    0x1d44140c1111028031825245a8801500b110301c0a4101020004e0204d0207800d0030140c0ca07541250506140700e0b85000800004d850101803504141c0c0d807000902c500104020b01040d00c2d00401c0e0703507901c0c001d520310721a10301ca5031806403171069030110501c981c00c100048000500a0b03400d80c100700c098066074000100d0404070144800ea903c0c2000b01041170600040c2d00100ca44103d1089503c4902c902d401810b00444d680c0d80e0208440408040d6030360342441d014480346520200c004038145d44944020003058100211f0305103580a496010200c0c10860007039091501544d04014060140d4003000e03c8007813280c0f003840040000c00f806101d000800c5c1a45007502d120000084a84881e416142c404800c4d411000700032140d0b00454800d1340060701d0f90703036646000115007054400380c0700d9407440101c00d146c800b022130100c0c0d488030309600300e05042032020000c142041041c81e040c04415100032034070245500b02901c90300f90002450015102e000710304018450040083d00284c1b40321a04020600306a07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 892774649 1250 892773399 892773437
    0x50108071103160201021e0115050d0c0b0d0204091d0d090f0e04051c09150819231f05032d0c10091e0e150303070f030c03 54
    0x103103040c0440c0d00400c01c4400d0300c540200e070f00031414414070440f0700e0038024400c5c1e02203503802180000c9840e91280704d42e1b8040d900ea05914030142c24255071040c6070081980312010100340c0e512403006444030005010041d1241c0b50100c901411004a092180d00d03440b040c4401010f90b140075070040d9004d040d0b2030400c801d20440c0110100c0780410101501c203400d10000341210ba0028000320ba55200311103201b0016198041c080d40d142c4040c2e04d40c40f08062038401e034240c50030b444040210800c0004403c0100c0403c0c0c1401148501c00403180020720f0048183c2c070080c2070180400001c4280304032604001c11401c020381440d481ca004071694803140d9585805040c0da5440d03461400b80d40400300b10b40508040c3c04462500840b6003406e040710038019003440481c081010076440b40300001c0c0c00075001c0c42070541860f8065401d01180c0000c80c501c030b00e0804a000c403280050101c1d50414400440c0256a0340d080065561564020070f0703e901a410918000c0c0c80f000f1042800c5000c1141e01003c001c000c5c1c18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 892775899 1250 892774649 892774667
    0x308100302060405120a06090302010b090703060b030a020318120901030f060308090906033a1d191a03092107030507020409080313050606040209010504150314040c05010807 76
    0x400b400103800d0600304020800c406440ea01240c4081c030a0344500d00200c1c90500420303204d240642c00020350140480f0500130009401441d02c010300d41840801c01c10001103904495001d841c0141c0141c03251640300c1c83d102c90342401461102a03201c1c80c40c03540c50384080d010040190030802d80f0104031074501e024160b81507654070321010340000c4003030058105500784030a142c0c0c0c0c003120040540e800003800e00d03e400340c0a1a500c0d4103c016488428115040c4450000c0031740940b4028101555683c4006ca0b0014804c0a801c00711406207030b6140c50f0a01c4c1380c04540c0d200d40a000490342d07100741d0001d02c01200b890341d001110801c85510070b440082c0c4081342501d40065150f8803440a4528190076600c003034442e0f0f844254100d0300305688460502c04604200017450062281c041601a0b5105a0408516140e005000780e44101c0c07040103822030710307a000011503003122031982160310b00d5030320311200390001e0802c0c03c5110b00c500666803c00c001c110820b00d840b801c2e2407090320355019035240c2003000c07200c000c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 892777149 1250 892775899 892775903
    0x1203060e011a0d110f0a0908060a0b0916050f1810050c0a0623180c031c120b0d0f0606080604081c0605060a17090a050a150e0a0305040303081003 64
    0x642005050311000c83d94116580b000c190000c07a91801036500303008021940b2181d02180000d40164080c880342505110080c0c0043c5d1b44031b8140304550082c400a9050103019001904040300c244d0881c1d9118050003d070342c14241c0441005445000440100070b0f002e0404854078032986071070f0000312640f4010001e807428101d409008101500e480d9907044000c04000c56000c1c000300040d0030721500300e08084001441172480b128105101080954002d01e4540c10707955151107a002000d0024a400404100035035102c00d91414041c1842d941500c003000b0112100352540001c0441000007c1c03101120304070352414860442040041d90b94600c85071902c0c001d58004215100c1000044070111001283e008400d01903c03000989550b640c0000c3c0a139446402c0e11804902c1c02034000e00d0011401c040740d41d1080003007000d49100079584e50f42580744c455449000301740040e2440c214205981690114464158440480e642140710b4180502190014031088000500090000d1909907045142c10304580d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 892778399 1250 892777149 892777199
    0x20310050112110a0b0910090302060a0f110c06030705071e080705070b03061c03030e0d0908010c0302030903090910032f120d080606071514010605070c150504031203060e01 76
    0x242c44010401c02000e1147c07900c0810141102c0032000d0703650701340206244481912400802e01034804017909094441c00101819003003800c01d841143c4406c03044940c03040180ca000d9913038019514001145450044503030170b540261079140e10801004500409143d80214102c1d450181e5a2040d2a42ea200032206982c002400c59000300d00008445458a48907101e41408104040811856440c00302140c40b400001900340381c080103040402e20400003966403602c2d0a620390b02d000c0c0c80c1e003652885002c05440c098610940000c0346072700c0840480303005c2c543c001203c52518074504c0000e680104038a01600740810510071030086460640c90305108400c0843c00341c0995079201000750340405d001801c040c0c0011007007000100003000c560310007160b0b20218000140040196a10050b11300050300a00d0501008100c1714012813000c00b0098111210784d82c08180c66001c18000b103a45008640c0028040d401e03102103084019019001141035a5a1202d00c0000340c1e03842c2c03009070f0180d88440004c7c04035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 892779649 1250 892778399 892778407
    0x60a030302120d0222090e03070b0408090613090c020c090403170705090a030606090c03022a150403020a02100e130213120b090d031116020310050112110a0b 69
    0x200b00c607001514640c10045801402c0c601d4901c2148100c0e00c1c0b01c9030460b445042c40070300b44036558407403048400340c6450800540c103106140c3d8414184502c0500090030003440880c00344030664485007107640f503400c0410100c010540d0790013000003818280c403121016000d80d01000fa01801c02c0c40b6070601c00c0750076641d940502040c040d0200a10800900f10a08106041203441c1607a281d100150009520500f070000d81c10303281c62024011105070305000e03401c0500410000d600d405203e146c00c1d4000d91601c00d02c007480981203003403514203d21031201007603010142042100340f50300410032041c8107000703a40011400400440441d60b80748551002580b150300030700e4201100ca215409800e131102204140880c858413020300403c683d504c5074046642440d02c4040040c6401c0501c1166000c5081d800c0c244034159456081015900424100f84203460036030021030103542d81048160580d010000c010441541c58401e404006403441c0c0040e2004004554801f00d2401c111520301c04940c1e18202c1c3d1410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 892780899 1250 892779649 892779673
    0x601140d080a1b05011b0221071506080a2003010b1003020d090b09010c170c18030109020d050601060906020a111908030a03020a030501080307120807120501080a0605060a030302 78
    0x7802c0e900b000d00c2070440d40c030002c1000004e0400d2003420120304095001c55011001414000d26000904045441000d1015030380c4020441d800c05580da540e5110f1071103031246202e0b450b95001401c0651040d00d4910903280e0007130910950303141e0f032024a01040440c0d140201c40505250030388554140403a040000c0501003d01c0510a0b40902140743d5524800714000c2c410303031113004103940240d031507003c1a5501c0c1020010650840481a084d04078a08519014074010510580c0e0740645803010316007500c0c2d2008120990703001e600c0b0200c0e2590041c01c0f10b400070f40d1410016640c507000d01921001c24141800031401d28000280b81989503801041001d0b08004881404445003480e05491544080601e02140090041c006018580c0b2103642c0140c9641106200409076a0107034081c00352074000300000070214030b40c488440c05500d01c60402c4051900c642200300d0b0480d10901402621910f040004a8a000007142803100c240c000c2e1410b1240c4e44070002001500003041c070006001d6400a82c1030b1030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 892782149 1250 892780899 892780907
    0x21060103080d060515130e040302060402130f1a0a0b0414060a0e060f220303021b01090504020a09031104020309060a050403050d0212040c0807180b030115080601140d080a 75
    0x181e40c10b11010101d156656000412802d50300c5961350700301204080350f404c0c01c140c0307501d841a00074403040c400d60b40d090501d920040c1d1128000341010b17000720602d801403003681100d41c000192810f84000e080128204038100100345c0e6455408030341c46140d80103c0041d04510800075101030380c2000d484d40328940c12480c01c00c61158050a150020b22201040c041207130743d9000003400655961f5248140c1d20040454004c20b000c030800151000040c400c0720920210781d000070341c1956145440e10000082c814200141c41080060388103c3e4080e00010b01c0035800e59201e003030f00c0c0c120b034484c3c0c101c211483d186104010a03400110303a182c05680c04080000c0c81e42c010754010581007400303410820300d0508051540016603108104282800d18050305000400008a6150000b00090b0000c0c110b07150900342403459001450410080480e118203034042103650079408101060700c00003219074140d03a04c1c140031392250424499405080301c400180d10480c1800031200f50115480380c0074602c1d00c02c025005503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 892783399 1250 892782149 892782157
    0x140f0103091b06080a0b01020a1703040f080a021e01062403060b04030b090f0105090304060e1f0306060212040605040909060912030608010b03150610121401052106010308 75
    0x280d44080c08a40e012401040c15450b0409000182c2d074a20140ca8840b40100a4a090003c514110b6100da0514004120b840441240708440314039a0756803a1030758101449035560000010b0300c43c540024006d014141c0014220300b10726402405041490a2400510300b00e4001e407240004814a100c54200050740c10208159903840c14140040c400351590300c0d0030f4054000790002c071400340460040c02100a420440d0f0f148107000d04c0000c0c031181c5032540226849000314401c52061041045401c002d03a0345441002c1030062040c01070424035101c02170b000700580010312446c0054010f4084140c000f080c081c08950941396240c4416140078035160407080107044040b8250744540d55207016900148441d1a600f007001c81030713540800d4460034040d0301400c442c0c85042081c4681d22042404100d41c1510054950010040b80ca03000100241502529a842001a0384040a00e410003108004d4008010141a15001c0e101584101c01b4013803414540c041d052641c3c0302070780c8480700410009039190020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 892784649 1250 892783399 892783403
    0x150f0809030a030c12020d15050607021509030f0f06040b090a0807030f03090807030c0b060d050c042d0e0601050a08031b03091e130b010f0c0807020d0f020307140f010309 75
    0x14802d405d0504020004980019201d1040f0340e840d2850fa0b00603042c00e68160024040890340da51a0007c20760000d60120300f01c1e0f420064007a404504500c840e901405001810052041514030744244e2022040c2c032148111000c940160142000c00c18503140040c40211503a48690050325113190760710103035103004262809604050300d54454100103488000503140347d0b80f007501e0b03222504034545000c242151005000c00c0c0074220400007200880e42c0000c03c503040c00c80903140041c0000d440c00e2039007605800204404001c0c0003241100d8402d02c00b40d4000c0048504500030703104682d8032a410048115554881c83c201fa0740140041c8607200d10441d5400b90b82c0a165084902d01801400411000b4048650029089800c0b013002059406c0200040e44a01300c00d07034040003aa01030200284c102c000344040740c4200841c9030010400c10132250708072400180c0040840722071a62a2901d11804825004100e00038044d142000a040d071402150034140200103103038161810a590044000301202c40301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 892785899 1250 892784649 892784657
    0x309041a0612191e0f20360904080d0204081b0f0d02120a0c0609050a140306070c0c050a0e0a18020919060e01060206070f0e06040b0d1401150f0809030a030c 69
    0xb94401d50105006d081040c810a4010700d03120b804a10b444d03030810b540e20792401186041010240c40c1d5081000e1a03c031440400c80e5400600d407254207205049000f114071002800c1e10004c1d0100e0f003088002603c0441030302404c01c0c1c6500444200610103d48480041180c102e00c0c141406001842c002030810354031040c42040f20006d203003c2e103685052090382d40c8254041032107010180080c1c1000c89494001e0a2520f0f805410f540c00c4c0c00100355034120041500041002d05110402000303944a140340c000d043c02048226913a80b145840f8012007001d48140b001585008106168034402007400b10504d13800525051180d0b039810398801e050840305c45078221890b0b07540c0c0d0100d0501e01d44980381e07020702000c0d4014009440c003524040c03c3c034001c91032400140540c000c01031091b55a50f80440d81560030048009445500390b103c80c0000e01503020b200c01d0112002400814211403146080c1c880b2000c1c0c0c3e1300e07075602c081c4208050381c1c3c542040e219600b81e80c00802c4070390300b164002e41140f902d020b19490 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 892787149 1250 892785899 892785911
    0x50d050606091905030f070b0403141603150c1b060e01020702090103060518061b071103030c0604061b0801120309031a060102100203090309041a0612191e0f 69
    0x183c00500d50512000c100326020600744000d0408010483c42d506041d0700524480307050a000683c00c1c011840002d0a00c60742ca0700d0790045034018000740c00380c19601100365841544074945100d000400d9803041c6056481c104140400d42c0c400c048600c20409011003000c4068050380380c034000741c450012003c0907907408000000c0180c07203065101e4001c40c012100062141000d40c541d040802ca003c404100da548540c00744403000c0300307203099080c10014040030103541e524907143c200d50fa01107140840b030b414000800c0d602982c2e4000b1130f24a1090f8401c610400c21000104002d0900004030114000066840070041c04660400390030711140340e029040c65044250341e41e842d800c441c220441c04030010441c990030701c143c550b010031100008100b080700139070561804080c2580e0f68040e040c01c05200d0745e11080003a6210000b400c80304510728001d890b2945e81c114045000004020949100d5458607541e001c06200c10464070454610020404031441d45511400c182c0c006004180220b0208503500d070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 892788399 1250 892787149 892787167
    0xd050f16060b0d0506040c1d18070306051608010611030a031e02030112060b0414040209072703140309060307050c12031518092508070609170d050d050606 68
    0x3e6801290b1611a4000709024030b40340ca4210030600e2a64400200320038a01841484010781009803607101660340c0c001605004001c960503e00741d084da0000c0d210f6840c0c0b03020f0042c1070000030170205095415032507010550341d940c4401c4424500105514205800a1003040c4601e8803d4104050307003030144902459070502951040b00701c1e482a80901c0054014000c00c130304000c500d014007000301c0811201009081051042c80720312100040009100701e8400c0001790314140104500e4581e04024102e6104000780001000100c2980707000561b40240140342254084400104130741070804060061800c64486103015511900b00640e140c0c0d250040c02200300c1c000c000600a1446166211010850810481d00340200c4501034503c00382c012806c1c1d400c2101142000440c46045c01c0045182d01d90000c464200247e065602d42084c5100e008800c030008000358000015002c1c1ca102d050001c080c07500308210299104240c3c5140b1012030418802040207030034a910595014102400403860500f900d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 892789649 1250 892788399 892788409
    0x1b040b041d060114100818010510060908011b08060607060207030c0213020307020d05090a1a0301060809150402060d06080d0804060608010207020d06020a140c0106080d050f16060b 79
    0x11100d41d01201510500792800144208046401010216102140502c0240c00b28001c600740c03d6840b403e00944030b0205400c505501d1010700b5028904008204504100c240d20689a030b151050b00000f03142a680071a920f4011b01c50042c1008091410755040840c14400781c83c40b08000300f03056449030092080c480130640c10b000601d0120b01ca641d50981003190f0b4030402c04629000700c6040d1b07c0510500130404c0c0c080d00011004030000060401c1502c0f03a0580001840e126015000115845228501c612500c444803002d1410b0315000e0300c540f045a42c48108499864510165281078110b4040125025003420701c028504013407003030004289962540c044516100b180025400020281d0341007000b4042039200b01000350846a000350702c0d120380c0343c00080c01c0700f517601406410705900042c0030201c6401440188040c201c441200350b29240d01e0540d0342d000340068440d03044140202200c102000d44228204c419258004000d24140350152481b01d143c0390307510204903032044d42c07800c004001d5618 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 892790899 1250 892789649 892789661
    0x504030f1103010c0302090d020f0f100c0203010509030a02190501110408060a1a01020a06020d0b040c081e06060a050a09170703020f0406030c1203120c050d0c0f021b040b04 76
    0x301c98500031410705409042c215929240780004240c814403000c100b03640d031061280300c120707012990110a0130102d40090740e44081d1100032503201301020302000c0800d4000ca60100072034000c4000700b240c1c1d40e5440036140c1701e102e4620403030010780252986505010904c418410218003601c0005003d4205591040084c0e00682026400c0e0340310300f08208040b00c090240c0c1644032490321a00203178030841c00000c0d598640e503003001000c090f000704a003100080164801180c030b00c002041440400400e5001901c00442603c0c0c242280008021842d0328240c2d9900c1d950103600040e16041c034005000c40121465049540e4440400150030340009030b0401e0b603000405190b406c0b0001c0d0060321b01e14410003900901011300f0718050b500300b00003000490031440c0781c1422102c0700c0b903110ba080c1d10146801c8400d0707502d01c42c608202c24036185015078415030100c082d001050300403804002002c5400e6058885206620079800180c1c000108450803803070214851060030005080440d80719640c2c4001416200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 892792149 1250 892790899 892790903
    0x311030409050411040608060703020711060a05070c0e0411010305070507050f030318150601110708060705070c06080405100b0409080d0c0206061e010e0a210b06030d1d010504030f 79
    0x1840b48180030a02188104080300c0180444040080d40d140846403601d40c04018841d206040d0301040d51070a018035a040546040001010399942d030500c044064515000740c84191942d840300c001c007080c44d8182664140c01190840d402480000b00080110b0103841c000380300d0070400506200d4000002c1041203030b0b00204030100c0141d034607803500300754450034040c01d1511010140c0c011a85940f441d030b5440e07030fa160888428a8113940d842103625000e840c181190b8004a4948120401c00c9000e5601001501d54030b032040001d4241550b0b0742d501203e030400c081d900540f064100300500342d4640c0f010b0388854811000500042040342080d181c40700590800c40d46110000e807942d1842d009642d041c042c10b54050340880f9041c40480413900e2034070302541d4820f409070611610626150442e69007103031903c020120152031208145046104501c0c1d0030307544c1002c0399480c4d89540400d0684c82d020a4035000001141d81d9254401d85000081c0b03055556100c0780d13414094100008800708001e606a891154 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 892793399 1250 892792149 892792151
    0xd021c0c030501050a0b15030615030a0207061104031122060905041a0714070c0506030403020124060c0206030408040308280c020a06050315120c1302030c0906070311030409 76
    0xc0d01e0760610307070300b035503c02400180c030340d440c0c007006d8101e682d5a000030b012a41c1c4000c00c030540300c1e0345d001c020454090091610031708605000c01006100c1c40650010480c040c46104248030001031185c04c10b00c64001c50000070200c080250740302c01c0d582824081040084041061030450074413034510b5030f0449401b034100100c002d403140100070a00c0208007201000e84c8916001c0368440c83c0c040801404a0307200c03010501d00310b40002d071741c1d4180309950701800003410000708036542c0c3e42030514001c2d0092050201001c004520391b200c81c4e0f489074030a2540310496115480791512111030b40c3c00c001040c0d00c000c1c1704a400150a00c00400407079a5540503061a5114401c0041c0c0b0415645607000780c8503c0000082c1008004c810780b4006072210110902142e10f5410140c7d180e80313a129180c4107540a0b0726100346c1051140000441c4800001070b88040541d0641d42d01001c030a4542044d820b03440100c0d4010507202007003095801c00e08000b402000e00b140a45404425260300000c542c1c21648076511000c80c503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 892794649 1250 892793399 892793423
    0x14011d1c080d0b0f060906190512070c030f080c030a180812041a01060509010f030e060703050a0b0d0c051c0c1401030b0402070201080105041e090b0a060b0a0903020d021c 75
    0xa0070301c03051400403120111801801d1171007030306c0000e034203100315406440491050043c5c05480c034060401d968010035440c0140c0580c1c1703004140105032913044841500020022000000314a0080422a000361000d10007946103a131180c18003006050b000743c0244140300155800703404280c00e28090140c02962400300c0165041c6800d00445c40001042808115031541c030040103800d070454110b80b0050001c2c01c028600620a0340d060f0010002c001070710303c003800340c44d0401c00704a40c0f540c003051098600390380401c00a05410148100e210170580002c000e42080ca90038000e03403030300900e03c1145072418000320300385101c95907a2010811441d4820035816a400c2300c024100d41e003600401112030426541141041c0040e000241444018401d0900442d6039403017008400326090104034101da9200814012041c162400034401c410403114910340d94500500032480308003060841322400465520508200e0454080029440c8000d0089a01c0f025504050410410300b110b0540060f015100e04050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 892795899 1250 892794649 892794671
    0x708100e0304120b040f06020307030b1e0a1211030d020c030d05070809150c030c07090e0606131e0c02010e0618030703140f0c0714011d1c080d 63
    0x5480d00503100d624140c00070710040c02070300d4000d00003140041d0403601e9102d464445007885000c500c103c00700503200038000002c203c2d01b281c040d009140c1c144015180150a1001500d42d2500040f1042c119540601d00034410009903080d45000018180281e101c3c503420815100001e1401c840c100782e001c0581c10540b11b264075803800303100304003c00042d400e0580c50030103e40e8a00803581f00b0280444e21034141e40281641700c1d1405010303a01c80005950803241e4491300424195a6201980308a62803181050408001c0f82c034045026401800040c0031800f881d80341e403003036030f018040c409850041d044a046181101030154010715000360031a4000281307401c00c0c516a0360901600a200c08882200942441c40c030540000c01c0351503164040c0b070010b40d0044913040d030180b80e100e81c0c0320131b485c2040d011403d00c4590328080381079012102801c0040900340c40316001500d007000c82c440e0400c00103245004100081c10900303640c020600240c0c0301d00d07075401d805590300d401c550005006d50030480c2c2e8410301d80203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 892797149 1250 892795899 892795901
    0xf0b180d051803191406103204051509090c100c110d03050406081b0d0b01090306020c0f0601080a02031b01020a0b190b01170705070c080a03031407031a060c0f070810 73
    0x24207c800e8030000c29402e0300703100c10030081c518803901c441c100004007059510301e1410460889a0400d000b081400a420b04420140c100094828080e02c2461158046000b4000c000360400d40c0d00006404021121007501055401c90f100250607521019035881880c42a42c8075407072684850b100c0d85a094945040c480e00410301a0001d00c2c03905a00a45d04005160803180d20540e16261032800c00840c0020070b134801260064450b500c018825130010a0b070416050010405034044484a821522140e030b8500000f6038954004501a4040e0048521400085007408400070b0511040c01201e13414050340c2d0f01d40c14024005c580c04495050760742000c071013050081c090020b10103c2460080307004c10a4100d5000012806081601403010000302c42c8100030703200900d40300400481c41650a4001c081c100a4080e0031140d0034110020890303800500300074003900c910f42c41088418003100000001e0b400b402038030b50180841140500c1441c1c803605100c1c400f080504050404c000103860744103c440c158030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 892798399 1250 892797149 892797151
    0x503010f050927011b0e0a05060d06080304080c010f020d170709030506100807050d0b0a02090118030c090c03050103052d03040306060f050603011a0904090f0b180d051803191406 78
    0x80100555000014455500d8860010030342340125009581d90307609a0502000344002c1e4042c1b5040d00005ca80080c0840d4049215100048282c0b656035041c0200030302261501c41d1001154042541c1c4a0141c001504414070390b46d1020b51800d003540d1f00c580365141e6a01c1c1c60313000c880a07155840004410301080c0b4052024100605007a00c425807004010344d29002e6004000788140016a030100744094036078850f007003030711200041c02e0034024416181d0401907907040441c000c01502e21b003040c040c0002caa1007440359a04aa802202030a840450000d801e00d000320f90400f10303101d001da0f0703180001d11400c041c0300074070045104d50800a4143d141141c500b13092100782d80030b1482201d043c401000300550040070000e000c04a00e40380c0d81d80780400c0b070010340140395222010b005210802003007030400804109e207034080c101004c0300500f01c52801c80415610051205c1c490001034003031020849020500b1389404502c00010b091321248901c1d84943c0d84c2d50042c100050b00c1d50189000361f140c6c40c0209020036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 892799649 1250 892798399 892798451
    0x6180309131e0209150d060b0301080a06140c07150605120d170412081f0605030612011a011412040501051603060f03031b050f0f0d0503010f05092701 66
    0xf036061180200001341150850b442c030b065041c0700040e070900000441d910032005040d070200c459849585a021555a4401d003034411990546044c0386110384401c40c12285203d482e132a5071041c50261280da4030b000c3c090b100e007103a90301071383c450201181903911307031520390a4460070380b0080c6848111600010021000d102488d0484910302e400c2c400807070310322525020111340b140ac1c2004291550f40003400c10030710b0ba5070441c2000008580101e91503a11100460041c1b40c11141c5d1a42011440342e4a800c841c00743c2c80410302d141c100c40303804c1d10950280c51800080319410760480d041c00580c03040c484418070102c5080300d01d6556001040040071916034400c484841a2501304441410503014480d81c00150101409100300c640540704e0b03a511000b8000c0002c0e6129056480b056001c0c4403160362540d20218000c001e0013030b21020340303680d0711034016a0f04072200941984c4840b89024240031007504003030030b01140c580c000c3c0c0720485031890070251001f18182440000600e148905c1004095981032805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 892800899 1250 892799649 892799651
    0x10209011d1c2a030201110607170606040f0b1909081002031306180b01060311220b03070c03120b0d0201120e0106180606030e06180309131e 62
    0x80c64506440346000c1c105030895a80c04280d00507400d08210310f240d40c03810076204400400001451442d00e00d0103015040b207100b0b032511900c4180340105951a00710407140c850028458040c3e18a0900550101541228016110a00d1f003078845038095080d640a810001c903450000981001503044085641c80020780307850040542418014000d40b1441820f8261501507004004140c070211207038498468154400404c0048101c001c600c280810540031041d6919012840002142406400348012540f2103142c00c0d85054244810300c40342840e07000703900d0740158400001140d84000900254040d00f805d0b12120003040345403030700410801101c1c40194106007000301d80c245c0c64440124101c101c2d603090070100c26400100766040c0080005040740c00042d800e1003800039030119030380001c40100c100048107120080c0c071080194103642000b0050380140e0700007000142c040102c4071a880909126000f03807494990981d0009290510216070012129074039910300340138540100d4107035100300c0c250384 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 892802149 1250 892800899 892800947
    0xa020619020f04090b01030f022d030603281205040e011e030b15031b0112020703081b07060203010603022124031002030c030603070e0f0604022a01020901 68
    0x80140b95406a4480c40d052262940302145440e07011b0340004504041400c811516401d00503141c403494840200c00030300b140604181b02e411546030108481c861703d400b0b002030010700c0290401d500d6810600201c101c802141d940c0c401c00045a2071007a20001d01281d44203600c45042c00a072601c184810791005040c030260011000024420034091400c0300d8006a220392183e84124411042c4224841e425901d07014043d03040b0301502d094001c130340c1a0076080e41c8015550b00e040b5400c0c1d00302e10601e080a40490221f00010b5403a810f011902c00030403803040d44903402d000031940e61005030382007030b049940420b40109101055101003101089a80000304101e0028105504980d507134403450407005911485204c3d040116031000c10820a19003d440000c541e00c1c5006244119160001c2d11094441d024254000800d0007680b8806070042c541b6042c0b56010391a1402040025030118001d5495200b031480c0f40d01001180d000d503a00400c50100000d40c1d04c0c5c0d09040010300c0030000f0050758080ca005a8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 892803399 1250 892802149 892802167
    0x3190212100f060809340b130914040f150218100206150603100f0b070c080703050d1b0212070303080c0a051b010b090a09061401030f110103060b0a02061902 69
    0x3a451b80640c1801d40d00c0341e40803411009a83c0e00301850381c0049440712071094001403461072000200960703410f1016911945450342c20f880165281d41e10402140082040841c01240fa020300d000d902901c1602074000c00103100200f00142d0304041103061141c020903884e0840d034188100c0102c900111403014142500d02096442c80c40c0396110a40ba014410100c001100e02501488490142441050410400d6034401200380e541d84030020407514400c500f1ba00181424000171048182c0fa80300c40940f0404512500803900300300740590300e100046178a000e80006d41c5809d00401c1652130604082c1c8000b03030540c1800350501030b01278442200300e00c00704030f00d04410b036103c070640301d0001d43c0e0500301100400d4800d28034050040d01410301d5104042005208203044a54468044180f0902c2e041c03209540d118034203411801e00b480060300141842e017200c80010a8044411010a814140018420344a26651035503411814003400981c1c0654280007003003405031111061250020070a41c5410040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 892804649 1250 892803399 892803403
    0x1091a04050a1d0d1412070c0201140d0e0f0d0f03180c0e07020d051303021c05150915010f05010e03010912120e0a020f090a0f0504030302070b070c0803190212100f060809 75
    0x408100030020300d1301523801160700c078001640349052203120441e1615100c0000c4401040c1c6500d1901c01c074811b121042240c0380001c40d450505c02580d0b2280154018100410f40142136114121508a03c0e4075865000203449840010090401000111320501d420140a0710b81100007882106201d0207102d60344091380c001003800140c0b40c2c15500b00c2c1006140035010124031003c528020b003240141000b201014080114a038400c2c0650340458071040c00c1d522071010046028000c41070007605016060000794090149100f00900240c0009481c010320b44800c280c4462000c01da0002802035003014406403821300990281d8101d040c06015803641903070000d003404007035105160003100f0003000919440701540c40503414100b01c4009000620b05031400030001d6000002c101c0324403840601003214039220707031115903015911000c1603145440e03500590130b09030030800d180e02d04113408000f040004849299070600849001030b0409001d4184082217101020942002e400c205512041022080c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 892805755 1106 892804649 892804651
    0x30a0c120504061b020d060f0203010611010209030601030f05030705010501030305091002011e150f0906080f060c0a0c020a0b2101091a04050a1d0d1412 67
    0x300100c2610140594021400040c041c9095001c1c0310700c070310324540c02860000300140441003071a528001034840c1c481c520700580e0b03004801048540d03003102c00b0444400521000750708103180e10010a95408051202600c482200c0004405000d000d00c01c5405158000c0000d029a40e101d0601420316031241d0f00d603a014201015081d030741c051062166001264207034400340d80c40c00480d03520300081d00c0c2a100e030624611405000040c0207003240c0e07245000740302c0c03a94049625454842d01609183d1280c61020b0031f50485803c1000720100c26007111220801c504003c1118680380c0081644c04403540c119480b0204001040c1991842c061150039801500195900d0583e8950400109503501100c010307081c0c1070400b01801243c54240c1003540d0080d070142000030b00d46024095407642d41e030b0030021040e10707801c80801046040e501242c16807903254021070403403500c45050503070080060 = true := by decide +kernel

theorem cover : BRFrame.Cov 892625899 892805755 := by
  have h0 := BRFrame.cov_init 892625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 892625899 ≤ n) (h2 : n < 892805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
