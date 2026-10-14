-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2690
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:27:34.975854+00:00
-- url     : https://prove2.me/submissions/19a5d0ea-2b67-482a-af80-5647664890d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 483633093 ≤ n < 483812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 483634343 1250 483633093 483633113
    0x11061c0e101406040f1512021309020310020c0111070f02043602040603051e060601090b1207090504020a051e0c031b16060903020306070207081f02121e13 68
    0x1c1e03084e1000030305001d1102800d801072440c0f40304c03102060341101002070341610440aa00040b4420390321500b402d2141385c082000e445503103100941c942c0005001e40c019503001e0b40035140721118034001103002c0c444814424140c0e801b40d94151101e08210380008158201401a040e4102440050b8401540c0f021052444200c0380f003202d24488840380c15082c00c0d540d40b40c00030340195070008190380e02c05080202c00d40c0c40c0d0b850f0007010640da004060002c5c81c0d641c0180251001c03260281d1a00b850403410200034002c00000030048020702100346408a075035100c51001c0c01d0504210745560740d031420400c1500603c20201198045088410408083c5040010080d18110801201461140c103c0d01c0d01142c00d1240340c20008044403040700d000110a94440b0090080364002d406485c016240d0340002c0342c5881881c000da95a66021421418188004019415100007851001410310200509140b00500291085000c0d207040c03036010011170b840031031185d4111100c1c507418110b030105a981c80801c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 483635593 1250 483634343 483634351
    0x21011030301140f060f070209010b0703080c0c012c07050a050d020f03071221030c02060601080903120a020c0d0906081612020304050105041506050d11061c0e1014 72
    0x4110000b6050f0007902c6101d142c89005400030041516010444650000e0fa00a410f0a07445101c0003000041c0700d051680449560f140c0582d60b00c00325940310040d4940030780c041c20544100750358813a10308066540034291440c0c2c90030781d05034540d40c52000c40c001a2400440c3d0b0460b611135101280c0c100810769032040c0501c00c1c541c1c107844008070301e240c0b500040e041c10a1503228060880f45a0b50310b00c00c00ca5281d90041c51814000d9400302004444081101142c0c030704001c6502590121021800c0c96000d588841c0e8003112500c1102e02e84091068051069401500c2c20032131680c0110300c10030280d005000d8404075041e5840c0448906141400040c280b0001030100b07044c0d204110180c140480c859812050300104202e010356a07400d0524005009210031181990074030310105495044200d14001c25048801c01440e12207041c54503154400040c442c03c0b9000c2d0300c1741c8100980f18030601c00c043d0503400c00044010028419410094a0307040003a080350710040186030500811951038816821604 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 483636843 1250 483635593 483635609
    0xf0605120718020f0c0a050d0f0c0f0c1203050d140705040b0a03060f080a05011a0d020906180403020d08060301151202130e070914010e071b0f030c021011030301 71
    0x20703030000004002c000d10a10aa140c036a61000601340e03a0741c0c2e070004070302c142244100d0846100080c0c2080480b055140c0780a1000003524010f00c09012a64010b002d100e05406100052103959680c0d0940d4401d074066101100401c40200700080c1d109501c0c80341c000e03500010244a141c0c1e1525502c000c229100e140202d680c1e001001c00e41c5442240310b51f1200c0080d002d40f075500c071011511055001d5950b000e041c000c8400e90700308176650383c4110302c0b5142d00c40f8002e00944411820f100a50810000507801413000d03070040c0850b00180c000400030701c035080c042d41c0079030050246400d610702d000300721440040c0f0050084c1c0c105141e40c4c0c02803c0510700001210344a80b2402e041c0103240c0300081b98031f0405203000c0c3c207540c00d1020403d4020301c003207400021154900c1c81001034840c0c50b40c0103601003009110300d000300d8590000080303026002d03501c00010304200e41a11250036000743d480307188405141100f40d00080080c078801e0114240381c40918003061403410305000e00c1c80780301001036131380c4814050340403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 483638093 1250 483636843 483636869
    0xa051e0307150212031806040f050f010b01020c0132130b16030c050c04050a0b010905120604020118090f020a08090102160201200616030b0105070c0501031812030f06051207 76
    0x1051b1100c1c0301c10800c03c83e80a40c180c074258100790804111500030810180d40038010704403005030466051240b09028a0103802922a019006005650f0b142c8030342d11340740300300310350582501c2c01740d80b0300101c80d0b4404031400440f6203420003c42c0d154900310b07090b00100500c070700c10400c120003442a10718101d00e4030f80c54a8020070b125840d00d00181800b5040c405160030a040505000c0c40001d25000b45256140a0341c4040c03046607141d00304240c900102e44050190340159020038090b510a200719014003022501d0790320400e50f101d4980045078241611004000d0740410000406540450160342040c0c202c8006e504001c080d942c0625003241241c0024140029501c10044d14010388040d9100800000199101c91900c3c42d1b4480e040c0f0382000c5d884002901d00800982c00d903018000795080d19810072412610f1b00e085c100103500914800e01404140240d0101f450b00080010300b020300002c1039550041a601d10280c400b4040e100e080d0005d034441c921178a82c11103585400101e6200f03d40c40103041034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 483639343 1250 483638093 483638101
    0x120207120507151704060c090e0709080c0105090109140301021902030a02161409061306060305010e0a0e10020a05040b030c18040c053405061602010c1d0a051e030715021203 76
    0xa2600c8d6007607803110140d0300500f0100950240c00a520300b0403038442c82d05903803c1d83c507040b004440511900d015a4003090461005000429440c940103031048809400141b61925429204242c0e07030103201e00600680c000030700700a80d294184101080c1407078641e1100d6510b0708200c002a440d51404100358020906400014030755520503110b41003c00d410f980400c4074035128500100608003d000751101120044042245404288140d0510f071000002801c0d00803002d001e120003030341c400201102000401d10010400b04c407841c00840c00740000e685c5145c2e0301c1041c085078403c4811589280b0f0b01c01ea2500c3d4104883c9034011301220300d244100380280281c00e0f0011220b0041300c2042082102d810460441d0a003005030018060b070240901042c1c000b00d401c4601000c90981d040c4002190016a19200803e51450100c001c10310308000140f10704005031b01d51020030141311944e2803190701581d00c210240c0e0310703040c1442030a0241250079040319071504505006035071603207143d081142c4044004001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 483640593 1250 483639343 483639347
    0x1305010201060320130203010803090f03190b181b040e1b130e0d030605090c090a03030c02040e011e06060507020a051216081027120207120507151704060c 68
    0x14017240e8a00b280464495231030301492a9640c1100c040c650140803180681c0d82e40d4600081c1c40e41246002d0a14014001703034a54800f400840b02401c0c2081417901c54104064002007400341403d440040364a00701c13024810401c000558103c18a20300301070b001103503a010080c00017a4411850704c0c007621005400b107501001c400081c40d04400310743c003a0080d8042d00320041c2e419045041112001c403200c48090311140f18075802c62180140850340401115000c10029018521219040c2e0008000160448003000304900707503002042c2820040b4a40c00041c400b400e000d11401c405003100340707401800e181103580403c0c26007130103000d9144200040481c85107414001c000e4000d012100c0003007490056035811040d0fa584003846a8a0503842c10003030301c0b40b01c1c0045071845181074050041500d5200080d43c851000d10400c086841c405c40c0038521022900c1000c4982c86940b4034407903001000300c2442d040300d1580300c840c03400d1702408100c01030b5002e0721112083c05d46036410980050340040c10a920404c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 483641843 1250 483640593 483640609
    0x50a020d0e130e06060102070506162004150f080d0806090c090604151409010816110106080a0b0f060d062a17010b03091b04090503030c1305010201060320 68
    0x400501801c0a140d0f0f0300030000414114043c210a800f19411a52500f040007910b014240d602c140e00d28600744408080b99001d8590340713030145822408158140c0d4440420705031220440302d005041c003003c0007003011103040b281e03800041c04080d01034a2952191440288180c5001e00654415240d202c0030401c0c2d40b01040071580101c20081182d9656913a83c02c540c84081710460451011884911114074503140920450b030700380034141e44480240c0d0725000101144881d4505071030400860440030110400b0910802c00a400007500038008060185030210140d40d00424039007291510ba000e002c00c0c2d4441c101130740c00b020b60001d8042200c03404102c01e000303140d66144241070100c5007001030004140e00290200b00e4408212150307000f0303030b8039840207035124070040e0780d0f148040d404002d05e1114603204102d545264200140081074036032150700d80c645550425604145034060015040b4070507203191072200d005000c01e00003444a2443c41e121b03032200034251140f114088450b40c21021455a070582 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 483643093 1250 483641843 483641869
    0x1b080118020411090a230324100e180f0102090102120f0d060b0912070803041a16060c021c0903021e0d03051306080c0d090f0b1e0106050a020d0e 64
    0x413800318005d0356842a400b0501c200b1b02814081c3c80c0c9411034025501300070507a41a1404000c80d020081091201e2403103070820010845060001200d802185c03030700d1620096030041201c400903403080c5100390301142c28070010313090036011030784100031421881e40c002c00d00c045100518501c0e0794030303150b041030b81100911440942d02402d074544140495041807420240c8030402003982c1c2900a000b1784210543e44883c5805094030b158000c0c40200302041941500c1c25500b4804895141880904110354417646190b600c11a042e9888803600750070035038100900a2801c003000404030840940700d10140c45d070101400045d006001c400020308854404880d40080f00300d003d800d0705003881c8542002400e0b904454040d019000c03030750310b0018169101b1003a140c06144d5100d0710310324041800100300024001110100c440001c8151410301052501c004c0d244203080206601000c881f403c03a4440c1c000105810400a1180900c0602401907000507095810040b038240702d1009030620b0000340d000c030b503524 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 483644343 1250 483643093 483643099
    0xc01111e15040b150111070504020d0209030106090c0314010e04030507020621040302010c050909010b0a020109080a030b030d090b0d0506031e1b010e010c06050408070c031b08011802041109 83
    0x1c401d00c4104110000031520800540081d50351186070300c0011501c0d244140100c0141d17620075030040c005450154018200020070200040c0343c5030711034010a0940d0950703441015400d070395400705040b4a4060140c40420080441e000703800e90304000c01e00300c030600060b20190411401150010842d2106011038140d0b07142080101c000058200c0981e9104904650460055080c40c42d4880418060800d031825500c004056004aa08103400031040d83c0048a40104542d03e13a602c900210f061400117203100501aa804141c43c680c0b4814186003001c03609151040000d810800c0000c0402c55003030f140c1031100c80304041419150440064a080710720848090f000340d2035040c01c00120800901d41c09403040c14040c0902d46521b00c001551684003180071580480c0e015a0744034006103082d400150300c5807107020729500300507007500c0b004045031443e0030403980380040c419801d0041030390719480001003020340000d00c41c465070700900380320071114820300034041ca072030304061074001d1100000c1d110425406 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 483645593 1250 483644343 483644383
    0x90f03150b0a0b031b040620100509550204020c030a18081c090f030c08100b130b1809070501081006050a0e03100c030606020c01111e 59
    0x10380840110b90710581345014910b403105c10072400c43c0d0b040c500383c1c0c0c129591a225801d0360311405100700c0510fa5131045881c139901541030f0310414400d0714814540503481d2040105000404e50040c6000d806090800503510141c501500031011042552101c810b5448041003450368500c030091010f805e403d100007176100b8004a600c9102910000243c03404406079503403246003031030a045c02c0ca90100c15002e0f901107a04186940c44066140d030200802034000c03807800e804400c1d034031403d000c000c1003690000c0301c04002010040010310070412000b101d40f6218501080342000160008000e810b50150803070107a81c41e428007002d940d0b0703100c03c8203a03c100d00c091010f0046ca03007402881d0300ca200394083c560209603440b0210b02401d034144085002d407903c82e140d56240500448043d01d00e0403000b80d40d00e500d8031403104c170038800d07030303143c0c06040f990034050b850120703105041801c040c0c2400d880d05c004504001e0800c03d0700b22005400038244d040e440c40d11064030054038100106505280b100d1440d0461080c007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 483646843 1250 483645593 483645599
    0x5010f080624130c080a060e040f0f050a1406100b19030e100906020306210d03022505010e0706140d050c040f0308120703090201170916030302010506090106090f03150b0a 75
    0x1ca0002c2c400c0c416800d040107d84e03110044c96445440954000d0981c10800d00b41000103005520703524906801101202c10304110707a5034000c0d0002d0000388803101a00070b4014403840d4003000c0e205002071718042c56003d040c64403018035036401400002d20401019151a50a0b00206051044010324000f0100502c60f10100c0d0030070f2000703544140c0e0320341d01400c80c2c5810349490420752000070f201d03da410005030680c111640f50440103034000b108454150440c039441c4003862240c00c07210301155031003000049244050003050714244241d0341d01030424842401c030034516404460049614507440c2c401c0008064861035414141c601454109034030b41003046030084184000240900040880100a40b551b40c0c0c54a030218290381c0700050080c0030a4140207a0304403da2400200c0d40e0101000c4d04841c4d2440014001d111256042d81c0141c01603551802804543d003048031440b80944001e0400300446172900c3c5082440c614148801b07040100340a41d1055100b915420419aa00300104602a440e407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 483648093 1250 483646843 483646847
    0x5150304030c380108101b08040213090f05010c110a030c1b060c060605041e050402030a020907090303021b0d080d020c240f06150a021204030605010f080624130c 71
    0x3c01c2c010780b807452080400034405054540503841014030000c20900220711201400e45a6240c0030b030040380d02c5a4044040c240c1010755210344601c042c01032509110006403410014215420000d4410400c2010341d00c2c28681c488c0003c4881442e980751604202500c1c550800c2610603c0120510061081c8000c00050241d4002c880758012409501d0070050300e80e91303030b003003104540b8260082046000240400310252502e03500040c2d00a00140503504e004203d9400201880c0d0101c5510340072406212050092685c1000200c41b41c600d4201d84400c6036481e0000030f8180001070400802220700000e282d4a100d840350107039001c0341070b030380c1c101d070702c041c0b5074010412006c41c02c00b40d5980d0710106613001510500c143c0041ca07000d00e0001e00002c11a11003070304804440e0340240f10a80075403054052064075000303554014802113000c2e00d0300203000d504028100c08140b980f6485009694452801e0000324100c0c1a0425014000d200301c0981c6150508081044100800b4140c85540d1030b201c0000381c555 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 483649343 1250 483648093 483648203
    0x603050d0c15050106020604030e030307060507080a0c140906071403030108100b0303090a0b030a0b210d020a03020d0315050909060910110906070f0b09030405150304030c 75
    0x58850b1001c0d40e0308140a80382c2ca401c558091043d02d006038840c3c800f03d0042800744004400d01d040280590f03250141544680381070b00d40c1a01e45c0400030711803500b0880c0d400300074420060329a006250900785500c00c419200d40c540500501c10f0b10804001807403608000d45c0e10100c1208004a10549460350b960300b50b9651078082101c180109103041c1035a01c26285004000c4419986008052852442c00c0800148107500002e201c100003a58640c420200769407903403030000d014452503211420341780094551794181008030140b43c0035903124074018800280c0118141000c0d5105180000d0449c0341282014151000380d4491500b000c545020b00c00c0c0d1010108066101d07104150482d4240740381103038804104d400824800c41209414840121140b038058020a12680a8010a059007529480340820808283c4098580b0350002400700001d00305820a05800014070356510704515081c0c038050406000325a005041d014105000240e00208008ae0b103030075034103444c8202e11041c895046907260703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 483650593 1250 483649343 483649367
    0x90c03081305090a0c08250c061805030c190b150d021c02030715051b10110415140d05091509010c090503030a0e10090b03040b040b0603070303140d0603050d 69
    0x31040300004400c0c4001f0305005000340e609030000000300b060640c0880c1d040e5048401121069244e40ca402500700c800c510440d0581c0c004c2c00590350318a2a07010452514101600c007994500729a1a82d002181e1040000f40d40856046c540401c0c032014400000d882d154050402580b094410300040544030300c2c140a503508502c00e901b100c0c00139440c1d11102048a00c00c1c9241000620204015040c03030945c54442c0303902c0c00f0001c0844071101d000810b64403e071024002202001d5601103401c0150400000104c400c044842c248071000d4503090b10a00030341c0c804c88401409280e01d076008110a181c0030440a0392a200400b0b258034582003289505010b049011409400144071840100701c518010085551742d5103980c46201110502006002034a00000300c1500ae01c817103290005182d09040b002107100703900c104072070000c81c42c107858a20640000500000d019510415080c00000c2d00000302c004c0c03200040560030b07101c104500e500380203000903400041c1740380100e2050070080380d000715401c164 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 483651843 1250 483650593 483650597
    0x50f061b010f14091b010513030804090504050d03050903070201033804062301080c0f03070504091d060a050a0b0a18050601020f0c010e0109030501021b10090c03081305090a0c 77
    0xc113441d001005130791001c81d400c041a000c400034600910641c002c0d4014100c0041c83c101c110001c3d035903a250441290020f910450f806030f140e00c200010440300340030410b54580e02e0300b030801890510b010100c1c2c2d0b0b4003072240b000b4141643d8920181c0c080f130180781c4002c1918503ca01c01c030003504844e17100340601c00d4000304050103541068000f1466560640c0103042c81c80b4800d04030b1110707003130042c011124080c0181a55100728000c01800400914000c001d5208803419181d05a13110300e030080308030803140781102010390345c0b41e400f2082c082c460006c118240c0041c8911000301c2c064584203611402450800000e2346d01002e410030000740001c141407000b084812a00080100d075883c40c1c01a6114038080b0b5400b0529009a00f521005600507032b0070018a0170107142101d4040c0d01d940d6610708a921803002c1e5a032903101c01d034084009190810581c143c61200341400c3c41080410b556515459403c0c0c04020300b003000105400300e400e00035044103c001c01c00202058400d044c42d000c900000c01c00c070004000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 483653093 1250 483651843 483651881
    0xc0a110109060c020d06090303021215031504050307060515040606180f32090f0609161407150612140102070c0905090c100905120601050f061b010f 65
    0x142d094095494039011903000341805101081c5603031460000d045c04442113046c1030f070074000c90406258104d0400e04c07510382c5540c2550346030084400c0614004032200c007400c441303941e00200400544040195440f4030b610540100d12501d4504000190349405003065030841c1c0740160016040e41c2c4005202c54502440440d03408882d241c1d520084842000d0040e060710318804400e510035403884414001e8801248503000c0c6645074001c0c0040c0d8001d04c1030b0b880d41c12900081c5c040c0000f030f140021505411480415035840d504100d81c00c0940403500c25071881c1b601c1d0300c02281c040140541e000303002001c044404820092107845490400c44002c90610607100f0102103000c0841d105814421101841c1e040783d02010388a00e08558800644001412460035025503460090315480d88004142036003510f8131080402401c080a20030551511000152260722100041007103441e40c0401e04840d2105603596540e40c036014800060103408141c44900c550b11f041040616003002d603000c0002d90f02003011080e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 483654343 1250 483653093 483653099
    0x20711060a0c0201051e0415030e1b040b131b080a09030503060409020103090606030b090d0203180f01090f290702010e130b060c1501050a03080706110c0a110109 71
    0xc951402100021004200b50301a150095070149001e8180001c4920591342111302c001912916600705902010b031120291041840181c1c0501541c0f100b6044040140410018000070300311400c05442e41d44e00070395441c0c1c2900310179150a03001d56504151070b4010302001c103540c050811812036605000340050584804140b103084503005e0404040d4240e565907040d134460300f04000c020410080b003207050594440c0000c00042150007150001e500800a50540c5d140544895052420220b00d15045410410085003117101c0001c102181d600d080d150800300b4003040700140c0c0c0d0f5510540000108007035032200003640400c3c0380c1954a40805200c211703000480114642845030184202c000d022804069024005080c191288840c810800b03102103100242980485c1041d404100004401d802103000c3c190301c502081c0e2100d004160540d0140f031254515299103070b40c3d004125006003502d80b14040440445804016616100c803010291010084249008050084010f10182c00310b80c11500c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 483655593 1250 483654343 483654349
    0xb0c0c010606090e04060c0903020d060f11070f060c05071e0309050105040e16020106090e060a050f01050a150905150c01110f0f09030312040b0f0a0903051b010b03030d020711 77
    0x18004507510307a03480c10383c3ca0b1106e5075000080e102c15410b4208003d188076001001d0b982c3e446400c02401d025500010308034600001300c07020303100403030141c48a2403820070030000024030f080191080e03560841d800141400c3c010208850500c5448c1000e86032901c3c8044003160b46040440c04095203100f911901c018a96681c01500c44c1d010358031800d07081c42c00070340c0080d403a0b5000780000301d00302e110b51000141550f26420301d881113a0380255043c0041c0e01010401020441a10032541c106c1c00700184c42c4a1503141400298800c5440e02416000744c545001400c5803501070903100d0040c00b401048000c8402c054a002c00494000c2c181080c0a5030030a5821a103215644040380c220514403500d00780303040001c10001059600144c81150503103c00c00154421280040178580114400c0f2144040341c2002100c0c0c406120010f40200300301442c04500c4000260020211040d40c6141c1418000c04200030301200c0c01001002c1d0b08507058000001c004842c0e001c1c42e4024084107225059020200d1048024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 483656843 1250 483655593 483655607
    0xd020f0c090412020a06290409020d02060703050913020304060c030c081b07060c02011d0304051026090d0f081e100807030c090606081b03070c0b0c0c010606 69
    0x1550801c80200118000c502c000c078640e000110b03140125802468655a40012a000d2040380c01c2076040e00202010000900390003c603042038201e4060000a44580003d03d1341c45c8135004c024440e0000046104c20103024405641002400400c00500002880c4941c03000e9070040300c0032200c4503e003100084c4420f0007840340c0304040129a80b1000c01e41c0d0340c1e0040e90000c0754049101102d1507814003a0308000340b2103004e0718000c1115a80081040600c00d1075001030796614680c4140960020310041c046034540680d4582c5103000b610f4441e41854422a0344107242c0064100c090800030b40d401008400000000d08401151050303a03010700e004140b80088880490030744031048000c6000c02c03248074241001000700d402ca2500600c0c10503050f9204500e0f0b281007241d038001c82d00c1d061052020010440d0510030f601c0101340605101144d40342a29003d01c0b24000329064075075807070010021954542c071841114013102d600221000d500e08000d0f0f03020040d5005044401c800e0760800310042805849414 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 483658093 1250 483656843 483656863
    0xf05040f03030209030c0603011202100914010f0e090702011d031303060f0e24010b040510030905120703050415020f0a060b0d020a06050a080606090604061412090d020f 74
    0x100d040c44480041c0e8049010398010403029505114011107001d00e565440010360007803220000a0b4690a828418460500072594130300061001d200d40800072000f47c003c80c612448001d00e807039044000700072000d49405081c9501c054019111342c040003101d940540c852025104580003044003840080c039441c0c1d81e4810030941102181850030200001030403604000b03aa490610408079148107510407652400c0d1120070b95007000d501850909010006034030304103000d080c1d8984410b29090a040101c1c40c0300458800410805a42c0d01007e0140700c014000d600b0840507044071644e56400d40c3c02c0062007a007090003030a007521a42c1c030908011301e000141c20040c103400800a042c54441a0315800010007182c13441d16004200d0034030743d000517681c1d03044510180006440341504c07003851200051002c2002412180606010440b40400d59101e0050f03d08803079680c41d003d800c02918007011004c41c0500c00030b010741e803101c45007031204150000c510841400d20307a0f800c5500131510580000d594a031510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 483659343 1250 483658093 483658103
    0x4050303040e10030618140613020906010903080f041805090a0311070e011203080a09320307060603050f0a0f0f11090a0b120c0a09020310080f0705040f0504 69
    0x441040702c0346500900ca50f002c0c0c248031425040d550f030398403440e007a2000300c1c0d80b0301813007050040c84000700b000f1028464113200d1204020a19440d0800c0c405011404481c0082d2041c00c101002a10782d030b00c80d84520740510740c0904556202c0d4840c04041d02c550b045800f481480500c40311005403d0022842490b100d401d200c0000e1a910000340c800380d82110305103219070380c2030040343e60200340c400c0620301c1140204000b003030113410400c05040013000100060100074403a81072448860201340c480e402620111458000e10362503407000204071aa4010f004090405400b01054141c2448019444141220302030310590316003c8004a119480d0b00400710000c00d555260820303e00828108400524800d124201a00911110200090304110102c1d05c44100e079031a240002c099040012200c7c0851000c40002d151718024080020f00791050390207204112680400080c1e0000200c2c404500144490000da8402490050f60f184c0c07120a140240c1380143d0410103040d042c06420321400c0d104503044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 483660593 1250 483659343 483659347
    0x150e09041119030b070203070201030b12060f090106093b030f1308010906050103051b01080c0915040602060106140304020d030e010306170604020312090d061e05040501020c0c0604050303 82
    0x3001c20880198051000d4a0b032400080b400400011100051a4040d00280e0003c64488003203100040075181990315240c02404045807160820f000010203d4100320041802c90242d541c07585000c0c010640c81c0d011050150410740c404074861000200d0800d0f41c10b0000c4004407180d142c000682c0d481444141c00d5405600810100900460910180001d2003000c480c039590165110000c500b55480f0302010b8400c190780d80010000c01404000c0c10000c81d44000300304000b1030f800c10019000c0d40f002001d0080c50803001400d065540e45210f0782d031444404a003902a152911418000d41d207410034029a03000c6803541119404070a8140107817449903500812114a400c00d81d0303000c4804900000fa141c0c14162104130104203010410b803c40f07000c03414403000701400e107000c0c010107190101c8030804030502c102c10040542580c40740d00b20030710000e8000c540410007ca100c824541c2166905480070700036454402813208209040d001040341140c0c92040300c0030103410301c1c10407a09106600c240e652561003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 483661843 1250 483660593 483660623
    0x50f010b0a120f0b010602011505011d06090406090507110706021f02071103060a020a09050f01200f1005040201030e070b042102100503060306070c0807030c08070c150e0904 76
    0x91020701d80b81c030318400d150340c2410000559406294034001e030410009130351288000b1400e180c550704003c0080200b464802d0000d03046c134002d05c5c040503881040f18014a0001a0503c0b140c83d00d41010004110000b810803035490000c2c0000c24548582180c070885000b243c0002841520010345d003600c1c2200100d0800c17800b540c0300340c61402940000320456010007840100080c1e41c0c0d00307022191007015208800743e60354080d071100800040164008610540c1c1010b00303041540d030b1001d00c2d10b420484031082052501c200c00029441d10500401d03000c0b06101d0401070151011094000c240214800e0b00d003030005210401300184c230b8042c1e500400300b42400921080040c03d00b0a20244401551102e240c1e0449486402149844500b40b96140118400100f80011401d0402186911030304d00e1500e08480c404641d5840103071700c2540000780c208800500041c040c44400012269080c0d401004052a00d03a035441c0508007807150b40c404000b003800320f6180d4009041400c1300a200b9507220700600d4114070303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 483663093 1250 483661843 483661859
    0xa17011409130305030118090c0b0405040608150714120103081b060f0c0a2a030915020c130b1f0e1017100512010509071d0601030f020d090609050f010b0a 68
    0x10007c175014882d03107484480c008541c1215144010302181203d460b034882c207210500c829540542d001d11300b0341c0d001e44403d03803490f02c030205a1904800d41d45081d1822607407034162959103000f103070840a50080114000001c200d0280003c040c040111204480e02c2c00784640e82c40d80714142215071150041100d800502c542c0760701c000811502d0981d003410f007081e8108030015401e00e10703200da003904500e0302c44801d61306042c0c003c00d405000f4030301c03a02074103460105401c00030f44a0b1408083c050051481107019050811150070640c2000d0002c4d250880c2c0701040203094550b400640219800f25804000c104444d0811043d1510440b0113070315082d09181490310310030301a103001051079800783c0d1544000310306940c0e00710b20346004420100c00842c00d400e00e03900c800d0400e00d045e805243c44a907810030300401d02c2000e203581540a03009080000307461010002d0716020b44103d002c038408840c82e164104040207429403044440c58020411607001c080303290f140c1400c032074641c103404d944006840807c0041c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 483664343 1250 483663093 483663119
    0xb040f020604180207050c0409030c150612030e1504050612090a0f050f0601061e030c0c05010f24050603280515011704080a050a170114091303050301 66
    0x2034406030401e460300d5901c51144042c80040c06010800302d8000907100300740b00d070800209040c0c000c01c41c2c0c01c101618a07943c014041e10070842c4000c00c115070302c202440401d0131603408407004081d5008000260200d0340342c0140201c0651011a01c245000e00c500c0d440000c180301554107444000d00403034503040018006015903100100981e50368415104d0210015922406e43c0c06060b101d80f0042c03144020500c215400d04c10705070880c8080040f020a860156208504c256003010000d043c00074082d048100c084640ba440b500000d01251308040c03180b403010313209504c601c401d440703040c0700d03800c2c542c114032007506c9180c42a1041c039500a20500c0481e81c4103c5100c4400c0440c00d0312003c0c4016111400c59281c2590002c07200b803c1081c451804a211a50300302082142408440c000d000743c0d8030f09aa161101c60103035000c0304042050209503403044a0091100b0320907041180d05c45041981d4416105000b4030080a00c20b003d519a00007044500890319210306c040740c2d050b00c030305040d42e00309180703101d0b02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 483665593 1250 483664343 483664373
    0xb060301051e100c1208060108070302092107090c03051302040b0613090501030201030b04150314030f120603070b1201030f03030f0f0501060305090a030c0f052406030d0801030b04 79
    0x2d401c009021542550781c1c070082900c0000d0b144c880303503858001420310410342c22803001a20107000400d0100040c2c3e1f070303215411a070b21187c90f040041e15541603501159250a07240b80340c10b40814044112a584400026600129840c1c1e0400344440c2d44038101c01c8080d5841501c00e941e0162642c01500300524140d080030006d40d0303018001c0f41c10b04040c0380d0568100d10483d8800f0350141d950740b00500035941c0c14041c0341441581a501400380000011414204030790b00c0c84060701242d000f02c42003801c43c030103008843c8a0740f03101c0d000d292951441102c455000d60300340ca490380b0a00c984540001c2c040041810344680245408403444160b196864901880c03684000803420940d54079560324110119206607282000502e10008581d8103100010f011154040c0032001d0b00e034424142c0d000069800810b241007581d01c8640d82640e59060701e085481d200749000ca401452070144614900c10700e0007003525200f07010071411108800c0c0b80c82d00c1070f540300c80c081c00045e01a046483c00200410040d800740e40b48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 483666843 1250 483665593 483665629
    0x6070327050f0d0f030501060c0b0a050c190216080601030302120d1104141809032b06081609021903020c0c060d0f0f0605010e01200d050304060507030b06030105 71
    0x8a00525140b60304006201c40903c0203d00100c88142c061076140c4181c3c1e0162807681407003c0340103a030f82c030354000c400c400604000000792a0000145201c08110903144008002d90b41200d415503007580103912444c0c4040524960340103480000381468001803581d04aa4250300509603015214240204992100000400c0c068541c840d070310402c4480d1008100501040442e02c0055440c4420028190b006050025001a070802030050f59500031003100c59550f401c0c02d0814603201401741d03109040403210820340c02e8901d048800241da030808100030611560302c00030722640356250b540c10000c90040604900641d0580c82c59268514043c0e4000c014200740d100c211560021034038005461070b481003400410b140d0300c603450300701000c5d1103019a4041000890003802002e0400000804500b042100c03141008081207205140442c88050342900302481d8081c1c43c4441b0604602820940c001c0c0c5046448620700000240340341d20a1081c0748444d0b10041205146074178107010802510f455880143c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 483668093 1250 483666843 483666853
    0x160c1d0f0c09280f06180303200a0605040807030f050711040504110907050904110c0606010503060a030609111e1e031e0a05070501050a14180301020705010e0607032705 74
    0x1a002524100c100000d04031111366014403800c00c24000c10035460220000c0081007042c00900000e5000074400b003030312103421007411241c17060b860440e24080c6c02031406000149022300344030500150f00000d0082a011341c80702d01f504400300408882900c116100a80311242c011202a07007032606800c607940140c019001c0420f4103400c800001c84010301603450402044000a02c24510308150060001c0204a41c6015081c0b09102543e40d840762401840039040210000c006103070740e5101400f481c05150080f00401241009181104d14040c0442c40070348125800e034008580c0f00c07402240603900c0c0345c000c0d028401c1801030030045a088081801c1d00c55040c042c0281d14400071100c280690050101e0318010280b040b6a418001d0400020342c2009041100400041c140b29802120f5100c101d48040141507031000b00041c60f610105010072411340c903500000341e0710300340801504040d10601c00c0c20150340d01c6440748142030b0201c40c03850459090224207880f82d00300c41400304040c041c1580c040c0c41510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 483669343 1250 483668093 483668149
    0x120f020909090a03090b07020a151e05070c17210913051e1e0a09020402031303030f0b220f1407111b06160c1d0f0c09 52
    0x40c10250341203401030b030380368800009201810391241d03c04009054581c0103c1c98800036401054043c5028000e04003e8224070000b040203e1180d202a078030b400441d00a0300201e55101e100030801e07030001809481c0c83c4070503100032401c8646c6000c0c1d030348441c0003070f801425940d80d5144070950062544220307014541040c01880e985880740d0341c82c01c486005c007190010b9145030888035090800d020851142803210410200700308842c045203500e0ba84440298418800c1c2d8030313800c4006c00b81ca0501c1009400034004400d00c82548040e40c440c3c4e040c64401d407800d008010044841d481110f10002d209a0701851140021a40a001c41c00c2040f1003216150041031001c0d010001350240c4042c50381103160982143c081100d425030141640b8900c00302c09018046100031b0040700850260a00c031107911a00b07001980520228980b807100c50060f9001021101c03a55a6800c0500140e41c00101c1100b0721800c07100082280403036401d454400e500041e0000d080080c0d400c03d10402840d410b00121071a8405200c40f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 483670593 1250 483669343 483669349
    0x60f040f020a020724210c050d0b01110309061303050a03050405150301030b010b0a030f060e0603071208030c090a180f1a0a0902181207030b01080d120f0209 69
    0x3580820340490050307514807903080b0007813074010681d021401704075a440005035078011103170700741000030b1030b9184c03c05044440c403006d0001c0c400011b0345e0340412407400049400701c0e44c0200c050320780703407444039010855030948000644049501c4c940140f0b4030b0b001003100d0754061400300041c14540252854402100b601d0f88d850a281ca448400280c000c100c010030100440d03d02460290203200792100068259451030f92031050140041c0070f25030091401080c00f0005501c65801254403c030140d0003481150303650600010001410f40e1072a029024803840401c040d8a101020b50685911607030541c6141c1d210740000d442500f202c40403d911900e02100003404c001c2249a100350320050040c001044007080e6941e004559851814802c0d080103007008846559070000340504a0707488110151b5600909100684940c00c1c480c1d4841e808000c0c001028006100000c0b45000c0c1d07845900342092a0b600ca001040d590a0501c20000c0021965000e48104802a03008054041c1038400f0241c2414912000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 483671843 1250 483670593 483670601
    0x20307050f0f06011a07031202071b031b0602060609091905010605040506090402010804020108040624050907020c1e0607080a051314011403180a08120c090a0905060f04 74
    0x6a9079254400000c249841c50280143d0b4014500b64502c0003051506294500e001d00404402400344240c030f020050380c0c09403d40441320116845002c80600300f904003845030f80300d4003d0200307171000c4480d9014001d60a190300a02e00981c1c80e2030b0000d2499a0304c034020410031041c01000540320780076410040c6060003d11140a000074802d40c00400c48505140c1030000b2a50000c0c00c403441800b0a005000160342c11180f0260031030b80a01e4168400d41e914140f0320050840030800009020000f02c00c1c94001480c0003050080e10700851700c82707407207403030b00c040803130765001e90703000440e4880300b2011100703140094038014407054500a402d4a081000c56219a0020303007240e035800010800000d41580343c01d0b90104400d01400c55070104160401c0b9040000b81050050141003594403400000302d40744ac3d0011890f410209180c0c401c0321405c43e094540350505070001410403010344d00000124201e54400000da6441c40301c0600f50162084c5085035107005880301405054010903090345201c410345941c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 483673093 1250 483671843 483671863
    0x5031207120b01020a020a03060c0e060f0c010f05090d081b0a0905040c111009061d010b0a060201200d02090307240813020f1f0804170715020a02030705 67
    0x5541c1c440c07039204000c800039912a07054041c119000100e6810044c2d03140400d05050300d820040002c0d00281e20702056890030950464694000000301e0b03401c060302446401451310031020002030001501686210060f40e00070350792a4015007048800314016807150155a50211213444403944c1203940c0c64402c0d04075030100e010800060400c60041c002070605001e10b14035031541e0325207040e801a01e24031142c0c440c0140c2040380c1ca01520b07000aa1706001c440e80102500540d4403007500303912409844440d008001d05000240180c1e94502c0c00129240188528003030b05541e448035500403c100d250036885940b00c00611040cd55083c03214915a80342000084054050001c07144031000390b9850f0030042c41400051321082080c554208401204460118900e90354103403404d00510301036400203400da80415450091100540c0400c807000c541c03010843d8010f6015804c481d42482062500c1c2c0082c0c441d168018280c02c072500090010400d05030b004200b10449441503905003c010342e169410900c0c188 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 483674343 1250 483673093 483673097
    0x305121c0216020a060503091c090b030108031b0706020604020904020d06140604050c040f1a0913020304020f040b010f0f1107030305040311060901020a060b182701110405040905031207 81
    0x6608800c60402054038409061700d4200182541344c80c03031526559038091080401180b100341028400f41e40540c0241c40981400e82c00c040c1c480da107c070781050307981d0807525008041d5100c4628100000002043c814144c611030b034042c00055886400b800300c1c40d800500704a81190f040d00c01800490300301d124286445500407070750304007030515030100710a43c3d0010700320b001840c1e010081007110240907039182c0104e46541c140ca000100100c1c5e04d6114034000c4540240c0c02429050380c01d01340b01100d60046108c3c9100f100c001551038a0082400301702ca40c003019080c041120610310503c407901070314050868144500c2c1130140405d80d90a000d0800500390301c2100403c80216007402000218040007400740b2058400d070342001003403c0002d41d41d0f07022010142a0701d035255459812130302c1e4264182c8449800000c075001c1418287c4c0c4400741710094002c0e41e004210705100d689420078040c0218000705580b404043d0800f8108420400207020541e812201c80c80100818a0619600b8800700d01c101c0300c40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 483675593 1250 483674343 483674377
    0xa03020306130c1d010806030a0f0203010f0c0906030f090b0705070f1e1401050f04080a0210060609091a090c0c191110140307030b130603110102070f0305121c02 71
    0x14911102d928241c4e8082d41400341d0a810411580c40c0001d46400341030300240b950224103c5400400d0040c4841c0110980031824401c204025542119544084941c81da0701003080d8180f0305054411101b10b000c0c002d12355105207002c6880c15103d6405002181d0062180355040e00030f558403403000c22100c44601740c041550100c00e60078030000400709100000090001e00451038070038400c92071404010002000041c0108105008a20800c80418040444441000b9007a02c500002e04003140742e22840e6100c40c202000e0341e00c2100c88800b80c59007040c0103080011103844800d0034904940005000702603e11030390701060003126582c01c0b8014403500500108400701005014801c04510307403201c610038090b05e01064a002c40b20381084130f502c03d1f03180c030700041c5e440c00207c00500007011001344002c0c00c41c2000808000d0000601c01b100d401c4201b42c086400d019615581003103d20b0003440090055080462500c040b18980c200800100c150741125000303030003010301540226080455081c43d14011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 483676843 1250 483675593 483675617
    0x318050105100b070507030f03021606090e01080f0d030c030f1503020307060c050a020f01030605060304050f0c03120d050c13091406010c120e01090506041d0705040b0a03020306130c 80
    0x60b150003101a1a001d02c000d8500203654988a590b200b20b440002c000161032408842414400d01c50b440c41e1026440c0c01702407081e690b403001821207225000314401e8180e4840005014900042d80e9103002c0c182402400c0d007192201401e81c010b1600300c410800789a02d81c424030210b00707400c0c4590411800d07642c00c00704410341503006261504e078141c2c0001040c0100c010794100407e1700040c1082006904032400c0d4030361075603c0b0040f000f40083da0300c50b81c0c20000c0071003400104017001c1410040d0640c03441c12660059011030030160b8515406103080491041000f4282e0f681d42c140d04810b81c4141103000071071600d201c12006c103080c281c0d107030721000c03e06507a08546816142000c00585d0082000d01e04014480c0365507c605001e0f900c160050010311a0f089211f1516034041c010340d000400c0c0003000c40d0f840359910400b000c10350301e0070303896828241894400500c10074000e4090390181d4544080c00c03070912640103010f49c000e5001510072a8002010104015104414080e036182c0340e01c540d4071203038400c1c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 483678093 1250 483676843 483676861
    0x80d0503160e0a0909050a02090103111014090d140601150305070315150917010e0c24030a0f020d091101090305101e0504120906230a0318050105 64
    0x1a01c0d6114400708040c0d04010503850b62002c00b098140c440515000400e40004e14000f0314055104800030741040554000006004560540b0005058240c454001d59035038140120f444015551221a05aa05102c0458181024041e00c1c585601c0307602c04150a048400e401c61400500368040802c8003c00c5c1c41182088c0d90500945070071100500701032107450303502031035030450b15114020800140c61400350a4112840344003818000c02c68152642d80040d800141103020708030301c0d8902c0441d44600300004109040c048500742d29003088402840c10950445403122050f400a40030800d0b03e5242c41c1c80d107850620600c000c1c4040a1810030002c1c1241e03085c43c1c0680711f001e081c80c449050025505080021840c0464030a607041e4115100185511080d0194184082c07122804000c40c0d28100800c410070440c5e01c18440300249507215100d08643c1e80000300c4040010855a4031158a602940c00c0c100c030781070300901b414007600d08000c9041d0030740c40d10f0000071040800d01a145a9158014081500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 483679343 1250 483678093 483678121
    0x17030907090203070903020409020105130f080d0c111c050708060109061e050103020c1204030609030306080d02030d051509070e1903020a1e050a080a0501050a0c08061009080d0503 79
    0x1c03040340e4065040d4a40b000000e841d040302807101a0060740c440d40391004680c03082003120035070401c10312141540c030307152194050001050b00918405124040510a00030b02404114400d2544041c04480440740d1409026410200c465200e458004420602d00043d206001e0740d409449500b005112940c5400d10101c2a41c01607804000d884080c403404210305c90700080c0700d006039502820056918504060000e160603a04403069002402c041404000c0143d02c1e004040514042c0c1d42c1800000d03150759035992103005881c2000701503401042429a81d11841c0c11141c0e12210440d800d41000082001045010104492600020354650b5000311903191083e05240c3d00d0304070104407420682143d010410009075800703800c841c010200090956010488985406860f0250000c2c100c00e50b15103040c0d03602c0c1c07a180c004807030650820000a59500642c814419440820358894007582c8900c001d0151040104102e001044010000841d0a500811409921080c140d483c103540345890000e0b00151 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 483680593 1250 483679343 483679349
    0x7060f02070f0806040b0408091201060e01060302030c0714010209060c030309070b03010b04030b060301090f15052202090402040b040e0a0506011a042c0f0a0b1519090317030907 78
    0x12044540707060003d1100010b0303d540c810342c0459003102c1a1180d0070688a01c1c00307418500d0b588204062200410440190042c01c12a4443d00708450540d881d07100680136804201c8181c0b500c2501405030764081a20300c1c10004104000c440014508070140e408100e46d079204040c681c412f40c0c000010302c440d100341008508018144c1030398050440d4103001003191944201c2c80090b0200d81c600000c1400e6640030f40c0001d589640c407100d00300046101d8608280d81e450180340f0040c030301307180031300080740c0840350008030f40c060750341d9500001c100c40c659082102100002d4005d90304540e450000d2070450700d961081210960f5201c2c02010a07200e285801d92808030160880075402400c1c50703488502c140c103142903905941d15419044c0f0356034640409415400f500742c0007100800d51010922140d5021900b45a00904e02d0345000d0008003929814020810000208042d02120170416040c050303105800c1d520b030300e403194a01884915544d0300c42d1030307413880082d03429407130fa00d070000500004002c02c003e42001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 483681843 1250 483680593 483680609
    0x60613031a01080d030921110a0524130b07050d0f0203090c041a0f1306090b0a0902161e02040911040e060f06060a1707020d1103040f05040906020c07060f0207 70
    0x90b80c1010790307070f1020a0045001d040391302400100259441c40c00b54240980e076502c0c23801101c800c1c181c00c2c14426920b0000032030003251940005100301d00000d1700e24000b4494100500c1068450785507035240040c5c00c500a0030a010007100744458031501445010700621030380c1f5034401586038102101041c2c20204034420392840766182005030803441203141241100e88008803850051b0380700c071001150301c1c3c0060700f0710214070f03514000000c28100965807040182c903400365802e08402e600c03044464201d100e40f000451800044a40700000107003281c91100d681d03035882a801055401c69408181503511440c002c0b10030303185203030140e026410640305480000005070300030140c0741801c00c1c0c441b034061070180000d1300941001075410030003030203194482000c44071740011200303034a8504030003501d98814140e01e40000d2040060118085000429103003610414490301041c0c2d85000e040200400c00c0c0340040b11066000c0c45982c44403481803103490010695600c86d01504002c00341d00900304100c0350440c42c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 483683093 1250 483681843 483681851
    0x8090a020f04090206090310060f0e0405150601050408071403061021031404060e011106071b060b0619110d081314070b09040e15060613031a01080d03 66
    0x540c0d144120105100750a560002d0410703d1030000c56441c1c441c44030350540510a0001d0380801c5000c89d40500110340f0307a6000b002c40280c0b41c0914048100b426200500162b11000b11450700f040d00c0c9080c01d4003c4414100b03075252030796502410303007004000c2d401013922203c450300880b0641004c0c0003041d445002002034906490078002041d030950a0754180901c4840c04c031801104142c060a44801e0708d6074002a02074541d50f503410006c086814141c00e5500091513468020000d840000b801406103009403190782140c003c80a1081c03061010302e10a840c40e07501c0e400400815201c2100500c1101c4102c803030942035407041c0a020b40705c071850024601c0786d0740c802050000c078564443c108035044851004220300c00086410400485441c2000c0030b18180078600b40020702070581c10041401082c282c600340803101d0610704141d255811034140b5038800d50b9800009440e46401c200400314a138452580c490029240c2d200d10812808518000002503003040061000d03050410014080850310300d010300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 483684343 1250 483683093 483683113
    0x6030e011410060c030c0b0c0414040506032505120d0813030f050d0b09010b0d0b0a030c03030f0908030d020315041e050a0f050901090c051203031f0b0a0c030809 71
    0x485000218031407602004130000d54182098454040142074542202008515040040380d1421640c480d220f94070002c1c0c005081710046060500807644500001400b800070a0340200d00105452010700c0b008520301c0b0a02d01c089903555070170b07810500414000c4002c02040c081c4150182ca5041c0c003800390008441d641c503007000080e900440303c004221091800340d45807024601d00c1406400c10202565100701e0100000c200308541e40b01030180101d50702c109005050702030f41889445c040380d000c00307807585c00015414800f20340240a1460407130072134588016150340d110707003260654100f80d00803c01c241d00042072140b030001d5840b003d00c9406007110b040080d03140e4400119120058030b1b4400c80095141c0000944541142d403084002490302a0305104c2c500d0142c455070b000b07244c42c00e81101c43c0d9051038000b0426080c01810038094200c4000218a15221600017281041d201000030326482d035001c030041823006282000e070041e4461501c0b80b80c10200c1c03e140c00390808600900017101d5500130000b80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 483685593 1250 483684343 483684361
    0xd0e0604081e07060e0f100213031415070c020120031c02190e190305030403080304060b0d031806301b1e03050f060f01170106030e0114 60
    0x1a42c101d0100e09805030034400b10120100240240d03040070303084500e480c20040c40841c001c5490b03401610f12505541c44582c180860100f24090070040a0b1000d115040a000040c0462207a06201c42904221841000300c40c101f501014411070340b4030005000824200c0840d40c00481280440303241d2007000902c070040c60000da03503034025011510070070914500d041d4030f02000e075811100c0d81c0310610b41c0c101c12050281c80242850004040f071030300031320100c80c0c4d0242428190341c014059030340c018003452902e0702d51b441e01e5031540c00c00703402590015950b101101721a500d003001c0d2014540b00741c035003804003608070840c410b40d002c0d00d9200d86d0a00038040301c9480e8484030740104070140e04c9000120445241d00d86002e0004080d8840c4286035030420b2685c041060390410345188081d91500359941c800c0d216010110180d8000780e410410482201001c1065481c0801e03202c1142c1106152942c1c103031010041b048504442039014001003640c84000060801c802e0043d00d00055000341c141d442070410200d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 483686843 1250 483685593 483685597
    0x2d0239150405122121060d081b0f0d02060403050f091309052a13060f080a0c1e030206070206120c1b070311060a050c03070c06080105030109031227080d0e060408 71
    0x129170303060000e880001c2c1c055500e070803140f20300c5600b0189a81d110074000e0700901c2c1c224000e89040c2c989218101c2c0c0307003642c5a1700040d10107a1000c2c55025000c562500e40c0c040d1400c2d080440710040d054014010740315686c4a5209980f8032112002001c40c0a40150a01e1800e14036184091355810b921030b040780c11030303c12188004c00ba1007000e840b071561440c03403000280700400558000e102d107920383e40c40010b10800009120040366001790b40d681d00695070360864040000e040a040c0041d0181a0001c10240c64004050455140040c0542d860240c90f4045c0c040806d000700c8001c020200c0110325002e0440401d10400c1c200442007004000d070301e0941d2600454050404280c034485c04000480c200070920803400c0d10783c04445182103e40311143c51a01c40007611580c003800780050342c480e000180c10302d814000e188490b501502c03245441141441da8201409004800710504030b07040c1c002022680c0c0c82008944000d0040589545802021420030f0581c0c1b0a41507401d0964001e6060002040c174a1027 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 483688093 1250 483686843 483686887
    0x72402031e06060904020c0601050f0303030403080705030a020f160b060307050d06090201170c0901030c050a0c0303090204060519030b0609162d02391504051221 71
    0x110410582e56000001e152031180c40c0d169030f0440e001081c0918011400550303541a14030032030340100034694550600d1340d00d000850740600010070341004950007a000d07000458100c19000c03800f500d84a10a01142240d51040e21401400946182c00030148141980001e4000001f01d0240c00c044c0c0c075000c00100d6000f40e000c4054542d82c7c1c1e4049500c1168059078007111044050491310380140740201c0c41001c01c0e049004141d0110b070421803e01c111910410441e052485140c0300c8810200e02d54504400608550208a030019950070300031886688030300000a2050300d0079201c610050461500511058002c1d00310780c00351030720784142f080c111400039044001c00b0b024030703202c95041c80900115102c42c080801d42400c028140901039000399002c07030101d0b0120b442d64000490302c411000c0881d0140c9080340d00d00d03030944418000d4180c03440d02d00340407522001003103030712420039807180e0000d00f2212a80303a0a1082c4d5010b140c1010840164068204100710a03414041c284921282d25415031a4095 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 483689343 1250 483688093 483688141
    0xa18020103151212020c011701030b060d060e010204030201180503060106081b040605030f0907030803182104290d091e0c05011106091e100207240203 66
    0x10707420910741a141c030140008091040082109000381c0c00c0c519131094a501c0481c0050140b56820f1aa55001d00700100400703490080100c0342e41e00c2c2d0786840b6203280d8050310b2607074414000c2c0f00780e40101d01c450207440956107500e800181e44d0b9107584009011000900c1078548100b40522007041556408100e050440340d60b1305045102e0b684003884810b420b020444c064000410104d00403500315400b1018511070307104002040d9880c0c03076000c802550f594903440000c0981c40e0410000d20038051103003c4032462080301048940101c9000c0055804d60406c9500d070641600200701006503801041c4846116041c10755030514210000c10310707000905c10b410078000c116403640890010480d802c501c070891032103840d409280c0c03042c00d440c00400c031810501c14140002c440040e0821968004540e00c1d001b210040000c10040f1400550f070b128480e07901c1c0009007540602c001c4500c2000560004200c0544150b40080c5030b43c2d0840007609254003414030051045d0720610800002065891045003030300c07090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 483690593 1250 483689343 483689351
    0x23040b09061209030409060504050603060411030312130b070f020c0118051801092d0e120d060608010b1828090902030c06070b130c17150a18020103 65
    0x3400c08104503208402403490b00191003030412030030078004805481a038180c90000d00c40d403542d900401003900c1e17041d01c0050340340e085540071400151090780100c9000034003500f928148110000e5807100150101d410001480c60100d460081006821020743d0003c03e9042540c00004000c0009541740c00281015040c00b2007028004100201d9116480040c04010501c50b00403000c510300050311078082c820090b00c607003070100d068007220380000b024440c0341c0580a03207040348615102c0c5802400345101150458000d6482664903043c2c202d004110140500c078001c50503504d0010002d00324001640000c3e0380c4001400081105d04450300c2400c00740404444013402c0500c4c10b920b448222100001010071a03220203070000d40380e0310f50f0b0441e01d145030088003514200e42a000a02c08a4807030883c00801050084d80011030005645000451079401031030103107a001e44440300c0200308035141c0039a8410344d00ca901144095a4a80e0141d5408005203501f440031003001d030b090306c5154840800090500d525 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 483691843 1250 483690593 483690607
    0x501030b070f230a18180908070b0f040c0503060609010b030a1b02070602100204030206090d03020304080109111c02130f091205030717040209040b0c0d0f05060123040b 74
    0x12440c2e01c00620040001c08914820f01e07000c407020260712452100c000300304644032440030000e0b2101c0c10001c903841094080c4001960320821001000900d5046500d610305201d030b02c020039101d10840c2d21542c5c1c0e08941c6180c034209800c1981c8442101c2d80228404c2d40a2001c002140e1240a641c504680744032400303945945688110901a10b007080141196150f001d0600242e980d0001d0000c0449126070291040c2c42c4c0007441c250300b684521b0101940111013040414601c0c104408941c0c5164020720680382090340b1802032609540d00c003082a40e414056580152403840d003041c0b11b04100a0382d40a480f031a03203040c0e0104085105020216011940d611124001d07844241c11101d5229840300b6060003418094030040e016030029a0208000b411301480500701000d41b40405000ea40c0007842199950741d5642c80e4842c00500400d29074401078140f00204480c00140610092401c1075040400c0910b4a030000410305208a80034101300e0700e1700f0780e070002040c0d8040111801e895103c2c3c451030350350300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 483693093 1250 483691843 483691847
    0x302070204092103110a0513030c060806040b1c0206160804170c011110050a0204090e0f06070212040311010c020603010e060a06030c120b04181a07030501030b070f 72
    0x241000650042c0c241003202d0100003042104018241054101c0101007200060803822542041140b03c03e45100300003080e141401540640603070b01452070120718081d125901c00b04500350070750040020070990300900580c0d280034069101c091000ba51300041100741a4480354074001d81d004041d01070706000802c171015001c00c405552046410014182da83d550b1040c1880041200381c0101d0034a020b0594488001d621444800c0301c940c400314010540a1074142e03080e4001e050140c41500019401c002c00508214503000d828a041140000350a4422014650506040000f400201150400030401403580e100b9401e8409403a000342d40b84084174080001030340d003422041c45c040d6110201000014106031030b030907214801c0e40c0903201e400386c0c10707a10f40d0150140c41498070b0320f2010401280419000c0040d9a018403174041c0010400302d03209002202004030358403101e40a84100c02a408582113420114840030307040740641c5801c011a40c956102c0c2c14050802078074100811a9200f403040b8554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 483694343 1250 483693093 483693097
    0x1050a030e010b100e030d0201150905150901080d020f010b2103090d2d1a06040b0a09020702091311131119080f010e07050d020d0c050405012705040c0302 68
    0x84005001a0402006110080c0100c8410001750f8032901c90b4903659070090f4418050106c4000912802040700f40c209607107500035000041c00b146c400c000b40d410f0141d1a5541e181241d0080c0703419000780414170075141c0024102041d0034002d59450781401c09807840c80d155468100e10f410502c03581003440380e0804c02402e0561040c030081651103034101d010729040c41180040d10410051540c3c04c5c9982e80300704c20f130f540c100c0a140c2c000035020348a50702c0c0036010707541e0380c4d00340d6079002ca802040003503845401c0002800f840c00d550400b569a60380440c0b40011420310555541c0c00004412003420300c3d502c1c039901e200c000300c000010305010b129440c2100186040c0d903084020045078100c4102d45441043d805150961b82c401100c074002681e403c04100c2031800351100074141c07044840c3c00480b56603903000540b8240d01c0010750301c4050780c0c20800056410303000e100d5200c01c42169955603a40d14035200004001008000300032114255004680151241a02070708040390380c05d40d40411940d81c001e074103800034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 483695593 1250 483694343 483694361
    0xc07060e03030705030105211c0e181605041206020915040b2104031e0203040801110c07080706020a02040b010309020d0c170106060212070f050d031a0d0201050a030e01 74
    0xc1c0c40044188030610b0303040805541030741c0003610440000c004074050f414070392491001e802c03d6600f0605141007060041c6c140c0a000c91601c0c03c0a4010101001c08035076000f1652495440001c4120280030205044200d803100305841c500d0114103160800c0d00c20f10b40500007800007404190300144140190f1aa00f40355030001d8541300c04e80b9255580d419500071140e11184000b851000614049071203d42d10080b06400340c0c0d09585c500c907003404500e441c0710b40b2003100c41c148001d600c014080080e444000b4040c00021069900300c454458110070603041c90116540c110085580200030300f88100c3d580090310041d0140c04580c0491040500070042e0000c3c08140c2000c1e4001c502c082601041c405030130f04140031030301d0080c00188030350100c206190880300d55002703103c0180c004040c02500000100e010b00f031200e00600003054800038964803540740043d210458404203032200f000a40d109d10710040b1030070690b415103002030303001c2ca650300003040d501c1342810010915a440702104407000302540901c0c03407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 483696843 1250 483695593 483695621
    0x12050912030702100605060421080c12070b0622020f07020a0b0a200705060304061103040b0f131203050a0e0105071d03071d0702010e060f0f10050303030c0706 70
    0xaa41020b00d402034851122600a0039594100480040d01c0d0800c0e9080f90111005081c2072066550407007802d000c03204000e40251002e22050151040b042e000740008500061880c085aa4444503032400c090860070040c80284620031070030354200030b00c60b488004030124020a400590f01c0510509c01e891030f01408134040c0d0032480403800402d440440750000c2000d000241c489034010a800f5149020401d51030a1100709c07074010303040410503424048091900039200e10344c0031070700040b6407808a03240e42040320107681c0b00070110180f1031401c814000d51900041d520440c044141441d8491092410384084101d04040d40c880010b2000c0010b07900c48400204800000e02c20307410000301c000d011015507085102c0da824803000103000c0b80307800a40034003143c50210303052800c071070f010200d41d5403107000810036805d55490b0314100c00703140c60a0103114818140c40d0203154035424038000050301075000615446002d51040024015503600000b9294822f4510030000d95030902403a000d0701800f0180601c1d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 483698093 1250 483696843 483696847
    0x2120a0918060e090d271e050909010b031504080d0c3507080c040b0301030b010617100b0d0f02040b040302011e0516080c030a080703060609030312050912 68
    0x401d101e169000b0100b198469000e0081c140c460702c00c184d072501001e2154002103805440c8608554169017a1407040125002641d1801c0d030b6140002143d4003060f100b5180321402c1c0720001d021520f044040280c01c04070000003004140e41c02004a5a2800d00c900003451a451000008040205a008607140c10103920424008060b040c880904000c1d040b03501c235400c5190756451400c0c00c0034810000064110004aa5401d81e00e45040903600094050f01c014060017003040041801c100000003140210f11500490001d0340c1340c03c000900d05a440a07034042d034081c0c1c00d028020709030181800581502c0815000e6580c0300f241088100c001d2149029104a65002280c001070003815540684103c1e8000c0e281d40002a1300320103a9125117100c005003401144c82070000c2a044c42e086030511030320502c19060305107419035244005145030000b25a0000151000e420000d200d9030600814004042504245011a043da500079013801084c0c000c80340300e5a503500008100074010800c02d200c00300f4980316a070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 483699343 1250 483698093 483698129
    0x41401090c0f0b0a1205090109080f030a0f05060904020f120d0806090603011413030e06030a1a030105061503090a1a04050111030106050f09040e06010b070c08030a02120a09 76
    0x56090103481802ca034951000000601c2d411203d08907035180003550395003a481050100080d00401c030250082d41d8542d07960040c030001815003001002d81c417044050444c3c407440c1c84982034086d100000103e032030341400c2c201070014030317140c40303507019045035048800441c3e0b21100c0000c501c1d4005160b55032003080c41616100741c0095040042c05000350003c0e181d4503d541d82d10424103081c0c41081940e4840c0c41e00f414001440b078042c541400c0a11340c401d1410441a840c8180018159042580e50040603640d8a11403188400c50300e25071481044103030000d001900c2c061740003560070034140d1082c0e00c40217070000024848010074001210074a03444070120720481c14201d410040040f08840c100c3d5550b2a04603061003650031350099a040b5001035454503d8203051101c0201180c200d06442500f0030b4031100851400c541c00e00c10726020342410055a5199407150800c0a203c201070750291426400c1013044c2c20b4095804070301d01c0354401e0103d010703541d2030481c0c4100319482d0882c1c2c3d1107150712003600b100391 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 483700593 1250 483699343 483699353
    0x2220b0603010f06030605030d021c0e060d0b19320307060203090306070305011211031c0e03011103090a0f02030a06110307030506180412030e0106031101110607050301090504140109 80
    0xb42d13840e694042022503100c40515588024003101d10b005640441d0f0384400f003044a00e550311340700c2d90340c0ca0034100c044280c81c041600c941103248140845602c0384501c0c0c0303850601c9143c13408586040d0740c00c242603500c0c0206242000c59403090140b40000805544d09000b0140300081190340409402c030b80100359501002500c81d00680c2125129004103000700e2a143c1c801e020f00c1e8180d55801554000080c45903482d15080030b40c144520742c00d405007201e440c1c55802c100c1c0014900d07031140d0300e6040f60382c3c20310010103003160072468007a0040c4400b40300f03100002c2c000007200040e203544642400e40ea0700c490b00010b49400413001c002095117080807413402048100300301450107800036031410300250700c0320300c1006803105951100c519070740200303000900802e4004001000110307150500003245e503210080c01d030030f60f000b94005988540c1d089a0505046d42d100c0c074008941c0403a00d02034a01414501c80040c403501c0188650107000762201c02107014094202c06208420503030500030000c440141c600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 483701843 1250 483700593 483700619
    0x90c0c0f0a080d060f0e150d0204050a0c0206090a08120612030c0106180204031e060e07120209010b0f0313050309180402090105120a0206030907120803010e01050102010902220b060301 81
    0x2c1000b804c100000448403803240c002003c1e14404803405019642d00d1074038aa00e02e20100072194841059841b51015850768441c003030203019005004a02c110300c0c81d102903d0300c10040c210303990aa1002d240d0601040303001080d101207d900d0f000380702843c1c8526000404440040d2002c00440c0400250580511030540c425130072520035014600b110414400d03000200d003e40d11014107003602543c000421409001a1105001c1c401c0c100011044140991945804a150058402062460000019460841d601c0c50040000d250a1071802d8401034080115010251000c207100c0c40ca44800d400b08481802500c00008002d0480d4031624402881c5418400060324140e000e94031140c0042280c2c01c160b201c040c10160315130028500c0c9051513003403004943c0020120001405500c0340801c038824900c20124079107004111040d241d50401d0030140b1010810b1f03011506580c0351411800058880c60b1051031841c01d16222601900070100f6032802411070682e11980c0f10500100200da524984030b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 483703093 1250 483701843 483701857
    0x150207262b180b1b030c101103150d0305120f01090c0807050307050702030a0b0702010e070e01120f060b0a0303050a02190803060d030c06050705032202090c0c0f0a08 73
    0x18200c2680103a1070151084014000c4111480c0d101c150140151040c20f0020002000840b01e800c9407055482d034014203580110410f450203030000400f203a2484198040d2008015a2480d2a4a98140302d40c4400c10300f40014901400751a403a4000018580100c0c191a003811040c1614101868000410b0100d14000d02500401e42d1030803a881804903c1410102d01ca44903d446030313490344c1c541d80b105a9047d001454126454418600311500141250a415000f400766800204922100c3c168507410018185c1029010400700313001044086401c0e505022680c0c2c00c66510180801c02c0e06105001c0e00c900041181c21890401c4004100742d407002c0100707201441d65080d00d42000503c0f00101c01c2c503200d003001414058060000c1007691805003c884880b0744281450085c007141c942e640c02c01c0d218100d4044001c6030b07001c000c0245a0320b50075890102d0b20b00c14200140c61700c0c40d660026490b9400604002e800700400300b0b1104c0500410082c5200d40540ca00c11a1640c0a682c902140035601c0a0303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 483704343 1250 483703093 483703153
    0x20406030c1b0c060509120f03040512030a021005060f0301150e0c13090c1803060f05060a0602061f170105090d0f020a03120605060f0309060115020726 67
    0x2c49603410601e5201c007031141d034440d00b48007059242a00880ba82d8100302ca80e1a440144200d00c003a000d08208812814000c002e005141c0390340c5003004010740103d0040908145030804c1181b4080c8603404500d42290140ca0070700044c0301d4840c000444d500c0d12800c810701741c02d0740c6003143c443c113250b41000c1104120341d803c10301540300d50385201c0e03045075a00038803041400200140c001407003101c410f41c2001003016682d01c2c2002c0300c1c0c0344c44190b0480c018516130060390042d50701d5184000d44001802140c0c1e000da0b055424410491805500a40ea45401070020381741440c1940b00303444140c1d10b00200801454034040d800c1d04039021801050084c00e0550301c0315118800e004400c10b0050003210000c0740045240c0142050520a4500380c0e002c1c00e0426540c0407031a07840c10082103da46c0c410141c41c0840250800c69107030310700019031525010068000d00c00b8401b0341d600c141801c55000550f0001c2c3d80c101501e4103991000c3c0c0403200b0040c0000e0079000000c1c01120008e2b406010f1240003110400620307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 483705593 1250 483704343 483704357
    0x501050d050a0617151015080402060f041e050402071509050703050609010f150303170c0c100c0315030c0b0a0215090319090e04080c030c070f051e0d170d020406030c 73
    0x9200715240c001b4507881404651524411440e440c14080e11016600900142241c2d18024411000d102c0a038090740000040308900901c00b211030381002c0f02ca10152005560031032508002d0784850740c80c01581d495141d0031700e80f9611030500300102800058000c40d070040032144541031200ca0707a8003901601c2c00c84000503107001c07500000709940c0074002003282c0c0c2640794004500040020303624815401030004049407020040c404111108016070220004801e000007900d40380100024192144a5403008030031310740b42d10600116580100c04030480d0030f120b00c5160703208260a016410310110b03418601c200d000400812034401d90100080ca4001d07842d05010240221043c020b47d1052002d0003443c4052400703000050010b031801c0020b0540c12a003504403802d040044484501d8040190040705808000240c10400b609001c003d880100110740000c0c0c442010540229030000e849140241101305095402d0501c3c003881c1d82222000c2c4400a4203540c1c60340c8071440580a8074004101c00001151 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 483706843 1250 483705593 483705601
    0x50a1a06270109020322290f0703150b03010e040512030c03040f0201091e06110102072001030b06030103051c0e0d170c010603060b0a0b040501050d050a061715 70
    0x24005001060001d6001190020b074245071500e002908010040c960f02e00900c1d510640104c5100d010144482c070840000c00c4130500c410304000e0088040c45400e4120030700300d003482502013400f5025a80200e00d4540001d415000f032080c050640000d03400300256013000000480d80c5c885152175984941d01650807034102083c4c03a40844103a02c000c58090006500074008100014001d0b120404120300501d00110416100d07100d0200070301d10041075000d104a824810085542c12039118001444410700844c01c0819980359103a0907041c80002104019940e2010001a0302070b07444410303000d1700940900d80301c2d030b1603141841c0d4540d444040c0740440704107640102c0c1c58030b2240c3c11a20782981e002c7c0802c51040666546d01c1c030300e5036821428181204090103480c00000007441454011401101d010034000b0101d024004050180c1e00110312214003000305001c285d07000310448007016910600060176039190807418008003104c6e0071400c4403071a0700010020090000407072802001024101d081d4580f2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 483708093 1250 483706843 483706879
    0xb0408100c0c12111c0c03020c03010516110312040302070905090309010c0b0a090611181525020607120f180909050f0105040507031205030108030f07050a1a06 70
    0x2d90400007041160f00703003400403040d0700c134580091040e9140d070205c2d10341c100d240c5000010010503071403000002d451a05a03105140d030402c442003a01c8400c1d8000c100d507003030454983d505100320708503850600030070803070040c090242002220301007142c02910110724105854025100c445920030340b0f071840d04002c0443c42d400d2011088403e50342d016103810855000b9a503072145100740040a0048440e0340e0382202c0c0c0410b000380503a020500404c20051b50341c070800b00e00e441c0514046003005025421000d1225501a44c0c40c0c11180c0108652640b5036100b0002e00786841c2d00440d00c80c00a41150020405404000e400c040200f82c1c900d454503107102000200f0b10485840da184008184851401c10b42003111041c6e590002c0d590b103028005864024201c00c01e01d500350b42050310119410742c4048010400d01011700710f114192041450028919450701402c1c56403030013500c2d41e01c000314100007105030401c1820440000ba85910440d4143d00c13050580040303d4991003114070074010b510100041107aa4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 483709343 1250 483708093 483708107
    0x2010b03033c09040c020304030203031821010204090501050102010903200c0a0b070303060501080c0d0b06041d070201050106020106052d091303030c03021908100b0408100c 76
    0x20401030015070030402014034055218840204481000040440e0160b030000c03003582c0099116119500983c0d202d100c4018071003101e03100c0b10910b003190003d000600040e42e021045400c1c0d00014a1180c03011681d04000440321900c41300d480d0302118034003c000b480e110064000d0412240000000c0000360380e51130040e82680d0032000c2c02000941821061024241c40149202d5455602c9041b07800703102000e17010a40440380c6412400055401040300f60800d0f90500698020f85400e28003140241042c01511b9001c0c000c8100742c43d20303242c07140100304ea01d407101010307140200300c0101c102c8920041102100320008090352090015400d000c004980e07240140292012520007034a03030025001c8007403c0484001d2a601006103040412480030010341d11202501d0007122f5400e44941c0d03074800b51402904a455141d00c0c481414018410140d200307035a031608503026600313410000516500c3c140101e4040c102c90b08000300025002c240414080d50005001c1d08080c50094200171003004040306880713403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 483710593 1250 483709343 483709361
    0x50703060501020607030504050304090e0c1309030c121b08120601020c06040308090d08040b0c070f0e0f060d0803160801091505060a0e09040317060a05130b01110a080304030f0201 79
    0x580d01c0007004c540070911a80c8500d038864009c0096038142619918024259000c0c001514040e920900c202005440e01078804d041c8030040300e00802c0021800e42d0701030f0885c1107554000c1c1010b0900a0030341300c0c07180103038050707807080003003158040303181c8100c3c502030003590480d0402c20088061000011040d500000b030b00688210001c1c011802c0611b55500ca070350b10361007001d0b02e9400c008a0111b10000075421009031002d4001c8500450b1030303c0b15094045d00e001c945038005c01100381901d03010400151743d0380b9100e4206110000230b280c00ea6440300410503c81c41d050307004042d12400001c00c102d5540c2490160380000d0740e41e5851502e079076101000802d81e02406509040003201d21010002c0b85007100040004056a040442092303180d42c000034a1780c2004c80301680031400070b026101401d2040400d640c0d02c0032040707603055201800c4c0408120766200120103088071070b030b40744084805a80660068040b651103401103420045080c03130111219001910b0440114000242035000ca40c0103000c1e44ad44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 483711843 1250 483710593 483710597
    0x50a0501062c10080405120703051c14041202011a0a050423100f0b121617040c030b09062203030204032109091503080304240f050703060501 62
    0x2051070284041d10790492440d500c200905542c405021041e1103002c000c5016200646948401d8606030800c1410080c40600b0070b0b80e009000c00c03c520001c1d41200960303154080c54000c00000118100540001304a00819007141081c0f42c0f0400c000c00c00d107505c601034801c4059009000c11500c5025955104d10041c0040358442e090600a22244c00c103640495080503000715501c42c0700c10400a2104641800c1d2a118030011044d541800300b8a01044054000c15400452514004415004090512000e015119400b041c060304444440c41840328155844204910200c0c9003000c0c80d144c00c10000f2440304807902509140080c00d0320b000829858415070031020f03070070301d0225400440c0c60304842d4000e046050640c24003011011441c00c5102a400b00340712100c90105c2003518002804010b65030b440b514031142807505503030301b4003085080002201d50129800d40c4a44031032410340080c0178202c2c5550300791494520015006031a981021540100141040103151a8003104901380c440a00840e80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 483713093 1250 483711843 483711857
    0xa061b14090906041805071d0105031e210c12070b130320011e05070e12070b22210308130b1905150a0302010f0507060603030909050a050106 62
    0x102500b89014a41e5100e6401400020380360900c481c203007080500302c074040e074403548400d4081c0422126421707806220754a40039801080d40c50708000903a81c01d0001c61203c40404c180400b6414207400304051045106040c000010380070fa41400755400347c12040d680f40f1240b15402c004044c8920f1241100d5106402c0345680c2115070320003260000303025900c44100d040080000091444c030194100d044580030340740c800402c10908030051a001007003001800007249181c00140204d158000d41c90151002e804d41d591206140c0b03d0350001c0c140480c5602c451350050001441c1c2c80026483d8030b010301c0441c10030741883d0345943c4402d8000741700d543c858a001003d000740e009001c00300c0d005144686c0e100c0185503661903422410303903407060300d200142e510384485182e00c60049880c1d013850084076070229110400b01000e000c8c07030340000e012802a20010b41030064102e0312288191142c0d08844d059034002c070702448516907928004054445601c21a10308c80c2c68803020076500b143c01c0c05154101c0c2c0191351004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 483714343 1250 483713093 483713107
    0xc0a1518030512251202010c0f2316060608070b090d02090613060803030114041505010c021f020c10031404060e0a05100c020607020706020307230a061b14 68
    0x240654801e0444902e03480a0a1000240d6403442c0205190f03544108400c5c000c210810720060f00b551502c0c0384400134840314103070040c0403075404840219135004100c00c001d80c008003000756510324850807e1a02c0c6456081c0020f409000c81c81d0482800c880311070302181e01071540d84200c020f5a000381c08040d603110f0b0302c2001c2a005071921610560300306500601c5590700504081d0a41c0c12904254481a11500003000400050042ca40241640c80e400d86042c0107102d040044040010441c1c0900c0b8181b103454120202592208450b081e20b07403800b1a00200000f000c500301a58403002c9560080c072030210821245403080c482e000b04c4039502401d500070111078403596690000392141d11500d82d1503124008100001c03c0081002d185260001d040000c4c0100b400080241042002070040c019940410402c200c03180d400400c0320007160f0068400c80d0030041c0155460852422079010f900c3e02d1140e03061020034005d60780e0050071400f000700003485000322140015500d001c081c0d0810010701c0411310401e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 483715593 1250 483714343 483714373
    0x41412150c09130f0c1107120f0f0b041101030212190f060b0304020a0506030108030d020a05130e161803030e13051f05030703020d03110c0a15180305 66
    0x658000100001603401c02d60940c0110380004020200309000c5501e4040b650460300c0300b4410080c4070403542c9022007100d4051044243d40b08900d2150780c170440640640c5100740202c000303003001950350040780040004aa400e22000c080c5d403d41e0269040c02c400b800d41702056000344211450100c4a40400010b41d5940204450b54003140e500c3d84182d913152480c0d061721a4061190030050007203c40d03103c1c1c490425006008a81207982c115a003c1e81003080103100c6c98000005a40103120007100159031140c85079000c81e40c901421805030b0a0030f1495801144d0360360903030511440348074071040c400c6001482c00b1017100c0001303a0400c1c070740401c3c01015003400401d03c100440031050802034a0041d40c04511080d0368115402141d400100041e100703c018904100c1c120180001c3c802140141482425a0000350741c031444045c0040500000825030007110f0020310030b25101c2c2000810b541545551a00140320610a41e64994006880494042c08001d2085110003e507a0884002c1030040005090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 483716843 1250 483715593 483715633
    0x10b031e0702070315020a140405092a03010603020304350c0a0812041202030a0203030606090f03120d0605090405120a140c0715020c090624030a02041412 68
    0x1001d0450007000808004222209000050252000b000503600d10844000500148071100c010340c1030304080104100c04d03a20750400c16000852941959203a0b600c40a82402c0342c64590301e06410b03002d020000148054050f0301540c400da005084504c0781c003a0641701038100d500d60b510666619610064080451800c04000d4501000d03030754112a0b018043e0780325403825400407608010030700e80820030001000700c581c2c2c0c03103460100c040c0003c40c105608260060744034000100464015040030a123546039581d071140320700c0a42c201a0a032003e0f05070080d00000164040e00d0300c01c00640c01e180001038a400d011001d144035541000142641d403450050100041c0d00c061101000c00c408010844020130380f804c0240b11810a00c401030140a142c862150141d451002d00d401c1990480500e40c4a56201c0341d200369400101183d01c02d00c5250380902e01660868010103400d441d150210800240fa10035500420035100e02440101d0248850410003c0621403070058a00c6900b007241154040341c41528 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 483718093 1250 483716843 483716851
    0x12050f040c060f0c0501090f0201090608160509011704120305090f07170337050901050912031603030603110a0503031803070312170708090304031118040506010e010b031e 75
    0x6000000e421860f05d40c5400e5074020f403001e54002607240c124a04541e00000101c00502103418404034620b00210802c0502c12210403407010302c240000d00507c145e20450031118241188824034421307040c075080000310303002a41d8039070000c285804003140482c24000341c801c11300d407900030060200c03904040b00100040e10940d0700c18841e201c01d2108140c040544e690300503010100e00c20f04003024008900120f03c14034644484400c0c04000c000c800c0e10340e6440012509481c500740c80c010320040c28080c80038a98451483c00190308822684040c08141d0326801001c1124001c0c81a00e1481c0112001c029452545200e250b0741036204026840784003909048480402800400740d40031581c0c3ca803544000f443c1b20800ea040002c3c844c06002c00c3c40280c0b4904903401160034501308a0501e094083c13a596032082e400080c0c0021107240c9442980c1c0d82e070a200903082041000d804119082901e4819602c14003030145003041005900046200206141a01c0c0f00d800190b2528100701c804840381012000054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 483719343 1250 483718093 483718097
    0x8190204060801050f0405010b18060d02010207150903140309090103140c061b010513021507060f0c1e030207031b140d0203030a0b0d0b1605130612050f040c060f 71
    0x5003000030110400e12945105e080c080e4644205e500d0145441c1d0300b164081103c55114403d04485d0840e48055500355540c04102980e140b0751007042d5000503440c0c0318441e80301e80d80001d89994020602c1c1c1d44030240c1c07022640314855821031400241c1483c1c1c0c49000b0a441103400500c4900100045444242101482e603402010f07500440005004a2502d84c40320a81c0006800d506120b0303020203009101e46588035410b0b040c1c1c4641c16810340d0000d40c49403042c40d0200e6030704401068450500c20344e80e10405020818000422901b04144000780122042c0001d50402e010550021030500740280200c407003660345955540c030b0010b103003030018440c29003e10050b640c2200700c42c0750f21240c0c203013042041c524514a80003140c80c0c0c84d02ea00c0d04800d0b00c0f04042c0080c0100b002070243c0000400c4841100d810450f903100d8122850184d543c121242e0103615918901c42c9816100003c1d51500000d09181ca032419a074244a541d9418046455040c0255802491034406c00f1080180c1d03441001c030008204031034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 483720593 1250 483719343 483719351
    0x3010e06041e020f040e0f0601020a03110709060e0403090e09030702060a0e03060a1b030204030827190e131208061306230d03091a040306020415090f08190204 70
    0x2c0010074101e0f080212103031040b4400003400c0c806200d100391015403089020340b03402454580310300002d444071504c00b801003c2c05041070b0119460351301403141760301805144404200d2140c0d12140c00004140c150780c1a000305000178000f00b5442400410316118070307406002140340200300d034284552980094000c404010400280001d2aa42401818003c05082c440071070060190010040450b459030660b2083c14810041000004d2200003960045c260101c80300b203191380c418411031540030f51180705503405010f405c03181d2660780c0341882e25001d8818103a10b14442d40c0e1100986401e20f15444805030810714120210041944680344840d448400030b44011074580c0c07160140e0f0141c0b0f900350441d480c1451072100d00030f003007602040240140101200d001051040030b0310042c14804490080c1d00340190034144d000740100c100800c1310000c6511410856907140c3c0d41400c003d540303c46000d0b80f00020118540003030f8440600c1c00e4401982c441001908035002c3d5000c14206141842008a8016482e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 483721843 1250 483720593 483720641
    0x1223090f1b1914130606230c0d08040c06030c05030a020a110609150a0b06032d0c0903010b0a0303080133080103022d130e07030c05030c010503010e0604 67
    0x10165000801c0c1000540041d2144041004200d40100e00b0031850180f40103001c00c00207a02250071f40940302c0880c1d0b01a4072102c0400032a183c1e00c158903001c0c0691046a50f0302a08551200303200388a41d001c0d507480200940c40f15070480503035080c40c94500011b541440481d03a009841c5d0300801100c55107003000c076050351006d4012400d00c03070304031080354180e000948a80b0040011b49a01c1d540310220130010041d140150000070018040036007040c202410701c11346040030741004154000e00003041ca4107000c1c90300d45100450915403200100c64001d500301003105496007001600d03d8144c0307a00d511002400d80c200382c0c103c0c000a502d8040d81311030001e48039014045048148403c1c90080d1140c1d0340c12115811070050180c1d090005c1c0000d80000081141801c40403461841c4001480d4210b030146055194500c0b0308010b042d0314402408503010f20720000040050002c54142126426000d84020001d20030040d0f03003601007441818152509600010719615080c2d02140038410110300c45200c1c4a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 483723093 1250 483721843 483721879
    0x3010302060d1407050a0906080105030703060c210203060423061c080301230109080312130213060609051909091a01060314130f0b06011223090f1b 65
    0x50555841340810800104501e071260b020810002030030442c02c10700041e52400b00840c0d5955954440a08420396030203000f0441e51140c0c041c5228111000d590310450a842031503c4000e51080d507505108a2809950303000c0e40c0c414444c180041c01d04010840b02c182c2d910001e1003c003005541840a00c50700d00c041003030020b0106e2000d036000e81900e2160b840103510045021b561000f049410a050065010041024000002c111440c0d0100c1c2d6009295944171204100d2111481000007540017020071700210300400700750b00100c200d84440da92030550f25507c000b84106031138039200d484405c184a0800b84001c480a40014019521922072441c1445604011010050703080e0003200c0007a495200c04e5441641c08800107402442e080c94120800203207565100e075070ba031b0b03120b0002c14000c11300000030100d80c05985070041c4080380880a10811002510f944007400581c003408400581120115184000018010301c1074091003006098000e13050401500902c54a6415940104d151201000f203903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 483724343 1250 483723093 483723131
    0x60702150d0e10050a05101215091104051014090621060403021510030615150504081203090c090405010b0d0b0106120e0c120c0607050606150f03010302060d 69
    0x310300b0202821422181403100c0c025a1005048a03914034200002c1c0950340b195942d4000444515040000003581c481c1b4002c2c04c000c0f440e524140d94103140030041018800345555401a22100312000c03c0183d41c3d040125000346264000c4440141c0401100701881c2440e000c0982c1108000700841c40c400b03860552043c2a04126503075482e5600200180410590108100651001c90500340d03100c40c41c1c00366546e1400800d40c030001d420151107401280100c0103004210001c1d1900100c1e032555022304c5403000e051507100b0b1090b80194030078102c400a81c40c1c00001035074082c0201e00054075000800104100c4d4880c400360040d03c441d50380c0c1100d9901503a542c04c01480852180b001c031001ca41c03410a000c0c00700894214100b1006040803200d040043c408111a03841c0c040449281c4554444c250045240132421111541c1091000528900f4003c0c001440d62081004868880c4128142840c244090003801d44c0e803001942c0600060005141000140c5003001c12884002442c0550b03203000d00c1a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 483725593 1250 483724343 483724361
    0xb031207050714010f05250620090d030305040503040b0d060302040506031603060513021203031605070503040504180206070f1101030614060a0507081b0d0e060702150d 74
    0x9110000390003010080d00b80b00711030083c001d86043d24821102980040c02106940d0000000c005c400955007554222004c160082003041031341941094000d8901038000b800d10541d4850185040601211000c2c031a00882c2d030804d1018150b0030060401ea90294040e00000d00110f030039000034440842c0c03070654000988cc54250000717012900500d180103100031160040c01150084d0814012007445c082503103a0101200d60218001455030b98100c00b03881440d02400009622940b1080040d01180c800409140030320b0781c250443d11500f88090080e9118070030780c10028030a4005200c104101c1c9450750002030036000802c03c05407451a16800900d565104820807580800f0740c14a180c18016044c2e40c8007030380f0b803081c02c04000341410300e142091264440301d0028440c060000d03040ca01144198182c68440da4040f01c0c1c03985586050301c00b202e00491005100989100b00840405002d201d128182c502c1c0350060407403803400550f9001c1c403c031601c100394a0792010404129564024886104611003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 483726843 1250 483725593 483725623
    0x30d111b030a090609213e1f030b0d080a030527100f0b0607030c050d1707030504020a0b0301090b010801090e0d080709030b10080d300b03 61
    0x1452020300b4002d094010b141e0000030812045980602950002d400262103801c0209903c940f000c545240803402c4181404000c0452100000e4542060610505004822003062032030131450160100380844640d03800c0003044a07440c00b400d002d00c002d0103944405494107001c0c20811900429849000f40759110805103800039559508000344240810381441104e40d000100f4030b00728180c883c3d036980c0c841486112104d07103a070b1094010440100c0e940003200a5901804440d102c514604016000c0c8540d0301d001e0f42e5600903022403502c040e1043c1c240c0c0340c2c001c0c4180128046070300d40d03034400c40c02014000c1049030060084040480c05902050145001b000309400116881441c03200040000e0b030180d109080c024201031845510700c5e800304034200003080703a1805483d6603465039402c580034203c41c0e2000e8040c1421606201c1400e42c400e6403e01601c0004007200c0590f81c50300e0b001c6401c0b0030b00014042018600403408859401207540441c040d071718901000c94031201c1c0304002402c2140090500c84 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 483728093 1250 483726843 483726847
    0x3040b040e0a0b030d0315030606030c03021503060d0b18120408071d070503070c0b0403020309120d171e0a05010f06080f0a110c150a0501090905030d111b03 69
    0x415024810401d540c4900c90200a110394540d5030003003a80c503042003200d0014907884100143d140b01003902480c0055401c81018003400b0355034200001214114081680503442629141504560b201c040324042c8801030582c00d4860460344403150408406000c888a460740b92044048a140030080c450641840701c1c08580e6452509400384d16010721540410300050103a07101c040900c00542c503140c0d0145081c1090303596542c90310b8003210700c4c10410400400039509802800103056000001e07000044c8190b4481210b1f0101c0e005040da101804201040001c20300003c00f05aa10840c08050304050a40c1802003207410101d0480103002c412030300c0e90703a9a42c0d80e200400003500d458100c1c0c1c0041c00c01d410100140d0030440c0d4041d1905000a190082594885685543c44c000b03d604480b074611004047e517018039032803101e12031603a5044d604040d895050000100e115280d912840310282c0d88100210714044002c40581c014041d00d0218807022101807003100420f44072001140d194400e082d01960b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 483729343 1250 483728093 483728099
    0x15050306160207030b0a060b07050a0c17100e011e1a0d08031303051303120306051507030806120f060403030c090506090f030a0c0618120320070803040b04 68
    0x9460100000e1584a003a2800504070161035004224202600d410112044403a0b4405001e04003601295112100a090002d070301d000f480400310b5078001c814850000402d003542e81d4010782a0b00e41c005c002080703042d00004d58025590036281c0c01741211407004400810000c4c881d40210b10a078100035403503480342e62502c42d011040124415501d01c0d0080464180ca03c81410742c50301c01321400020088101e88003819150000d00d4000c400b070702d10b9a60f10080300503045032030703240101c1d8204001d60342c8008a4101207002c6070503d80342d8001807929218800144c14045035441c102c0d04060043e002c150001d2819183c032030800c0c0240038682800142100406460a0601e0018102c1e4800a50f8804100203c0340900c4586e0703500b0200c030001d210807520301c0d005444000000c0d0400788841c40c0100311880d180c000107082d98202410103000304401c0c45682100d1b6503840d0349420040819002000601c40a03810f81140e5001409030403002c42040c1220251500c0f4000686582e00982041e100500045420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 483730593 1250 483729343 483729349
    0x1c0602030114090604020a020d0c030e04090614060d171b0d020706110a050714120d030c02070803040b0d1512060218030c090a0c020127050114040c0506070303020405041505 76
    0x141d0041405c1d10118981050f00600a4071046000300702d400300401420080285032062420824201300140108145500c900c0c01e00014031540303401d04940c1251000080007841e0120845080b150000401d81c3c0c807030000070303440300c2c3c0d9400985030443c0c0c2e010802070901614006c0022403003131080d0750014140b0701d05028001d45100803a8820701c14541c40080c00100103a4042404001c4940d0804007400100c41d80d400252028016103000c4620b22420010b1181d855141e0001c0d0380d40c2a25400341c9180c251290b110b00e840f480b07a80a040b091500800040480c01c1c42d95011a59100c103424120181703c1d12481420500460400c058a81030f401180d5081001c2002c201280ca8150440051420050b04c4000c00c0d90380303d00906400040756a86860003050303000790000902c0d5010a8801d03860454034600000341c4102d03d86d0169015841c10300e28444c2400a18841d5010365000428141000d1600d0704000e031507408810104c04050b000d0000245548840c081c1d070009201d0a505008424140828 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 483731843 1250 483730593 483730609
    0xd020a020922110a1e030b10030c030b06040f020705070e1303022d1504060b04291f0519030b0105071104090b04150b150f1803030a050c0d020105070e1c0602030114 72
    0x2011048c03103c2510810000f50300b00040c0c03040780e80c8003002c00d005940c0c0d20700007001440e1a4194051803030000a0343d100f040008200031068a400800f888034640380d40d40560009000d045d03004001d6441000c0000680029402c1014000b411620f1409908a42c000103401c0c0a070400510301d40300f0002040c441040420b025051106c07409680801aa1040c2d4511007480c100110008103004070001d01d40215884071010f200d01c045a54007141c4041c0e222580040c0f65600108807070340e40d0b510014005518074400d000d400b4141c44160744041c02c040441e1030344040e41390050100e07603106a94040d6070b0001031003221000c1c40340f801082881d4046000e01444015201e800005c1d0384070307419401c1a8440d4a04031001d507001e1140c03264066440b2406c2c0141c0d002d0004207600d403503501d4440452412403080c1c0c018018a107050340002a18040340400d04281e080c0c5070159032100c0424a910b4445600f403c21414000d1001940c80e8811915041a100e240480c1d20a070440d9041c1020000000d026062400d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 483733093 1250 483731843 483731851
    0xf0602010c030b0607020d020f10050706050c03060f09071106070f020c0901030b0106050702040b030105010e0415060501050901050a0219060c030b03070e041101020304080d020a020922110a1e030b 86
    0x600b0302000b0f2061000a0203481041c400902c2109903d03102c07010740d102c0d482c0241c140c10015104a0135040b809002030401c1d00510300c100c9919040a0000d40a4401d850550303000d6031001c2c021035102038404080085201e8024a140e003001001e061030748034101c1c01c21106000b0340031500d6400319140002d100034140030031081240d018010820040001401115505045941c40c0c5405503d868040c40082e019161242c411039040d070a01e070020070301d443c034490085e009038401e01c3c00c00120078041305080141c850300e10401c3e01140040c4188103ea500071001420008030324810341c1c1803428403905050512106c10b0095503025035524000c50b00680500ca008030440c0114018001945010341d14403030030740010401403944e1940c00101c1105e03402002030303c0117840700d0000e40382a2003d000000307640304000f6009900c580103c1340130802c07002d0440001403c507030102c2c01d4000300102c6526844c0140302d00c00d035a190025802c00c00001e0344212480c9029060391000d8581e2056807850170140d0720088050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 483734343 1250 483733093 483733097
    0x3032102031911040b0f0909061509060d0b12060612010b0609130608031b16050315060109051008101e1404060302060c030703090b030c0a0309020d0203070f0602010c 73
    0x1d118070581c44200c02c400031a500300d0040760720082190b1040c3c0c24055540002a8503c0101e02219021508005401c0d1010141c03156485561403804204840708043c1806451035010000c50a4505021004104010f8080c0000c987c00c841c100200b0000c16159030300c6106c1d038026038144107140c5801400c2c0301a04607400000d0107a40030480010f9118883d001c2c8080c422601c00034400c001240c550021710040691500381d84d2617844406851a268252150f40e8840e405951444411030642d0001c020036240007400034082c240b101003c6542d14100a000c0354103200d4542000139640d40c40160f0041509520380d21010b00341401c0014035540215138000034002c2001a80d00f0b40c0d13000b400c010507802c4441e200c5070008110f0b00900480e00030180fa0300083d41004e4000ba802030200800002451407a201e50f4414001c9992600007803010b00041c0c1d10b1386405e035410018005241d1180d00729001d81d81c0014a02c401042e1158002442d00e04103138881ca15081001004011168080c82100d14849042c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 483735593 1250 483734343 483734347
    0x1f26010c021c08190507021608070b0304030e040f0c0509010806090402030a0807140a2109030c120501020c0a03020f07060e010f1b061a0307060302070c09021e0403032102 75
    0x2c012014003100d081504228603400043c48807141380102d6051003640900401850400c500004d4032004a26200154810f117401c000815180028003c400c44e88074841c0c03142103440d41d40c6c00700d42a0450119055005ea00c620f50441220303210320522403196019115036580d0300403e400501460b60040c1750368400c152030010800580c8010400060b05a80030000c0d681d40c144900e007500005480c103142010500c1540400010001810074060004209404c100c00c4070002d680101c0c2d400c82c05000c001e21810060804000c01564034410f4a00944603800141c01e080782d0300c141c0781c6080c482000540060340604030b01c0c01075100902290001d402c00345800c0307505107040c50020f8800103006054200b00001c003903503158042d100724410010f0303da10000611025450110101d210070300948924803d00804200045140c020f10850f4a05070740046034120440ca041c00810081d0031407021150100c0f0048003c0c1c101c400302d50005d10181d442510342010400c000c0c2248000b10038140c21031602a841 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 483736843 1250 483735593 483735613
    0x150801020313033c03050903090a060302091210020904180f02062109010608070503070602150604150b0c061302010c0b0601022a0f0a030b1f26010c02 66
    0x290800440030b01d03014113040d00804d800f03207001c400754440c0b14003280d203100401d04082540400f0609a1a080401c1d50741402913849200d400f40d1a440f91b58041a480207500e8400c000c018029005050222002803200c0610080d001580d8201003489036480300c015800101051985041c2c400c00d080600800c0504180d840165034100c0b032040d41c1000a44215804616444019030341910910f4011520b5070070902c42c2070101e2950b028040718080e01c0400e00640001040d10308000902104846565000704201d0b10524a050281c45000c1d0803560080d0b1940400c01341048500c1c10200100b1000b103e4503611a56400140e007020b070058104131840020200a50150380d010584810b1160005880c00607070300c541d00142d26101a00120b0015aa442c40081e24518140d0200004032013003584c4920f5007010380401c0202401300780c0802401c003c100c0c40440d04d85000039081501203001d401e4280709581d02ca00b54221070070304440280a12003550055211040760070701941c541c8860342c1c001031900b612 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 483738093 1250 483736843 483736861
    0x602060c0715060306020a0f0f030b281a070c06050703120b01020c120120070804150302210718050609040905100f150b0301080601060309030e12011508010203 70
    0x718540000c0c081414000001054106a0340100015540a4400c654441d0007500241003030b0101c00c055808550303010344801c20b85000740513503000782c07400400c988503121000408440703440c0304074a2803410320002400803130511040d91a84401c3c01c00e08000584845607450401c0c20310210740c02c10001c200c020311450000035000603101842c1c800d06100400c140d000000100d19150b200c52101c0d502400340010b6008001c019444102900715981c002281200c0709810280e20b4030034580c0c01880072100700010401d101c840540b03480c04480da841c1c05031a10101000c0d4102080d500c601030f4000b01841414042100c0d0041016a000301d685009008041d21313203000501d41c2d0184905e054041c1e519490610100181808030701502c0b82404801c1142c3d441ca1a007420050407050840d10030040c9201001c2050b042910940341215201d000420350343c1c0c01c28008038040c01180340c0072404e2100055124400780e548003001d000c00e240c030500014001c044c62503400d9043d0100e9201400d00d034410010b0003c000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 483739343 1250 483738093 483738097
    0x105030f0d080a0c110d0503010515070506040f1a070915111507032a1704150b010507061d0606041107060b0604050603040b0f0a0209010c0f03091d04020a0602060c 72
    0x1c1d0f48580010744409140c4043e100711800d0202e0300b40c903024074505104800e070400c0c087c45c1a0396080d140c1d604410a0300b66070342e074548603d00f00540303c3e03407110300000c0014064403028210321f48a0100418941d841c4012002803000507589130000c02d408032030038421544411544041008686005c002c0e0b0f803912075a04e0f4460401c0d5044100c512001000610418060340064511503403111410700e10461070030169414040c1c00c140c4400058800280441c6107003120849401f03180c200d0301c500203c00052103400010800840040c3c14400244130f82c0001c25001c0c030401c080740100316110321019040e50002c509181c0020b108600c124908421039480c0808503090b205025441600000c04036152030014059008503801142d04c041c0020030042080b207005202d41c01030200500404050302c94264030810307800f13000003076400180100b1140c40400c01c800c9038000e0050207820424001e03502c8004103804503091400c260b01ca9010201484214140754080000415031440030300058203000e05405194 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 483740593 1250 483739343 483739351
    0x50604061d0c0903030a03090c0501020d050f0a02070b03041110050c03040b0d02040302030a0c09050f04080a0e01030b0901090605010e19060c03030e100f2009011202190203030105030f0d08 83
    0xc558010010307080c280d8010855001c0c840003405c0300d454480c1000014003a01205004481c6000b40510004555000041451074401103441301ca0502524400c11912030704031103881c00440c0b00f03000c400101e40e0b26440007907000d18000c100c0110304140c00814814101619180942086402c100415903450007009490075101d20510700f030b0380c0d003c017960303018064080c41d000607605025241c1c24604008083c80e0b2401180c001e0b0b041482241d07103803820b4801c3d9a00480b000f8210174070410883c9405440307008026450300c0141000142c00d03001d0f401007804240240c0000c0c50503503688506200b5980c2201f5180c2d40c100341121148148000e011448060301d00d503209960500c04c000310722004050198101c41c040c05940c1c000c0307484500720391142c00050300302106000c1400f4034000022035800469160307012030014003c070062602d515607004440220400d41a042c180f94280248540040c41d5040c40c841101c06900468680d4103040402d410010504420b6110758029651400c00c640c00c9943c3c3d940c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 483741843 1250 483740593 483740639
    0xa0c020c0616032f0f030f040905072d0306050405060a0e0903160803070906020102070b07180506040803040303110a0b0115050d18060b030343050c0405060406 70
    0x60320b01e0b260a0740c4808007007258088885200401802c48000e82c43c0d681c0300061103900320384002148560583d1284510080c51405040800c01407203c3da0a036004150060102c1c1341c440d628910000c150002441e02d120800d01400300f11034000300e201e5150007024082c22045804000c1800c0060000710502400c0c0f10704520282c2200c00980c16200c10f100340c03010341545c0c0582c01c0c1d040751140780181c1e0b00d500885034500816148040811145d10500c25103142d0383d800040030002e84c03200c2005884c0011892111640e013000250080b03090f0f240c50016200405965000310b856500398071700036046006000407051554058240000814204245036044030702a0900042089943c3c504843d00c1c0700741160110310908106110140130140e90188006600410040150360718a070704041d12880341d10b0758aa650552030800740e416881c142c4a8100300d041181c070000c113081c0658001614500c0701c03901624aa00a4058034145080a0044036440302049034108641030410301075082c054132103491804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 483743093 1250 483741843 483741877
    0x60612040b060d1407050a0b0c0312151206010e0a0b1e0f213906070506130b06040c0518010e03160302031c0504150c0b0106080a0c020c06 61
    0xd61500c806843c54580d6800100145900c01038450031651040300384203040c0120035020740012803000490607508402c4042018614216981c020700c031440c40f02038100d06503416841e1900c04283c0d2840065000f00070120050441c035803604481c0e0030181c40c02043d00700e03001e08100800e103403075a822680c45c1c0c00c8241e0707001e0007852442101c04210012030812020b0b82101440c6001014007683c2c0400000a00d4244100d58100301031001c0c42001c1c5082c1c20100020707141c0d5010100010a4945140524500c06014581840c01d5500e8281ca0010300b43d0780c10021003e41440541031008003501e4a91000c02510300784040201054010444e05c21000c003060401540b10f01704031280c0c401c0c0b284407050f1800404490900c29401c00682c60741ca82032004070f2080c41a081030a9140409038240c0340a411f10351a898241460140031140342041000300704208103032101908005011008280d007e44045c7d40e98003068038003100d2003c221950140d0f80030555024070660003c13603407400220f03880b042c01d2011442e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 483744343 1250 483743093 483743101
    0x3110d0215090a080304080403060e0f1c02160b0405030f010b220b120f0d0c02090c030601120c0906300f060906120c0e09101a0402180108060612040b 66
    0x150400f0000040200380d44000002d01c000d0001440c081d20035a4020300007000726800a14074245d442d03140e01907850150300006100117010842e01c0040d12082000e0040e140c241040742c0800c1482040e6801148a02c507004c901030205080c10400d0740c2d619003061008103d69461940003900302d19006082601c0207024070340180c20601d20740c10100394400040d0020820400b180019500c0318011048403045100f092058081c561060a9001070640c02070304110490b1039a01400e86990f1004128034180080d9954802e43c841075032180e00310169940d510500d0b010300b4030030011308014a06600700c42002141c03c00714030f803c0908038407414241d403d01340000e041000e200040046c0140f41e00c1118602d2034001c000a0600310b21b000c01420602c118142d0551685480d10240c01d52000e0b605401603520031640b025551400780c2c800a100c00340b41180f00c4600643c24001000d07a4412501d01810804c1007000c10641d582003c1c01c96007040c0100d481a052041d00000d0603030b28000100083e20b955401d074045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 483745593 1250 483744343 483744361
    0x1170f0a06122d0b010e0a090f050c1003020a023708040504060b0a020d111908090907050306010507021c0f1a0604050c09010e01031103100303110d0215 67
    0x1080007403450b24100c0d161402103081244141800c0022142802d407035400c0810865440460a502603500034004801c1e42d0a0003003c03000803d004041d0121160340d80c4481010a006c07801c0041214400c030300034200f410019090000c00130030411150189030060107440503032900407410030600161522404006404580d41080e440320529201d455600040e49090a10103040014419144103417401c0c0061a42c0703c03062006486140040700041e04415090600700344240030544800103504110f421869442410348050030701010221aa030200089054003420184481d030b0307206e00365060a606620f0b00400282c0b0b01d1141e02e0009201c0da6a43c03114002c0340c452903001400150304140e0080b02070001c0e24081c0c00c2c0a44d080711140e0481c0c0040001031003860035001d40c03072250006c070050301d04140e08540150f440402c000d190a05158903122600c004d4507150015510402ca40c000080d101c0f0710f1410060b00e075010040004085401410611072042d4001482003414103000c01503c2850303440707601c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 483746843 1250 483745593 483745601
    0xd0b06011806020304060905030d140a051306030b09060907020601140619020307031d030c06180904060b01030b010e030a1b0b0703050703090923070212030408030109050601170f0a 79
    0x199140700d140e600411020782c0003024005807010758650000e05915401095038071316112300102d002902c00d00c582014609058094030340c448541c2040c9080400781406010642c4284e000306c00001d585901c540c60754604000003030f030440000d40e140c000300e0802c0500252541c0d1305018614620189000042c016140c40c2c0440395170010860351503050b814940e100a40700d07481800190001860307040c255100280000c40f0b44207100005008190f0701c950356090100c0c030340107400456211910f8401c4c0c507510741c48010603241315911030000081e08068410014003191400c646d00c5041180c0704005181c01d441c0042c00e610341c00e40080c00300450100d0301c5510054003409410120216401180c45020542c101c0302800b00c0b588030341c0b00e8202540e11004101d040300e01600a00e01030035400d8190030b001803070003c4000d81210301c91059034001c68000712748000590065801f01d0b580c80001004014800061191540040c400d20b4480008030f24a82e8018201c50040c050f0800c1c2400f07a4003040c40c104150f44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 483748093 1250 483746843 483746867
    0x170f01060f180e15010503011404050a060b07061d010209030c1201091e0b01150804030f1404030f050f010b061b070e07030c120612060203041a090a0606140d0b0601 72
    0x8412407601c0d103c4581550703074602030756102406100401c01d051158002c1041d80e040c1c4111860161502141500b013101a00c0c0c081d02643d41c9a68034000480e02440e00c000404496009000100d1810025100014540312012031484264418403446145540214003106000f00c11205440407d1030f500f02c3d0750042c482800020701e0240d0b88841c810b69580c049141059107801248000e002c0c1c3c1c0ea031101c0020742d48031007070328400140d0324600140001c0e0140d407400b101c51b4a00d00c0c01100164080003080916809500181c0c2c0e18620340d0007417010002c040041c2d0089905810090003914540000328520f8007844000c90002c83d548114803074240c004110503001003075051520100c45c01c1110000c0d004040908508001400d620148003014a10380601c000710707541c03c04503c1008500752a541c000750000b400490745a4144126204040e4502c151b0600450521010b48442c1c1140d2034540100d4032580d100701c0400c2c010034001d030410340d112844144855048841a8401e40d2a81c0c0102d990142d460 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 483749343 1250 483748093 483748127
    0x2202070c0f083403081308060702070f0b0c0a030c050109050102040b0307110a0b060d03050c0307140f060f06040f020705010516020106050d173403170f01060f 70
    0x40700007030b4903a0002202d6a440d02c05251031007418100b000800064081401e07120010820020108001980c1100030405c18010000040c8015180ca280501f413001c00d82d0524010ba20120040c0002c01110031300b20001d2600f6030515241179244402c40b41c4807080e1107000b800f4000805c2d82c8506010003900300e80d01540c0e02000840d6110744464484600750016079001e400600b402900410100c40041d00e8600340340c210060407042e544075030400000c4024203404804206052000c0c4109200401c060049180706061050310328a840d141c440c41c081c090391a201c0554041c4d42804035001020207402d41260701554041440300038034204030b0191290711300080c11586844d08001060b450b4402c40700d01c08105a00a1001c2c035a184204124099013402c090441380c2e111141d0328506d06160f004000c5003411001040120141c8445103400c01c0c41e96503221028000c2101c80020164400812600104031058440c06810801010b0b444008140126024000e039a41010400ea0246c04100002500c503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 483750593 1250 483749343 483749369
    0xf040303030504060b0303070b0c09010c0219030b10060504140604210b13031e1701080d02060f0412080a0605040f02090f0402270109090c030e0c2202070c 68
    0x34038000300184000c4a0a440307091900b44801204c4c034010049540d40f5420401c40c86054a92952101c030076403080321001d0511010311412801070b101c4881e201c8442004622144c0c80500d981031000d0020300084c01e1084007040f01e607061106540000581d0252016102c0d03410041d2400030102d5440d1041e0740129628201410a00341d0755112005904c40c405e21902c960032031911342104044408014440040c01b080075041c170400360b8411850241141d91980c580303d04095025183c0c070801440031307045501103420001d44150425010814130f03400a0021044144510b0319844d0000f406812210400030020060701181210825400c440003506008000300851422481820000c1d88a8030b041d500440d923a04145410340352900c2030320406840c0580c00007420b6005908803c109402522060601c045440c010039400d41d5846410303024592074800103454141080a41d01d01420100d802e4450a03d0041c030058041c81c40340c1202c0d16001e10707031000d0b890b07103894a000008105190046905c080b05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 483751843 1250 483750593 483750599
    0x9150313030e0102010b0303090616120230040608040312050a0b01030b0906060318010f0510230310181208040b07030b0a1224051005090910050c0f04 66
    0x202554000301903109444145800415400580c00d941b80703190555419003007400800340600303001000380000c020103842035018070015951b07808010001d807460801a8803080300a614102c120107941003020001c68104d03000d4440d02014111482240a40c1c4104403e050120381014013070b10001c1e0b10a4690402171040b442d00885020003070200034502400281403c1e5109098140140e03600e00541025042c140346a0320010b000151520346241c94046d9980c5242e0211101d1700340c41010f000b40401c07021030780c44a2411a40040031800e14010100c41441580d80703004917540081c010f00100c1c01d1900c0803400c5000913000305001c000d1400302a100c109211080801c141d844058140700d2441520000c00f5034490348012012140c2600301103800a01c0000244400310080c2c98102c09241300c0c03800c0c8804101ca0f0f810120034106a2080c00070140e40300c2c070070302c01410741806041c40070301003c1c0e40d495140e10742000c600b40e861041904051200f030752207000c00c030b50342c001030101d0b40100103100515940d255 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 483753093 1250 483751843 483751861
    0x4080a15090b0c09130608030a0f1206060c020a091e15030206030415140408090607150e0d020105010801290f100203030702100911130b040e1b090103030f05091503 72
    0x40301c4c008041c4941e030aa0400300702d96903c1e1040f00143e45804c0019820212410804d85500d01c842c14084140702070f81e080804840802e010f0f0b18040e100380e54602c0d5880c2410702c1400b17019010750300301420b07140c1803110b01c1c0004a11500310350100d014094000c1414400e141700505408030642002c2d4101800201f00014032202d02050180d00b441030004008000200d080070340382c104180c900525144042001f810b0398034104005d008000c0c003e00c002c0003449900d9455000b240c51010420301c49404c0210642d2403240c080c450b46004042c030800074000e100d040c810290040107200c06030f0b100c071001d8051428030703910f8842c5d5500b802d14020345400d401c1e0500301c030b020350360740c108643c44030041c030801010794000102c03030141c0c1075615401212002201d8201c070410410b401c61740c1e212461680c0c4c030030a4101d0b659450280000703101d030110240054540382c04036824203c0d082070106021b00180401000000c1e80140028031181c51890f155444002d4400080d004455226480c0c0007248044240602d202c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 483754343 1250 483753093 483753097
    0x11406090a1a130218040501050a0308071104020c150c0306010c06090602070602120109110901050d05150a091a0d050c010c111f110109080319270c090204080a15090b0c 74
    0x5c01403250b10103c3c241c0040c00c11040d00c000340100b640149166030708000140c02d44018000d150b204034200c1840c0604e0b00c000c20304a03000400c10051542c04100c840c03049500d07102003660050110444c0302d145161010003c5c00c003e020100c0180100d903034240c22001d02807140d0684212540c00716007503540b0720400760b920611080a00900164034176001b80c41c2c1e182805002241d68660048e140e143c00c2c412001d10f018001d01f0024110300c0c0d480d40c1c128224900d035440481c031102800c1468400121a8200001c4015020001c801240141203184c0c5003808a4800a007000301d410f802d2801c40a40c4429240c812190451948001d800924801600010525040d0a150764902030780c0d8856440c0e4021120720b0903900358640280c040042000440d00300040d5005070342c13502050050100324040781089442c02c1a43d000136030803031b00000260b40d40801000c40c0c440001809a00030a40c01d160520043e1a25a18141c00007021040352071400905808980c001e001c4207a04903149004a24191058803455 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 483755593 1250 483754343 483754357
    0xc030408030a050403050d0903050c060702040b0901090609060b040515160614041502071214040b030c030106020607050f1206120d090e060102071a0306041b0c0302011406090a1a1302 80
    0x9401f5451442c1e110511540a240440e03411800074403402d410b20042c00000e034029440ada0f00240c80700b8225031207881c0c0d6005c4030b000b032419800002d00c0a103815280310803140c69030007940000d40c0030401080155a0143d01403c401100600fa42d43d0f00780c00a84001240001c0400400725414182e609000400c1e1294142c4643d005583c07000d00f22650201010483c03003140401011112148403c0c000b2500c14004200320102d858603040c907094a440b440c0c10302d03400c2281c040446d000004018071002d035041c8000d541003485428003504008801100307211038080e43c212030113100b000702c1c001009a682d40c003142d00c1001003013066504502c0e1400000b8030030b40540c05030300580036640001c50141e504c00102c1808039034070f60304099003c0f101c15282c801da6500103080c45078826200c0124541900b40d0380c84001c1d40302c042d030300c0304a0f0400540c0341c041e00391a41e900840ca02c1e404888100041c6494424810794021f100c03d00000d071008400440703090007450144c9041e00302840204440c0161030b680d00030450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483756843 1250 483755593 483755603
    0x70303050109090327080f01020712080c0d15090606080a1406180c19091802270111030408010f06090b0102070302060a0e03011407110715050c030408030a050403 71
    0x40ca0b03807154075140585045403c0100056000003400d030381c401390b203000f9020703940c03d02041c6446103548000943c503100203d24404083d07540081c8000404c92a414024800a00750912154624155007004518011542e141e1803650b02d4016005a000f0a0300c0781078050700d452401049640e85404006008501c2101d070388080c503103000da1640e240144035144c01d1003084010301c0070303000c031070011480c1d030302c1c00b0002d051620102d50038000a45c01e1404445010741c1c56046968483c5094175110250300c0b11500c4c8081400407a00c10446214000c000b4080c5058501004002c6078a0300d0341503004813484554025684007034000800d0129100030b042d08071070588020040c050001d80e84403c144411540c07907070801d41c0980c2c0b02800c10401814031401505208609050410740100c03280042403d46042c45843c4052140c1c1c5010065095007000d04407104040c0320000f00a05420110920018840340b00c0030b00c01d000340800c030700108401c00c10468005e00107a10991b516100381c0d0300c01811681050100b240d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 483758093 1250 483756843 483756851
    0x11404060c080f060303090123030109140c09010905010e210601080d0e0a050d080c0f0c091e0117120c0c030c010804030207051c050109050f0610142e05070303 70
    0x50701000441283c000d13900203024502d0100039600566030a00d005040c03865804c00c80744801a00085c2202443c000c1820400205070b0104046264001401c010028000e000041c010050740380d90003003400007a41c40c00e003462129000d0100024a0100200c01d01110b07110b6051955084c152020a58a04032034030a401c44508114901f001d690507041c0c0524540c001e05e54007030030042d900e4030818091469014950207403402006010060410303603040d22841c9a43e01500b401d0100e401c0207080f465004400e031240c07501c400113602660348028010b00c0342c02c00031034049041c00410101409a0b400703c0d000c944001d0b588064082d101078450ba21100098401d004905c210a80c41d401082d0180c03044c0e0f4035238084e1910f641018100045c0d811354840c80f40004203c1640d00d000a0303c01d119496005000c0c000414640039902d42681c0b4081006200340d4800100d12003c06c0141da00c07003031200c4407207000c85030b400d00c01c1c6110b18140154400301e104a00c5c01c0000d1007008180a4108000301002800782d94144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 483759343 1250 483758093 483758101
    0x2070302010606200619110f19112d0f060412080108030d0e120f1c020a0e21010504030c0516150c030e03070b041d0c0a0f02011404060c08 61
    0x2815204242c00301c0b0017a0006000620207007034031110500450020200081c50901c0c1000001c01d503003040000f160070f06000600880201d541c0707000303c200801945070000c680ca40fa400481c1c1c444a50344000c500020310400003000a0042c614401018001a0100e407945c180740c001c4035030b1300e11042d28103030740d95144038106204c46403017000d101c0e040e42c1e4030300d00030361503c800d251b800c0300203000c200d202d0211130182050182e5081174880c010800b010f02c2180b42ca0f1900303005680e40000c014640703000c143d42d03441000600011a00080400368a0b40c0489108110030841141410705418000e000f003019440d1004000030180c0042c5810b0520307001c1c2d402c4400d080c00c1251000e400e042240100d4051003003c01d0025025803240547e9003001e480307490a40c184840c1000032901d4a503268211a40c145400b203002d00040207503001d0324141220705e06180000c0d042000301442c2911030a50540100320a408401052034003d400a5100c1241a901c0d188907107842e01f0150000e0020f42070303210014507108045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 483760593 1250 483759343 483759377
    0xa120f0806061e2b06031518030c08070602030a020a11010605091b070c0e01180e0c090604020c0d05090f09150913050601060f110615090a0b281a03010e0c0d02070302010606 76
    0x143d001d20f0440206566080c8e071500c3c241d40c641100d240c101c0b1291400c010b20f0300000d0742c900207140220050140982c4850490710081c295201c00390302180a60f26103401005580d0b120810a80c00c1038500828080702e181d04482c840003031081c3c000143c50f1224000300000d2070b8160010403070480394101c460090000320019680203940b54403200c0c0748a903000130946501c5d46407110340303650000d60081005250450040030305044c041c403a40d07031102045012503440c13058106460040e04283c021290500e144c9400c4d0200852001182c0314140100c840701c0c001a005031050003000c0c0c4641d080710845a09680d9440002d000038050660300000642c06100103403030303c000250700d5000704140d428040d84012020203000310f205008022038030690b00c8020020003a150044800441c2c4481001c0c3c04012881d11541c40002409a000c0c08481740000c0080d403a0305d281c0d20036203040d66540c0b1956541d503100c501107244940504070304603c1007440020f04104241d0154040c004890081d00e50b000c00e00d10174030034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 483761843 1250 483760593 483760601
    0x1e03050703200c060c04150302090607020d0507050310090305250203120706180f060504060f151a03090a080705160902071505130201030504050a120f0806061e2b060315 74
    0x8816031f0804880404400760300a4001c2c0650100c05000745003440a20b800040072003180c1c140907074041d040b084043c403441c1421b000d100508050380e441807100361010313980181035200d050140c205034895851019191164011002c0301260000c0460f00902c41c4a40030740b20a601c82181202e45900e0900f05a2a0040034004c084009030401780c580002029503e42001501004108480c29a59444d401c400c0d00d50034400c100d0102c010241e1840035604114400c6450642069100101c40b010300c0bc00410103c00680c60403075a0b0301ca04021b445191500d0054500307502003d80c01050043c2c0440400c034000d481e03010b070030f485004a41641404480000240450700d00f501d0407100c07140c0840310440554020f030001504a44150100e40c06582182c80b10301160101507440c8002400e210002502a50300c00c0020703800180884060b8988900003100d181c4500011003540014500130806c0e01c05030300304007002080d0ac080c40349400c80180416440d08020110340c00210f03903010641d440940c4070817142c8a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 483763093 1250 483761843 483761849
    0x903020f040506040e0303130303231801112701170c090607060204091b090608011505120108210f030a15080f010f05071e03050703200c060c04 63
    0x11850181103620900015000c01401943c20a48403200700c240c01c4020401107200744006003000c0b48040c11450300609803003180d00d00010442c50810503a1614100c0024103801c034944c00d24003071201080151309809856440100421400007188600607000f45510541041c19030300e504c03070100d112080040d20720080030f41c1e200c01e90b5400800003451062600008040000300202480d04101c04c43c0da481c03041e60311941285030115183c448500b01c0020981051016100760705000c0202410104001d083c094140f04d003141d00c1160759101c04440b40101c2c1203035034036140a4100038681da11242c51954800c454ad40502d4403d81104921600003208400d0b549245801d0042030700c0c54441d5001c003805042c200f01e850300000c020203800958a0010007c1007000070079a0000b10702107080ea4410403c85100034520001c0c000086c00103c06a810890440c01104a609000429840d84c1904500a040118111030320b00c4c01c81020000090048000d031202200b0300c0304642403551041c107501d8041c0030782e00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 483764343 1250 483763093 483763099
    0xd05011a10021b011b1b031103121204210207030209011a1c020c0d0c05100506010f12180303060e070c170c15041103071401170415020f1801090302 65
    0x3071510103d41c411302540071107a01050004140c00c160f52111203c503928044124001086c1d12020001c0082124503d090000c04401408104410015000c601c0c403a60542518108801001408000854002d894000f01c14031840b0070303500d00000302941d2035186000a9224a0a600002480021888050071003c070302a0b540d5007041c800d211940d845804004600000e50780900c80d601c80c0ea035040000c42c800031360565500716a084103040241c14010408100039446051004004d0266004002e00784040c10b076250122680305012200390040444a2400b14a00450503079a014142e064016005941711525a454551102c0506460301c11420030020304c0c0e002106004000d910199000d0102c00820740c1c1a1204041004480c00f00400b0444d411201412154180081402e0400c86800078201601078507204c000b5010001c1c01e01c1001510f00c03100003178a00009010000d00d280001c0c0d0842c410315040d91180541c41c0c0e0440c568101c501c0c40640d040481814800a6106d407007000201d94000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 483765593 1250 483764343 483764383
    0xf03070807170a060c1805090f0106080a060e090d020c1e090408220801140402210f0307060605100203070c09020c0a05070b0a030f0b060307030203060d05011a1002 72
    0x201e0b202c459040d0701d108020609004000b100d20220f9003a000c0c02515049a640b44003c10210903e8860840e40030340085028180410803c60882040c00816064034800d05004905a4610703002102070006074016002c210304850512075000e40004074010303030741113a4095a90b080d10300f0060202480348026401d04209000054144504120b4041c642042c050300d1003a01e0010b0b103840c011650703d03480c030100140030325158080000300750a2040800c0b040f0381695400c81410030390001909920580f1000c4000c001d1404140000d0f14100846103100b44014240e81d2501d50b2400c0901c000d10240c818240942c800602d030802c9144040100c5101035071090040c1107981c01c0020b460700940140c1e0124034035200340104a400b0841c01c0084c2002489101003a50f41c2e0b5514031030007429180d446100030045070800c1244d607140e0340d0340e9003503c1d4002c0031841c00581309d40d1050001640e0035803601000e0300c1c1d5460078202044551f407042c0b0b09281210240c1c0d52607004000710300203ea03541c0d04050403455440c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 483766843 1250 483765593 483765599
    0x6060a140a1502030306042702041d01110c070b071a1b07050601080c0f06071209171605061216050405040c110d030e060112170c03090f03070807 64
    0x203440c05800500303a029140c1100240c82d92207801000052103000b901581c4040200440f5107858014540d000d49182129002c8184181815521030b042e544000c0c0702d10740703640e050001d050240c0c034102c01d55241c1d10028042c0300c008590070442a48145183d01c514003c04502240c514070040c1203030794a80c0c1c01118850140040c901c484007502c2e0140251038800d44200c007868030000940060120140641d006c0c03c1603502d088603052030601003000d900e000d408041c11440d00c40da04c0d13009480c0159040715030b45000306842c5e0702c100c0740f682058010000c4800c03001c5851500400c00542c1c1c5801c2040c1003000b02d101a114030030840c1a024145400244039a603c0c0000c1e10001c0b805010f54140c551820507600b0a601d5a00040950326101d515100081c0184e0f044026003200b00480c01035049036040c200040c00e041c2d0700a94036490140035014180e14a00c1018003080801c8100c005020781c41c1441948580d0752002e401d480c1d42c08801070a110b2400900150003078540402c0d120b085030003080c01002c03514a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 483768093 1250 483766843 483766859
    0x60e010b030a02040504020c0105090106050114090402130f0320060f04231002010c090b04030218101505030610110601090f0e0f0109052e050a020d0e0d03060806060a 73
    0x700040c074a200580d000d000000740d540f560300103002c0e6000041c00110700d03481c105d420242112800c1d4030142c1000101e0761206e241c0301c810700458811b444252005603580c00b8420103400c0840e056440300304204521400081409541c1c070f0045020009914003849901f507510410140380100403881603043e604110410064645d1144540040501500d180503044400b0002c4c59035903200d00e012002d80d4482c000c86102c258030100341406814110041411700741141c003c1910b1204500140f014000400d01003403500c41020300e40c030700409080b09100b1070f205003804020020307002510054012072b102c615283c440360240c0f001ca00c907003440e0001084a60320780030b0900e029000c0d501d42d0343e0490395504129009880705004030754690440704000300b1540014078044d49880da100c0d2491000e032044119070007001817a0054800480116040400c0301c0d110072040d00000d1041040180016140030807891154a0200c1c00c0a60503540d07840400815940d030324070f2521140120f629581c4000085000c0c02404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 483769343 1250 483768093 483768097
    0x60d03020f1b10030e060c13030803090d03050906070c031d090103110109060f0e1e13050a0e1f150b0a0302032d040b06010522080709060e010b 63
    0x140a441110300e0340d081240814100420500180c0d0200da6000b104100c034106500d1411002e2554a4200306000a1141c0c19485070b80207004e11203120000a01000c080601c00b41e10f00c040e580065840d2b86d682010545165120f02d034140711b6002c00d0030600020900c1002040c407034868055078560b840c4202c029a01100c1342c0c0e0546004100e40a41608584401e0301c400429038069440380d0251040f0001020000d0600c4105522440c02c0100c01051514401d500954010180e101034504a1100003440086207840480c5284180c1256950b803c1c044040d0407030300001d000c0c0030f901c2410880d141d10408095128135900e0310302c140c51002824084044044d0f039211200081c0f01e0004007081907150511040f080c2c0c44602d02c6400250040700f407101c2c00d8078800712120f80080318060340d1901240d0301c440500d075000003040078080300f62079000140b0b83c0c0d006400304c84403280c0140195021380ca45a00100b00a4040c0c010111544102e00d0702154400d40e51103500c09841232444620026840c1100810b21a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 483770593 1250 483769343 483769369
    0x90c0f010c0b0c040902070809090916030b090a020d08070209010839030a030206100b1207050d0b030303070903030917190510290301140a090f05060906070f020606010806 75
    0x8000c1040009103460302d0348007401d2101c1c49030780b48d20342c3d4401c29420040c000002034100c070312542111007038a02036035214034041d048035442054100e02da5104083c4d103082c0400c084c4042c1d0450450000e079420030950703a00803c400c510884071a44503980341c075a034540d10f00d00c0d010f0201e800f0000b415144010f01042550201c0c032245901c100601c92004008281018001d440890140e4008018400000e00010040001c0c01c4c08442481c148000401b1940344248040c01c100d0a10200058072541d10034240c012200e00d10001e81101d0343e84c10f00c840d009110040500c0141d00060452a010a031085d20440c0810034500c4100108100c17050040f60141018000e40c1c2104d40340302d03112980058420f180698004400c0201c055030702c00b00c3d01e8202c825503c031481c0209101b6450203452001c0c4070003443c200c940048070850000340c08096031515000f490141200504030784555002c004600c0c5000407082d00c0354041c0c0d034628410002229090781d03610000c2d9205c074040b9594400044072820104018021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 483771843 1250 483770593 483770611
    0x1802093601110412050f0a11040203090109020a030803090c1507020108090307060501060e010f1112090d0602030a020a14070c21080310150c0201020309090a150b03090c0f010c0b 78
    0x80040c882d010041e42c0168002c110203109600c90b40c051002c00e00c07001c1e00150102000e0f040b40245540c40460f042c407006082d07880b865010001c40e11a5000354400c3c074400e9809010055034907168203200d006900205e803200401d2081000308520b0b420301001d60469160442283d50070600781d80e0055440e00401040038403070303200911803400442c031b02d070147d02d00a211070b4540100f07402d0f174900010400d030400c3c3c03c00130a2244410406501d0b000010310b00500445001b405602d41c4894000100904035089000c0d01c80c0740080103000d208083d43d4007e180c1c6142e42e46910700320b43ca01108411850140c404081d100c00d54108082024120490b282e01202805100509512201d42c1c1d981403240c0040e54402a1054800002d101c002c404c443c00464a801d1402c004801c0d40d02540001d40d203100d00812503004203950b0010078441407080c0c104d022901103109502c41c01079207071100b01100f60400c844000c1180308406440f1694207000700110103010040c0d4035084500c02c55100c00c0c0c40c3d00b5029142ca20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 483773093 1250 483771843 483771851
    0x2040209040b0306130c060c0819030b0316050406051807050a0c0c080a020102070e1911070c2c06090f10031205041d0c0712121802093601 61
    0x100c40d039014008144145070f85c5112800d03051844c204604c4803c41c3d90014024803c1141650001c10a048240e8005400600b10700c0d03540400c51900f1009800d9035900c054040c4030341c3d10740444824059401c0c00035503000361401c1119654840c00c02884041c00ca228105680d80600851803581c840d0000b800324808908281016040700c4e1754003c0004002d500900031a00407542c888115a4107102403801040794003001891420440c0070b0b01035035890800c062034000e6540d0314a080144c40c6600780c520281e0043d104c03e180740d03903419510f00b0140c0e07407516203094820309042443c1c200c030000f9404d07030091601402402083d90b808507900a4032030013030100008116102c00001c0003c844004880c0e40044c0d40d5181c4e81c81381c0c41e041034a02c5503200000752800751000101080a40e0f010f060a990325160040c200034041041c1e80001d54040304401507003071445083c003814155460040b484294100e100740c0d0004d1055550201055007240d804008481080410f40c00440fa00c860f00d0700100c08083c4070000007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 483774343 1250 483773093 483773111
    0xc070b0103060204080105161d01110703110310091a070c0f0302010209120601051e0a0b1222020901180e072c010b090409080c01020313120315030204020904 69
    0x480811000d9008564480d00010280100582802000d412010f1013a100400e0341404002030488040c046030030009101c14203e401c441d80c0f00c0c2140e103000109440a407083c091300c81c00c0c0030441c01d0140d00d8060007031003201142c956130309903840b03040e05c0c1c1074124104070074045401200b000e112700f014010900f0403c0071780000000c20782440c2c5ca82c0c0030b144203400060b076808071807050040c4c0c0103030054907032034a0f006000108502c2e01d409600142c4088191020800c1c45108400946000403507040421100408600798210b06d061031070f0f05008111000e19880c2d4105003c40c80300450324600c40094100f10315034010001d07000c1030146501c0d031118040c03021820300581c005181c076002043c0c0c8140681c1e140301c003e1050070341400d0140719071401165030000321581024541442c921609420303e0250380d0314590741e028803412005070344100b82c00c20000c0d035403410030320604502c001c001401600c030101c0300502e000c0348900911403070364414000903840e4072441c40c5030200002500320044440e04552119640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 483775593 1250 483774343 483774353
    0x303020a03111909060509030606040e0a08070b010518010b12150d08070614091c0909090506060102010e0c0d0807060209060708030a05070e011d04061e0e090c06120c07 74
    0x1d00003ea1410450301c0c6001100d0000414030f0019074028424090308010450b0103071800b08425034803190580d004640c00103080c112074681940504040e15421000c01d0003003c11041c07040311412150126464503102203040742c01440c40000384070302c03246081e0070003200303510388004ac421540c84130040d0b034991000c01d6680d0200321a00c0c0d0400c4102c82c40c0d90000b0700182042118030031040c01c003c2900b441041d03450328240f62982d41d6540341d41026420a205c1c00c50703190714415840100901808141400203030142d05d09039542d1141594024055400c100920798070744800200400203420050080d0944003498990640d03a90240d0401d40d41150200180c11480e25030800400c1c40174800c80c0030340e5070382c41d203072204508450019160301b040100520349803429a901030340d10300c1c0c00d488800152000035041c10011717000f0b00e0641e12146003201c050001100d8030480700003220443c2e9400e042d00755aa0380d0380015a0301c920b0000d25080c3c0c0f000c024440310079211810b0410585c0042140c00240c5401c3d025101c2d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 483776843 1250 483775593 483775597
    0x90c03121d330405120c060702010c110319140f07050f03030706020a0504030201020d11100203150a0305011e05010b1b07170a1502090a09020306060708072001050c0a0303020a0311 79
    0x2100b8000a0002010421030a0500786008030030200c1010700402d803600740000741284030f0b840004e41000781d0004000144003c03a0304490000d480141118492411815070100c1c100c62800141c42d041d01e140c41d01c6052038404514213074032101c2c1201800b1414100b00402040c4d03100007102d546c00d44414007801c1c0014200f48020500c00c89961075041d00c80f032851000a10306043c104200040054103041294501c4001074410f184403403c030009030300e80e075540c1000c00e294240c4101041c0e10401d401c4000091220640c84a2802031610b4038440d000700c1d43c00c8170401070303950a10031440741c15020001000352410342c4500312030b1843d81c0c0c019207144c1591200100722000e40b032450b11655070840c11582c1c0400500b08a00d6001c051406019030500303460000180700010540f00c0c0c2c580094001000422a5030b1b84030841e44c8032a800103241e0340340c900d1030074480303107000000c007903070342145071408403030b01c0c40e60003001038886441e815001400e10303150541d011400307500708040300c40515031a429042c00180c11000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 483778093 1250 483776843 483776929
    0x327050c0307052b0213090c050405010b040b030612031204050d0f030e0c100e0d140628090606030f1b0608220c0306090c03121d 57
    0x24422400020201400d00b482503000d41d00c81c00e0a281001c101400c1801e4218040005480c00030700d01e0014004105070055040300c264409141c003502d03200700821800901c0a46034240c4042000742c0e26013620f40c40c2c6100703500614041807018400101c16107018901c00d40d45180010549090900c48101d41c000c1801c107580448407078200980c0148082d41c02001ca400d041500e240501410307144000d85911340c10900502c90050415113283c004041c01200045141c80c009000510642001e00301808003c10903869100c2c54040e03c0d01140030720900140804021100300c990f4403e0002e003e0b001e43c000e203084481200e0840d1545800070100700800c03924130009000d20f000d1392804100750000c03824190250840c100384410031050041c150140500aa80c2c84581108042044654100034189801d5a407005041e01d0400304003008019000d500441140d102d0341d100561024402e4040d00d000045450009201f41042c2140c0100d103040c0f22094401c1a0042c0d40c00e6041c80300c000b80c1c03004151005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 483779343 1250 483778093 483778103
    0xc0d0804030e0109050d0311120a050717040509281a030c040c050f2d0408070f03031416020310020a02123c070c0906051206070327 58
    0x81084281500720019800b040000d18090f00c0503820701c2c000038000100c480d400b508001910a000c2d051245c100409034200220300700858403000c08080c0200142c3c4801da0440380c1d0050261107900b440310300c40985003500c00c014884d50942d640c01d1b030440d0010030103402105100120000b8130021041b18030a20f902020f9032010707001c00c05030709820b06290680310070481c0d0080746480c0ca03c244056121068428200c0042c1c00b00e07507101d07540042c1c132160150f030380d0705140e44605003401500c0444000340103104032004181035401e01c0d41d4411184800405610000e0041034416000d1045869504001c216600c441030040d03e2120b403540229141c603c0740d401d1917091942c00204514410b8041100744c03001003189035854940f11000c401c2a40b030650070710022180469091484040300406100034a90407100004541c8483c070505105a280f9224442c01f4050741c540200070906040000e400d4102e412580c0040100303841e1918110003c12010f2403248850380d0601e60403103555002030208800502039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 483780593 1250 483779343 483779357
    0x220302250e0c07020d030806040e011802010315080c011421090601050a08030712020705121b01050324130f0902040b01110a03030510030b011e05120a080d020c0d 71
    0x115040381000c0ca0050405a803202d000e2202d000141e0700d00300d1080f83e0b164035260000698803000049400342c040e03d880c00c0038650800b1018150282d2002c000709669000760790a10001c1d9140102620a04403401003c0300398004024840302940502402581180c0d450102868401c05080c101c8500901c0028104a81c000c4010b100202c01c1c10407007503025250448010311414030b01035641d80da03880f40250082c0030349031000002010500a10402d801840301402100c4d0030100303141843d884400004aa08d800740c000c82e020740c00c55201d14145ca10544040c80100304270549440c12000d00c028140d90b195100350314900141c1242103d001c0c1c07912100c200303000407864403031900c1008240c40b0f201e130b10342e41004504070003142c4000c000141c21300c03455018100000d8940f81c02001aa9100d07aa0b0000f5200d61281307400042c2d195a40c0d0b103003e4011003d03031043d1008540b90302c02c0004d107000a68507040c07a81d00080d42d103008901064014000b041890350014948607001c0340450030101c0100e40c1802249103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 483781843 1250 483780593 483780599
    0x80d0501150906030c020c0f03150c07050f1f051015020312150108040f0f02060a200a0b0c0c0106150203070c0905040b040f020402070b1f05060322030225 68
    0x2066000300a4010f6003030901503055412030081d80c85848016062080c0420804002552400d100300c16541544210780820380c0b81c8404020b0b825400f26104503050700c03c0240040304c8040110715161690b1100035058165030f01c224041003e8917018103e0368074265011320005071a001d012a42c04000c81c0e0f6005540c60705d49580160700300480041110364141c0c0f141d0303a0102a0f80c2e114050300e83c030070307448a441901d60000c0c0c10001441001e01c500250032100009000c3c00c41600440c0960f0103079001400d05181140180381c207903c40c2d200d400c00801a010b41000300305440c1c4501c01801d213165200e0000520340b96100348000c0c10b43d00e01d81c041805070304001621000d100b1003100704405418800020311290500c1c1d9030700c07140303081c00030030107081c0c1110740203108115900c0b0f0b011154000d400500352841428007410700410115009021254503d00010005540c1450030a407841000115481c1c4144090101c64100703007840c0312401c408601880300307400540103180302d00c03481e401000001524101c0c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 483783093 1250 483781843 483781847
    0xa0c060f030b03030f0c0f07060513060f021b040b03120307110703050a03120f02070c05040605040b090406050c040b04030b1504021206010309140d050306040c17070c080d050115 78
    0x100250200d01014200502c4000e16100041158990f0480034440c0307544107018907050303003001c2071000392040c54024171300005020360b480f5000d84150700d118405880000d80d030b41002d50391b82010059540240e00f25025160040703890482d0100316050103800800c00401c42c00000c3d08007640144c2c0011641d80210902c40d06a03809074000c6541702981008041c20307400c41d26500d50b1030010340401403c120241d00081120600c0741c00c603000ca00141d80c030640d02e6001d036240c1b80040001e680100740c019803030700b040015145000d026110704402c1c083e1020525450f603803152005007400134003001200004100018000c581000244010340c042d286024084c200303044920001c0e01c110030107600c41c600602250700240c0100c000f60f40c01c42024200000e942d62207182c00d4035240321403101440e003801145c0c0760700c1882d45c2200c02503205290071035003000480811203056914242c2c081031003222000c02c40004845070700590711021000c1c0184429800d2001010050090f10b900340c000c1544880fa046804040907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 483784343 1250 483783093 483783107
    0xa0c0507080607080c0d0216030f080a050c07260f0403170405060d0c0908010e0709110c0604020126391c0605030102040305251d07020f0a0c06 63
    0x450703808003828140c104440001d00c00e40f405040c54000040001d0410910359542c2d0489100c94002c00c0c143d8502000e6007006800c904000003810045052400003c481120610846e80720300203054410b4202802621511002c18600030320f2684000003a82242e04070001402520340e181001d0202c56440d41503280070500404c00500c0b400110350144000d002c0c607600c1a06440c560b02c0b181c4c40018034181d111104907042c1103194084e0741d01354a404d00301c100d10800800c845041e200100b07400d110746c81104c9980300461150758150320054001401041c0150701c0f41e01c60300d0b20700701e080f0900e0006200c480e000100e50402a15410424411900c409503088080b464424000110945900724840c60524a0a2030f1250703041100c50a0000b40c20200100444d60001001c0c04014000f19240c0c1d40764a0315580e280d080e41c6001c0702d42200e19a40012508000c0041010780307007601c40891170507080381d030000c10700400a030100d019401005e191040c02e42c0104440070a2900528036200d00c2460107001600e05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 483785593 1250 483784343 483784349
    0x303040e0f090f070803090405150909030a180f090209031203130c050306062407140318150405210607020120070308010e09010908030708090106050405060306150a0b0a0c0507 77
    0x41c0e003103000108201781d8003005a400d03120050b103012405036112843c40c001d6642c4c0a0100e176009106809001020f030002014041c4100d5940f11a54400203404200403002014030407010706210002060210071002d80141080100140440b0410b45980001c01ca054104a0b040c01c8401d60381c0302a0790a0141c02c1c40050010103081d0040e0489080c4a004180300102010f01e00784000f00543c0b001407201c100000311144c50f500080c12101c3c1000361250a51680d114501a00843d0082d02c0d00c20311904d0030b060441062894442e9039860b140ca803006101c0c440414010707140602504211300d1501e48424020644106019400043c211a1142101c81c01100c0f000000702d0f03c031130a00a0000103500049281d06640d440050001a03941d0080e01502401e02c82130300401101c0007106010f16560058845400b401074540240300080d10340b804d200880703104440f010340c141d1090780030810740c030b01000b00420f040e94058940c607965a100c8001144540c000101000000c845c1d010f0901403107002c7c4416000317 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 483786843 1250 483785593 483785623
    0x1103010c14030f090f0d08090c03030306010f18050d0812010b0405060a0e060d091a06100e0609120304080d030f021e0d0e010908070515190b0303040e0f09 68
    0x54000201c000461800b00a2800c20307038286a80129400c1081001400c1c410b6401000b01c0d03a941e24000001489a107041c1c41d9a8001e204404403030040c1e15000c0141e038896003041c0d49110416410341002c0701d54070814202e0071300c80d9000301c03004615500e03120a410300c3d450181c14200d40d40c24184c01d8800210f0016401180b030f80c481444148215070b10781d4100d411f54481490002c080100510010b5114440c030561010f0051922403002c0c200804c084001111103600100e0b14a165601e03000c1c014021041144c0d1000104541c420035401c0c507100001d0711301c611014101821aa09011000380741d5403060300f000c1001e5001c900d01c130103255418041c242c8142e201e00010750400ca800924652903020031780d00b1180d0b1001c08514038500364030680c411070907904a00300070301200410781045003050780090010b031b8581c003a002034211107520801d81e0750301680281409030840340c044c1000b20014000413806580c103000c200400180107168408141c002c0c0c603002c54005a605003100c45520380141a039103921 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 483788093 1250 483786843 483786857
    0x30806030f0c060702010509041802100f051b0a1b0503010c050403150c0c080f03070806010e0f0f0a030b0c0406090f0b0703080a0e011805010c0903050c210601031103010c 75
    0x2214440116001584074000d85403d911400c440c80141d1b41e84c007600070843d13041440d00b400000d84100140321454001e00aa9a0818903c1e903032001311a09148102d00f20003180303040109000c0708094407186140c1d0280c10082e240d40549175510340c04041d26400f000c50228100200071310180c6000c0c0b11f50000b04245080c100d2401d451555008281c1451000301e081c11a43e03541003090450240d115608119070000301259100c0d00c90b41c841200d6042601c1000c009035000d0001070603035021f03a000707003098100200720400d21255001040031000f001c0d500190411203030f000000001e0440d02d11342c0c1c0a10242c48240d52118201880140701d10a15401f401c16005500310401042441408907814103030140340c660103079512801d500e0094048031a4100e0b6662a00c3d0360040c07040018440d80482600c244020300a0180d4003904507074411150001800f10b400c4911000c60707528100c03000340b1030000000881c00e04101480c62241c1001c500760700550b15110320113507040e454642807149603055442410014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 483789343 1250 483788093 483788113
    0x120418290102120a17071107091b0329031c03060314031903050901560405040c050a0b130608010f0306020c0705370605090d1703010603020703080603 66
    0x8107000710b400c111105000000c1e0101b12030030300c01e841d09024254681c0c01c407403104d65580611001400d124400c100704068000c040402103100b40551125400e4600c0c2d170b14848407424003103c030180c402054070799251080c400d064820391181c485003003850034143c4000030418958101071210900a01d020a45031b0410410f42042c2da1000e001322a0810f00c91400103915076600b003c4600501402c041c8031451340441341080b4104448084840c1090342004921110400d80d50548540181c0700fa0000382c0c060800400c11042c1c00c0c144e0009070300038050128001c0703036540e80001c2110103249800c180e8101c0000900ca11100d2280110000142440d02c3c1038002c5600d4034844d0b1080007410700000300343e1500010801e00c409c0341001b406029140050000c2c281410700341e071480e1402d001c40c211200c49810b01101a140d90182a4901c1c03c47e0050340f502850949a00100710090614220480d45c4104003a0100e21100082d40998060708003070724010303a0b800e103038100600381140080c100c0344654800c4d8492 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 483790593 1250 483789343 483789347
    0x51503090715050c0a0809190602061303050f0406080f090c0d02010f1205070518010302030402060405240301120c1e06050a02010e030f07030908120418290102120a 72
    0xa40c01c450400825940c6030003200b5040710305100c0c81411682c03a02c02c4002c90b01c02d0000c010001d02030004110380c17414078508054100301240149205000141e0030800000b0010031401c029140c00d83d1082ca807041c9841c0c4034002d0a45548c025401c40310002d1000c42c02c00c40c1d0341c00c2d55030480350000c81070b20080c03952542c0c0c02c00048130350045142c02410040d541401000031030280c00e1040d904070381c0e003805001524020200410a0300915440302604400009485440d40640b003124000d64029014601d814100814860700024000d40c5c0380c0075983c0a28264400900304000c1e5001e410f40c6c00e242c40360300c3c00504208400c002070342c0100104424500d1000c4c00601401a50811150281000385c0c48201001c82a8010031200820288a00002403c041a6031152000340900361094458008103501d0341d19190f540c10841c40c450090303040c1080b0600040742424014400d001c841e880125403404101010401c59008229210a41e200d40202c0241582c043c80003c2c0700084200070707142403000380000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 483791843 1250 483790593 483790603
    0x16020a380420040b1e192102150a032c0c04050a2903070f080d03020c010b0d08030412030c0e131103010e010f050a03020d0605092505150309 62
    0x540550110140c045060315210740d044000c0021000300306803030180f6012155403451540d0080e0501c94541108003143c10000c00003803109a035200c1e511f060101580c01c1c6249418092144142d0340076054050030f070b0440f48144014803504581c0d907400b289600304c038208080040d60744a0500540c28452700040c4542d840043e01c0b01c2c61920807540491640c40c0c0302e14480c000d11154807210148030050f001000250109005458185c1c4280e00b207800d4203548140c0040360076030500802400390810802a0880d41c03090700904000b215400c000200c40f0901030004580507103860003212040c90100c1040203106e03c48418810800b0a41010300951006010050181e0603030154144034900401c01c080302084254024000062283c2c4a165a561540c541c803078207180901c00c03e001c015100d1000300d4241032110b101d10850380d010340500fa4090320382d40c2c3c1c030014090041107521310744640220707a01150354119042481401540080b07454504010030703c0480304070002400c00d000f000700184485078100250b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 483793093 1250 483791843 483791873
    0x8120a080a1505040c0c150203070801060f050c07090501060e0306040201080615040302090405010209120a0b0606030a0f050709140a050d0f020102030f12100e070816020a3804 77
    0x5000514007401400b02c0c0902110b50026904180344c065144182c41d0800310303003045c440c01580082c201c050006120010707071004490800002e00e901004111607030080914a1122810703050245c14440300145030f6241c18010b84c004013040303454000412806812619449a0500c203601520b107a14041d0000303040c00c2401362440d40207201c0350400c280c443c10140d0581c0e000d1540103040210900b02410840e020307412150f00306100c1e0120340803411500ea000118100e00382e0703201c0c0b401c03941503641c4020030a454200921151045840780942500072500d4480c440c841c502a841c1c1c2c14401d420300381d0110803040b1200d40c0a00420542c8401d200c2e070703a150305002000690281311980c802c40c032072004038114018810b00040d10312002c24130112140061a20750720a8103207600300c400060f03444030381e84440b0505982d01008070300c0990208640422411417601e0031405030044404480075aa2018080c1c1c80d00d0320750001d00680d883c110001907490308144e051015203a003113807106040680f204600e1602c404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 483794343 1250 483793093 483793111
    0x150203131a040e0a0f11030114010f0509030a05070e01062c19030303050105031c0e040e01201206120706111612030f020607090303111204060908120a08 67
    0x1000792650261244100d401501c003840b294100e41c18a01c1d0140c010b480c2c20f0000403261800c0c0000d20310302c0c0381c6d82001e0303904032042c1948075807503410035100559685a41881400400008201c0c6540c951000c0290b0924503100350003e06074940381c22141e0100000607000201040219903440c40f2004081002d07202c01070081424400114a2000144500500c1101d840c000c15103004008203064140d40702c24100c5034290152004000803c031010581c10000b06403401040e04070342d00d0006410250711904003410180000a40c00700d10352803030807048001c48411100c1c01b200080180501c291003811507000141502c40b8040f13100700c0c00f07010384c64100500441c82003040400300d0164202041200460702c804920b12100c0180e2900c5080413120342d00c1c0d5045d40810504a0088141440020703054404c90700e640d1420100380c195a0300300c4d44c0380424898008c0a2141b504011040c010000007880280102d0b210300c842076290110701030a00203242003600d8440c40c188080d501860b0040340340c9901080e90 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 483795593 1250 483794343 483794369
    0xa0b040c0e0f060c06071821030c02150409020a0210271707060b04141009020f0f0c03030108060c04050102150a020c4c09290115020313 60
    0x4400f0800c1030041c1c0e2000410f900c16a0b082c41107040c2c00040c005000c1c00c00c0582d0340d40c2a51030b0f0300303030f07503d020040c032807041d11408202c92640210303104400c02c000c42440100b2800242010560704044d542103a080000c005900107000000541c04204640e524103180e041400b903124003502010034580c0680c52818a100d0f2124864100720281441d0a407000da40c140040c0c807800c0504002d8000c054001c00e9030300507450032110050710901d00d1416132082100c00c5000c0115070400c54581c000e9004140c045044000500101210300013190241503400443c400641d01c0358500392480e0b240040c00b81c10580c0400c403c02c801d01c0340e40da0129280c0e010300d003642100c19007034680350482402441030b050446803d0050071407803008900c0300e0800c052012075a80122403c80c0c2c60743d29416000c1003001381c100540a10700d52154420318950401d0300200d020b085001c0712124070403440006840038000c907031007410b40d84005000c0d16056161750780d00d802880c8015810585140644500c18146010780c030050100c2e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 483796843 1250 483795593 483795619
    0xe061e04080d05010602100e03090f330918010e040605100824090111090d02150301170105010b1614190b16020f0709180605040b0a0b040c0e 62
    0x408100c2d03520700000c180400896940d054025281c00100c0300c0c440105050007014150b20390b001064807280c0c58010403070784010f0b0605041003c00188201c4005812969402c032061500e11000300d12070034100c640745141d440981d0f8007005003001c06840440c8410041400500985a482c1403a91340035600a40009980e00da01c46940107096080d0301c041054480e12141000d00300c80024000c0c0a000d11003694811900e9144409098a20f42c01100c20400c109224050132854030f0f0003060390301c6002600507901e0060345c140305520340e40240c2040c4ca840b8103221400250b48000d1160600606d5844d008606000b20724014084905140d003024092980803200203558401c00e002c202170003007880c0d80303440c4590030078030344440c503088111107031162801100c90007420103001180421500b01014080c110031818510b0315002004000c044268001640c002940040c005126032070056000d074000400740d01c0c064014070240d503281b551650155045c11500705c1140e40145140c0a401d40446804000e080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 483798093 1250 483796843 483796853
    0x102040602120c1f0c02010501050f010e04051803032d10090209030f0619241502010207021c060b04090809060901030906050a0c09080d02030406081509010303020304090e061e04 78
    0xc1400d074030a40d0613640300700200d95082e1503800103016107000e030000d001517070340c078400c1200303014000b0b00c124003007000092101d42034909903008582c807a44200f203120308030f1264818185150000c0b20300c45a030702c00400d0501d01409110780da829130070080400090440c90100f110151100745440380c43c800c1600420a2049985c09100610700803082c0380442d201442c1480344c0c800e00c004080760701c20045207814a250204c41481b48a146d032a00c0e41c008004109151002200424042c1c0c5042c0d0110b550a01030070006030ba071072244401c1c0c2001208100700d40d8610381400d1040307805120860707204500c1c05000c080001c03059010303140c42010445650b0389503009000180c01030070461400510452600041010114482d07000d00664071455440c0c052098940021650b44c000c590310040242e4814081044801d2242221310343c407201c0c07490a421401c490303001044c2034041c00c1e0000c80142c0c001240a000c0d451030340c4503070145100301c072700148158280701003c2030100e0960040301040f040c04030000341c1400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 483799343 1250 483798093 483798103
    0x6010b07080c0c030115090f060503030306060714030a020d031415090a060b0c0a0507050315040b0601050912010609290907140316020c12061609091104170102040602120c 75
    0x40002c0d00030f000e40348910040c1000d140d80c1d805000c00481c90030248c2d6254055921a14042d41d20107401180385449490030010141c100b95000c030307480a04000b0141644c034080c40600406820350f001441c2503900101c003d8181d44551f081d00424440c1d0354100440c42809500c1710318a080300751100c11158032954900d101030300302d80e0440f46550b80001004400180d001529041c05d43c00f41081d1810551075100301a150000425046161000a0302040109080c0048660403002c14100b903441c110245000c00c0428030801f00001d9140d40d1000f0030003421140c0d020700054a000b61007514032202103e0081c0100056158246024404001c006210f02e0300440716414240c00c0316605945a02e4040f091100c0c00c044090f0900060282c94103204860074540400074804503054040c099a580c0d9049200507003890000d420200950f51000040b04078451241084d00e011041000360307918203001145560013817a1844610302c1e03204100030409960b010800e88104a8ac072400c01d0f035a00c00c0340861074645 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 483800593 1250 483799343 483799363
    0x6060c050c04090512130e06060301050a0308030c0d0507080901150b0d020319092105030408040303052101060309140307170f09061602041508030f0f070609050706020f06010b07080c 80
    0x171080058400f80e009003460050049600c240181c030950307039482c02801003d0001784606900f1408000061000407106006035074801441c0325410705124802c80982c050700d01c1038900d240807074020f1042c091449801e01900c0462040f07250301000851905041a0705403081031442d012031580440030404003500d5002e0091403022015003442050080d003403448401c240102981301e403215500041c0170740340c0181c00ba6441650816055400c20786951001e41e515400644c40140d1412444050307011302000705003660203051943d80c000b81c81015890055850039608440207010b500c103100450001d81202040c0382a00c180403050b5440e11b001e984102c42c507001d44d102c8148d12400c0440d181d2400384071041c00c2900c0b140215000d00c02d041c09014a00c403000d0880c05232204580080201500b042c1e11031004040c0d01c14034881c0d4901d0805603407904811640344076401c650a400c036032003c00a684d810004041c1208482c40036000c070354540440400588101d078402840882c01286803024460244209120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 483801843 1250 483800593 483800623
    0x70e011110050f1003080706020f070b090f10090b0105040908070b0c031005040207020906061b030c0f0c01180608061f0c030f02010e1506030102070203030a1206060c050c040905 78
    0xc219814507070300241c4000c441d002c400780000c83c00202075480f007000070001c5070380101401e481c0c42e00684608000c0d40c4251560f4070b8003001001071200040010002c544142c100c24040c00c0c8000c40c081d6403509040d42c601d48031184908021f40c080103da1640380460441d5021140000c151130304e0b282c41c00d0785000b80c1c0c0000d4540da04100c20041040380060040d4031551540030349108480d00d800400040340107070400a504044008009200c03410010010715115810303403041994032007841710307507880c507031005141d1801d540106404070f0300c440d000c03c82801018824241800d00c55105400d29903603030280c0c401d440c100b01d1040081070581c2c8401c0008100185010500a009040100050000d51014400303c2c0007522505070903091510602c100b46105a01c1d0002e440e00308121051650b0b0024080e0071164035550801c20032005035020401811400d100c2d03140e441904000d080700c04105d0b08503600c8a01071002c0e90144900207240800d02d01c44a0b030049400060012040c02d1540c036111721850a682 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 483803093 1250 483801843 483801853
    0x203070f050f06160516031a0708070818030403080919050d1203020d0c111e15090c0301060e0a0e03040e0c1602040c090317041410050c0106030f060506010305060306070e0111 77
    0xa48a494140981603030b01030880c4d415001170342c010301d000c4012304036607201c0000d10410202d4100380c86804415000403c0000c036028880502c0d000034103550050744100d640c00b000040241c102d00b014151001c04420104e41c9400d51840d00c0040340f84002c03d410000e01c05140c1c4a44100707010300070760540d14001e10040741040308070103c00000d004d41c5d083e03021201c414481e04544100301d5444c13801c00141d1051103406002e00080300e0300d02118030070001d0030080044c05207103010504c50714240f00d4040207042d414007042c5141410345202045984803112610a9081008244071750440c8010072a0800981c000e91603590420a010044980200038020340c001d080600c84c50740c03523034050a01020340707014018166001e2146044514284a14400c0f04134060703030f0150910491800038080304002240303060241c0740c50200101c6a08580301ea820443e0101e500640103010301c04035110780c5620800a090800c100d003843c0740025940d1100512410802c050941c2d5a54664880c0c400c0f0180450784000b158 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 483804343 1250 483803093 483803113
    0x7231504091407020c09160c11060c030306011b030903020915040501030804053606030f010e100c0c0c0b090d050703050114100303090306050a24030203070f050f061605 74
    0x9641c4060a861400052141142c0303400d4600d001c2035407e004a103219190500c14852440c141e507040400e4805440404154000a14a03142d10004000302d034400e4002d55076038a407120014129000300d003800384030380c1100d00c07010b40000c0c5c101300715070706580d01242d500d07240d60b40d25544000000e01503080b8540140c2490000004c208032800a0003d0720012581c0e6407880c00218a4040d041111218000040d241800281c0c0300d4059002d003e90040005000c0c2c034540d180c3c2c0510582959030309800d2841a42c051860410b14414a100b59030251000b840c01d070728603045a884070803a071905800b8a420910000480b454141e0b20424400c480350b5212003903641c05130303480c14941c1c02482c030307a10701c450071414820000b290342c1c0304448020280c0354951280c0b509581151030b541d00601c001422062007a907a550003484405248800d05484170b030f00001c000780c5030301b0346c8103240c02c000340c50344406055086824180b041381c0c2d500100000c42e040c02e80794907480d110f401012075607000c0c9484000e010b81c0100d040c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 483805593 1250 483804343 483804371
    0x618080a050a2603060603130b130308010e161d0a080102030f06060f040303031e05040f031403010510031e020723030405061b0f06070f020723150409 66
    0x408440c0c003540440d404000f0009200700b0918a004801529100820009401d4a44200510b030024500030105401800584d56075081c9042900c040b02e00e640380000c04020141d101c00002d0141c144103114400a04040f0b84840414240308020001d0160301d0008031043d5006410041c1000801009049101d5a600e260380c000e41c401e440d01003150010340005082400c01d4022100c03091b103480b1100c0c0c5018a140c40803001401480ca0040801100208900c14010a070142c42e00490140030503010406140ca4040c040700400c1a014000f41810b200402c159615440b4000c100150f500380031811928204141007130b4a542940704440d10f1012071410107200c0e11030021204030304002da00c00b5035a8400c1042ca41c0d280100d04c51143c2c001010029094003221071243c3c0b08103940403a0440f04003110100d019030400d481101c0f0040010342c2044d01c3c02c21503504205c0b0000400d001c450a0812101c050909080a0540d005948c010711031913030300722403260701c00341190700904410100b000b00302080c4101c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 483806843 1250 483805593 483805603
    0x302010809101e060f05091b040f030b18010b03190501020403050303070309150501030b181c02010221040221070f0b120a051009050711150610090f0618080a05 70
    0x2c0b820f610340c0781c43c20118045c00e00011410542d403009003003244c03c0c1d942525031075045104000c0035a94000502000980d848081c1c0403102441c032170701c04e82c039441c036003130405120240c20010446200d0317061940020407510003280140c1010520b584200f240b20480c2070a03070281c820391f8001040751000008101c0d10b507505038011a506481504000021103c0d41d03100c0081d20000c1c0005400c160f45100494101e03400c8000c0c4591113420385003600c0c03400030f4a0144100444040e0355040150b500000c4070340e5442c0d00080c1441c291200c07180588ac20781040c4d00400d00d2008049600e40c1550711030005038100b00030170001c5000030810041c0c02c0c02c2641d1030303071010000c42d040f40c9114500038440001041c4003580502410f40324407034003410030361040e01e08070704103010b4400541604280140c40c010503000072028824040819a007000760030103401c0c64000c2c030441280405502040044140040c0300030700380ac00e0752000300c4d419494840d02101c3c1007242400c00e0300c0aa409060315105d9142c10b18104400812 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 483808093 1250 483806843 483806891
    0xe1f1b0501050609060d031b03030608060f060a08070b09100201141e0c0a08070c03260f2802030619080a0c0504060b0909100306051e07050f04030201080910 69
    0x8601c00079403101003c1c002c2c0806c24420007000b140c0b82203100071007803a10803480c101490003842c2c00309110342e4803030f101401c02c0003c0e280350007034000c0c4108001c0d843c00c08000d5540140401001050407500d000c040746424080c02e45818451003014810403041f501c00d4000941d403200d2500481002c0c00c141c000c4a08908615100340c20000809000401e44c8002e08180d86003695a41c40d0300c1003903602c0300b1f000c8448988250080342400072100229a071141c0b50300400708440c2003c0130300d0b12941441c04259000b890010250500040d41d001035862502521990b0700c00218044000f584070380b1500c0c00101d0350510358420425541c592640001c00c100700050445044d0301071000c9540d00c54840042c0415900140601c3c019803108026001c01400c0c00340c81581e22803460a44d0f000f01a4599640900b510000d5540c1c107440140784082c0b04540c0d0010109030b800c442c40303081c203d15011518041c036000b030107030380f0000e070620040b0800141e14100c28480300200e0304401c0e608100d40314100c0448418150055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 483809343 1250 483808093 483808099
    0x4060b090f090c030115050d030c0b1302120102030403020a0312021606021b01050402091311031c110102041202040507020328090e101401050f0c010b01030c0e1f1b05010506 76
    0x22110b80f500e041c10f1060301e00f4910114940c02007182001d003440309821442c1c4084042004029502e404a54004400390003000011074000000700c3c24010450b40801f030580d0003450780d1040051000080d0005a1007411641c54205250b0b101c086007441c100a010314050f07200030030070b05420801042003950050542d5030300e10001880b41c0d05584030301400c8400441d4001d4000118501259070a0386411000c3c2c070f62442070444103002d070200030203e800c0042c18101c2105080000005001941d04240078002000d0f01000850030710f460154640815400440042c0c0215900c40109082c40d109000700d41c0f44243d5150002000d00c8624100d89003800001c0d6104000350f106400481e45100081c080d50081d03c10f609c62030340140c1000d5aa940044080441178148041000f07022007060484010300300c50002d18000103000d011100015095511258200c0304000e1605140340b0141c0d42c0b038482d078084807078140f01c00b40c0c040a4034400ba52010642120b116100290086260070030005402c128880c850a07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 483810593 1250 483809343 483809353
    0x12050d080c090a0302191e0e070512150a030803150901050d0320070e010e0a0615230f0d150905040f030813020405180c0102121204060b090f09 63
    0x805101d155000d01020303a584081007180c200058a045882d42d4800c2007a00540c41002d030b40c6030381a00c04c0350705502200f44030000c1c4150800c0311542c065400e030790004560420030b147c5a111459003451050083c030f09510701103c82003901d210b86920841d80c0245600c4a0078039903a05002c0740345210054881301644c031584404001084904244010010043d030580b215034406001c451880141110562000502e00c1084e0001810407003440c4258000c0c00654414103031824682c2e08501a40e40c20b4001ca08486400500400001c0d405650040110700c0340140364003062166103a01103d11420002070140c4c2c801007112005200c0b10391002c400100c1520706058500d84d110300c41c0c0b0a80701e04a50160820740742c20900000719001d01d070410385c00310784d13840048a4900366500203021600c050310103a0450f4842421040705000800251001c0d280900003058451840801c0010314421303101c6000c9030000440c049010083e0b1030b0450410003800170318851040c84c0080744e42c0c1c060b04040303a02030070034428 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 483811843 1250 483810593 483810601
    0x50307140c21040807090506030102120f041103010b01080103020103020c07090507030c0e09071e020106180204081e1f0b12030306090f040c050409031206142110051012050d08 77
    0x1048040b00c0840c0c102e1800340c17611034500038940b00200b030024600c03a00755400700b00c01c0310140110070101d13100302103084a114046c102800c0041c080f900b00e101d983d02030303850035884100b04c0c1c2c0c0010750b507411680d09180140c4d6446020441d54100b92481d842120500c0c1000c040c001d00d07540540121551040c142c0c0d81d5801c044807182040514481500c1d4032001c6001184215100c5010103100001c1c0c85181c000452401d40d6211014101c08805524820036175011405001c0d8400610a4404d014004e8181b03404060b0541e48454650101c50748035440c5500c1200504580840740c1c0080b4180314006120a40006812000540384d81c81103808a205000c803c00041030000000e20041c0520f0b00072840000840c01c1c0070074440140381d840000d81c01e110041403000340d240305074000d00016002500c0810189003244c0180003240b10b0411900d000d4030742c0e140c4d07200040c00c000500c0384044103516a020503652248441e02c441400e4a4105805034100700014030f09000c2d0001e82c01000c4100e69075203000750381c1c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 483812949 1106 483811843 483811903
    0x908073c02030c04052e09050708091027110a1d2a04081516021b040f09050f0f0106080607050307140c 46
    0x14180c018100da0000d580804400e00c44002450480c5a00090300c03001075030982d9024640c0da5000800840c400c0441941405110070039840d003600d811948070f546210342c010800d00900340f90100b51440c1c42a02c04501c01d282d0b10006c0d010319100e0601c00c50103403406188852101030359080c0d40d0391501c0c010007542b80992003100c14134100316491080c06000442940080e10a02c0c40600442500c001801d155500c2000d80101d846e007500c840122354030380981038040e90310300c3d400414045480d2000083e0b50350340d8900c04100300420b503140c030600414075005800550058000341005030445414401401300070400a001003080c1c1c3d86140f183e0201c5030199019552075200c3c122192100105100c2100c3c0c07040e804000340504e60070302107140d60741c040241107101040300c0003000400c01c40c8140c0200c0c2c92000d407100350b01c0c0d40d8140701c0d20303107551800384200c641c0b449503400c004807008030 = true := by decide +kernel

theorem cover : BRFrame.Cov 483633093 483812949 := by
  have h0 := BRFrame.cov_init 483633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 483633093 ≤ n) (h2 : n < 483812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
