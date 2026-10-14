-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2691
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:27:55.336607+00:00
-- url     : https://prove2.me/submissions/cb19226c-99d3-4097-ac4c-f3f327f8b30d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 483812949 ≤ n < 483992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 483814199 1250 483812949 483812993
    0x8070b040c0e090102090f09071409040f14090f0c0d061d010c020106030c09050c03071d04020d09230709020a0201020c1203100f050609060a12091110020619090807 72
    0x1b001d00b00030250704c4510301c2c58041c0c48000d080c066a1944822106102100002800e9440c1d5810010400811040c0d04010f82a454039901c0140300581c4826036001e10300a000700c0308101203c07510344e0b450b07104404401358056282c0301031000260007900030f59008604c50401081c8dc151142806094810000f580c000507513662006004024100c0703000b40241c0440c440c20405403910240340f5005100207000c2105010708100c0441c40c8864002d96900d80a030702800654035502c9090b02d0f40d01030411048102d800c0c0c0710945c120091180013501940000c58031400503d0000c2c035240042c0000e60001e055241195001c02c000000c0341020015049000e880b40b01c410350300c0c544050000c2003856a600007000480541c082017003507544040176110380240c11643d43e591154400401d44142c294402a108050704100c0c0c5842889a00014002203104c1600d0059481c4112901240c649608440d06040c440220880c0396155030700d5032020401c588507401091511f2066110b10560764501c1820346440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 483815449 1250 483814199 483814207
    0x5071709010c0212131e0b040905060f030105060d03030c020709140601031104060203041503020409090507060e0105070203070e0702120408071a04210c0506040306020310060c08070b040c0e090102 86
    0x3d0341040765040000740c2440784c3c1d00f0004001c0c4400701a64262040c81600b041b088545a60080500c280b60004e00116054a503541da036074184a01408044036028807030760b180c5001210a003010f0060358428900103080814103546980c1c00d03001000890040c10440c410200040340c01041c51240301c0250b42071700155107181c41c140c0c000500f5581c0200041011240900081081035000015141903c10510300c040b89000b50110450080c0039941c098046203007010445001d0101c0400c8010694481d40c0e030720301042c107550005640034841c44100070340550010804104425803e0901e80d086286031054502c2003034812080d0141c6d41050300070b80d4803a0081c0404220300300040b903103a60305030341c840400d42c240740c5403e60601c1c080c0385c03408159000d0076484d2100c00c200010f0611030805003400070041922203440b420143c0c000c1d00101c40821950110070030100d9802e0040c1d05690049078442c1070344d0b2400034140d4030b03203459843c080c2c421288582ca0040104d01540c01e140d039688070b4a0075000058807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 483816699 1250 483815449 483815471
    0x18020d02101e0c020a05030f06011514040e06010e060c030a0305190203100e0105030601060503060d0c0f0b0909011a0301031403071e0b150109171213170601080a03030507170901 78
    0x2582170940c0b001c0c2c865400b0000c11500454049003050440e60312019072400140c0400d029500c1515407120b107202d04d6400030700410021046801580510380aa8824a001c01400c00b440141c0c80752a00311413907a8400d001040b0503500ca42c0149510060070604000340c001d0310f00011301680c0054800c03e800d0758018406000d00c0d41c407101042c0c014441180200540c1d490541c002c0c04600c80a00101d024010f11002102401043d51400004080c81481c84034002d03924203043d10a41c20010009200341e1658000050340c402120f13a814030300e42450142c0f8916403860f40c8000300414040712844040c08140314042c0440c540c0c01400e00c10311a103454801d44c0071241c0c0341100715002c008050300e06810500f000f14440742d90104003e8141ca07207a051070740c41f0641d4240c90500c0d04902c90850b042146c3c000510340c5102c100103402004486605080381034a180e040c0c6010340700c1d5001d004640c42c5620004070714000c20310a41200b90054124101182920510403800d92002c00844035511203a4527617145001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 483817949 1250 483816699 483816709
    0x30601020d0309030e0d0f02030601080303011707050604051c06020316120c0f050f1c0b100c0f02010c020d0203030a02060f0105100504170309130f18020d02101e0c02 73
    0xd0703030605034981040031107415507001e41828041c000303a5004030000b10806040110750710010503c180c004045601c00d695603c040c6999a000b4003400d0700c40c03520050b4000300080c00042040030baa41c000c0c203440c00c1504040900c1141040c01c1e4120040d01004003141000c65a10300c0258005d40501d159095000311460700582800d00104070300040d40c0ca03008042e4580c646c08400c02c90007050303601c0c00c0c558030094000801814021a18040038100700c2e251080b28008c0d00303511442441c0b40c280c0d40d600b00304d00c042c90155090b0900c44800f504241d060f4803403c0042d8400c00b05414141e01c010410404001550003191840d04040710358000b40c0e121b80240038540c94800111401000d044460200c050000c11005005000e1842540803100360040d02e500000014810b070b52480c1b0010704040c0c0c01084c00d0500102603e8101c07154440180317049240340d000c140310040c440205030060510704e640b500d19030a001201e00c641c032080b000c0149a4880d2a500072000c00d030000c0c560803a50350b5003107030161401002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 483819199 1250 483817949 483817963
    0x2a0c05010c090503030a0e03100c09030b0a0606080c03061503070c0308010e060a030609050c150a122703120c1d09160521191a0a1413060b03060102 65
    0x84180b2440801c01c000958001040b540001075500d451b0001c003000c42e02091815680d200c4800e489030902c0e407040d07185603000f540c090840e07000701e44404164841d03c8461048800e140914000a000c4200003049828010011034005001a000d00d90705801d265841c034043e00252082800030354094030f00b03018103510002680c050004541c4e80c00c202c0c2011030000e020048240f00003440381d0384581c10302e8181f0005000010300d0740c1c03010b8440f440d010b18094a0403065403042040ea004902d1f0079240540d11032141c072600704000001003100d080d40f80300d110000e5a004a0000031400c010404030011032186060240000100c80c1d0b440700001d00580c8114a40e408426040690150602104011a0640f4035810418000003030400341d40d40e01c0603214025134646401c0307150083c095402d0a1020340c0752180c41c00341e0a14010170040000c00c5a0580070000d0110a4100c954400c000c4e480a10413041d071480480c11040c002000c0100c1007441c00c410f01c050780c03525030002442c107002008102c41c65806019003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 483820449 1250 483819199 483819221
    0x40501030515061c0b040606031b080403080f0402060d1e0b030f190c0308160b0106110c01030203150d11040e07060503010b0f0403051e01150602060a2a0c0501 70
    0x504038142100456618042d0306903841400001384000c860303500f07440c1d016190341d000280062000c9034891034080c4c00307420f144070016241a102c22080c413540348100c9510340280d03450b54824003151100c50926196002c0035000360381c012010400e818003401c05104a40e0b134060004241d81c901e42e4401402ca04460100c4a800d0094201486200d030044010400100201c02c0e03540d902242580d5042c110b07c9096185c00c000c00f0380c2b60000b003800900c900d400302002158400c2040c0459a038a03800101d23031010305504c1107a490341c08220318140547c02034000d150700c1011984503c145107420300001e410002c40c404140c40720302000983c101c40303040038040c5281d0400c07200c0c014144c4500d000e074001c20603c01403242d1021400082a0009011310b1002101c004540040880d40c40c0a0410440a82e0356040c1c054582258a8100c409041c05040320200c01212403d4001e0481c560b5000c80e418040c0c032840440c1d00324a01025a040c10302e80c100c1010201c0000c1607070b1042e14495072850710701d003107803096000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 483821699 1250 483820449 483820471
    0x5041a0403090609120c0b0a030207050f07030c0b040b1e09040c05030402040509010507051b07030614101512021e0f0c07050d080d0b0415180b040509070302011107030213020405010305 81
    0x90030042500209002c0c22901079050860f40c236282c2c01da04600a02640384014100d02916812001d80000020102d00b56402003120b82407941e45c1e200060725502ca20b01c98001540002d00201c0300d085649050a081e140d0965541c0d4075091581c40004c0481d10000355090200c0c40100034031003035040034800c0c0c1f5449a6500000c12a60804610151080c0240400780b0810000070488542203c1d041c80f4210086600c00000c1c429540b502e04c2c210500700044030007200804045d03d001a044101907260203180055840c3c24182e00c030700c03400c440081e620220248117079141c180700c80c000050709070b0000c0108284520745162603a510110340b2342082503540c84988102c69001c090401f003074104c8116925840d040d070300018005100004140075000840c40c110200100c61400a040144810304400101c1c02d43c00c00c02500250000b004200c0740140c5500085a0207078409000550040c0401e4555084a400703d602e0155a58000703168502c11170303480b2102c02e801180400003543c00d4055550001d2003510f03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 483822949 1250 483821699 483821729
    0x302070c240818150c0d0213080f060105150904021e09010206090c090a05070e030703140705060310090e031c20070f1704180b01200a0605041a0403090609 68
    0x6035041e139443d4444801440312000b0400300b1a9a4003080032201e484800041c20b5407281c1803407900e68003844491044030f8803800741d28101119000080349590580300028040c80c00d8427000000000d039a084080380c2e80c0c010780d0811103541081d41200802e03101000d40c94055503030361040400241403040103000840c0300c2e400038030110459900d003c0c0c000d034440707540b0400181c140e56443c0d08a40b48a040b001e80c64041c050b07140301200f40b150889074160441c80303900c02c450810341d0356030510003d884115150190542058010301134880c944c3c008800b408030341000c03130b424030421010140892541e030001c008419030300e070005070310394180c01d011444115500f90315600300301c8552910320203100810001070400c40251803451046103c08107690113010b4a0342a141b10070f001a01d4607000b0800480d0071808a0040120702c4026001c0e1a8007804c185100c002a000d05542c5a8448010f8000504111410008104101e4900325240b0020b44030b1802a900c0ea20a5458214040c2100b180740e00410f0710410002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 483824199 1250 483822949 483822991
    0x3120301210f0213021911120f03010312140d0203041b03050a02040f1e390804170304051606020c061b030f0c16080c010c030302070c2408 61
    0x119010b00b03981c0d0141c49041100803003503600c500a00c40c120320390710245030488408850b01e42c052000104090f000007210400124160407400c903004800e100d04001604100610008400200300090f40c481801c0240c2c2d8640103c020807a56000b52811602c2d040d400b004001c01d00862155004661510b521900425130a680b00c0948801c04010041e00858556040d0300d403541a9500091034010408230a404107110b004040c0003600c0030035400310203000c030020701c80c0c1400c1c180c1405140d09204034000d00005210300c40140c6021100400590f0085c94070110030704800e07032440085125511a00c0504604030180308102c0b03091381107804c0b8400f1940a4507501125450390b07400c80760080f2500c5840c01450740500940391a5200f1580c200080b05008240314444003000034103101450904015888219180d01f03150350b43d03800302981240011146000d181c0400d020340c2c001c200f00d0b8024012000b00c1c0340c0300c601c1910704913001c0e80c0341110b02c040d40300c01820080d4080e51158120f0354100d81d2a180704000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 483825449 1250 483824199 483824213
    0x213140a1a100c0f0c0b1206040605010e1005040807030c080d0c0b06120a020d05150f07050304030e030307120e15091014190201090b06030a0b010605090109050312030121 75
    0x40c40104052042d4507011809100405480c10301c01350b840164400c00b180c039031852040c103820120410100280c0d42022403041d241500548042c1e074010794a84ca2041a0781c402c2010300f288040700f0105000f402c110200b01800e080c001500698054540c0010321842c01002918003100051540c040044851654001a20109d54150030030400c64000c0c01400041c0c1d401403c200100c44001d42c041d4026001c0340c100080418151100c440300c01d87d032611541e8400c0c60103000c3c0012518200000c10400014000070f0150681041c03414018003100c1c00d0101666032444003403d140c03914004144903008046652178101000541c0d110f40340c2025060072161804030300d00744e55610600e001d01003960390600130791914106a0f080c010620700d412941c0d00040001a0081c504440d040c2d5030642c0707000001c2c509e4140014a40c4400e5401840020243c0c07034070000311065040031680c0341c10411035020001e09580c040000e0f5100304c280380a456070f20351600744e420356241006400b14080c03006881d1900c0104d804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 483826699 1250 483825449 483825469
    0xf0c09020c060c0a031104240903050d0305071412240d060207050a02090a020a032d24091d0f0304030305090d020405070314090105220213140a1a 64
    0x41003c0d00f0341c0b908082c400030360140403282e00c0c0700720518002c180001d110b0221000c9164001001f246150300d0300524404645600b11800003410b40c1d486100c1076070815200343d10580e400030951a1610051070007008144045d0b2280c0d005145544000080c403100301d47e8900c4007030058411505904d0000310301c501084101c01c1402002e000241c0c0890341340144a018054621515401080c910f003500c4c14a640c07030020f4102c42c03401c0380040d25080c180c1c0050f40504071a810b07180c43d0b031482c071206e403144984000e014080d8168460106031088482c548010340d51a202e0016000d44500403801c003400c03000d414450b80c12000d0300d1509501109400e02c142a010080b501901e0b0585480d41d50f443d5424003052000001c070000a40181c500420006166410350210820350195400d40300541c540d081490f0907503c05860340c82d1511101d4441e401141045150304105c1480602240d40c200c8501941400b01e8402e5003071a4501c2070282c0420450074090b10030841112000c681406060381c00001007100044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 483827949 1250 483826699 483826711
    0x9081b1f0515011806200313031208100b030601091710150e0c13051507050c0a0e0a09060e06010f0510091503020a1106072309030a0611040e01030f0c09020c06 70
    0x2d11080c40b940f030525000c814800501010300303c1e5a01e07a8808d00d41010b91045210590b04803c0042076500c415120781c4c0e00b50300078560030100e180d800b8103007403d0300301d00d500c06030030386040c425480303c005110640d181d004020611000302078401d151000c5050000d40e810340740035103451015100e05010356040400c005412618881c0c05544070206000042e0035a03909070131070780e801032440d41054200f078030314402440140d1240c2c05841c138446e12181409802e191900924030711030713904000035001c0c00140c0c3c08811082d001706000725451244601280c10411300b0b80101c4152020343c2e90038801070620220060f10b0107a00c1c030b08000ca03d487c0a41546098602c04030110416030001408c00d6420700c1405d41200c080494000e580c05802e0118020300401c0d02d907020303800e0000508a00600503c158000d948140c040030b8050b01c4010920394640f401015544580c1c0750070742c001d21000c5a2080401c0f80103010b54070500c15103c240030142000301040c079041e07010511040c01000b2100c0c0030700000c10b02c590028 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 483829199 1250 483827949 483827957
    0x6051902271503041209140d060e150a0c020606030610060309020112020a0201050106030509070b0403021c05070351110a0203041809081b1f0515011806 67
    0x4200e40c0040c40b41103030254a00026903010050000780464190704050a0f0419100e03650b007203964501e079900340c082e503044081d88108032400d0400400c10607040002040340c04800c1e80c1d14490b070700c0e4154020034404e035144000c483d610240b00d459980c041101c150070202c120000d1116240c100c02d03030300e801e03034050140b002015203c418002c00c59018260f002c401900f135420039900c0d5020004000d00810003482561300190600c004141c17209404210803003541e045005442c54a82585c0901c82c425450402c400c444236211903040b40418030600c01140514855020740c80d1180c1a58030302444500d690442130301408032942518580a100340d181e607001040351501601c1701c0e504060b110300821403030358001d408840000f000c1d55500c1e4007100604c03e540c1c3c001c001c441d51601c031845075007c4403603102008003820000c100000d0392100d0391604204809141044501254501c14505054003900d440f441446c0e8486041c0041c1d0701d80c043c0c0d1004481001e1034845c1c6081e504009850310844580f140d0801c2c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 483830449 1250 483829199 483829267
    0x2071a090d240203040f0201030506010912061e0c080702010b0f0901030f03140a170c0c0303061e030304091e200a0309050a142130010306051902 64
    0x161942d6034030b10465031003481c21900d81c030b01814448202242000c1c00c900192604000031000e601034044142500d40c0d030822500825810391300c0078024031905070148108200c0c041702c0011103849003c1c24200d181d440d902c2000c0e5051440019094918246000d446140c54411a0201c2c2d1641e0891504494103c021200700030030b54181983c1d408000307504440c8448001808041e4940c0203402d1501c280074201340e003c0550364036003030a40030340038440c40000c29800c1000800d4031450042d50180071004a03c9044284d4800ca00020740703158400d41c8800b45090303d070440600111020328903002000f140c00e4082c0800340c40c4509050140c604050001001d14002c540010164803e600c4001c21700e5122003100d04800c0c00b4203042c1f0800c0380c0c0000714440b600c0f48003404182d10405564030000f01524a030560b017030040c1c80ca03090001d8000e21015001880b1119130313001010608a40c1d50307009500a080001e098149031040101441c0040d04250210340108040c0707205a554071005286d44880e20a41e8041c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 483831699 1250 483830449 483830483
    0x10b130b1305041113110703110f070608010e06060a0f0302130513241427070c020f040204050904080322050d030c03090525120302071a090d 62
    0x15841003601c40d807070224030346070811007001640d80d02c0000e510700c11504114120188000c82040c0c4183e00c11090b641501030207041c00282c0075040440401ea611416a207080780d80f0b540c11443c001d0954440c60000e01c000004001c841d0b19805000e4000000352030700c910300404200c0140903030350f00600c42001c142d800a85284211100703c030300d0300030303010040c0743e080c0f82103203e040343c80601951304030f854244082ca041c0d0403a08203420590310444002914082a006410041005807004400e0342c542801c0a6189101c4007540b800665108040300e45071002da0341c80301d0050010101000c00c0041c080c92042000707003c142e0311340d901c6075803160b4041c41c00707680c83da1519000c4c02c0f80390500790140c6403030b549403a181d000c218000c60328000d056242e81c0c04106800420401306d00303441c0c50b030f04050001d800031645000b1000d0050041c06c40305615190034604240c0e0398003004600d82c4100f2007900183c21448062004e2401440e41003c058010310815082035021400581c0c29000340400030140c0030400c1840344 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 483832949 1250 483831699 483831709
    0x13031d0303070c140a0312080405010f0c020604030f0206100905090c060f03040314161101030b210601090c0206070c1b09050105030c15030c1e030c0c0d02010b130b 72
    0x51880040c054944500082c40d220010052a0003504469100040324240038101903c03007408583d0003098484014010840a03100c54074050400c0d101d45d520b65080b110205918000c0301c8903c401e80c1d00505440c981400c0050070340d404004104115001181170004480d2144030304002c0c1c4950940c00031359600ca5901c040c0c90319510103012600000301240113032090003e240511f11070f50107601c1e554154034030340d0041003103441007a690700c0c0c03d40c804904840200d0142d1403001040d000604002070824080400520800742c51280e048a2102c00c02c00920756013010300520340141b04c00c03641407119181803800652900b07001408441001a9001c12009001c500864840e01c410248c902c0300c0135649413040300c0c001d05424050107000e48a145c20071107075810300c0581c011411000820890858a03072804c100b0541c0d0040d10342501c5a40c0f10054001442c80410045000715109201c06a41c0c1c0003e4034280d040c0640c0b010070805591501d035103c0c0304c0e9126035500d8010b41c40c910386c0010704181214009a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 483834199 1250 483832949 483832997
    0x130c0e0a0b100503160c020927030a05031306020c0105010b04060e011806050f13090203100605030f0633031512060f0415050901240b040e06040b060c01150506031303 73
    0x40d48c00003008050000003151900400c105803051841541d08110102045a60340710301d07815000011000c200040300f400d44092041c200300d2003480d02502e007446014103e820354901380c01c480c214041c00102001529002407142c0c4d945a02800c007c540800c440f0003803404044180304032410b100c030005a2001411030700301100e02e030050144503200c40585038035010002f0b4000300d410350740000c0040008100b00d8000c0003568800c0172090840000c0c2d59a850034410314a44e00c1404210703c40e240c5424580c000c00240c5965004202d10101ca81ca13441c00c1041b0080c0d0b01d9103004000d0103020b00f001004950040425182da2000d9800007104d0141c0752882d0480d00c0d10740c4010f5003c18180b903c03060018650043d004009000044e05000030110f0100c030384281c420070144944120041c08000070000030708035200a55000d20020030008401c2c45200214800e82c0c011903248034565900c0300341c48400307106a42c00c81c010300003c0e90260300314607003402c5882074108010005000e10400b003ca020324131070305403154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 483835449 1250 483834199 483834203
    0x4031208072304051201110408060103030e150a120e070905040c1703031602071205060402090c03010f03020d060e152d15030115170c0303071109130c0e0a0b100503160c 74
    0x903548c9540d030f1070303919840c0d04007800704400181d920f880c411942d103840501702e1504c01420180070324280b030041301555000d280c0b9907010a00c548404400034a0641400010f0080104080215181c82c1604e400020700c0582d402010403450012030000c6081c800206482e480b1066202ca5613274120005010303841c100315540000d810600444905080010110321140614800e42c4ca404041d10340742c072040f034580800d002e440f10500d0b01020030070142c901001c050b09039038003840000455040c210700c0c1c0c50904c10300300302c15206041c1e1300e410701100031188029124001c5030b000711058603814048800c0f642110240c40c0310046090100c03c0e100070303502980300f4050104ca60b066001c0407039682d00190400e01c0301c007003802400c1c010800e80000900b4040304403030001e940480403000300300b5500204111803a0152000c0780c800340203024580040d2110700c1d124040c103049040d00085150106c800300c06c1d0703084001e01900408001d40c0b625140b03038012003680d8100e00d50000c3c442420f018520b0403600c00c01801c1c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 483836699 1250 483835449 483835481
    0xe072102030616030513050c0d03090308031006171603020304061b0e01030605120a12050d050109020d0b240306040e0a060f0e06010312031104031208072304051201 72
    0xe01c000640300c40c0e02c1c001016419141070016079102c40d0b40740000380c1144409801f90300140c03851000c0b45400c15500300014407900300094504e0b141d0302c0309000d540044502d00b80607034841030288201074100c0340e0103028900c40c502c9040980b034020030000c41148950990024107030003002203401c004450b045001c1d0f4031146181c030240e182c1d0801000300307020810a24107011918160000c50346040080502c0d10700c1502000030042e441e42c2e5652151040c041039008001c002003841950780d02c8855005e030318002d000304c50002d601d911400740d00074215003107810716602c10303103604807124800c40e021100e40c6d1f503403c00040c1003600c0340d46410109010b0a041c92070700c0e02501a1030400402c20085034412103003614465010490001008400341d0344020a00010744021060024500014420381000c1e0201c840d003295241820394036502c0480e582980702c0c140c408203e040701003050b00c0f60310041c0025841c50000c40703170340b8008070441d441031540700b103006140c00b600500710403020001007500305019500754088 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 483837949 1250 483836699 483836701
    0x7020a050303030f01061d01020c0d0c0f0b0307021c0807030b011803060515060405060f0c07050a08010c0e030d0c020d02151207080708100905091c0905010809010e0721020306 77
    0x10084130026404d000c2c003004505400210a812241e0317080300c000308681a001041c514074034804000903504092000c44030809503810206900c50b400349070000074107000300400e0300d0381860200a401c08a02c00c0080380340e1401e9850741c640300c3c0c2e0b0002c4070390340280f0203050004581400000403101c0d0041d6007800051010070150000800200354001132040100c8034038200000c110f00208520303440fa62242070340c000014000001c1c03a02c4800001c0011840b44811034000542d50350100764100703c6980516078595642d0f585403003241d0482c00f1b000384844201c1c0170b01100b0310b040c4405040d03000c0c890400b9005600b0006d41c0c10440d26100c0c43d40700410482071a00d520b03210591041c1001e6003046810798005000200840c0b8020b020302006401060506440941c0c241411000c1d0000d02000703014484034421340ca400c910001107040030b02041d07a95a030f108801c0900304000500640f4018000072101d03031501710490b580030004210344042d1014400b4841c500342a0751a1081410303008800a5070502520b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 483839199 1250 483837949 483837961
    0x9090f0f0706030b041b0528170610090b0f0f0f1b01050c03010b16020d030306081209091501230d052a30040c0e04051207020a05030303 60
    0x42200c1141d1043e5020b01c0021082d100b8002901c0300d800c0c0380e80c083c040039100301200d2405600074045600794041c10007113002e60400c0080d01e1404042e080e401140c0b41c9082510602100a074107036000f9400e4501d46220303039501e800280400d0182c0300c0e20b05040070110b17644003041024402c440051141c48505522071802040e50381d001d5201155060800d42084505803040c401809124461200110796134216803034100e034601644d01041d0400c1144e5103807240b80300183d980c800c3c00c420b40c03802558006003903400c00c11110300d4500c5204940002c000117000c900007641e180050290302000d02400c07940340d8a0301d1070041c0c035070440c0d00c041c040c24018030408200c000b040880140000d58624401882151158100c402c1040c1c1014402d01c002c21401d00d452288007146402800000d2079004030300030102a00c407001b2080034100101c40b600264107001e0205012100380e90b0806400c2e48a1201c1103410299501507403031400c943c402614100100300301086d5650030320030b040140005010b59550345020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 483840449 1250 483839199 483839203
    0x90c03050c040507110a1221060e060d0506181609020c060703090809010804080405120601030605010506190815040509062a0406050f04050307030819051809090f0f 72
    0xe80489004901d040c0021314820f2041d54039082c507840075000b80031400e6240d1075400808403101101030a0082010040a1a00015040074009103280e0000607245051007111400c00c00c0c01380c0518400c14101700c003000820004910359802803500d02c1a80040e031141c4d5059810440b402c0c041d010783d4018810f00140001c85074000f0004c403562401550402d41d6080816400c9070851940a003052205100e891490350040c4100c070b030840c0c01880c500341000c0c0d441e400030380d2111a00d0040b8071150880001002003140600485016000481c1d280b410a0003c3c0902200c4000e44600903081064040110308203443c0f4a000f503140410182060005140142025944800075144510030710151042003a139007020300b007070620a000d460700c081d203410b203070040c00c07100b0b6081072110b1302c5140c070f00300300c000340d03643e820080e140c0210b104d4880c058a500811928804c46100565004248038082152110285040c0c00a05624200700c65484882d158509494502009040c00210501c1860030308100d100c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 483841699 1250 483840449 483840463
    0x40f060207140f070b0306100e04052e0302090f04060902030105040f03080f010303080c0d020405041b0813080f0706020912011a041b031d0a030503010504320901090c0305 75
    0x4450300310fa4501d03060901c40b07a42c800c0d5038814502d50f07020502c0458041c1c50300c824400030804492501c1002d90030000b001408843d000d0710442e00100000c0890f550110311044056240f00c103101c0c003030720781c0d40c03850300414a940700013081c00c080958404005020000c0030341c42010781c0303a0054001c20646c0341071325040328406442d003c160081002e80c40050f5072010310401881c103a0b941950b80c400c031038036220548050b5420000b82d00414075020b110109594680d0311840d00500c80750205580c07216070040000d400240041c4c42c0620502101c60b4507004281894221100e1010050f00c80d03980e012a820700c64020300503241c80903031102c40a040482c11180c15000b0403201d0050031015104480404100000c803030040c40705041c116010040e08900030f00039032007a440e03004605210010501d440c143c05040020303102c0128081a00030005102c1c50600388100f01100c0340b4a4403c0305a84150540482c24000320344504079047d520030001440c1c80c00a412030031440f03074011009034400e912031402d141c494103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 483842949 1250 483841699 483841733
    0xf0f0b0402040b0d1104051003051f050601050c070302060f0d0e011506050a08041b0e01030803090d0306030201020a12050f0403050f120405100e010201201b030f0f03040f060207 78
    0x10030905019503030301c0c1c12200000c0031688546041019005c06051101805005020a508920700000000800d10602010015000c503050480f05080032100380c1040b25805002c05040180c103002007226031400148500540b501240e1083c1c40d40c400d41201c416a1003001b11510101e820146640d10313004054000150a48a9005000f4440e450354012100d44c01890b10580010b10f1650100d0041481c0b851280c0001803406080c12486803140a10b1017980b100707902c21160304e4000010003442000904c0300000c11000c51a0a01400b403441d00000d40e40c180c4900e01034013082c1302003010200b0034060002c640351780f9403551410307454690341d042580c0c840603841d0401d80d40707001d0700030840d107048080c001b1101070fa5002400711801c1d82c0295401c907121110142d800c2e05540d42c903076a0803000c4810804c0d050f520301d92031217a541c0d81c0d6019608690080103e03c00000250302c1800103491f003900325000d176940d08030606a006d441c1c2c1e0b92401c1080130b4002040d0301500007403000030f120081c00040800342e82114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 483844199 1250 483842949 483842951
    0x10021005060321070203120f04080c0105130e2e09060e090d140d1503110907091e1707030b160207091805070b0a0311030c0f070f0f0b040204 62
    0x15031898181510f4542c002d00408400c80302c400c0d800c81c0f00142c034001d0405140085d0441d800b888440094071030b03a920800c58007242e00400300d0308111006040104403940102803802c91b05100345509030480ea507000380250034441018400013501071800701d0135600c0e020510701ca14500002a40d5010214614134042c0c3c100c01820154049440e4800504440c01020000c00400c079a8010300422a00203001c0c000100d5610400c1122103840403e43c0544841003070508030040c40d440c5503140115440ca12000c41c03500a80a0004100103640c000008001b12110b500c05110032140c0315445c642e2821282d0000071485402c03615100c11000002032150550b0311421001c1d456403107802c2251034010828480d80c0060b80b0842c01441140e141d60072410f54845c06001e0300080841e0750f80d449040160903000600300032008210074500652601854892500c0310100750324508150003040c009100b2500c05103095030740000c00c141004002740c0d1400b5074a03001403480300703040b20780c2ca0b00c1d08034000c0c1510186e120f6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 483845449 1250 483844199 483844201
    0x20a030608120f130e09100e0105060d0605060105040e01170f070f120f020d050d0305130237240f020c0114040f090e07080f030a030e0c10021005 64
    0x407500065614440341024039200c1c02c00303020000240b03083c0e10007074000c0260030302d4010010314a465410420300540b042d0f400703445040c04202c920b1048404403c90a80c00d6070401c0c0c00c1c400ea546031511a9015180c01c0280800d1580d180b100507104e600c1245d0100c001c4005580000401c100a00084120440aa415555000b010301c80c12581e0700114011400540d010003020040991820241c420303851264000850f094804e80005950350740502081d01d11750043ea070a404095810b209141e80001582c00f1000039440580110306603505c9690001a94480070000003149a004a80c0f142d4088889100340b040c151206428100d000c9071040c4c0e000c9110741108200c0125001c0d520316401641d50b0380c0144400030341c843c0112000750000642c503c5840d02004080b079158801c52101e00544007820021495140c40244c2c580b070442541d100482c1904082410201c800d0040110b40c42c001e201d10740860702c0880d42e0000c0d03092040320910349074820701170051440103a801041c0b0212650151901b0003203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 483846699 1250 483845449 483845459
    0xe011d060f062409150c03030f01090629191e090e0a021c0c02010915020708040315020c01060f080d020f06130f0b0a0605090c0909150103140a020a0306 67
    0x8012400743d04801c0201d4848060410b040041d8003400483e5001030a150040d14800490070207136003c0540c140c62504000100200e540513400b00c5801040300c1041080f030a032500d020608000100c000e41044200c0106c043c1c001180c1a030207580c40d0100c4010743c440100d64007000508003600c0407410042e000120814140740340c0c0902c10542c125401204550304c03541c1c1c0c40c6d900400960262052004c001d41d0307051400c0c00b605092103000b0004600e9000060203036014101030741c10113020300721186d0550041010000086469080d2030032613900c2004d44400c00203502038203019024464520314a03600c1c1100015684404044e9981121403000682d0f0b01c420385030200701d03180c441050060391942c0c00000811a9803a160455a03e164018240c4084c1420f080c2d442c00700c0700405468018080b62161001e000500e8015803483c2c000350760b0558a071801035000c0103c0d00f81c0800508007562101c000d43c1202081e4000c2d01b201140e4884d0b0340c0b86440720f00e000ca8102c2c000390031111015001038a44940856 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 483847949 1250 483846699 483846709
    0x4110c03120a2f0d0504110a140d23161a03070903080318030d0507021c0905010e04020c01050f07031b050702041505190509130b0a0e011d060f06 64
    0x60350101403940d4011040040c801500840807804081201081080044c1c15040c0c0c2d40305280c06607104582c074000c110300340c00401c00340139100d80014400409444000d0a9035688514103c20907620002451000403c4100c03502c0c404010034411415000d810b079080c1034200c0c140401d60a40310940e171040d001301200d082e0706085010072500680425100001407000c61282c2c4055a40a03264540303900c00e02c915151100e08540000800c0305c5080d4640040c01444d90b01403024a242c5090a5140c01c0394031200d400081100d00c0c140304441c140070807050922015100c80d01210b0f000f110000081c4200c0c18515144400031200b01c84400000e490100444480d0102040d040c641c0d4880b80d450509000035a02084003d1044483c03500c100400600e00044a440e0000111861050101c00f082400d2500080c00f0518a001701072084106421000100145e449030120303030001c1e903e0328005000823996142c0380c0100308048203030f00420524100050071480029200d8414690458440c0317041d103e8030300b804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 483849199 1250 483847949 483847961
    0x302030402060702091902070507080f03030903040b0309011103132a03200a03050d1e08160c08030c090f0f0d08030a09210806010c110f04110c03120a 66
    0x20b510210421103d4003510705080c0940d0400b05014003080c0304032402100d00300301c2e84100811115a0001d403403c000070181403044503002420000070310300c0c42c680880001c0d10703881180200d0f9414400807011031046a801d42c85032021900c8200b0440d9242041803c0f104040c4018404480145484242c148100c402700c0490f111001500f0840d0318150071070b560340c8410140284172a1207141000c48030381c1c55076504442d8500440c00341002d80f01907001e050b0000e0a03019060f04c503140004a03807125884159000324031039404a41c8001d035200e0050400f00803910b10b00e00090150502030b0200c10301a00007088001040428003c46200251151120070300a1441d00c00c0b484690002c040c40d00c500201da00d001c01580d01001e820400141a030b1583c3c2d644508014110b11070410b00e01260080c19401d800501703060304400c0900700840200e030f007695400381407042900c01c5401580141d503010460389441c3c001c001580b4403021010303241e5181000c0c440c0e8907002a423a42c1d51000300440460000095440b580d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 483850449 1250 483849199 483849203
    0x10225170d02190c0c050609010c0f0f0b1f030f03120c05130e010e06190f06080a0b12070902180405041406070c110f130207110a05030f060a1d0a05160603020304 71
    0xc40d511b08410401c507078104400890612000b0120f650000b0800101c100402d44601101e45440720f04e800c1c48c100c0100c1c018158100002010034180d2040c03020188081260303030100e80341d05540114501210000100c03007400b0682404d1082c0443c616810034064a50307104198035416860303590318510701c10801c0a21801190002d803001056060a1401124601a0b0018419030304507581d00c02008201c3d445074450f400003410030703051110300342c594002c075806824102d0b5070141d04401c5050f4135480d91013510a281125600144081d402c0c020910017950368107000f0700c200300e070345085c0c1031144e05e80d20b21400300d06041c0194000a103c00740691140324146401010381403000c00341c0401c3c800341210240c0500e07400960041c0050300851309000030491684540c07151018100a41c0c1880304011990300100e100b60000c01035403885110008082c1e81c0121102000701e40624008004006440c004600c00d000d4000c50200400b030180014000d9403501c6c600080d485c607a40c0d6100114100d000540d80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 483851699 1250 483850449 483850463
    0x1537050f042009040b12010f23070c030e03010e0f150f04030c0c03230c121b0a03081332061c18050c03010225170d02190c 54
    0x8407100c8201282d01030074920001400018481080800003082c01800198040c01a0b444420050000b50346009a0313a000c3c44460321488460700300e484075007130740c0f100400d0002004404584101810702c038803071402e400c1002500800a204040c01856280e04810301002000d110340d003c3c1142c1c20030003014070385c42025001d03078081246e1120365049403070049660041c1c8550f51040d02c08000304448410400304806074034158400c0380440301c54103084c030004007402e40c0315400b201c00d0081c4000d00400c405ca1300724610141103504101c00400140c414049400c00341c01e075580411107040c1d40318400d50030415075952801070a000c004407004045401403d030b02c401301488a0441040c601d0500341c0c0a0006e40324049040d040d00b1034400c4215089030b45c0c0c0007140071040b1464400d0424414144034000401c6419802546052103421646000c05515509502e01016400740003052180354800b415070507268400c10b03070341d0380d540c40083c6010390010b5403440b00520f0365149207242c160251520200c4580e010300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 483852949 1250 483851699 483851741
    0x190f090b1602120d0e03040609051e030c0d05010e03040b03180616051b0d1d01020c0d080a1101050a0603211e02070302040e060403171537050f04 64
    0x810311044d045a403441c880c03240ca48000710f00c110001e00240010300790030740d500448075140404008080104411840c8910792001c4000d00940b80801d180e841e40c002503036980c803003209a24106004084984014a40d80000305021810010040045010b044508803884802d01064071550f104c0c02d094030459281d010119154250070301503005000d10641d0782000380c6c01c02c85004065030814003110742c010002400c0007101010300e01c1e0301c0c45000625400303100801c6600c4c4182e0100d0340140b05804003500300d9001003503102c4441e01c03450709440c2555124000f40480c4c14446003081c080d18150008944e5090180310b0000d4884480900c000c03140364599500d2044881d0040d10b0721b0841000244100318062004080050707280c070b008201c8800fe40c00000c128a01d8141001080580804214074009200f2414020040000103072000e80510072103403810103134604000003600740d1808a5040003500480880d4942550a4485000b2034200351907412030101c8110400040301c034001800005908503203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 483854199 1250 483852949 483852973
    0x1b120605060105040e07110105100e0a24030809130203060d060510121a01060503130803090307020a0e0402090a0b0303160c0509040b070909140f190f090b1602 70
    0x5001541c01c4030040c1840c1e4030349500d8062008403190225900b45c04180300740c2940c182d1010911030540d008100144180f04642080b0390007007810b0300580384001281d220000c01004425442075410f4002d42c5195140d0300513a60320b4800e1303040c0c1142d00564401d02c0a141c81d4442d410707841c0200c0780300b0180140f0028024142e40d49030380c01004054100d01e051203a0b0580840c4040c007010311807000d1800750740503034410b011920400c000c02105800034010881d0034800d0120902d60a07440c0c002e140d81c06404940c0760b99482e5040b03490740c059004041d500044505c4005007140c840d01201e0b001e039000b910402d2081d50b03046145800e0b40e03002c2e550540c0680c020480401e6611424030045c505501c10110500700d04c0e92480010a0204292070030303200c0c44111001d200130182c20288000c010420701d5414003614905601a04a00384c00900c0e0702044045480043c112a13000c03245441c071030002c144200301e9080d0440800b00240015607003264101d20210100310030b503450810904990313195038001d140d620001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 483855449 1250 483854199 483854201
    0x5040b0c0c0703080c100b030a02012c03031b0d0306180f0905160e0708060a06030e0f1209030706030204050a090b030a120e01080f040b161101020310031b1206 70
    0x2600c100d0090b800380da04080300040c1a0401440d200a200c0000c180c034802c11a0070904a8880300910fa110341c0c0880c4003800140d82040110b11420603000702064840303010b813611001e5004948559505000000300c2c1440040340361180080e070210340e0100c82d0013640c101c00c26012203210340911038000610925030020840c6540040b06100140e48001c2a01c401507600e071490700380b0a03640700c0c2014410f05028021000139044450748200c2074500b0486070b003030101c049001043c00b8014901010348a03e803682da625810041d00c1d1581c3e5114003100c000a0350321841404c550401c4901c03030306c240501c200000700c00d480380c020303207007540c8008000509240c588443d00004143d003045154050141f4100c01011500d9850902604d08880d01e94405038580d10000612a61000b000c85181c80103000c1480041703400c1d90500c0754881c8551841c0440d50106040580e00f0f000705450b240c00d598000010030a034070707510b01080c0c1c080700d200c2d5154401940582002181060403800f0300b00781e100c480d40100000c9201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 483856699 1250 483855449 483855457
    0x20d120f0207080d09020f0d0b07080a0b0607030c1101090305030d021e450d02030709060303020120120408030402040902062b020a090501111005091c020105040b0c 72
    0x9a80d00061518030356684001c5150820241c20141c90768a4401c3c1d0f00350b0914100480500000311007a03445411690765950b80003601030070030402c0041d03260019040d0040342e4001026140c0c02401d65885d2040b51130003c00300c0e54100d50031607481c039480c01c50820030350041b10030b08141c03544040510b0610b00c00b50303200b500075000311052030b51392015070310405105016580180008080395100809206440b2446409282c024651a103105024004544811080c58807240c0501e4121400380741d908041c00020328040032900305411907468200e0010400d50154486130802202034100f6111031181d40b00c040280c010303013540d040004032503c00100000d00807002507234010320092001078605502e4000c690f00d900200b01959140042c1241a21480040411410914840c0506516143d41103100501030b05e0305c1e01c501414070200f8071600340c044000344240c011710b15502100300705918040e035105944240c680c00b09200701d0100900150380910600403288119000001d00c80f4a483c2c0c2e0105507400d0340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 483857949 1250 483856699 483856721
    0x30c0907051608040509070c050106120c120312050c0a02070e0108060720030f090f220c11010903020c0a0b03010b03010b0703180b1b03070f020103091b0305070f06020d12 75
    0x44100004105507440c0b40c91b050007001180e42d00e81140300b20f86440c40c02c44032140c00070440326404c01a040f0029804e040b10740700342c401e000c0c40e85e40240a14074040c1c0da54203142c05c0c07140e1071605010030803908112680c0600700280745603080340e500540e01c0c07a040041d0902030040d01c041d60024400992524010741c8000c0400344402c03400d0040100036400b42d421604521354800e40344034001007255071480c084c005008035034000c8581c0300e0500d64040d40e0841042c0e41c0c45260280f00d480328090494a030150108103103c41c10500240400c4100d494000c2d2920407689626206032080070300850281e905a00360b905844460340c4052840c1d080ca00c001c20140c1215100b00d0800003006060310f940030b00c007003481000b000d0f08a41151910013065140f405c03480c0c50100e881003a0300610401021a4011042060360742d02800c00141d1440a410406800d68441003020381d610071031503002041102c00210442143d65494004030219207524080745c07a011155801c1c40081d4a19409118440d484d9001001c448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 483859199 1250 483857949 483857963
    0x20315010c051005041b15090501020f0a030e01030b090f040b1608010504090807120908190c091a1e0306220b191a041b12050619080c030c09070516 65
    0x51076000c1c0c806106d21a60401600c2000052882c950300d9042806100940310900190811401511030180d540203014409410010f80082200e0340343d0283c1d201c11030700751028007118000e2921085c0c81844180a0b40c084801d02481800102d040d12045004c0c1c081c0c403072981d01c070401a4640070401000d820400801c0e10000001c100b00000a4200070400941100d1074680748020340c80d02608904000011180c8500c6450080c1c081000034003480601e000d9034009800060f00342c41c10018460a0a61070004903046044031040d251852403401c0400000201102100c0300380d03640700c0c09800848010360701c10003050807030802c080c0068a1090602d5020181040001490641e190390005450f0001c0000b0100041c004411110f41854020420303d919900c8201109a14402c80100380310109003221415550313039004120150358244041d014541e0650643e0361039520348844540320401041c10610178480e5010000040c2005405980f180915849640c241000041002100405900d00311180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 483860449 1250 483859199 483859223
    0xc080406151203030c020f070b0a0503091c050309100b10050a0201090c14031204030b0f04030c05070311090f06010e0f01020a0204090b09120408100c21020315010c05100504 76
    0xd0454242e407001418060307600411001803020000c1d0800d0351000c4a1100c0b900030319801d10421240e241250304200641c64200c0e0743e90340f0301c1d40d014180458080c5034001625100c0344034012552080195000d200308d4819074000800d0140000100c40e0b10700749540c0c000314400c2440d682c0600030317405440740d04034034000411224503a55600c080064142c01c0f00100c0081a01000e10b2410100134200d19250550102c0340351604540380e04030842c4005103002c1032020700c400058101485106841000c65200c1e0440f1102912890b140e0803003044c010140340101c0c80d100003d20a814000360703150284030107031518107109003100c060083c407900440c4102c0c19403280414900040c6c55512802d40d217a40500b0a040f503504020364060304040c0024203c556076401481309010219010450030514155600d001400b80f400540070b54200302c46800c1980f5610b001241c00e00940307910f030002d5106002240034481c01000160065840412444001e85241e100d880b144c0c810079040d60095820900910800c030078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 483861699 1250 483860449 483860459
    0x703110f0309100c080702121f0b090402040b0d05060c0405131b0806180a09050d0f091404090803070201060302031002070c030813051302070c06030c0e1e03010c0914040c08040615 79
    0x41d80190b40c5510b0712a40c421405020903000440e04081590202c14090ac245c00c04040080c1032014090800380c4103590310b243e07128481d5a0250121002a4000251040344c50011902d1825400c03522405000b90340100840000d82c0c1d6910401900f0712103100103090f4140c000d807084650010040c01c031900040100a4511a904024019403086041800c0420001900d24010b800d109a200b02a82400150303182c0204ca00c1e0060900070a444c00c45d4668811400301c4e2000402401c0f1301e1102610741a0000184000282d06401200a4a009030100c8d180104441ca0000c00c0344100f400c0030349416031003001440007a89040003088189806e00311401d9580c1c88a001480d8410101c40386400c0d40c0d40003c0000802162080200c0240030170f0908000000d4907910180c100c982c07100f6802e11407408004030841e040d05a640d0300342075003000350017040341d25070301c0e80003412003a2a4020125000d80001180c040c0e40303018016a602d10200c0e50300c12881d0303255030b0f0704c1c100a07106540c3d89210000c2c81300c401081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 483862949 1250 483861699 483861709
    0x3010b06092d03030c1f1b0c172110060e090a020f0408210304020108070e011e050a08090f071505040e0c0301032f010e150703110f0309100c080702 65
    0x7010840e0005080003001d01c4003c6d04c401c03121540c0c080c000c2420280c070800f00150101d078408507082d141c02c00554030980d900d03000d2005031460f54003103407000d001f0078241c851030116050003104aa00f5601d030105500c50054a80b9403110754410800001d50307400401c107060400c016100d400090700365016041c007400c3c1c1070221640d001138002c8002c581c00f0081c042e020031144181c119618a2048451741b4500702600000c0c40e00000410050034000c000c000b150786644104081400743c420380f2003040e000c540d0704d000203000e688030383c0d03c440000d5085804280e0300d0002013600c0360b00802c00c500408056141900070240325201d80d10349000e103c0709210010307642000790000c3e4407034412a070f68a5941d6046160080407203164440c03411905110320100c0705c0c4071200030100c54450000f4241000380c520711000045000d13a0300c5140c090401c2011480b08101074101190801c00104441520f20480c80c803041b003a620b0240e8030740d1951200710390b80000c040d5400303108400d6400380034402c194504041900401c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 483864199 1250 483862949 483862957
    0xc09010e01170702010c021e03030a020f1306020c010212040f210506010915080a0c061b152c060103080a09080319030516080610030b09041103010b06092d0303 70
    0x43e001d80d469503584015568140140105040740700c00c18800540141c45099581c00000d0000948550001c2d04401c00700803081501c00d990035000c5804000c90b03c560009444000d4501d4a90161103901d40c0c450f41043c4120542d0180c6108100e2840c0b810f05d4040c040740c19407000b10034900c6c41500e09611001003074080c00500e0182a40007004100010b07141c2c030b451031102040c0e000301d003142c101c3c50006000a00401d411780444205281100f03c07000c6841d82d500c02d012202e10010000490f0b4800380780031070400c0c1c03c0b85040500c48081180d421100c401c82c2039500e4074418810a03a40c01040050000030140000b1b03141c01119440c0a400203138440c0c20551441e400000d81020542100405000807030740360140c50340c40546040c0c0025600358101c40034240c0400600f403a0b20131041e1444a80c0054032030b50260024003402051800c039400c00d800e01d24081e00c0400c030000d0095003441c0402941c3c0c127107001143c81c40c2c41c1c042e02c4081f20780616000052040003140700061610280034000d11140d500300060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 483865449 1250 483864199 483864211
    0x4020c100603020a0f180e0708070303030f060e0403050d15050a0b1b0c15090301270c050919180512040905010e0c1204030c1718090c09010e0117 64
    0xc8003421401000500400d039030114070380b000700d0700d003c3c082041100312154405080f070030081031668182c000d07e424400f4507007201403c0d1042c21400000e15505400070b102801070042c5c00c003e5151200e61841c1002c104980c040e0215104002c1416500c00716130040c0492815119134040725030320350000801100e00c0d03a200509060020848400e0f03180ca9000e201030785039002000303000c3d0040c6500400d517007001001c003240010f940031410940c1c40e10290006100480c0b000518954180b148000c3e6241c2d1450100c2501c1040c0405000300c3e9900384444c80b60300032003e007846c00500854685030300300034000c140d910644c10440c90101000140702044921041c03a402d82c052512a0b003071591450440303074168485585486101c0034400100501c034100c0b52012418084420103940d07a007001e071031108400500900c41c000560608424890002c0034100d10841c2411000540000b01e040140319001a05c0c0240c216408102e043351540c09514501080101810b180509a02403902c0418002c5d08540c0c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 483866699 1250 483865449 483865451
    0x309030b07112a300706020708010209032d15180c09040f03140309150114011d010311030a0e251809020319030801060302040503060c0904020c10 64
    0x30140c40401c03d0050550500504010003024150301c1000341030110a2020300d80291610781504030101003e8001c0c0d042480041403048004912811681c1d40c1e12841c818400180160400406d4156040c0203c500c03125000b00148903100782030204140304a04610740c0c00c2c40d001d820b1a140e40e6090180700e124a4441c6400c0000a907103003410291030b42400b521100311444d001600020801d03543c40d51501d070050740021030030500b003840f4a0292104030654414008005001c02000707011000098990302c8203550859404184c1d9840343d81d40654060741d012140820b02c1d0b00c0c43c42d0326203001c0c2803002040000500d0041881380030980140300aa100b0340704c0c21002e940322840003800d000c1c1040380002d0081811003a000c3e80162983d0050003c5982c00f81d44514070308801740082452098000c1880a0b4000b410b4404050701000c500e00171810035101100403442090000800303034060302c20380703044410180180ca52980c0380007040c2461b9000c440e209a00c16800d0018080650040045465010816034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 483867949 1250 483866699 483866717
    0x90f030906081303020717031201080604060c03110912030f0d06030b070c170c011515080105030f070504020d14040b09150c04091e1506081f03030c0309030b07 70
    0x1500030b0014000501c251081c01440110b000007a500143c403400311641007495070119080c1d07081050a47c4a020b10043e00d06100500108105502050076070160784036080801032080315031011360039101d4071881c04901e01c1040c070815405091414414881d0700e07141080e03d160400e0091448065042220900141540e03600248204440860b485800041e54241840081001da440305420081a21900764070b000106102c40c21420940004480d10445101010255216400c1c8403500c1e01e0000c6c40e5002408201c0005501d0030040340140008140001034607c160030f000038807003c2d43c41805001030069480c8500da07400c1c201c0e030b10103500032382c42402070ae042414038101040c03402c50143e482031100c018502c2030241040e0f00d1001c40342102d240318400b1039a03214500161448801c80034441c0041420a030449901d040e4031607458003926402d403221701c188d483e100b900c03100e005040c404090b40d407000c1c0700e010320100b0f00510840103118032038a481e4040c2e50700c0755110704202c1e1080e0341e01e10215100c11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 483869199 1250 483867949 483867959
    0xf0804020a090f0207110a0515131203030b010e01030b030d140c0d020f060108010b1804031b1101030c0912171905092106150402070605150109080d081504090f0309 72
    0x7500303000710baa034100c2c0e60000a50911001620355050221080103030000011903400f4503602012b12002007034011780040d01d200c107e040250140160394101c500284160740282590340c000d100700e1a41c1d04014008003c50410301e24243c51706504100c40c0220910140f01ca092000d20802201045c10f000d54060a50150704038440da18201041e000100d032641849140300e116114606000c4240d0031900ca9511140c556003000c0da41d031b40f50516602000542c504903c0e0500c9041305c82401680000e076410400300004480881d003180560043d10815492601c22001007040000942c8103000f400c1902071030402c1c894210030455103408402c1e0027080c408a00003804d0700e0704250f0000c0070214a02d045483c0c1c02064500b90b01c50038002c1c90b2000406920f2403156003030325280e05032802540e0058080140f4100411541c600c00d40c0c3c503032440c0c00980311000214001d0f8003c2007084107076101d03860300c80f4107849000b240c620040e84a1142c2d40c000343d0310392542011401c2d03807143da003d1500031b84600784128100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 483870449 1250 483869199 483869213
    0xc0e040b0402161a0f0f041e1509051c020307120905060c0708100b03031605011d07050f03010903020a0f020d060203190c0504050102030702010c020f06040e1f060f0804020a090f0207 80
    0x141700d811200140c0c0b04004041055000c3d41d1381c455808401c0c0a0403c1c2c10500d4070740307030640707010002d0507000d08101424440440c0d54007501c40c941c020811507004d10802e103254442e9001c48071180005820511a00002922450783e038241303541982810b04100e130300c40001c00c40c40e0b00722041400c041c1d48222020001803205001c400c000d01a03a820901c0402c03031000100e079881c4600c8030110a00005070004d1807c0c00002e502c0560313a0529000c04810300710030b214946584403003a000d010f110b490504503000440c5030500c25807021720b40c550090004500c2c0d030b03100c2c04421a041d200c140d0f0450078000202c3d00007040c0d0f100442c42080c0d81aa1114461400d0011030101d5034500203000903c17a00308014001c50b82c0000a58820380e0b0709180800c1401024800b245d4855a01c020032500502e020501040680c004000c0510980c0c4800c1c0c0649012158580389100040d00c0c8190310100308200c8441d035000c0c2c40342503100d51040c00500a000c44542da002c1d040c04a800308214103000d1039002c240e10041081c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 483871699 1250 483870449 483870451
    0x6210e010e031b01090f030810170a06050603010216020603040c050301110307030b090720120a020105160e090601081305060403090f060804121b120507020a05040c0e040b0402161a 79
    0x492002080507041903a10000e004107146401f90038055488001203424003040c0141d0003401080c04c43c001d4104aa04c011036980310b421004803811400d01000808600b014402c2e294810300c00d914400e45003881d0340a00035a50f101030f00640345400603060114840e06c0c24010740050188958590ba913901e041503005041710a00c0c80310901c0b03040d03124140040c80f03a2040007a0039600c01c070b1f4911502c00307000610705844d100402656580200c0041849000c1ea41c065011034824213811003e01c800c502518400c81d1300704d1030503007040d90001034180841c485520400302c00d60300c110004034900d07003c0816110720303203031400446048000800b02c0c01d0910030300c0c002c00404030041c000c6007800303070841c10b2580d1a44521088100a0030070000b0f0716a400000d800b583d0801d04580f508a2240c2c040450b115400070318684c002107060340141011180010a41480e10543d01d05065550f9503007911803181003084080d0680081c02079000d6001e00c03042603100300307050400040b9485030104007919140d20b0b40e03003990307144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 483872949 1250 483871699 483871747
    0xc08010504030f1b140a050c0d0c0608060d0f0609110301020f0409150e01090c0801060e220605030718050a06031a0c04151112030106210e010e03 64
    0x4104014407002a801a030420200c000718200300c801c00c0c0c00c00031044041181c0c04800f07013806140095141c80303003901182d0302040b0350107a000d07a01400300d40000c0c007840c0801060000d0800741140c50800c0294410741c8a01e410403001013030755248214544910b5009207400078150703201e540d0b42000904005040c111015120030a6000794200b40003030b03034805400d000350321840b1001600d480b0707401d0240030000e105001030207a0103045201941c40758503907402843d054500d440403508903c00454942d0042d0803142074400c0007490326104100c007040311200071000e04940010142c580c41d002c9202c2c1d40900c0010041e18214107814280c007041940c1b44182d5001a00ea03080f024030704482840403c0c11800a907441441881007844c10b5141c428050501d44140c0e4403c1d10609140071440151690009441450002040c01c48010303c1345805504060b1200707204034400300d9a0310f940d8a05003264605042c3c3d211541603030001e03000b41265492425211805a40140e82c1c1001401d03020880703248410b00c618075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 483874199 1250 483872949 483872951
    0x3170604060b2505010e03030a150f15030b0a12021309050303010302060714070603050117070602031c0920120a031205090f070305030d0e03121305030409060e040c0801 74
    0x140b0740300302140c00b0322034003e0f000c20b4901070300c00b856494401c02e4984200030341e1100003013200c45410500c0e96240e4205a9038001e616040c001d90720940c02004202400755181c16612801c414605080c3d02402c0d25400c05050038151545172603251540c80200c042c0c002c1802017018400c0304030910400c00200107050690403002d2800100402003107000058070b054960640305255205070604103040d0144105d4040703440c070b10452501040c1154180c200da0f040707610403520b00c28119841e54910b91a2200e6005a00060b4014400d1a003075901d41511200000700d4058005108030194aa10140034001281035008034078946502c1210f081c4101281c07250300070b00019148072400e6580080c18000c81c400b02c1080d858603800440c2e86250240400c54804910008444c071f0700380e0f41d1801c25201d401c403a219070200c915110b50000104008030480d80001803010301c4100d19075030b444400c000d150042206840300d100030720000c03a0401e05072003104040c10000c010407611703140614101400301d0b026005441d242e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 483875449 1250 483874199 483874211
    0x1d0609160311090415020304060c090b090f041a0406030b1005010212040504020304150e0604050c0414041515060203041a0708120613020a051902010e12030403031803170604 76
    0x2085030b100d0035411007481110700030b1683d1074505104000c0d80074180c001680600c0001400300704007150b030010301c00c80401c0e103d40768144c3d50783340d0391450740c0240307580e841c2c201c42d03040107190051034154055242242030440414422800502280c00c54003c0c0d00222a500000020310943c8025528010000c2601b40300a0060010146c0301d00c1030b038000da2240038019900031010400300103500c603079503075034000460702045002c81c00d024241c0d58001c1941e06031228018015102c54900f420301459a40d8011135517503141c961541e549104030105040c5800072010355480e0008802c4a001003088000d01e803a500940e12a03041c03e41c10031750240700400c801100042002513200090385401690403031448112510700641e1036202140380b03000b001407145040c9100080c0c4408031600a4058032541c0e0b5261031000319490040380607402c80d00e4034803500280d075105003850003212400a00940d801072092030082111000c0c40301001890055400440c00300d90090040114040d000451980c0322008907001d10034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 483876699 1250 483875449 483875453
    0x6062c15010c03210c0c0b06010509030312130b0f040b0604020415050904060506161103070b0f03070201020405090711062a0705010603020904030507020a06081509060102011d06091603 81
    0x1030b0300c20320070700107061000e01e04120501400d00000f001c0d000c1c540d80401d1180408001c0300500100705648116428190f000c04a111944039070f042d109260b01c003074010b51810703401d0100d111034280300070000e52440c00b41e030b20000000b03841004079030f0248021a00084650809203400e00b0300b0304008215a001301e106010401545041980c485412000e03410010b070395007409008030b00548443c0d00090341003c00001c0c94178030401981004041381d07000784440e0314071a40f014105521030b0000c3c4160700000c0d90074020018280030b000c0c02160041154000140382695410108045542c1247c03090003041e8005560454001d0500c00a0307070011042e40b94504141030240910070840c1c94226a05218101241d00d104000d000d52080c2c1c0a960010807100091400346002012580030646c100e004c1c805007600029002e029900390f900840d542c41c02d50f581020540140151008002d00240c1190340b40c864103c9601c3c0c140d4003041003003002d40301806880c584190f030107140c00c2c0300d032031101d400034444102040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 483877949 1250 483876699 483876707
    0x80c06071704080a0c02030c221a0a03081315080105100c0309060813080c0604030e030d05031909060e0609010e071413150b130902040b090d06062c1501 67
    0x104c07082c000d0078080305810640c0080f80c41e208940d4507042d00501441d01060300221440302c00030345840711038001d10000c1e10380405800e64998141d009070b04041c904409100003104403024080c0102c05400b060a4982d495081d40c4e003529103809400045040080140598103002a02054041d01400c080c1000841c5a60051000d009031003104200407950700881c42c10140318402000b00380c1c10284054840c2c0080002d0f0f80c540100303a4044000c03030310030401402c0074180030a0000c000502a1100380c115500c0188082c0b65145201010302a81c0d42e80c8074420003c0c1c6d003442a08000711a050040019141030a201402c480f4003101e00f16160707201c10b504201000074044a01d24001303003954548030a41d0308040c3c40c00600002d1005006446684038003140c000f4000d0040c000300401750242e603920a54071a025000c03842a80284c09200303004000c810000e0420a20000d0710300c1c85008006851651000380700c18400542010340c0da4482e21080020300174852016194116a80394009a03c9101d8800060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 483879199 1250 483877949 483877957
    0x2206030606050c0a030c0201020f010e0f07052b05010b040203070509040506042903010204030f031211040e0103110109090f140c03130f0c120c0305011a0625080c0607170408 76
    0x1400c106c4282d940c0c80469200b4800311080c2480a4004d00482000005442d180c40311020154014071440000281c02c0c601101d8240d4506c4800d401401c80e070000c0a481041810783c060180c07119920740b85160300c2c81c2c0b103600c000e5101e0b60705503842e162036054070420042a50000b5018602c41c50501d9041c00c40b0751001c0704105501c640d212802401c280125000c82c3c0640510380c0041e00503031001314181d050682140800b0034480d6030300010000d208c229410002c190041d13000341d01034942c4840040c40059084006900954014142014513994038400002524000c05c0482c2c900c9881d000000400701a00d80d1403038001e00c0c003003455400d500d070504542c1001c0102e01c602400c0c6490415944041c4160042001d0103044c45020301000d80c0b4032410114542421440704035011f61800a0114280346145030101980b800208030300d03c0e10039403441c21340b8207800b6525204101c50380c40e60144000b07280b000081c051840d201d0081c085030f00d004a0041d02c401040e004e500ac9a142c982c0070080000e081c00304607 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 483880449 1250 483879199 483879203
    0x1b020609190b0d0204032a0312020115060f0e03010b060a0804080f0f030402090703090f140c0306040c0e01050a060c0611041e1403032703032206030606050c0a 70
    0x3a80d1404040d8003074035102052a8001560100005042c2e003039803007680c00800540707001340c03406440d00a0421800c809500404860b40803880c43c02d2040c070004a0081007562001c06600c00401c2070168410340b1602c400d0941e0001c404a680501314030035681d0885003503030743d02038210020003800c0e0019011400601c5201054000c00600d50009805c0040c10b0003911901a0340c12041612601031160015555100340c0b8203038451043c1000141e44184240191111641e005040d402110150765485441ca041031046d18443e004006800c0090380b403c100740b40c840c6020b50444a80c0c145820329841000c54180c00060040b030400c0000d2000580004d14002450343c0860001070f66064240d9204440c01240c002039000129091207001c8000b90980d05010f5a034469519860f80442e40300305583d03032041c01200c1d403d03039072a0380807524048820031143c0402038000c1c00b40c3c0d2401500201c100000a122200b44550703c0c0d9000050140c41c0d8035200303100141015003016442c0c00071100c61545d8401000f680 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 483881699 1250 483880449 483880459
    0x706031e050c0705060703090b01140d0f060612050307020907050c0d0c0809041a0a060503130318030507080a0b01120201050d0f0b090a060503190b061005070c0f061b020609 76
    0x8036090b5000d901c226444142c1020640b885030400440007406440c451a083c3c9444d1032400c000706190054480755031000b400144100440c10040c1e95050b440392010b1804d49503103030b56680c001840031264407540e240c01e00c5440956500d030044c2c810080c41110113403051041000a02800841c0c0705c001486001c0701540e8206a0040074062401031100d204400080f0342140c2009404900f24284411142c00c0342c40407101d00e03000d980c0b1813104030340a01046503546110b400800c00034001ca401368851505404141407050100d41d16901c9151030000586d02c04109580000c51010500110340001d0340544200081a0b40410103900001d1981c09580741c1401030596806c0c1c0f0304030481d519841121044e130007405001261400020500013404103214850180c018100c1d10117181501c0d4081044581d44030711040b58070f488003414850b0409000d50414140442080359501041c2d0141380840207043c00c150203040e007401c00100902034004200701500f1204041035200040e501d801c10f6411541095074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 483882949 1250 483881699 483881701
    0x1707030212011506052d2104170714010c020a02091003020d060e0c0d1416120b0c0403080d06030303240e0c0405040614032103010b0702130f0e0706031e05 68
    0x40072860440c94640310603c14180f001c1803100b104400003e0504031b00700c0c000000000c2c801161503d4038200c01c231001444040b108081a14100402c0090f11f001802155102c0040d00e42d6181d5a017155003401c180d00241e840b1004203011441c01201a039130250720000310103011403555022900484042ca0000d09013610313425a40b8040700c04014494182400a10f10820740700a420089a005150469050740c0d025040265100382c40352135107141140c0080302c00c40f404100c95103401a000e41c000e06203000300c1d2400c00000010400420140508005000001074031620b50316000e41214809003c0b018544000710748084001c0f8680140e80854100c41d50040030b560704c40802007298820f5422003607000e803070144d001c641500e443d40c0a1840c814181c0890b490100c1c4c0c1103543c48103106118800c401c4440400052000e904520094141c091014090200c8001d003400244181e52a0300d54042c12142e462800c12610003041110314001d000604041003100a0b0384e041307000340707181c0d40d04500c40161544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 483884199 1250 483882949 483882967
    0x170301140a0f090f02090433050d0206090105070c03150606080c03060f01140a050301090c080103121202040504090605090d08090c010806030f030301060522060504060315170703021201150605 84
    0x42c0403922406c80c01401040b01013105141c900e03400410440e00650714190903111042d04000f107101074107644000380754920302440c1da030810109504c0700400504008060192200144c00030036130320084c602c142c5250800e0f030041e00c0b0060032035901303920400400400400b8092140042d0048941103031040c2d4001001c08031110041e542c410401d0f00518100200040103003400364010003440c107840d00342c1028071495160741e404462002d4280409013400290030f904a5941e40250f0300c884410031069405403d081c0e079500054100c55007640243d0742c43d52500c003003220582c0103204191469845080a02c4075080c4824030b241c1c0d601d058800507040c8054800400c1c5d0582d0100072400c84016404201d13907403581c44860040031601b01c0400d070442052160040c0000140203142002617425540d260350500386030240440c042c0050f41c118564400c81c0700c40105280d24502d0f4420b04204040c0001e01003e0326610500460f04034410100e4020303498407030715440303c9110b0102c00b81120f038072b0320703149e5240c40c0e03c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 483885449 1250 483884199 483884201
    0x50c04150e15090a050a091e0c080c0c0115032003070f12030c05012f040305030a080c130b1c0b0a0311030f01020403050109020f011115070507170301140a0f090f 71
    0x317400aa90018868100007020551754120b002c0240e18490300d000107003600071a900c140e40e1008040c002160f1200c0000b1282201c11004c0c00c03004195030700210f03018101c00b0000407e1080f03508140c3e94074804e10308400c0c101c0704e00c1e941d810708003d0131b4004204031072034600c000c8078089c000d00807000241030b031109000c2411310900d15200714070342100080040310b0415a0000c0180c51102031440b0720110007042040c400c2e010016102101d802c0005140f4190101c0c0045440520040850490740f50a0000004034452803501c03401401101300d41c43d40d9040c03410030700a11268412241e014503410101010860f0725490b45000480f90301080900c104d600d20f000007824801c4184000134590b2000c10000144941501f00f400c102c4e0094402703d4000164500444000034455140c4669070b11410800e01031100403852580d21060030318201e814403459540d04038204880b140440342620001c00180b003240562410301c0d40303800c41212042c941701d14000b014540034415218031084607948030321461401e551 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 483886699 1250 483885449 483885469
    0x6051c0b121506041b0806040c0c0f0303050f10050109120204061d06100503090a141006090203090c04060f18060b2a0316020f13050c04150e1509 64
    0x1003016198509000350b00d8404844007200d4051245040107025115500c81a0703000c0002d2541d591142065660002400701501c895400803003005404034155000c91070541414160500c6560b001c03546050407910143e1054002c1c040c01d4500940c038004000301c1c1e801000c150102c864a001c09480301e611400083c000b45916441810f580741d01c4914541c14540750340110340702e00d404a51509400035901d038100e440b40811240010750f0f070301c026130303a0b000b2840308000e042481c0200d204032180708440101800540c1c9841d0f016401d12600442400381c2e12601344080040107809a40811203141741417100100610140326001250381c1d201900c0c144054281c0014000e005a2004159202003035208510b86081c401440d02444da441c90312803001901c0801100d6410100b54118810399404d07400304074001103520a1070780e00806104400301c4002e01c5004542c0b18410038100179440c1d5140cc03c02881c4081000076400800c007000140207055680c0300c1c0c20050400210060079110503c44010031040e1403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 483887949 1250 483886699 483886729
    0x10501051606022a01060f0e270f0c1806012a08130e0708090c12030903071d010f0f0e0a09060e060a06210b04030c2a06051c0b 56
    0x556030080034400b61350303090303081000001c201c0200705d920b0b81c0340c00e10300032403403a0b020f20b050300028800030913440424044d4a14907035031085801c04240c1d000c42c00c4145440880480c45260303400c20035180c4401c3c03401103807002002400c160b240070507141040000340b0b860969048500c0c04006054500245903030700b1380034174009a120714815a1141c410400c0050b420413449859406480c54001400151282c5607490264620100809018120700c0800c0316954601c42c0500d03e41c0704c140041074043d43c0030807400700140387c10007011a004111250740415080e050f00310507101c00d400441080030140d0740303039030104941e8842d01c0000141c480904c0c0360080c2100c0231014110504100300000b011901140050240704940c00400c4040d6440c040711901c0c803002c4000c424804408001080032904140d005a803252107480d01c400490800c6e0307981100042c2c21842c2e00d0a02032113480e000c40350000416448041e080e80e044c001d00344100d03038580703505401103035100c1200d0340d03107400034a0300350345510440b0301450b2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 483889199 1250 483887949 483887977
    0x321020f0a05011d0102070f060b0310110a0f05070b0106030513060207140706090f030f020111060a09020f010804020d0f08040b0c010e0709020909040b10180e1501050105160602 78
    0x107468100140a840268410203c03602c00e250f4070071980c2c00501c200d5010a82c04522100524940d40f589070040002000860300f601450310486801200c0b44150800c5522506801b5240c081160001700f0b5092400c0340d0b4010311404000d140081403e8000d030904481c8145400f00300c682d07038417103070b9194204008002000700c1e002040003006c200d0655510005060428102c500b82903846c08212060072417071059941c00600545c00b4404556640f0241c03881d1801814203405042d00181110720703207001107603c5d400703440c2d44504507030441c6800418112200c00034600140390303003020340024541780e0030408014600283d0441c00e0f0104803210b4243c400408910301400e86070000c40300c082c0d021f44150900032809000d807150100f9410118800d86940c00740103040c08582d82d07a42d544043e0501809820000ba0202e501000034203140000150100b5002004000c10b200c108401a01d250030341030000340d00b402002e480148040c0c3d90040690710f1480030300902c12185203042c10030500034851041128800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 483890449 1250 483889199 483889213
    0x807091e0e0c040207080c010b01020d090e0a0b031603031419081e1512010e030a0c0327051e030c010c06020702100206040c14010801120203250f0f0321020f 69
    0x4051088050007048520790009c2c010002200d004903264080340141c0000305404100501c10744902010302a4013040e0104002540301c08200006d00e000310019521580c03448a403404e00816901c04034203852004a48032050400c0503000035107110f5030341d0034402010003032104005000340c50320303501040c0448142000c618180c00c0550100d0035800310b801005026103450500c800c0e01c40b00500c1000c40300682c0700003650810a002c807081394402c209900030380c10024a024031820b500400809101080d41c1000d081e02003030700e041c050000c03407442051340c48480d921542510304191000300d64100034003024a0896400050707403a20710002e0090342806900202403e00021013a81c000403007500460040340b090381a00c2d5540c1c14022101d6048110900081d4000010032002c00700030040144130344001c0549400c0480b4240109004a101d0320a10b011600c00504014070308c40703098400003500c034610704107000604640b101d10140301aa100b0002800d20b64412032107240c42030064105c010301e0001914a1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 483891699 1250 483890449 483890453
    0xa0e041409030c0106060c05151b0a08061c02030c100c05010e060106021504200a2403061403030708090a0b0307020a030206010e0118110d020a090807091e0e0c040207 73
    0x40d9400c10300c1d004000d9817030700801180c0ca5024417112102d00303611000a006020b56101c4c44840e0b510090421024076040040a03202d4100205c003415100e0005d90700e05556150010404c802c481031443d604150540c1c015114000d0388010841c50302140043d00c0c100c15100d150307881120040c583c410085c0c280c0d4030b0314200080211000c02c1c114100c174000e500310380e05642c0d1801c40c0f00080b034090350000c01040c60300e00b01d1304102040c12489100188018650b00170781d03581d80300c04403058044002c050200000105504102a09841400054003d190f86030440c41c9010340402d94a1003204006080310f00081200c10103907a46c250b240c0c02404c0d09201040d00c904007404065900d0801041c200d02501403c40007064000380c030b00344036040316403684c0c24012807080300000302c000b04880780038681642c8003007020f201c10702d040d400186881800c607501c03144a80d15021040c4c0c1420390a4100700b20250501c042e40e105118080c8410b01e080d149600c001030000c80c00f280c0c051900030302e1600190460700109607081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 483892949 1250 483891699 483891703
    0xc0b10050406061707030203100e22030e090f0717040501090807051005090d050301030201110f0706091d090703080c07080601090212160f0c0201090f03060c090801060b0a0e041409 79
    0x401c0752240132400e907611354000c194240c1c0002ca8400701c1d4280c1e880d204014007403030120300581103844d540403032501c55150400a00700840002c2d00750007054510741c082a103400d19049190b400345450800510b90b003402c190040c10400801c80d0041e010320f2203400718050000a50203100413581c040c1c0515a111a949025600c035100c140e000030110307140c40000b540725a00458408088180c0c0c0d07035202e185070b003107900549020407200c108014031b01c00c65036043e803a82010000c02000e00303441d03250603075461702e44007201c2070141c4604c002c0300c8040c500e0000e00000d04400690601642e038010681629404540d101d51700e8004290702210721481103c00021302c039612a4000c01101c0c3c00c00b0510010b50f503904070f154a00d03c007152102800244201605070340148204669a2001c0c030500d400d0000329079541984400322555001969a6956034488514907900719196a00900c0d900300203200e51031070441500e6480c0a0041038200780302821000304625643e80d88a01c4000d155040c09241c3c81c1001b034070f495 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 483894199 1250 483892949 483892967
    0x70905030f01090203030304200405070e040b1c08070302250603060b19120204180f0e07030c0e10090e07091815020d14090c03060c0a0c0b1005040606 66
    0x5009009549800d10040010f0007207103400340d00500110700d1034686585400c0f16176210700f02504480f440800c03040855655000359402903c182c1e445640c1284014108421260100019442145401c156828100020304040201500f080c00e2a03284d040701d0900740d091402d01440c030605003900820030307031040700100104c4c410b0310003076581000020780300c1e50301a00c107200c0c0c5400d10a20074040070303140041c80d02ca0301040d4036000d003d24000d400c2658400c8041104408a5003d41003a500c50340b0b407460071121071254100380d240c80002002124034644403100854964081c40c004201c01c440011150f20345101c2c480001c0915580400c0703001c01c02c2c0b00e05a1540f00341d014103d006400d001c070540c880c4001c0140c25602ca9000100301005840120a030f0b40254420f0b554421380d9a2900844544000c800b034910b4864001c0802514080180701d0401d0f00b030103001098204542c6007030109411240e406800100e4403540b0281480c103a40b56652101144039540c1c4c40070703038070905200307020407401c0e401a105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 483895449 1250 483894199 483894209
    0x6010806090d080708060909010b040f2a051806040317030403030c09080c0d050a17190c1e0f1713090513171c02040e090105090607260709 61
    0x50760b182c5408100c203d69101090b9000300000b4215004907107246000b404442e048111040001081e100c1d200229055a003002e603c0c03d4007507500d400040882c030344000d040c02e86000219609003042c58000c006001406040040700010140384098803c42d2242c1048030041e5800070985400d00360b168800f94143d0340100d4044000a040810100701d10f400350708030005541ea49000f0301003e40d0301100384103050620319029591072060200c2400864501104014514028041c040ea00c0c0482c040d00d00c050600c40c0d141e44104000304030f500700400c00982000f0408055040c440030b0340004d0b401d00790b01c0000c070807030090448010600ca00702070501d00c000408040320000400c603d09c0d50343d0034007802141e80464046d11506c0305582c2c00d9000503030340740811036080a4401401d0812403810240c0c55084454181c0c0912513500007800e1020303055a030303010707035104001100900062400c16039950322200094110001d219056202c06802ca10000010148061400c2c064906103004040140540102c3c424 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 483896699 1250 483895449 483895453
    0x10504151802010f0e011206090506010f0f050a030e0a0c062015010303050304080d05010b0405011b020d02060c120d020406230703200d09050a0b090a05060a020c030601080609 77
    0x3408010140d00207040c0c1c107150140c44500890648060aa900f03114041c1d1141c10020040508486190319110f807a02824524800103141d02d80b0200250442410101400c18001c42d21100d01000c2e41c40343c101c800f0749019180109042000c10551443c0c9042014020f18414010401280070359000c01c80e8101c0b2040131506110691040d1045a00c4107030554400d881d44501400510100303000340001e58105128140c1c2d03914104200f500c240803204203030032401040074001820070456a00554030ba6101c0362248012560342e12540c0044c18410070310310000c1c09020302065100f4000703c1070100f1084600d00b1881a41d45030407a2415000079071190140c1d9001c1406800028a28128101c134540e44000e0388072030741c0c6040d1150300d0940b00700040008882450806440b84c1814200a001d0001a507c580e20740c0c94445041c10100112003a03641c1040000301c4050184503595036404111030b01f1110203640c900d50311003c14404905051400442a40510458000041081000420a2080c401002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 483897949 1250 483896699 483896711
    0x1b0d050d030f15061b020f030f03190e0907140c03040308120f06030d0c0609080c010c020f010e0709020309070306110304060b0d0c030b1008060a1a0f0108220501050415 74
    0x40701c00d0709240c29000d45070004e00b04000c17030310562102e042c1e4a40c207140000c068101501003503000a2811200c1102c44645400119071a210400c660200340340c4c00c44503051500b09103541c1c0d0040703804072000801d158100301980c1d022405075004c0000300c2c1c10701d24a40307017501c2d540c41e10782c140300d800b41c0d04c840341c2c0c01d01d95040740000800301d80c5003075030403409140000c020302034100e424503049032040349198040d5002a6078010041c0086c2151004080002c688030000c100035445000117130608034034100c00103803039040510174450403002123885070543e0a404c40c0141c50b51580c00501d0301d00f18031500014903207450003c1440b0416042070285100c0ca204030000e0014003480810701400d40d101160042542441400600c006100368005503440300406030038402090f034450540d890060140c0361000416501c1c926a107041059201c503990941047d0780c104603003180c1d00c00090402c44001c04044403410b44900300d160801008895500c0507400100030b2049040a040032600c0c00d024205d48240700c0c1c50a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 483899199 1250 483897949 483897971
    0x1121209030c0b22080705061e030f09010c02210a0905030604031701090c123812030f041a0c030403050c090612100b040b0301020313110d051b0d050d030f 68
    0x52030401c25500c0d005c02078880a40b038a01400364980090030703600c600c0459512036002401480020b14420100102c081d222401c000030a282154203085a43c0c0441d00140310aa400e44040f2006c0840c061444a6840ea2039100c1c403400c541401c01c030380007550305010b030340140418954412440c40401003035403250740442e640c6802a20407a5020070201300400e0388900c64445210440c1d11040c0c2850a07046507440c00700c0e10740400507017661815010a0042c40d42d4207100c4081c1405003100003c1441c02c00203510345040b894004110707000c2e622a030b5880180412655000344800b030141d445c088183d40440792030b0713501d0f460003a4850b1104a001405002c0000000d200707840c020f0b2a109080024101800844040311101d0340038000e0101c100790825200e851a2a1a85091008501c5800b5000e409141400307545881d0f40c600840420091040c4060625100824000300c1c4100441544140800541d581c3e400410301206120002810318001c1101038502d054250704500520502c045040140d00c290f4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 483900449 1250 483899199 483899257
    0xe0604021809070303050f0c0307031206050607081804110a0201092d0b040201051314090a0507050a2a061b031107080d09060612030e0901121209030c0b 67
    0x40798010540d80c00000c0404c0031a010390010000c2c20850f48149103000c40540300d00d4035552010404400007040070b840076007171046034440c10002d0401114018a2316815441c0c5210381d0145d20704205034203038501241211940e881d070280001d00e1100840b50b032904c0450b00003900806000200307880c048003041404040c0030705141a544258144806070000c1805c9840e002480000200100c0c18001c0402c5812689040d44410340e0080c00580000c0107090200e009101110303e000c0e1040e600e0b28141418081d80782d40140555031010114034280c02c4841ca0402914100d03040310b0100d030088400e80140009109464004a8610308046a0412661030444c011000c440310380d154100c3c1c05e40c051001c2c4000606141c01011440903201c008a4021501d444030ba08072241d5a01540c400807203001800e08254126040406c495003c403004100c81d850315030000d40d401b003490401810340106483c9030314114041c00d4003078013445d0800021081903407100302d202e015a210864414400d10366060024a400d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 483901699 1250 483900449 483900451
    0xc0501080f130311070801020703090b040b07020d03090b030c07021c230a0624090b06030f06031e0c030c030a0519020604031728020a11130e06040218 66
    0x140d210202655038840b80c0b1109416140d401c2241000180080070206400c1005480003504031a030005a41e07900324903015140c045660310003110600107000820107044040182e0b0b46007031701554040441e160300d25048400c22610741000304011004420b1184015046c80506011442614642c240f020b1030960501807000e000300080c18044400c6100da0030342c49003c000044420603d00b15207120506a50340c0040c0d4000400345172548165040c81400d020712a010744000b401028810400c000440340400d80d01d12004104541d445880408130321035132420001c10b42c039410203215002c0903c1f480654940c48201e1070811ba03110303205141802c0c2007480c0116100c41560350201c01004004010001e113880d10520587c166071254044c80b0000100b01d4404c42c1480b0101144041c03661501d0405c1c2400140c0c2039444508001403a01556400c0250001650b8004607041181300c00b05d5a000740c002044c07890482c05004000d41001c00482c0c08400014545000c0c1e4406c40e0015550500e544100c034107200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 483902949 1250 483901699 483901711
    0x6030c14040b2211030a0f0612031d06042c010602120405091503070e07080106030207151a041103041401140c0304051c020a0c0e070e130e0a0803040c050108 69
    0x41400c90300504240f0031140601d21000c4650104e03024220003140240c54008a6402100940302c40400c2010a0948030300405045104c011510020464900600407052000610780c01032003013403000c400b40d03a0305042e1001040381108448001c82c81644044a10102862441c12a0403400000c1503590021401c3c0d030b041280100000e09003403408080040042d0003030090104050300c0f0001c0055901e040c0140005068880010089401c2c220f030000d0403808168808002c2610500c0404001154503190164030980104081404641d28400701140e002c0c101c9110f60051500c0101c40c840440704000d1840385002e0845005480400e0018600360351003201d82c1d0784502040000510050801070245420900a00440f030441414444150410000107140340c0540e01450145082108404030300014200901d1424510b052006003e042900048030072441500c08091600d00014607922582e68002a2000c44000b1082070412a201d5401a00d06880e282c1040340003180b254012501207008074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 483904199 1250 483902949 483902959
    0x50106050a1a1b1207031716081b0a02010b090105190b070609150509060702011b0f0c0204050a0605011b030f080405031b0f2a010e0105040906030c14040b 68
    0x4008800840360b50b4042514003021002c107003608030000740208078110310311040f9411282e4501c014180604118014030080d0603419610f010490042c54142c400b5000c21001c1c01d006000740c0304d01070300d06007410f0003c2114051035030220700c0d9011254150040314160005594070203882c1d0300c40703003030050900740d4410300c003500e80c842441000781000d50700090080c81c1c003070040081c64601a41c0e58003c402c10084140c50f441d81c5807010f101064200740409a003180c6c3e0b5000030080058100481d144661000031a4424000c043e6894003a160003a04000121a4020070030001d900d0144a2180140071501500b8006860046080c00d0b4901180b0311803042e54240d2540000c2001c0031804640f03150000b40202c65501080c403140c28000003603035101800c10150b002820b002e20950a1131460f0910f00044420301d421204d0018a20304050501e10507a5402860301c80303441c0d107440005076468811b40d800080039903d080c0c0c00001740301a0b1900a8156034103021000b030b90010001c200070690300000645a845 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 483905449 1250 483904199 483904229
    0x30a020f010513080604030f020c0102060105011b170c16031a040c05030a030e09060f0a0b030a020403080307030c090608061309110d0b0f0f09100c090e0c07050106050a 74
    0x1618024203009a8080145030040c80e241d807000c8800e0f0008116401a02d0b83e5010b03005100403da0044465030f4030f0080ea10051056001e4000007d55a62042c8541410721802410515401048000c0c091a46070407000d465051881115140d5450340a0381c2160000d0180900345c0303945400300c4c140d500480b43c0000d43d000041d00301c05072054100c040a04110b50989031510700080030703101400f118520a00a4490840c0c80d40540c0912010304d200074511840303808040d0802c01541d40710300007241607440343d00c59140c0301d544090b1403070000e00c100d4001030301600021080000c455810b401c00811007405030f440c211540d40c3d401003668003060643c1c40e2544a010300e41d1080c55002c040d030008030110300842da02c00059043c3c002261540720400025100601c3c0360342049154200d1403003191304061100101c030042d1610142c440d071a900404c0301768402da91140c140b802ca80c1c0c0b14a00c890080d00c80384100c0300b06400e09800070441a8030195085907503508003400002d00d4a06003a805088034141079541d401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 483906699 1250 483905449 483905453
    0x60405011208120a0204211b290c070f15050a0e1c0605070306050415080d0c301205010602030f0a12020d020418091104050a0b031c0914030a 62
    0x303d418001d1104603c50b80c01e010020b0b00c80c601005e00c540540303265403100d5000007103080407036060100d2007181c00030224030081004944074600f904900c48000c40c2145a0800074000c0001c82480b941d151a1214821080041081e500042900b0700f205c1041c0c1900140d081c01401c1039419008028a21005c0340410f980c940460400c8220f115510040c46d0390304104010300c0d0f580c101128401e451080019036900401c1c403003070415100b03482c001310040454441c880d01e071880130f680d2031400410f160f0800c01c0c0c0c1d201d00c0c020840500c98000c5003c00c4428020708010710b61210b445100314000a0000061200140440b038186501c6428140c8003070381d02030f42c50500018621100d90f80003540e4681044818588031881d0381e40da00c090140440d5040c0050703911860240040300c5505038140b88241d0900d401c4000e80050b4000c00036000c520750aa030b01080c07580e900034032000240b49000c1000d405001703d030305002660405903448490a13840f92108a8100d89a031076850041e600d5050b030a0b01a408071381c442e00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 483907949 1250 483906699 483906727
    0x2060d051302041b0e04020c030405240706051e07090b0901200c041413020d0c0503030a08090708150604050903090d12021b0105070b2203020303060405011208 70
    0x190041c4440001c030441a07040d40460b08036000e00c08502c1c621040c240510721050f600180807071482104960039070038160700c4d044554070b0348a14468184140000d04007000702c0141c4901610001d02c100e840b29441c0d501d0390425001a002c1141c12640a9844902001035001800d40d0039002e01343c10b40c0d881d0182810000c0450081d80031043c89411b20600034801d214999040c9581c905414041014010600302c5005000550380fa16064680000b865010800d086d4800003980c2c1e03041ea011500da003510741c001c0c1003e059088940c0c0040b038042c040054905c0340190004481d50151440008807058550b03030311150381d102d41740070078103062000e1400007140d820310b02600f1182d0440300000c182d0340381040d420002880345e166250f0481d4180070800d03101e02c0392901881880300d05580000c1c00b0000340c501c040000c01707034450100d0082030340c14010301152882800c216482090100d40001c42c446001034100a5600e0b081107070540d101e54200b0001066020503c00000340607a4008880da041041c045040e0b8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 483909199 1250 483907949 483907951
    0x120421050309042408030307050307080a06030f110f040204060e040f0f05180607051207031a0910140402070809130e16180e07170705060c0d0f020a02060d05 69
    0x290391444244541d4405503118400d5004803c40820a902c100c001d05426650740b8010350701030a9550428010803800e030b600042160390066191800341425528811420018070340303a000a080c0005078001039040000c41000d034803070020202d621220a0b0810030800040c0d2195020b60300c0040e401c501000c5403030400c2d8002c00b0001c120400007140b144849004401110300840d140e00d02c1c0d8400e140c1108120034188015070704000646082407429680946020844001621880c20140d46134662000003480020b40c0100c1e2800501002c002e003000342c4004850b620780d000344a4624180b002003029845c240c400c841d601c80c1d0000002d401c10b81c0c08403c020101111a814031101c60f00c921400024400500c40c803503a5042c0c44920168060419001c103080c007210107902c0750075a1501c0c0e42c4c0d646924000480100b29184441d04000c0d802d080d4501c41c3c100342c415800250400d1021a20907415503000ca007818601c449a03072079103c41c440910f0101d0391030703003901e00194008804001940c0d0042c0590051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 483910449 1250 483909199 483909203
    0x10061211041a0a08090715121e0c0f09030215030402060d060605120a050f0c0c121b0d02061b1305130506011e02120a09050d0c030302120421 62
    0xc0d410942d651501469905800c0200b4050040000c0e450f5030107500813100c15005500a002007402ca4100b80084000410f038880042c240f02d007000240e000032160b074000141c2104010740c000407840c400022040504010752400010a054420f215641b5105404d0031088a40040282e00c0001c082400e042c81c0e07600181c020303038000703000300200402054140250801803040c0c0e595103503a082a9101485810380c0905500c2425040905010280307400c5252980c2000c0900d0006a40c0c0381c801141c18a080328040c080c9922101c08551502c64580700c0092030410404881510090030309070404a84422040f500d844060b00b045c24480144000500038110440c65205c0c090821a1108000b03010b49101e01c0b011041d03107480e0020841d2950303000841303a86225011020b000351003881d8502945130303c062514400581400f003039102407a4450301d00c1800501c0c001d010101c004140c0c1c100403441e05840e0100360007510500041100c0d1942c0c80341290201c600c0600303044200410a054100d1030071902c082 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 483911699 1250 483910449 483910481
    0x903130e070306030c0609030b01091107061508150901050702160b09150304230304080c01030905120703080108010b030613020d0302011d010f0f020f071707050a0b0609100612 77
    0x40400040e9920b107400c5e010b003010340c8035118a1465031030048600e5405030855503209003058081c0c902076001009461074241d00040114408241021205052080f90301000461040e6103c4402c2c49241542060240c40c090000344900e544125040c0d80d1401e0558000c3e08400c007541c0f08201140d4440d01404841c4030081c0380d022080d0080454280d1608195010707180203002c00017002001d040e000c6010001c0851201a60030946000040c64070f9000300800941419100d158160801000340a903032051500d40544e82c0e10303418039084c024401ca00034000d02074203601c0e0410404aa1500180311803045000c00100300c04d10030380e9400d10690341500070045003550b4881c010041c840c46840c000c60000c40002c800020410899491a0295001310100c0d044861041107211001c0c000041142c1c8220b030000c100d40700c3c071984401140814803403980043c200d4000c28010004028041400a000340300403962080702d03486500c03140700040000c1c49440040340d4503481c490710b06001c0f504035000390a55005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 483912949 1250 483911699 483911711
    0x11a2b0c2c150714060f060f041407050f09030d0228020306040f03022109011b02060412030203120f0a0c0806030a03110708030d0e16230d0f03030608060903130e0703 73
    0x24607181c80170550b000600da0582c1010040d45007810181d00092000c1180c1c03d014594081d44080d00380080500450108000068851081030b410000c4906424000e8206e03a20050741c0c1c44025100d640609001904a09003074540040c224511304c0000705a030020090000b81d1101c0e41c901da544485401c0880a502584244001404200804090a202e95403510f070340c5034651000140b6181e038095601407a410520f1119015850344c82c181c0b000d130b42c01480040690304550605a1840c052904c00a04e00b004120400074040d000c1c0c070303141b800740780034036000e100b00c140382041940d01280442c0c0882e00740c0d00646000010911826081d0620007443c41940c0e020707512000c02e81d04550044507c0d50b0341c5c90b11052380c641104005c000000ca2000f041181c0346d1010b09000740d040b00c1039440b041312044042c0320900700c561513031504100386400d07502c8007021024107001c1ca00a006400584509001c0e4083e920014290fa0b4000c01214610684030341314500c043c0c10320040d0032517204068440d80400d95602 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 483914199 1250 483912949 483912983
    0x81615020c042a110f07061b0503130303030204090b040603030c0228030305030f010e1006080a0f0905150a0203090c04090521040e011a2b0c2c1507 65
    0x1e03e440290a40ea9070313040c039aa1040440e582c90310303200c1c800858080d40700880c100600e41e480703501e03580d500c0e82d24000c44810340341d282403c5244d400b80c004040f4001c02c048600104050300341d40200211107104100b403006030110780401040340d010340b0000d400f00355800c1e000e00052404582c230441d80c100700c0c003200585250458010120b00384a170030890120b00c1c00400e0111420a0b6912036004000301e00e40011145406400c9052040c124418501440340c0103000c0307080710510f5005812080886101040440e69070300317101d40d40f0300070301c01c485400c00c4800002c941d0013515030085900c11120300c4014180b10000006000c0104210202034400e8040c0c00f105a20305c804c04e002c1d01d15400310f00c2e540280c6446c02c00d160141e06500680c8400b0303002c500100c0d480140340c0f445040da09a92082d00b82120343d151000c3c2a115010007102070f024286103400b0b8200740040d0481d000340400d44202e1200030464441040c60f41407c02041503490f0300010754040940d8a1410000400c001032042d0b800c2c40e00010f442c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 483915449 1250 483914199 483914261
    0x30b0a060906060c0203011b020706050c03090603040606030b0f0f15120610030c062f0c1302030115110604140a05010501060e28150201020403020604081615020c04 72
    0x10f07004440041e0030000100c003545000d001d441080c0c082c0340d481105102c00880c001e55998031a00c903d0040c8180402e459942c80350520513250030000203408541e607454546000383c0244500d000c119101c0c1c10441c0131a07448210402e41c2031203028811020015500d88180e11452501c0a10300b1651000c05501d40e1903c41d1030912203d8050001070161681c06410762074540001040c0382c01103420031103100c422140917540c0804c15031704540c00c2a0781b01c0c903200910f540503040c01541001e807500501c00401c00380d1005804c1d4000d40c100c8180d26420300c0090400e0b4030403201886d01c442820303020740c000c10124000c40c40300522159119400c104462000181c3c0c0d85181c25254241d00400c040343d01302807150044e04000f25100b2046045080c0c940c03015001845401100c01c0300e01450680d03070f0000e9900f840d081e001358103d40c05541c000740007944490365000c0d520740d61284020154004050844009039a2494440504003103151f034002e0300000c400701c820300c8000c0100081c2c1d0b0200ba00c2c2c545d1c09501035400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 483916699 1250 483915449 483915461
    0x290403060b04050705030c070204180f030206070e040603080405040c0302070215030406110f270a08330a0f0b060a020d03110a2307062c06010f030b0a0609 68
    0x4038610100e2820906000c00007191001400c9005101703081007000030301001e90041301c2441c4c1d4100c0b030016101c410302e94030607080d540c0001c00801a02e0400862002d05030005801403150546940795141d0803280424001611604c2c400107041040c240300501c0135184c10b0300a25011019890018240700c01b0343c00240e030580d1000d1159494a10010602c03051040c1d502407621000c020000706440d01d400c403c00e0b40c040d0303c43c00321400307d030b1f5824000b044480d5401406d295107220b00104114005a107540d8250b0311800b10110319030584061001142c044400d01d8203c0d01c4bc00e00040c0040d40c0e40d6105110400079000000c00c0c031113150b90310b4002802658502d0050400c00300c00e46e000700000b20049002400302e47c410550011b0000052141c2684141d101c220303450030003500c54078140c40f8500b0000d582c0007405140401841d56007004580744110b0018054610450341100010085041041b5499102c010a0040c1d1450315010f24050011521130142d95400c40f01c44440000c1040e5550400f40464407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 483917949 1250 483916699 483916703
    0x60b090f06041b17221202120325110607030c020f060408251509060507090806070e120604050a05070f0e0a090311070e150415030209070c0c0b0a0f05090109290403 72
    0x10307200c03511b9902d560420842c1e108502e5030302c0c0c05107181040e004003500c48a484143c9a6040013030044641d5052161a01c1c12407600800202c0d2020b0801c1240580030303244100b403010043c426040340401c00b04000980a00854101d44110720b040501c002041c50942e02c89070043d40417204a42100004040a088041c10900d0120000700c0311440d1800070b064440c082c1051040150702d10050109103008170386076802c5841c03420320f2000c0c0c641d0342001c40c00d00070507240d0445082c012074040005003d0045a031700340c0c1d20b00c640203981f09140c80358581200702c034113130042450404800000130401c81840c1d221000c5103000313040c030301d030500e40f084440e40c40c0c816143c200000d0650700009101c02c44002d00010030490404480034800024102c2c600341c0284481e100191003080d000c8081071425000c0c12500c010035405c030301c803021040c1d2a0071001e0100c3d8083c04200c1c0010b001d04040440d013074030400c242d4007040e030142c0d183c28107185041115985060744c0d0503072000703101d8401030500c20300c0454402800218 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 483919199 1250 483917949 483917963
    0x18030f0610030b010602030309120307090f030c030203150f2212020c1e01020a1209030804030809010f08060117090304081506030f07050306040807060b090f06041b1722 74
    0x50652505502643d03041c1d0015082d50b006009000c0819004100144154071504c1004e07147d42d01e10008840c88bd05680c860b03181182861000710500074070342e079039605480c025002c2b40c0642d85601d004a01800c02114415000c1b0151404105a102d00001c0181b05140005842486031001c1d1075403120b01c03411412810260741b0503030035441c0b10b04081032002010740c510040c0a0f41c0303021040c0040d48480a1100040000c03298020030300302180280758080145070015040c544035030f264609058207910aa00a0b8042100401020701880c0f04e0003000f44034230b070103a454500c880c809001c40118020003500455090100740408034240401300321030b0014186262443c104c60609105160403d1480d2610f1512a0030586017404292030000c0c003070390003c0c0e0001a455840245040c030000400c0b4008160f6440b69450342404561008401c1e81401803c084400700130440a006440c1640c2601310f0703c05c8042401c2040c940385030201742e520698820b5024400c07c242c069007220000022402c2c2504031141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 483920449 1250 483919199 483919231
    0x4090b090c041103010501020307082d03040b0a05060a05131d07030c091109060a181815080d0e01020109020319140d120209010342050618030f06 64
    0x7500c1c0c18061410741c40c1480028601e07550400000035240d100c1c040d00035080c2c0c10f0028210758081708051558594031000c02c0c1d01c0415501105616880b54000d840c12f40d20885000b021480000c1c591007940e000f41001007182d011545031400b40f1100f07640000180b0f40c22a52206101c91850420312002040340c441d81c05819010b0a524203614070948580004400030b1602091083c0f24044c04210342d8041003c990464403414019801c880d0f6a03c0e21050f2841c1c45001680018490741850140e10503603600314044c4050141210800c102c1209442500002c1e0300c12000301426a015810504075008188004100f2800381d4000c00e01d007184034081e81c1c91503100c0700004010f00c030003522031f80242c00060000d44180c0844010040c00340c04070030149242c0941c001040307240340c1c1c02948140e00c0280302114801c0d0300680d104052141c0b05a40650012000a031051070827040d030310f503501c00300342c03000140541c4c2010340100e50a4140409c040740e4076014422014061000701c400c002080c0b00e26010a4001d0754 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 483921699 1250 483920449 483920473
    0x13050405100f091101140f040e01050112090506070e060d0e0601030501050c1222060c08060f04020703080f09030c190510050403020a020103110d0e150f06010c0b0604090b09 76
    0x403941d03090542c4003540d1910741c2401c0062041c00c55505610340c246006080c030862a07031070709070b14400c1400e200f000000020f8001118011158484d04032802600c0e40c46002e1a501c40130303415a56031440050540e0004000114040c0c0100380c00001000d0140081c0d042500c401d02d247d046a003060000482580000010020014240600c503481032203070b501941400c01701d120007058400301402132103420008815141e03840742842c1507500d8850b04110140401c064070034014002c440f0039101c65010f0542c0d16011901400c0c64002c44032110707070581e1000115545c5440c07114003000701a000c40601c0c001001200175000c0c04100e4a80741c6030105d1705e15070110304030380f070601d140c090340d01c40e0214120301b400c04200c082500882c0802480e502800d0204402c04040000381186c840c4040740850180f4001d0324620400f8000340640f071030203000b400c4608985a500c0311a01d403000443d40d050001e007074203a41c1000110842c4c02c1070741000c3d02070400308203400c0965031015080c1085a059107254818a40d0400b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 483922949 1250 483921699 483921701
    0x80105211f0603060c09051305060d02330f0f070206120405030a03140709030f060e07080d1710050622120b070c021e0307051003021308030901090302040b1305040510 73
    0xb1701c2181c0d4142100c41519002c0407824040284030b66032003869403500003406649444102c0310450b0781c02040740c81d42d00228102c0c00300c0e0102c0304901c60740c41401c000810281c45142c000311840c040503020850304040c80981c9011940d07101e84022038100d0f006002e140007034a80341e0301240c010380c4100095920b45140540040842d07004002510304000210180304001c0d030421001000d49402c508804403041c11030034408040c0240d40a610031610070580c00080d50350010030450840c2106076540b40d21400d1062461802d43c0303043e02c1c0000c0012002d003007008545402c0008214131084000e4201c800c0c5050100308040d07440342c3d400720080e2441c1c41590410805c00401c0c42e036100c0003500700442c4004240c0c0100301c9511000e682c000c02400303c480f001d03029680412950004160051484d0360107500b507000207020750440e5411164000b40ca00d8040b810080100503a41041c206a40e5284880e06c0d540804c07010344010424180c200300ea174401e400003085903000c2d4500c030b54010710007465120440c014181c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 483924199 1250 483922949 483922961
    0x2309060406031b1403010b030a1b05030108150411091314030702120a0314031f030809100c121815090509061503130c0b0d06030c06080105211f060306 66
    0x1c0c10414031380c1141070b042400000703413415540503942d0183c882d542e6400d030740300138903959980ca1034074601b240c902a0015440300055050b40c010740140d481c620200c800c01048218241c90042c04036180c4e15a0502d68144a0900d9038020303c03109140142e50322503180c0b2403500040003021003041e0070000b680c0d01541840c0c103000100d000c40c0303001042215150b88000f805155200d80c000e250304400001324a41031510030101c9206070f8040740ca428100d50764907098203154441c01038580039150702c6003580d011a01403031040c80d41a40281107a600000002011140d054541485d062001c00040d004a45225a0b52042c0504900e81e1941c21046042c00c04018844000900242c86103581004003c5040e122000b906c0c3c010090560104092030b492800352000780e07480d000600845c8000c503d0b500d000145800a0382101d005050400800b912544101c44440090060030340099041902416101b001c2008040c02e0b14142c0076104a8506004a403030041c60204041ba00719171075900900920069104503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 483925449 1250 483924199 483924251
    0x7090c031104151b0510090302030c12131203090e040302012003040611131a041208040e100302100c2301060e0105030307020f010f031107121b0201230906040603 71
    0x50b01241303040d84c81d40d9440e50140f242400c100c1e2a0503503441098020415100b080c015401a251102c1e03200084040503080301082d41c1400107212000038814049840b04113119816960305808036051411440d00480060003c80c1150360b03408040940c0e48060422000041d000d2400613928202402c100040d0b80340003000c018000c3c0100104580302c1c1d40441c0311402c1f11030a080c0d03500c0140c0c41d200c211449004583c2b1003209818040090700c1041291002001541c1d803810039030030340340c940300da20b42c48403042400000c1d0022450626280458051548009018419900404601c682100103800580d0070480c4d21810b0717440b00c50510a8946a0a41601622003540110308003c41900002c00d10b454841c40d85060282140200d00000c0c0300741c00081c200f0350300b03140c2107642305c01038030b890340101d40c040001e580001d03a902c0c00c00703841c1c0040401809200390140e44440075420309052840e0f443d42c5912341d648510408005403000ca4070b40c030000d88018006a00c0018455840082840d1004401440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 483926699 1250 483925449 483925487
    0x10311010806091504060e010e1608070203070b0405030903010c050309240a020309070816050a0920210a0c030509120d0f06050409060902130e07090c03110415 70
    0xc00c02c1c1c54590449182c2d01400f010068800d6914503008540100b506410040c2e006515100200e0b054524041e401d00885041e40328102c0e1043c505030071a03001000356084e0005801c20000c2c180401d03100e4007890703000784c000d005491510b482c40000030f086510707a41440c7c0206502108210161030309020200e240782600480620044404e814001840002804503103030560102c082491000201f0001d005821440102d07880710003c0ca41d40103141143e40706544c4105054480411140158018082e04070000b400c520b410703842d040d40c181400d400100e207204640000615408210f40c021064600600c400ca60005050001c910010b05503903004012402d41e1784002504c1c514103420000b01e64204040001c005032480c0b0301240c41002c1c080d10f0744000c0e0b005090074490700610005601181865100701c030300d11404841110f103141507072001c11f460901a000150304010312540d507000741d035600f08035180c00100034480c100c5000468115030400001010710a0700c3e00c02454000b90120701011004203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 483927949 1250 483926699 483926701
    0xd051005220f090b0408040e01061706010e0102010e070308121503120307090b0a030f0509060705121902040f060201060e0408090d05070803220902281211030103110108 74
    0x1a1881d00c40c440c0000940610340d509541400701903250b2000300c1c201e034003c6a0706180d080c2402d0101c501d81040c01000d0820b03d940000003041c0d402a4aa120004942e80d0010440c0d5903110056a850100c075901c0e40c1555203a528200b1107840c00c1c400180518810340400d030f2522640b050382c50051100500e0415550a58411507483d507400140c0c0440500d000613815a890703988032011035036507055510071101c030100456404c83c01038064200030a01543d10b0701c2000302d41d0b262400039640300c1042d9140800700d4010090811503000103d2601d80c008451f4507602d8a8005c00001c500481e4000c0e03100030641c10b0440010b0201e20b0342030084100074103c080c40703d8072900303143e264501c49110741720505107d4600d058400c01003040c1071290600038515002501d4840c59268801000380c485d2641d031004000d041280840d0b203038500d03c20348021400c280c0c01a180c9c07400d060400380285511910150920160146600c01c0d01d180740a62160b00c0c900000287d03e0f94910b1415001e411145c11001e414460f8102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 483929199 1250 483927949 483927979
    0xe1002040617090304091802031b1f020c03060109060303080a02091e1f0513050307030f121b0303020a0305070c020d060f18051501080a170913020d051005 68
    0xa014000c1c4031503244031842c107403101e4110b58554400e991014100501f03240145035000045031030f400343d46000780e0944050001850542d01110304920b01c19030712070400030f11080f9010548145003000313602801154281c9080300c00082c0b421500741d02c5500700c01c5d100c00051040640c800034054114260800641c28000c10314009014580d407a05100070075804510041100c0c5c1d640c1c03903820080d90074140c540b851000000300c020500d5100c1c0389049203102c0c401c0030010741d5080010300002203d8108400201c1d2504960703609240c0c00e81200403404101111004501018881c2c0749005068840d80740143e0f0780d50360410141c02d844d8010400002d1081c200d031940e015071103402d01d040c0304a0707100710001400d06080c042e8000402d0032038482e4980601001600c0200080064064aa00c0758541030002580c0d0b2014090f540c0d40001e44010700e80311502d50380848924150b00542049030008180d8405000340c42c0e840001ca0b0091003a14030215114018008000f0780300d80d028010380300594400201d5a0700c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 483930449 1250 483929199 483929207
    0x3040602190f240518060c07060603080a2a05031b10230109020c071403030f0f12010603020a05070f02060c06040b0a0507020d1b02150d0e10020406 65
    0x907810300480504a08440030020500300800400d688001081801d00602031100351001d890310803010014607107404140700301960405100c2d06140c00c1c004120983e2000100c410a810280c02180c120303446d02c0b804000580302d1000b03401d1480142d5a00c01a5640c414151504d50303004440146030b1070382903110303130003c680d011003103030000700050f1303d0200080c0c440c01d003140c0385c4443c42080d12a0300e1315000700f007180703100188821881c1c48980d90500003180d0320358440004034842c2c0300030f501e0590b0040308100300a11010110341c0c07070400c00a060740c0c104100086119980d5116401080300080001a55506080c3c0441014054012441c0031800d0040c038080103421441411070180c00406241581d5086540c0c0c84225890a0f40c03c405031910b6041c40c0c070780719424030750a0700c420400360308010010302002e20000301500c00c91b6050384c0c2c20b00c200041e14141d43c112070340600c00b81d800c000d144403007038418900e2200600340440c00c0c040001e425001c20400e142804c040c02c00d10500703240108010002c01d580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 483931699 1250 483930449 483930463
    0x403150b2707140d0b0901050a05010c02100c020d060605031507080a1a211b0306010605180d0b061513141309121b05101107050a0c05010306060203040602 68
    0x720588082154903a56810303111654000d1944143d00800903460031500425001101d01c2101078810b6000ca980701c8017009401645030094070700284070300b001c8a0151510b66600c0446000f0360518000036003c80c1c001c00d0400c1e01165058981070340f034100030041c42c01c08100309407007481030390310040e014200f1020082c0003000142803c0034194403941e95030740006007174505901403600108884140406040301450010607121441301500815040c0000d00c910028800d240c04001005081c036030382807400c15920303034102e4148115046c4450a504a40b6107426020444150155144c02c0c001d181500401c034501d0b05c80030310030b0300d1718106200c10586c943c840e003948400d5601190a4040d14407211001c1070540e070030b004540300c00d0f5042008107002d01035001c00c5441c49071a80d541e200d546410b80f1440d02520403c04100904603807109003486651045036201100d40c00c8201040c0c2d14020407501c84a1520746d0b443c10907185030a4003a020405503806109110040410b0300181d408c1a18103d4080d407034480d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 483932949 1250 483931699 483931759
    0x1050d11040b040b0d21050316051c0203091c05090d120e06130e010b040e060108041e0605090d020105040c031e060c0e010e010e060d0e0a080403150b 66
    0x1850b8a000140d03540c443c0c1040e41500c07070141c00f040e8081018104110001e00c0154400c4130803070b14524070101c541c4241d044a01c5a0088003040c0c103031b202c0031030301190f030ba5100341301300c40707000c103002002500c00181400190f0003180c60381d009001e6100d81c49a85181c50700811030213070a02801704414251602c58080604519800140a201514001000f43e03064403074040556802036000030302d04107401d50780030840242c500810f14901d190b070729149445070a1041d400b4030700d900d10a030400200c8a621071315409034001d01c0b9813280410081501012184041c031a0000c8840607201d1042051081081110b0100c1355885e200a01c8282402c0d00e134a8500d1140e40005010b030711803001c00d8180c2c605d540105840b041e8fc0190308002010f51000b0081055030890906400a081c8800b5500190701c900501e4852401c02000645015481d620000007072000c0d00181150340180083c041c04174071070700c01420007180901045c540404000410030304640b4062040c1d4410407040c0c4d12644031281c42040c407101c0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 483934199 1250 483932949 483932951
    0x60c0d0204151e0536030102071a010b0a2f1603020f0d020904080c030c0601060f17090303062e03200c060601030c05160c05040c110303131a04110901050d1104 70
    0x400c0d05c0c002000d0104400043d00340d800041c0080810900754201c07500c600c415407040780282d0b01d5540026080c131542c0401c0000404010740100d07414510f60014501d5099900460500020400c0290a1035007084240c0b0740f10b8204901081581040c01c280742c0d422a00711a40d50500e101e503030006141d9503007d4409000e00102140f00c141c2118104115203008030110300710340a82da540c0c00000c00340b074081c10ba6400041c43c042400d800310746011011502a60614000d9821969018144440280361461040514140d6400c2d1083c001805000403040204c0791307000f242504444014105a95802118a050400411840382210130105220350004000d1030049920301c08404104d616000340c503402506245056020303410003814448050482d041502d06100620101109a50040100b03a2210454008000049001900f00b0f105254a481000400652850301146084040381220112841e204240d5180c1d02071415146860061008032481c00c841c2d030661b40c03054002094106030500032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 483935449 1250 483934199 483934267
    0x403030e130f050a0b060c06040605060102031e0316110607050a0c080c0705100e0a0b070c151214060f0d2d06060801050405060c0d0204151e05 63
    0x16034810900c0c0140500d1424144160502c1c0320000005201c00c1c4e4404035014503009129200381450350907217081d5648040034240a650b0382e11240e0181000800701c0741140010411148130744101580900a6200e404200d9201d05c0c004030507007511074160500303409201507412510071030400010b1950340103001c0d02c3d055440f4046203006503801c1035180d0b0014aa81e01c04108851821800105102114400c5943c02000c2011180641e01c55031030103940703508045940b42c24052560020001e24500d40704400e1802d505941e041109410280e8141c1c500000d80c03201410340008119000b4490701010204440c246030070300380c00085404000a001c1030050340c50813601800d1000d010b00d00079280b52a02c0001c140342002c07010100e0079146180007218024903041010544200c140300c0d480c0b240e40c0c0f10006040c5034840202041c0c6642001a00420b41a020400490308000014954100981540360754451036205c1b154500005201c030269001c10030280117100142060340074003803444a86031024901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483936699 1250 483935449 483935477
    0x50c0607140910111b06091c08040609030b0603060c0a0f1806050d05010b12131b0e0604050f07120e030f18191a0c0f0604030305180111040303 63
    0x40c05010b070b003180e10480c1860b000c1002030304200b800d010700b03201070152852080400b0040303081c0b40e03140c08003681101040c00286034600342101040b4074100c2c0740c0d080401c01d10a9640311500b5a0154001d0400036011103420410000c2001046400010881c05051545086035000d441400380d0900f06c2c0400c10443d042064440c0140c0e60324014120207040300459985483c0080c0040c0d0059920b203800f10316102c0000f032403944480580e40c6500b00350080c01001d848860b2021440c00303108005a130894040300d080109180c2d030256600c01406811348034007003032425408010072220000c7c2004c0346e130295801040100796215001c4000f00c0c2004400155080100189600d10702542c0b40d00ca092140000b808c1031000c04c205400080340004540c1c22886841c2d08125940d020b00074400c04245456120050950046160203040c180300c100c030480369070400c4010340328644201594240c0119a44034240099660a00010b13101940d01d1002480201c0d036641580a00707100740d02c006802c02c00e8420301492 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 483937949 1250 483936699 483936737
    0xc03031806070b0420030a0c060f09091406010e041406150d060906030c0b040605030a09082104060e010603110d031b030f080f010b030a051504230106050c0607 70
    0x801c29042403c1040074501445c045002c4a68000c00c0c500481080c011a00c0c43d2400040c403500311a404844020814903141c0c00360741000ca09010034040c005d43c80d00100c1c0720343c203611070248201e40c4c01001440c5070a0242c009001c800090510364008d40c149941300c1da8050314881140e40002c411748080712099041c21360b100c0c1d0350280b088100c2c646070401c40001a10180e54100c10140c90041380754500140e40d488030003200d0f108900c01c1c040441d4050000491403080356104c190aa40a255024500092124900c0d0038050201344044420070301c0b0b05110a00425101e280c1c00ca042410080001c80e00310b4170f90762042183c1c2102144140340107501c0500b01403051103100d041c1c0300380c1a07056910007070f01e07d805041105450519400a0191400200d00c03071420745400781264040d4880900e1520344078411000b03018000c110b40c0d0318510750b0841d40d15039120340c440c000d6510703c428504d040780d10030042540100a8103034040000c002c811301035408420008182c0a400280a040422a005855005c98 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 483939199 1250 483937949 483937957
    0x6040b0a0939030302210304260d0c0807090f050a09230f0106080f0124090807060c0b0a020a021f0e030406210528060302090c090109080c03031806 65
    0x198040114442c0002010340000310081700d00c0182c0c20400003070404152441045c0070444000c3d05254181541405426000e40180c4550361440c00c1c1d02e01e09800400464241c5002c80001000180c800d0200085a0b5002031454090254071084601151030900010102c030340c18003403842e40958940325164a8602040c41040c070b0140d80220036070714a0200c002590b03044003481402c020a6018001643c02c10b100140340f03050b40c294100d1040d0ad07006e0314282c4c1e001108402d44107010700003500300c0072034455420803005005241d1951010103c10483c500480716220260503a00141e006108603144c668000c2044803002005080007460300c51a22100300140c44a2041000907010024001c02c1c0380b0790145410a4006c0b0345030208801d116030080103000c4401c21580c0c0e68100d11038205440b02d41e0380301d400c45030154903071000200310542c0740d80000d03854040030350f40401000340020340108c45507004400200141085409022480b491401003512486811010301024880d9140e801d041d980b100309031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 483940449 1250 483939199 483939293
    0x9011209020405010906051002061015021e0f010c030e07050409150203010b0d0b1c12090b0f0711090127140906010e06101202090102010e0d0206040b0a09 68
    0x42c003c2d540d42c0c0442200401e076501615000c0c080c4200c034400503500005407a8024003400f241d00000c54604040303481c40f5003a101c1220218052104030b0f01504440c1d9201a00d001101c0024201003204098401e00b1140184124001e2608144c20341004040100355103040f641c0550b8081810182d507e005103000f400c1c0c0d405640c0e014804800454506a900083d090b4550310703440030004078607000100410040348030107240c0c50078041070480e80018190209021a40210708002401c0e0b034a5070440c1c0307c6608008404803040c00c000c0b6201052002c00669407826030030030380b07681c8415410040108501d41002c0c1e0b1a103121405441d41004119059000c20382400321124038408604001e5081502e4213400e1049991074001100172a1061910b00300c00307402030b0640e0b11030945d00800d01e9984c9010350030440809040d95a03400c2e8022020f0b1007800103c00008a43c0e01400702450140303040704203007001500040c9020314040c0c099000404001e508844140e942c3c00c0000030400e2505880c1500e221b0400c0307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 483941699 1250 483940449 483940451
    0xa3006140a05040c1a032e060c02040606030507021002070503160818100f031a03121e0301030f020105090307180204060e0411031b07020603070519020111090112090204 74
    0x700521481640c1c440d030b00640c03060b1400c072520f55070b503840c804001036044003580b0040400c1001c24624040455010024006183c031103810f400ca00103107180a4040b40d02603804640507000324821031400d031042e00c02500b0b207402c0c10000c07420640e100950b10b03501071b0181d9012139800070356081403101c00c0058440c0034016040301c0100200b83d180150f80c58001b6000000d000081c194950103c0c60410360a1407055444e64401002d40d603a4602240607046200c02094140c10ba01501562900c06024507800b5403000040180da64003202d501102d00c0d200c0300045283c2a00500c0180001030340c0b02d0b0080b26071502440c08a80f070b000200e0000f401e1400c00c1c0c0c0401c0c0100c0084a086000d1800b94001d0000c807001c90302d80d030f100d83c800c410034401030301c1e4800045401e8103000c10000c0c50100380c4088112401d954015018140313070460340410303c294016a10707480441c6020600040c4828140b006808203800792000f4031000703014655003840b5000704610035040c004088100265107075030768081d01100340c000304 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 483942949 1250 483941699 483941701
    0x7050706060b450a1205011e0b0f010c151b02010605240310150810170607080a180b01030210080c030106080615030f060a300614 57
    0x5144100ca600c900c02d450365124500c0c000084801480c034207050b50480d03440c40c2640300080703064190f0501e000040510b5109000400c0411001e4046064100062013100006030580345003c0100c030703181d10300144450301401c2c8103c0342096201c00c1a582c4006000703007845542c080300d910b8908103d011503c843c040381461f00032000d4040318402c114800740c0e00c5d241c00802031280c460302400b06100a144c0300c11041c908104186c40ca503075607a03000f558000d440f00107440000303460b80d1804002c030410750500d00004040500740880741c83c0034201079006022520001410036618041580c844100030550001e00c2440b4000a980d251070340c1000030064040d03410100f80710b0710307403600a40c6a0801c0c00164010025040b000f21005e0103050182e0284a03880485415a0f1074014100c1c1d16240c0284600c3d0045140700c5001034070160301002c0c40c09540410900d21040c50148140700480c515523010301c090850f01c0001d0008540c1d0b2000112254086105150021039142415070141120141c0a8215001d01c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 483944199 1250 483942949 483942959
    0xc02030a05070f0f0f0b07030302040b04140f04060e0a0b0a0b0d0501030506060102010207050319170a0207020907020c0a170304080609100c020d080105010804110a06030c020f03120f0705070606 85
    0x8140507080c0c070100c1c2c1060303c00300d07141c0351498081c00460099240101c1d120400b0b0000207103c4010b031101510924025180a890368004552500541c0c802a005103d054141c1214a0300e8000343c6010344007030303504000081c90a60b01da02da208000c2c12007190180c1e2442000044e45650759000068001c0e0b960302996220075032104402004240300640c1e0601980002c05c50661040c000ca4104640020040d4103000604a07040300c20302041104000303001c402c1d158101c43d100070540e8540b14203023141005072110040e00600161800052030702003150882c0400220a03a240c00c43d0074141c6041000351071703034031290f41170003840c42c4a00d8000580c1d43c810182009051000090f140300c01c03850041050101001d1003400787c0c3d84005094080700418180303401400294070075a0441c1d03001d03000f2010a9040311501011459140e00f075040800020340368801c40324525010080303c844040c801c030080d46400317003d16021182040291100c0344001020303000c04c400c40c1c4100705807010543c114901b0440980e0714 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 483945449 1250 483944199 483944203
    0x7140d0b25120e010b060a1107091803021606050d0902010302090d0503030414070f090509010902151306050c120c030c01180312290607150204030b010b16020904030c02030a05 77
    0x24403003038442c0c80d003029107400700c403c0103010342c51070284041c1120303052403c90340c000d0352040c4130107035800030600c01c21100003003a85482c05010114480300320b140d8059585810700908005004200c3c0070191034a460402c6480c0d4000d0848000807040100060702a42d180b00403400b078410681141d0f841000149901c0500c600800114080d910644e944440e94200301003160700c0310524400d0f00c1114144031800c1151b20310310307040385500110000c00040c0f081066400180c20020751014000c0a02010034511810380b00b620014028002c01d0412038100181840802e5440c60754240201c908100841e9a1903085000c100b6500c0c0018624028400c42032001686400110245010f41c00519505c0303400384185543e00c201c0740b030726003000b00c0302d8a0581c4101d10000e0030110301095540040081041f280030800308910300b0582c405100025a40700d196080800f13403940180c00600c1114800c120042030040302d0100c803003100d941070711002425559810140c070280c00641e03002c1d42500031b03445450100440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 483946699 1250 483945449 483945467
    0x30606010f030e251a030703050a0e0f1005010803040308090d230606040b040b0102060406110405040c0504050f0f0d060c0513080f06150f010e040f020f0c07140d0b25 73
    0xc4402c030b04c2d110350f40c4141a24003940700041c4044c00d01010004180d52910a4200c250300004c040c4010907280700d100c003100c0c689299101202c80341e400440380c00005000b6801141e0041100310002c1d418103003162542300b074034854407900700d100380c0c8010704e81402c0000004c0078030030b003410040071080728200c0782c000c4a44079001116407520580c54590b242c0090b142600c074401d41004103034002c1c00d80c0e88d81c036036915004103044031510030703045c00a101c0014a0364850252030074a0f407482c0e503020344541c900b00c107200202c0700a510a9104403001280c000181e100e1803413924801d5040140400d0b24031a0038010354441c0715403000c287e05090503000201c0c1150000a07407000f408000005c640e042d50710380010350409034810792000c1c2c1c0034000c0c8020030280e61007040788904121004000146012064980380201d174429541d40d031051402141013004482c1c140518002484044860410070708214005600300b000b805005014850150118010f080400859803c610040100d8030f40c64003038070005009105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 483947949 1250 483946699 483946753
    0xc0308010602150414150702010e0106050303190f050405030d110d2c061303060501030b0c130501050a0c0f2609060a0e0315040c05010306080606030606010f030e 71
    0x4141000025410700c00103031420710f07180d4100a00e10684966565410704010003d44208a00c11890b1342c81c100c250101c0080e0141c034042e000002c0d810b00350f16aa0342500c40c9030780702610a0b0014481200245a112042101c9040914060011228100c010307140c502844d0003081d014031850b00801e5a06802203d45a00c00918004841d00d1003250841150102c0390243c849003102045845030441c03109410a007000000018020360400e01c1e08003461844081940c01a90b8a81c0c43e08010000c1c42007030341c0103940045044901519205c00c0960102086101c1e209450400074001160040716205004840c4a01d911104203e07119185d410b0420007440f0031424140c2c0b54001c0c00e101e4418005640403240030b024041c059609244200d607080d0703100202407040d0b64160148500c0d120078002c0802c5158400d92040e03003000161410000010102e40e90360b000407045501400601080740d400191144d44031900b40b800300c055015440d01100548603089092485110740109100134080100c42c07203a04072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 483949199 1250 483947949 483947957
    0xd05070320190614070204090501020a1e0f1805120d0905010f0c0605040f0f0c03050c01030501083a0203070615121b0b0c1c0e03070603150503010203070c03 69
    0x40c4507004001c040340201c0310308a01141e542c2c80030044140a4944070814244040516050600a4001c20240d581c02d02d4110b034140d60000303180c1341d491340203040100e9002d07090741701d6045030407001e1000d440985010228014000064078007030301c0c894813003260005840080c2404060010300324a02c0e5075501c7c2046d480011a030b13506804103da5120f068085403c400a40e10700304c1d034580585686000380005001610b5401708002a200450034065042403103034030440d80303240c205103141402814101d112500c8ca0415003424010840a240014000a820014001e907007143c81005503089910421813182c00800c0c0c58410081d6200b81c021000d400710600a913030502500e601c03001c0044542c145405015812030705c03082035501107000e24120980507102064002c001da5210451201c56421819017001d403680041c580c1d440080203030b801410602c4c2d031404d188001c0403d10000907102c01c400d00076007080643d150800003200d6900420303840113010284c0219500d0602d04001040002000300543c003017 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 483950449 1250 483949199 483949253
    0x3c070b0603030319020306040f0c0906090e04021503070309021e03060610080f090a021905010e0a050a05010e06130303020d0212130501031d0115050a0f0302090a02090d050703 77
    0x1d0a010040742d1140c0003107495201c002003580542c00003500041d080f59000350350342c1d070540074a51180c07150403e4400645c8985181c40e10700039004110840c1c40d0410303c0f200c41d0900a220040e11a445425110040310160684980c0c070320000310001c3c4846500a54020001d1032112040d0442d1904003184450070740503151f07075560f00301c01d010f031400007000c04c040001e89503400605a1140c0e00166600302d200c030025640340048540009161205c00f1444100c41403035001c0822039580c2281d060082e6800668035090540e1034a400554111a1480750505210b0b9002e0344404654581003190b030400101e1011030f288640300d040095440d40c404e0509405407080c0b1344040741c07044a9a0607034980654803080303045018209001100608400c4800840c4a440100d04081c0d102081c01096021443c4d2450301c66824a0441000010800d0350f001940b040c4000c1d10620143e05d40528156004040c110050703920440340c40802d03081c0c85100c1c00a0500e025034a8044200b2914003104541c0301c412014203844 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 483951699 1250 483950449 483950461
    0xf0c02030f090f0d05010606120507020c0d0201081810060905070810061808011b0e0a06050409020f040e040b370c1b03110d0c02063c070b 61
    0x140703128040e22840100018803070315007145080c261440d25a240071340344822943c060341d5410300396111030308040041038204030720344240001c920a03958000f549100914035508440302040480c000340d1006170420050100041c205071030745c00c200d0f901090b103030112a01159517250300402400c05028039107000d420400031881952241c0c04280c010320200941400032841c0290030790b40d8102c003a0360b074405e41c42407080003d0240020b1041a00c07000a0024540c1d2000c3e110380003d00310221080c480e4803402d03194505120f03850b4450155801c2c0c03000184016582c07c0c1201301d048d094041d03503100d403519050001c10001080b08100540e4061051803c255004805114030000c1d040940790303100304900da824207400703081305082e0404090b4940606200c0310421242c00c40c2e0035070007aa10b60a9012620702e07900d06140704410405800307481c64925242c510342c0a0344c0d0000b010382c441c40b1400d1f41d14140b941304601d50040f24910406400807884001c0300c005041100b88582c5801038141076443c02825400901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 483952949 1250 483951699 483951703
    0x606100801030213180c06080411010f0203121504050c0a03060f0302061206040f05090c090c0306091b0c0601090b030d0806030618010605031501030b070e010c08160b0103060f0c02 79
    0x10507a54001d1001e20351003220304d43c02d0028001c040d51446401d8036041d0300310100d040107003040040d2581e565501c8651a01f07041880d44005181617040c104120b50ba6071004203075011003070320052200841da00c012525003180c02c0106030010000150301034546001c2c0300c1e20038000401000300000c10b407010702c01d00d50345110040c8111880e2201940182c4104005000c210001d01200d40c04103002f0000504450486944000c03104101c3d000d903013a61040302c00d03201c14601030106a900c1861004841d11350b1402101045403440701070000f44142d488000c51040301c0b001c0340d066400d04c282035021542c0030761f910300101c80904401c0c0720050180c011241581191032040403960301c105030140040c450307070b22210b40c004070f000b0000b800032146550f158800300300d0f5038080c0b1041041b1400c52103581c0c0c480d411410480002c0c0c0303000d4142424881c00688840c01a6084400380842c281c01486c260340740c1b400c009502c07100c0c070755080000740002c0c1080004400c0010950000c0352a80c11004200a030308000d681c10f036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 483954199 1250 483952949 483952951
    0x30203150712060311040506040f060306020307030e1c0e060c01050a0524150c10111b060f0604020304031205040f122609031e0304030305060a030201050a0f09120506061008 76
    0x20780700c0c900003000300038903042c6508981c0d0420710150001501020500ae10800c0764100d4100701d03a2a60000f040c014440c0d4940034002d10303007406401620342c145102c1034424441409440850a0203e20514038a040e80c0e064140c0b5071240c0d80344000d01107441c2c054285801047d046400340500d4048151101800500c903602c0b0b900300c003018045181440d80c03c1d00c15082a081500c074a40244280071b00c1400320076203401008070741d051820240e600e41401111802e500302c03e4800095544d441141003204420841d500c6607000107068a0040c3e03682c40c0c43c10700b101c54100c1b40e4403641c00c15040000380000c014143d00e40804660040d5051200d5420f18130713003118040003c015040d800d0f001c242461940380b68900581e40c00000c04812285041c425944564040302c0d440e04000c0c0c2c8050200400082c15094014158440011148115428250f90001e022802500d052400b0802c903c0d46030079800d8018502c402c00f5101c3c801501c03000070140c1c90041d54480c81254498050005a030015020034028017940d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 483955449 1250 483954199 483954203
    0x50c15122e1e1811271e0105070809061207020d080c09012102040302031603050c03031606020d0902060309010923070e040c120b180c130905070302031507120603 71
    0x1212880c0580303ca840c0180c07000c120b450708500d404001ca92540180703070000c600503005824400005100e4001003001c140c1460a81000c003091100c4440916030340281200c050980c4041030b1034889242d8030100350030340a045490032040c0348035414482e12741c1d000140081d0303011080d81c2d00c00580d51180561001c502443c03c0042c041035074600d201111038050306034510703540078150006003007030364036000a0f241040300004092080c4a80800748203100017401480b10550040c0c00652920003040c158813203c00c0300440103800c030755010605129140c43c0d5085605c04c80e0700148001e44900b07040321458003c040c0500b0807120016080180401c203c04403100d41810548400030308a150f00d0459064100d00006104651803201c0d58004142e548005012103a00c0d4000d01c941e60252030075500c12035826101d02d112404640c0040b260400303a5031032446171403c0038854000400c1d000880e20b051850201240c00096043c05809587d4200c09001c80c1201d12684540d501c5080462180701b1641c229102c2e8000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 483956699 1250 483955449 483955469
    0x1603050705060d2007030f11060f0a14071e080f0406090c0e0c09090106021603020f010306030203030309030903060f0106050708031918050c15122e1e 66
    0x81001980b801d40c000d08440546518003040483c9407606130142c08450000c4070300759060200301031050561007096a1050001402e00030442650303000c0056480c8001030030351182c00b40c0800092902d01560300032004008540101c2e0006080c500c80180c00d00c1a5450710b4080d41c0e041031200c0c0c080c05d2041c0e0f0083d004d07281c10511103010782c5551b21400f01410300d245080e02e040459203000180f021104003110710074401003440741d4403652079104106564806902c2074003150310092010381503046032020103007161780c100c8143d402c00c080400107074040c003020360019515010200070440702c0780010004240006084090365055618141c420135121400c0c0100780c00510103210203c0001d010390000e64018a45544884800e00c02041c0c01003074440d0101c4d40c4805060b10051035040190800c000c503c241c81c102d800306410003011120b80200d001d0307440100048822000400c1c0002264403254188090320314200d07a81d140e1580d0383d41070349e4015103e80d020b0f028071144006a4482c0418848040e2030303004003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 483957949 1250 483956699 483956713
    0x3140909010e040309051f031b020c130b030307060608060108030a1713080a03020c16050d06050c070204090b09060108150f180601090e061e010501260703020705160305 74
    0xc4110b0100300018002c5042c0403002d03401040781d66414405003c6001c840c03600c0044084803281c0202501c0010802c2c50203000d6a50070480e07400e80108552000e132005845220b411842d00302000b000d022020010340d010700000440c0410b000040d0004025a4910b0341222a166600e10b440c03903070303131107004410000604525130714407070080c840760300310740000c0307083e4030026158455198a011a841312400c2c0b000300e94001808541030740203000d440e072a40c0040d00318400c85442e08003c10b404d00004140142140e07955800070303003102102000d44d03001e9a00a40708201b032001da460220f40c1400280c5000f440c51041c000005818540044d5140c3d14031811100010740703850304107540c800a9005003044000c0e140c04a902c1940100410060780204204c010101d150000d20040d10f06019016003d0a004a00000d518110055103110541190020310340319821442e0600101c140e0a14401c0596400c1c10003014802c04030f1303240e000707081d407640583e00362015a0b02d80c01c24040b1502c2a84002011078100706 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 483959199 1250 483957949 483957959
    0x311030a08120c0f1b0105070e060a03270501020703111b0f0409050f030a140403020306010e061c080a1b020306010306020901110f070e0108280f08070b01030314090901 74
    0x15800c070f604002c40480003810400fa140011201d500b00d0041c86041c0003407501c01d81c905220901899820080c04d050440503070840c5400308000380300b0600c1c00340600d91104a181001187c0079001c058240000901c6140ca48580c50203038080e51062100f03030b00040c2941c09034a14007001140d84184801c503000c4010f032180344030060103800d41428168550140d550506600031910901020380c42283e590301440c0d6940120b1005030541c050307080d038507140301414041480140c0340043d299064814200c004a560358038400020800d503035611000400c000b68407284000c00019401230000050176490f00f05500b000c03d100100452034150003e0f40c560b20070001040410941c0c1d0092002800624011140c00b070940501450300580c000100c4c40361384100300c1000f0001c01c03030b07154901602e8100c0180001d1042c0744041c130007922090340c03044040389504000e1303410411300c1c44154400a60100429854122605100415800134841075000c40c0030908641544020a001c48a03e40c0e401020128264240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 483960449 1250 483959199 483959227
    0x303010f05040908090405040606050a06050c031c061a0a0807110d12020405060f09030139180e07110d0203040b07060f02040806040515070e10030914070311030a08 72
    0x840c0f42541d0701d9030200581d0700644c44a0107600c2c481d45c00303400c0c00704d116860401400b035840089ea00020801c80c06000260030050044101d8002480c020000529682452404001001c082d031003031486500321314207141c1100030036000d8416060251105981540c6a5000796089122640015140d4000e00e03d440005e501600c080c0c81a180d0582c00141055180c0e004070388558840401842ca4500105441003946800d0207101e0030100b6610070300010b40a1034246080401a0454801c0009000040341c4c0c1850b205401003030500344800c1044d0901561034a1030880014180c03019000180070443d00d21b031041c0000b409000031840c0e68015440c1c1850040c10203240e4100c1c000448440781c985089089070501400640060081c0b9000740047d030806241003450245c07009117038250181c0c41800c10140c00c4c2c100301007d100c0c140a07552400070a00b101422001030004450040007414014007803144144002900300903241b00e24400c14000910204066503021000c0009110b181c08001c0441101c0318 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 483961699 1250 483960449 483960461
    0x7050319270605030403110c09090a020f0411030105360414060103051b010509040f021312050d030f0b0d0b07090504020301030b13210206040b160c0b0915040c030b090303010f0504 79
    0x40b000680d444234000c07d00040000b00243e49520302c2c0d5020300c21103c1580b401e203000c0410450111010000760801244004103070005214840c46030560b161002c0c1e104030f4444815084403808002c1004080402e021200b11758030503102520001408020b01ea003048000450505894010000340f00d604900514460000401250141040804c0c8044a1f803900d81e8020810300c1c00d03000d040903071038914440c44c040390a052680b0030342030105120401070211381c0c0810080c03040f4119103008682d0400c4d18001602030b06080110941102016038440d007804100040c0c1c80c010038041e642c2c4440560f40d0810001640401c0c00060f12201076400030500002c464581540540d00c900580c0d55201070041c0c001580e214803940290241c0c000904110401100c2c141c4998081c2040002c2c06d21044200001000e400061710b004019864640110304003100401c003c101d00282c2402403842481c0c203140c07210301d03189148003c50300410560046002ea410110030740e41a01c0100003c3c0b80c1c1149494200000303049 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 483962949 1250 483961699 483961727
    0x60503040b04200d20090c0a080411060c0c010207050402090f040c090812130512060412030b0613080105060414070f05070611090307210807050319270605030403 71
    0x1e04825075a607207695484105045c000d1105885000c0c08034440c0050100903081c00e4440c88540c01040140c04020040c1c44500c4840d2910560356500ca00d44410500c0e24105003c0d80194041243c183d5000002807100d490002a0709965090b5138900500060380120001282e0141d88001030400b941440d038041e40144420345001010141d80300c2c050740c10b0800a9002d1440401d0000381400b007402d407000710200900d010749035010f10702c1c115000107440340c00c0075000034920541a40e19000032442078010400c9824014034556850f1020b0020079412131031840b44003c07550809000511915040c0b04650f4505c1242188100b25034440e1022181c80d01038560140070b102d018070a10001c180103102d08110201c40d40c5501d40e4416125003054034018441d40a021207914003034984020b141043d4050070980d070301c00222a1078080c41c0c80c0032401c5006900342c06c4c212120014041c0c0d1075a42c080400c209071000c13500c0316280040f5500b04100750b20000e0007480003045080001c140024804d51304208424 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 483964199 1250 483962949 483962993
    0x1d0607051605101202161e0303141009021810030606120902100f170f0129160f080304030504030218070906110c090702060702160e0601050c0a0803010b1201060503040b04 75
    0x40e640f95102c7d20302c45c03154080c6010b0b0b01c1c40c5049039000c050301881648100c400011510300f081c503044480d04a000c40718007481d034500b071700800e001208074000c400b25100b421000b40801c5090240000c000d0091003144140f01c005040da07078058121031403501c200190303141c000c0e00c0d0415205c012142940c0c0e114900c0d1900d03080001c0100c0803440c0024440c2c071755001d03103022020a0000d500d801c080102c140707421303055a00884440103440594492180c2141c40495101da60b02011050500f00461180000380010300f80b45e00000c00c0104166004006005991080b43d50398155907201000d03d000b248202d4690740441c200c00c0e000e10446004418003540150000220b80a150340940481c0204c802038a40002580c4144140b2106c19018003c0300300034120400544d555500d040103c400b104009892039040c048001402e00594000b4490f000c40301d41c200c1681541c95075101034015041d0302c2014003504086100d0f00210700b02e44240308980c00395400480c40b8079641c941e82c440d0030101e80001d0350840d100b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 483965449 1250 483964199 483964237
    0x1030507120603081c02090a0312020307020604180c11070b0306041b031406030309010c080705030c031210060c150e0c030a08070203100c0c031d0607051605101202 72
    0x101040d02810700079602c1384403e90780381c600222003440002216110b05100e03c0c010f0000703584644030511070324206c9800c0003100b03200c4c071800042a4114400c4505c040d4021100089c0400d4042c815a0a54002071540a0410040c1c58141c400c8415400503a031110f00c0d9001500c04000b907400000241d0b8202c07100500c00078050454100c103003e070b607403c2d51010340480c1c2c448a0f03900c51440c1415426901c034105a010b145003a03c5400020902818080c008108180100752a018400c0810545121700003510481c1c0d5600e464501110030b440e0200c0d02d940740303103402400204080348604d0068641550101600b4912409002c3c0c2c000a494680d0860321a44141c0c1c1e581d03003030343c0e41c00c0180382e103d02d02038440c01d5642e8000d40181406c0c2400c0c07544a03185d16040070109881d182c1d225020b6441250140ba1101ca21840b0004101e4044d50454001d1380c03142c0003168a03400d110020501607584823601c900031141c540d43c0c0040c01203c0c0503035010702c004500710040840075012590000d0002005c001046100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 483966699 1250 483965449 483965477
    0x2303160e010e040e0a0506151804081b07081c0822061b08090316030503070306030f15050a0510140a09050f011703030103150c1b0b0907060302031501030507 69
    0x1104d00303114207040e40750302100301a8144401030083c0b540010000601021481703140303021138080e51070b24243d14030000141001030140008d100580700e184c48140f40556001c0401c032082e50355002d843c001d13000103004500a10b16401c041043c00d1901e206140c5071580c5580d1042005a25180e80d81020054682086200000101140f281010710480c55144040020389948014424000104055007a90080003108002481111000700b90356041c41d0680d9a0f5030341d0034048000d0401540020581000c20140100704104032144c203035410343c1c01204000301d43da81009402595815107060252420402051007003801d040116800f80d80050b1655404580d950031010890300d04450707a0a01da9864001030205502840c40804100603010003541194190344800000702000d07450b40d802a660780041301c1400713004550400e00c000380c481e02c0061441c141c0c1840c80309050111070310707032640c010844082142d902034402d880c0100040c0d406035100d0f10186005400502014202c101441400480c1e611 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 483967949 1250 483966699 483966701
    0x16140c0a0803040801290d0c211502030708040312090c080f070b27121c110a050705040207050708030304050106140d0b060d140d2303160e010e04 64
    0x4001c10101004580c0c580c07808490f1402c688041d10710b1452100620050740d11061500060300c01094119104032a105441c82d14013101d50280d880a140440700e075030000304030450302404408182c041c0318035602c1a40320008070310492200316000404691341c1d03400710f000f19100f5802c0c3d5844003211100003174424210780300c00b95001c0c61a480190140c3c400c0f1500440708a040c0034005c020203076201000e041200c011b55408100f501d4800c050384040840441c10310b2a50380c0540600f4072407120f010340c0d00081d00c6202c1416021451605a808102c102c1c0811011143c00505075240c580c005010f07065840c1002c0c2000080e5200301e4060ba4030b0700c0b80800114004601b03000642c001c43c0318000026450f460a40c00506ca00281c590107032194041449200110350a0000b00c1c0e40100204c5e1350403e41901450280c0f807480074500000740c0352095100710ba0425411290060495002c008180e2261500340c00100e0b4910003114400f400b952440384250242d0300841450500c61414107184c400c400042001c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 483969199 1250 483967949 483967969
    0x30b13061e15120b0a111b010902010314060112020c01060312080106110606010507030302090a030b0705130503071d0403230301211e06090803090a02030601090216140c 74
    0x448180d45002c20741e0700e00081e1001100602004804003694140c540b100100d6800040698002c940c84007000e2249035185001c035007500c951407020441442e080d05200c1d00030700c682103049000c030f4903106c00840c80b807003c3c50782207200300c00c1651041403101c401929507000e50042c10103000340d0740d25900e021000a070300b000701c1441030810b5580c0404d103601d000030084c03034002c22081442c8150401414801284d07400000c17176807440d400d800d016aa90b9001c40c04500441071036071001c0c0420800000f40b11006601c000100b00c11001601503094850b01c2d0700405840e1140391141101d8811800407010f110b100c070541c1d860340f10b070090a00d40181c04059503032030120080c1080740380f9003000010052000307400820054100c0305000e4004070082c802540c828100a000d0700c6201100f0b04801400b50400005822142c9156170056000d901c0f82800070403160b0715a1148002c13403190043d6800032507208464404d0300c030340d40d400041c5c032005903045840d00384640c808621243c6d070500036205c03990310603142d00d540b40d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 483970449 1250 483969199 483969251
    0x15090604021e07050c0310050105010c120c170306040c05040503060406090215030f0403090e0702060f09070807080f0c060315130e0102031302040518060a1104180c18030b1306 77
    0x340171031440c48810903080060307000310050264036000040c03080b6640003102206050303026990f4032070a42d00c1e00043e521401615070003010a10802d2110320041040e2000d940104825030713050002510120301611a405580079190305640810700060104200341c00a01c0ca050000d0302c14040c3c0e2407080910803080d80100c03076510400041000b803101305039000c0d880c400101103130362943c0c55030b0800d40c00003500c5540c082d08080050b1803a10201d00004828001c0a00070501901101c6926035900340841d11000c00500c601c2103401040d41c0e0458500b41281101c0c071400062215070221000d040421061200032802010600d41d5075800081030a402d10040d4003888080c03031900d500704c0141c030401090310401000815001c4601c1c0d10008080e0b070000f040e035003111040d140400c080660b4541c010850013070364055a03003020014051020040700d83c0c030080005c0343e0341c0d45440c65188080e02c6800b15020071322008101d50305410000b0080d400304880b0042e428801c2a000c51110594034404911501d80000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 483971699 1250 483970449 483970453
    0x210703020703120212190b0316090f0510030624060c060c021b06031b13090c02030a0c020f03120d060f0812030f0709091505040515090604021e0705 65
    0x80000b49a0000d4100c0352090000740d0130f601e0410b4401041d0240c1c40c5c0034001c03110340300c41d00521031402c030303a00d800218043c00301030103e88404118680054165810307106c0c81c60480e24005012011015900443d84500d41800d0307010411403540c0d482c18010804028582c0c1c02030401d001d100c2401c9056070544000f441c05546010a41e0902c0c1050303c00c80790110814070549d4070002107840b0640343d0445000349000c044400d1500c0790740b90688071000000203045c1446440b8002a84541c45144050726010703196500002c01c590011500c003a60340380300342d61400002c03526080c1000c006140c21684d911881401800703807041c05104881a81c21904181505c0704181d880c0c035024044040082c40d2600201044801800301049840e45800c052001400010f100808600000c00b03039030141d060040103000d00300e010800071004052407144490580940c511860814011410020400441d030b02c915000812000c1035813200000c1000030751010103003004094010b1001f46441c0b030980041d0040300e0160b80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 483972949 1250 483971699 483971707
    0x1090c1203023909040321020d020d020a120915020309033703140a20030f06040e0307030f08090c03070306020409060509010b0406081e1003020f0d0b0a0221070302 72
    0x49283d94815080101400341040754100404264401d800709500200241c0850040d012400560007a10418003203496030307800061000f004480f00c2c1d00404043d2002d0350380c200c943d400100504141d50162002600303041c0c815800c03601a0409500541c1c00188500c1100d01e00109003001001240b0411503010420055021803864801140c0340035032511020b2a042020483c40d080900031403074080c0145a10681e0386031200079210303402c590030840703148222007282c5924166030403059003802102e040340558240f103155900d445001090320046541501c401c84040d5242d481204c0341c00000f0701035003261040c0b0130301c070f1a00e803001d2001001440c000e441c0540e0710341c104219102644e0316680020301886020b8010000074151400351010b680c1d541c6000412a00c50411251551000d10415140c0402d5002400000c0600481480840340300f40d44101c0c00030441000c203c0703441800b000103403000b0801740008500c0300c20b41c0d0003442e80c44e00481d140c01010035040d141102f4600c0498401021942c001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 483974199 1250 483972949 483973033
    0xe0712150e010b09090c0c0a05070306230c0a0e01091206020c011410030f0201090e09030d110319110409052809020f010f12051302040e01090c120302 66
    0x5a10301418610103e54640407401d000700e102d66000900e0310306131034000f01d01001c14402c00d100c1180c140c0c0e04882101c90303198880c01d109000700003d0444040324210b08884034020700c11880c0052199410416940c201043d0540681d4000e9040b00c00d0703810480c580c0380101c0c96898006a2003481d81c041c25005031100c0c03090a10303a0071036940b8191103000d20403c0e000c12183c4014032400030192540010007882501070f901c01a11100f03c01e40045804603005402c001c401400080134000b5040c4140040c030105200000e021164802070b9041c515890510b00000014560f58001088010744032490383e02d401e0307944608400312002503840700c40303181240c808000d64264801c90195209460300c01042405150b40c006a0135110400c00c1e641071018540d0583d44203030140c100d15004540d40c0c503043c0142e10341141402596048100200d215501d0080c0342c00042c04148a030214181c2c0c008a0310b408181040d4200440c40e44c140400c0341188204d02c1d00f144c003a485443c400700340012526044610100c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 483975449 1250 483974199 483974219
    0x40e16270e10051509030f072909030715120c0516020a0b0a0203220b030403080603030d0e0718061208160f0c1418060415080a0f210503010e071215 65
    0x1f07801050703895222100c00d05c07040c8084115192240208804c1d291080c00b0107401031035501a4404e1203600d400380882c0020864500ea00c1801211029aa82000040d80201c940100c03040612540000f4400740550000448200403070340300d241c00144a035055558401d0248201d130300070414403006802c0401c204c150310304802c0311840c0517084810801c0b011810080b044655000041002e4208201d001c082006030f203041c0102d812011144005200440c1c0c0e01072a61f80e41d0030140f040552540b0100340c5218566400e111302401c0d00c03083e12072441e0050b02c0d42c072900899080541110640c0c110102032100203a44880c001080034072030801c1c03031045407410b000c500c00c417804c090318a40142080e004032071004180300a031a0707105004842c0003030307190f0095095950388000340d0072240b094860745004000b406110b084e078502c43c510410703182c14484080c8403035040e050048850740340407500c184014410130821000d0b080d03000300249002c99071101c0742d4901c0415250100f00144281c0110801485100c1c49 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 483976699 1250 483975449 483975463
    0x902030733020c130e061006091512052d010311010305153106080f070b121f0e071706030a0305030903040e16270e1005150903 56
    0x144402280c1d41c4180001d019440da0480012140302c0c884c103401201c40010540c1c04281000700150854505207481444034040d80d505000e2400405c9081500041c07001502c100041c00c26071302d6a400b05082543c50030f19020b09400b62078a00c505030f26030301403240b13040610300782002840c6000701c2c2c042030f51460034041c040d4400c40c82000d040506060800c04c0e041b4101e404400020b43c01d4a200103501ca01940301d107108400e520030340300300508150440e5020b01d6143c002c28107541e031000607a0741040c12030b0300c032558500e06481000d00860003440402006070030b81c10b906d60301070510342d844240c0c1074001c002c01c1503054442d004401012450703c180b10300031354800150309151000d102400300504000002942c1c6600420006040260002c0002c1000b1814410307100103102c080e400495501300300a07a41040000940c904c0c0006880c0030000b0101c440c3c02c401505c1d96201c161491940718100064401034040c014001103800898400002d441e03201c011404c2865404400000d8944059804140c28112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 483977949 1250 483976699 483976769
    0x90609060315140102071e0e060a0e1614070602040801050f2809061a1201050103080306060a031d0115050a030206040b03040c1a0d06080607080a0c0309020307 70
    0x3141c0b4000e1000e05401000b03000903a82d60020f00c800b0040c0c2240100e140040c2500001c460603441f040c8101101860300f289030554002c1c010b209403640d503c00602c850382401c5e110b40c1417500003040102e480688907510424400200d0710b021364410031020307605c11850348081030480e095940002c04100a081c00e110303050700101c4d41c03c4c1c0d511981c1420700680c400303080c5c2000090405902400001001800c661100d2a03c0350302c048240b14044000c2d102c85d0150303c00c0c00c01c6a008003107201402141100600c2840e041e40d034814412070554a90740240211500007034421801c3c103035604220030000207252046030704602500004280003042071089c2003040400d134000c40c004c1c03900303203402e00041c1e68620903641611007110025403240d6035410700c00030f4410a03602038141d00c800d114064500300309900044c4030f4144132504c203000d030302ea40d21410750f40d4100449901c80014102c401013810846c45410030b24000c0300074940842c83d501340307400103424480b01e6840100c0c0f162050301d030b000c4000141080389503451 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 483979199 1250 483977949 483977951
    0x103030e01020309101214040b0109050106050304051c140c0d020f01060e1306092001140a1b08130b07110607030903080d0204030f060b011e0c0825030906090603 71
    0x150088020940c905d52400d106418012030b070104030b10f6000298040400036a4108441c0403c3c14130341405071584a00703000700450b00b428840080f500a00800450740110360000080c500e5032407401080060000d005030b00c40400401d00d90f201c54112000005e4601c401104018204001c48200f020b07241104600322908a42d06101c410800c05078841d202c0c0341e00c008401c407125038074030031860110300802800c0001450031084190100c1608001c5040300301c891001c1e29a140d0020031007401d00710a019180e1800001000341c00200741c0d050903a03007000880d03071048403001d00385a15040000348005883e000a1b1540170041825821b010ba800c485207801503069500c0c03494000551001013811145000c007906c041c20005602e2441d08259046030001c0d900222080c00109481c0b5000300503129281055001076020310b01a07602c0503620035159216085070b01c031803107000d00c180d54a44094115228007440c003c42c5051480e803510403101107402840c402da56105105003010742c040c012070081d0304440101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 483980449 1250 483979199 483979207
    0x4050106020d020a3203180103060f261e0606090f1314010c03020702010e0405010e060f010c0b010b04050a32030c100306080f030c0a060c0c0f0b0103030e010203 71
    0x1543c0204802c03003425044449205c0c3c2a045041c6000c3c000e66044039000174601040042203007142c080090950f00e4151070f0074510071031001004400307454550185a92450003540100a21801001c10f9203520142640b01c111000d400c411031800c0c4090b0070307503907010320209500c0b0f040300d41c1d0144500f6600000850f01c143c9541401d590060540f20020030310034000c808491036000b8000c0602c000014101258001d0101050107500140070b9007040a00724042020500f91104074a4a13000d80b505a5004440000940c0d980004020105031180d04540c140040e8980080200e410900100d001e0460481c4150741c452900c0c0c180301c50900c407948a6141c0103a42c61410950003a2022a06c03064510042e0140201c2d034110000303420007021000050780f089001410202a5801d070700450202c5d00b03003005176880c0b520640c249545a114201f015125900800d0083e8005241507000b120205220318101d00441d6080d0303201c181840d14048151000b62803080100109a030141007000405420b102441c14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 483981699 1250 483980449 483980473
    0xd0804050f030f010f06050f270606120a0203011511060411150c0105180705010e0904050c030d050c0601050a140d03140a0c1b0b120a0609020c0c0405010602 69
    0x11405580520341c4108050142104076940030071400d0b80d00c4035003c008000c00301c0032820074002450188101e9000300211030b14481d0070b2820035120b0610b02040d0603c01d14440348040420a480c000514069014106004080e0035203d84401184503040407140140d495061040b07140c0c0d05c0a0b0a010b800400408140765402d00a0208142d80c2243d4400e0042c00d000d02e0100003d110401102142410b01034041000340381c00030b0540289000301c40d00a098501c14903100c2626454403503d00036180466031010107205039040400406a0250040054072003019840300004d003007124850080002032804100c00e5442c4d9401d200c00c900402003180c130031014620f0310200d02003801480142d03902c034660390a01e400a0500034400c00e400f11a5030340d82142c1d100d4511101501e0b520101c0c8d400d99004010506400d6460044d038407410030b0b15859103074a030a000c111001d100c1030f40c400a08603036000703449500c005008081800031305484816107002e00a6100004103100886d001640511308550000d080140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 483982949 1250 483981699 483981713
    0x706090306180503040b16120816020609071403010b0301090f0c0f0e040609050a0605010b0703021c08010506070c03170309010e011e0b0a080706050a08070c0203030f03130204060b030a06050d 84
    0x3c1105c00c1086015113800106554050049204801503c103039188c4802c0440b16070300600d843d11070784070804001010800c50034201c0e0b54440c00c494000c0c0c0d990281005000800101502c001c1c00c3d1401000801c402c074400c0046401c0d1070801c18200d0f171410314050740c02d082280c0c41c0c1d03280e0060700703481c00e2760f440c4140b801803e208107110250001d01102d9a46080390306000044c0400708409800c07200c240102d50f521a2056a194400d20054005010780f040e064055400c4030030684082800f42d41d0000241d08020400c00c295000306003c58240b282c0b040c00000140d84100c0c580c8184100d400c14548a03d0701e02c215600756000304041000c142d141030200c408000c0c1d110395445001c402117100081216500010940d40942500000540d20400000040c000c3d0b00400506a036115950781c015141c440200599499400c1c2ea0000c0d407603001402903040e00400e980c082d43d07201489108280c119106500031808840c941e4225800c145000010485103d0041c010344c00107100c1581d01c0003101c4001d17265a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 483984199 1250 483982949 483982957
    0x2090603070f050c0a0b19050105210a06050f07030b01020c0112020d2a1b081606060e04030903050c03070f1a0708030907150e06070b180706090306180503 68
    0x79007440450740803000352070301c10300580d40302244030012a00d00b03403600e0030102d605d8581212021100c078002c840c20591103c541c020f185c101c81c00508041080d0030280710245145500001d02205ca11500314840081600341c0107150043d40c07410450302d07850525a9009090b96411100d480c1035500c03a2082c41040d90f480210090240b102c1d24006813109030711a09240038001d03110340b504104e1284404090740048584019a038141181c880352a1000703001c81d594401d10710b207180a441a101449983c0c1203c4c0b0301351082d41d4546c411032000400c10386401000c40d42c03a070b080d1070a60000c1c80c0d05209000b00001006003651f007404c21801410450300d07003208180c840e042030042c403003035141e600d202c221030f5000d4000b41c4e0480365112295a0300c9203045003030f0680c0c500d010300c5284015540411103500c82e50240c001100100c4003d41903d151146903115040c41c12000382035000740c50074118060700c1c40141070140101401b8195940c20785149181000010388505105a0700d2017940d84400c1c1e40007070f90020446d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 483985449 1250 483984199 483984211
    0xc0603090c04090c050607150e0111030f090709050124110c0d0203032a010c0302070b0a05101a0a0801080609031210033c02010905210102040e061302090603 69
    0x46400b0003546404c001502495210310303085100070a2110400c80e401c2000700d45501c3c0c0d002d040140b44078540c1100d099810b0821100c00c00b80003000412107221000141c0c40d4042904011500e000d40e488000100b2500d0982c0510b00207084c0703a001c0083c1140c89501842070704514079060b00c100c028094040d40b40c824141045100e07042c2003074043d0842d00e050041d074044601d0603101044403c0414440700c0c2d91520010001e090703520703001504022501070320946074442d8001c940c500059450f03070401c0005100107001d003100700da030744100050394071000386100b40d400c02c2800a05441e044d142a000d425031206811075545500b14604100d41d9072000030555001040c100d050440079109c044a1600c01e01c4a41c04c0580102c0c5004c2c4a90a2840f4801e456110030203115022882c080c0d043c00c0c00400c0c2800600020700003400030345c04000034038003c04801081c0e1880306418169210305642142260301c41c0d4002c030700d4444000100700c01c0c0d260449c0006200d00b04e40d071081d49407004080004015100c02862 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 483986699 1250 483985449 483985451
    0x8011206060810051603020c1222060e0117040203120a140c01060501080903120c03090c030a060e0106080312010e150d05010b030705040623121506030c0603090c04 72
    0x282414800c0d1074000d5030042c8040e070180d885003680e643d42d41e80908801c4580240003d48002540b902c0762081c821500d010081c1c10182814039031080f1451001e0b031010766890294080c00020003440403905c81b0703010041619449540034018800000b40035100780c0400e100b8025005d0b02000003503240420010b45451010b84400e9940b2010002035441c80b890080603030001e080491509038202056002c1c2e002c1c0e607002d8941441c41d5441564141d540d2088983d81c0d905400a000800c04601c1e458025641004040c0190b411040748000440e207400003401055485a8451490301d10000083c41040702401c1940c0143d0301d0004806046800c6100602c01d4000d440c1400000031001d50807204009000900141140229103050812a020304410342d4518401d00840000050710b29051082008555643d41c03080c0d042c14040144401c0e85a038100442d800c42e102c200c0e50a2490001d100b01c0295400c02c0c1202489400d25000b8107190820f0f0a0f9424020001041404031b42400003c0f00445c0c1c4d141110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 483987949 1250 483986699 483986729
    0x6090402010c120c20031009060612030c14060112030503040606030f05031c061a0f090423060d03050304020409030e150c161a0703090b030c04050f030d0801 69
    0x200488a11503521005400343c82040320300c3c00f81d160b10140040e202d5002e0700c00c901e600c1c3c12a181850310811103103038240e4560301c4214840e5000d03040e44c010b014040d019800000e41c0c5507803500e4213401c4005403c812000500038510000801c060a11500d608000c080c00404056040c5204013507580d0b9040c80c06401d210010002400700613050b0414005154480c00d0b14000c0b01d00391910940d607801c1b01000552001d40c500c0410b0600711300b03208030000c50308001d81c00d01c84603182c480800c0bc41d51101c41c005054141c03c108481151b10ba5000369030302d00134442e4440b0101425030329405c0340660050145031280402044203008286d120054a4000d60110ba0000e0840700030310741640c1100c0080c000e1500300d41d0420100c100300030800060007054130010107881040400000c4080540ca040c0580c0c15044140b42d6000c0c56594040d0240c1800c6202c0e0428035030342034540040e650150411600004240f100141c1403082c0e090000380c950800c1030641c000d019100c25900040d01c3c891050140820b8000d01c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 483989199 1250 483987949 483987953
    0x70c0b030108030301060516061e0b1503060411040f06020c03120a050f0901020a120f18050901170a0804080309040b0609030a120e040f150f0e27060f1914060904 71
    0x401c0500600e58082402c22180b10003410022b064034050740d2100c541803805c1032852913810626400c81200508440c590702d5690b859082000a1826281c0e04958100c00e01020500d14005050380c8045c02c02c540040031601d050030101481c100d45801d0b0748071801b0007840825030a40e080070699071240c03000c6d40300c10746a8540d840100d01d003000c0782c480a816540d41d5210b510640d41c114900201c0300c41c26030794030042000d075994070490020301ca00c52241c0244402004000c4c100000b0f8808a182e8001020390310020103c1c1c440751295045a0070161030b41d00300250308002c5240a1040e00d010440c01e40790142092110760000e0340f1130700720220140c0303e0000c01064400207407042c805100c1000e0003d004104d103100c894134a0004148030900c200040d4020303140031030030b04101c2000c41704480308030b0395140c0783e9503490000c0741b40c044022031501c603030070240412814140c07014081d0910480720080052a80c0c0b07040b41030720682c0b1200c03d1210142d50303d440090a6103c200b2160164001d4046d40c140c4000e403101c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 483990449 1250 483989199 483989227
    0x5071e030902150a1701090c0203120403090308040f060806010c02010e040b041e0518031603140904050702010b0f0f0a030201140c0109080406030f150e0a090503040b070c0b0301080303010605 84
    0x6843e10300ba030510009416004030741c1000c42001d481c4c200c134010118682c2c0b40c01a00048800705030101025a00038403000306944040e1006030b600500c246450640b0607500c0e92000c107960002d4110340d40170352412030140210f40e440241a98003072001d01c1c01219824803034001038010b08240000c0d502658664400074000c1d2a603800c521940d450018070148004800754001000b0402550148520a0270100c2c40e01e07551f0000060310417214041a034034001040301d80d015a00000300c10211280d581c0c0901c0701481c6a0784034400e4611074101c5800108034035080b02c0400c1030b442c0f9107100041c403481e006400b007402da848a07101501038a9082c2840030b40240c5000504426002d844245e83d070940c04c0c4420b001c01c2016400c00380c070841c1e91645040c082e5136560240203041d80c21003400400c50b0035200300300300440064014030b9600003070a42400948501d03280c48090850740140c01520700268005a178000f00304418640400074154546054203550420400540700d11042c8074407000c221003c201d42d901080030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 483991699 1250 483990449 483990469
    0x100c080f040302010b060d020d060b070804051c02030a0305180102120f0a03151205190503070b070507021206160203070b060118090501080706030605090601020a120e03011e05071e030902 82
    0x1011940c640081781f628002079440304284000741810f21600044581080c4140c2d400e1541c003c078241c1c00e1a0070b04082c801500b00c2410f400c82c50401013038420000d07850900a0765081d5010f40da406980e040e03140d008143d04103031416068110341c0300882c00c400b4174000c00203954006a1a80d5400d40e40c422200d0114003420030360800d4059038542020004401890b0f5104800c4140704400307942504240100c4c045c1131000030301d0040e10f07035001009020000303088095040c2d071103122410081d0401203207402045201000c1861010385074810030030b0041401c5208081c00340b2100700e1004500c1c000c1ea43c0d6400c02c135a40301070300d400c0c184100c40082a0070f15902c41000b5000e8022207500f00101d680d5140c81c9640c4181c6445507001003458600042007038206551400c2c445da00c10380040c22072a44907600d054800d03651064400070806c1c0752210204070b82d828007400088e550000c18042c2901441e10741c81045070809000c1006001500c8034220884100160441c03140c0e0703081c00d0000d80e220480c00898100d0380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 483992805 1106 483991699 483991721
    0x5040b061c08070c120546080f0d02040f14060304030f140d090b09010b1f0207030c0608090c0415030b130501060b0309100c080f04030201 61
    0x42010000c05183d0300c40d0b401c009882c3c1c0e0f515003c10040000c910704651980044210007200c2e0507030b00c00d10b5101c4c1d824000c0f003120740345090f10300c001050361002000014001180c542c2d0030311021005481e5a0703100400120798540f140c1c80018000d41c403501441130341c0c100d446004550b00e8200c54155030760300d0000e4540d41c99529952405c2e5440d040c1c00d03803007400b0400306640a0421014503009000c8509202c0d2003c19003070524035040140400c01041d00b0307043d0785000b44a51580e92542d500c82400724044e242482c1d00a814002241030142981015102c3c00e500c80c0001030250b4800b40f2a8072030303400310056035580324820f010001500e038003001303810492640f4078007400450b095011071a0002e0112411042c40c50303041c0d40e43c500b0342d0401d40c403443c41c516020040002100082c4100d1000440000081014001440000d040020094040e0409c1c4200000141c2054003d60224001803 = true := by decide +kernel

theorem cover : BRFrame.Cov 483812949 483992805 := by
  have h0 := BRFrame.cov_init 483812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 483812949 ≤ n) (h2 : n < 483992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
