-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:04.905786+00:00
-- url     : https://prove2.me/submissions/c0c561c5-bb45-4ead-85b3-79d54fdabfe8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 552697841 ≤ n < 552877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 552699091 1250 552697841 552697879
    0xf0703200105100e16170612120712050403023f0a051507050406180b0307080603010b060903030a0c060e0d050d0c08070c02121f0b012c 60
    0x203030420191055090400b44064a0071507040c5106484400d2803100b4643d468084060108840962010000346004244400100340b0500c842e0000000340503689035000407080e5900c1c10f40090b0422504d030400251000038004200e840c03804c0300300145030040c9054a1500090012000d200344101e801d444803c080110745002840d44103225030424040000084aa070903985503402160700b9640d6000d82800440c1035240003482a20540f001e84505091900b0a4011038410b0038140c02a541d0b50390020010600d085010003071031140c0b11aa07221501d501e882000e042c00d49000c841d5460080009000780107180d9008415a03000d030300d081c902000c0241640c1404e80142100c40c0d2441564052400c0c0c260503240e01c1001010381c9021280e01b072120402526080710980012a0524009454080c1203030040c0703000700401c09403020400c2120580820050b2490000c8004509500c01070f41c2d85014003083d50300402c806c0c01c0301c01400300c4d419803001c00803240c415a80200d41e44520800d5025411558090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 552700341 1250 552699091 552699137
    0xb1b070303090504150f0b07050c0a030b040b1801050a050105040e0706021e0705060a0e1e03060103120537020a05030f030c0d090c0e0c031b03060a120f06110f0703 72
    0x41c2190381c600d05c6d43d03600752000303095128a1080c0c4550203520b201c00007034100340c100b0100701c95100101b100740c0e590700d450700c1d0016000982524884500409400324522090103810f0180700004000a03240d4501020801152516405030404d9007100000b0040c180d004640e800e0404120003c11102e80002c1c140d0324100708694100503400640480d100074103e52105100c0c207007171019161401e11841d1120482c078501503400303c00342d06030320200041c400a070381c441840314180c41d281441414101410356440d031000004508140d076024104480c404114101184503a000d55400a0311740d008941e2a199201d02c62641c220744168800400319104942c0e003030031244010301d00c0354100070051082c6004c800681c0a449450000c20b0018003103522425004100e0b40100140a44000c003103036030006004050f08020b1580c0d510641d078110000c2c0401c08048180410382c416070021002d4400e521b0820210740c090307490010312110070300041001c00c07142ca045034001905403c040b00ea50303214100e4610207407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 552701591 1250 552700341 552700349
    0x21002180a080d0806060c1f0209090a0c0905100504052115010e070306150e0a05040603050a0210020a03080c07150e030903070801020a0e0411070c0b1b07030309050415 74
    0x16038590005102c0c6004104140c09040d02c0d80e40e0b50103501c0300c030308100e001d015001007401f4603084407480301300800c04804002c0d084502da0303c0160404682c100000c422a00c00c65a41d482980c41e0708140244035404580b4101a002c01c590a03a1080b120000c000c0060141d8001c1360300400e01c0080945481100c01c0118039508040c1c8203c40d510765881d020707010202028810003501000f1000491a160b002e07020701c40c00e80311034072900d00704184c5c0106c0844513a060750503240d4000180c148081070039100c60082c1c201450250008101500503441031281c500a000b502000b190020645d43d00004c0e407010300e0980154480c0c0314a511085181801c000d40c03000062140b4503c0d05d00f8000c92003138540031000e006a21011001d442041d81e42d90162805d0744101c85140d0000b8018880d0080146040d80c000b08200242d024040d003842c40e0703070f40e5201200d032054100820140c4003240001541c007140c0c3d0398001d00c0e01c07240080c203101480c0d81c0e00500407200e58000c640c466034440c9035100980c01d07040d18500c028 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 552702841 1250 552701591 552701599
    0x50123060403080c030703030c0c0f080d060f060309030212041410030e0a0c060206070305090705060a0203190e0a0f0503120c0c1806040f0b0d020f1201020a180503010c02100218 78
    0x1a001001c40c4c1c0c0e40d0b9072001c8012004a42480900032056010781c10f6000400d400c03030100c5503503241c6540e440700c150744130300540340741d25507102000308500c00711b088044007801660b10b0005000b0814100a442c1c80d000018045c0b5042040000b80041e2110f0703c004a025081034401550f25100d0000503800341180110108542c0f0a08072007505011900a0080c12540180c0035030709141ca5a03001142900d80440b00c00015a2010104108038203001c401001c489002d84141c1381011a000c3c80c44400c43e080041500014100c0c4120b05094038100c43c81000520644e05a840c00d140341101103a140d0840c40d00d04078450b14003181440c1017581c2406a4020710800410b00b4131b06000e0fa00d15604455016164140680c0c508075021030692210700c512019100020080c0003070144c01c0d82080081010354400e039030451501c04504591b5030090010304840e60960f221241e01c0400048070042d001030f81c1c0d0040e07119a051078005000c554000ca02b0048600080e000903030786034050301399540c45002000d650f41d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 552704091 1250 552702841 552702847
    0x150c0b0405010b0909010b0f010f02240a0b1c0602030c04080d0801080f0106050102061f150f03110414092a0306030c03010603020105270603011d070305012306040308 73
    0x10864198003c599401d4200e84024160f19000042402c0754400f010f004d421212254050126601468005020403640c5c811103c041c84c542c84403105040f40e56105175010694041882200000d5000b00f0000c1340c0140c6455004000304072015540300d0452102034909540000402c0903100074800719400b604012084407000410048000c00c42e0000340b041c41030501640006d1103620740180910070031250164010051600c031500401009403076580702c23120402d07004100090740071400031160410480e0f5120700810150808000d000d84070505144070b03c1c0c803801c00051080d400c0c422006152a08262805081c60755401c0707002e48003400c04d131550195038071040d01c11324030003004c400214031604064003520545851a400d06090702c1c03490000a000c918240152445402d100c4201ca50017501c010041461500c003002041c081d50007a0000401e60384182c0c54031000c2c403d03209050343c000c0c020303250800456140c001d40502c40ca6100348800081080c500c182e5600d0f54520065034065508480304c0c5036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 552705341 1250 552704091 552704093
    0x40618120b0709140a0303080612060717010b070c060c03030b090c070201090b0405101404050406120219060f0c0f02130506031501030f29010602010e2104150c0b04 72
    0x200c1040129000303030014a803c000030641c40020621058a41d01c041c3c03420a10501310380d001e41d0003500080c04c450304000611045110080200481130080000e52100c49030b000c1000384080d00004160009513903064100718580c0002e00311101102142d80524210f0444465071504070082c0c0700304041954080d500301c0034400a04140801040c0052003622105074881d03480c0c03108802401548201c1e54040b154614041113507029803608842c804170140100c5c9030070784400008080f2031550f0040034144900011107011800d110181414080e41001c2588a00707103802401024400c280400100700310216a0020401c2000e4003041c60305680281884410200c90441000038442140c803148079114103090700175544842480f06060381e400401100f120002070712252032402c0441040e005a0b52810100141e0780081401e00d80a0000c6a0000c10110f00f000c202c0d5142040c0c0341c50074100202d1250020703280100c0f0381c0031a004c40d0f00201e01240307a580086c40c281c9203400420400b91040c040801000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 552706591 1250 552705341 552705353
    0x1d030a0804060306060e09060f010912050c090c090a030210030221090d17040f080c1e010c031503020907030b030a03090305060a050609040f020604080a060f0b0306040804061812 78
    0x815940c40b50790800101c0c0e45d60004031504100a0b880340c0c0c010913a00086102402c010b0090404e0300b1060419100d040c1e600c410002504505d40070a071180d0b04400022200c61400002c40354101c001074101d40c1c1404503810016412045910000344515401c15001c000381d806901540d81c6c0510120905d00f140d145070040c0100c20800301d0706500d9a0140c1c840385814280948109295040303541e07040c00c81030307485541d101150980303c141519403d0050010f40042541044010110a411a400200108140c0c521829150003108490034541404c0d811205c2094061040007129011520107a141e2100c80003a8024800e981885d0f0701401001486002d15411a24413021248940c048030300c1a510f0034504812150161240b65200442d0b10100c2c0120b4902c08004072810f000401e0f0502d8956501d546510307201c04e41108460a948805420040e8011032103000c2c03a80c01d041d400b902a40c901a510340700984101d000e218140700400a0f0a0307210f03203002000c040900a03045e04070384541c1c160f007808 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 552707841 1250 552706591 552706597
    0x9110a08010509060a0618200307030902010e12030d0207081303030503100b030f060d06111b0f19030f030b1804061d10090213020d061d04020102030a1d030a08 70
    0x800002d2059002285e00b0206030f20505040301c2c22034801c40074040117106020060085001c540c8000a030b91500100100c0c0c46800075402085a41c900066403e040e00c00503180d240070b502d00034442c2c04100070806503210044119030b070581e0b601800503581c140600d40040d0a0154021150392091200c130088100350b081001180241304201c6031700341c080e41c1e80040380b055100448007034000300e07464400305215003801e400707005002d441f4080114a2441d0082c2c070310115001140d5142d084003480d002510341c11414013070340400704542d60160828801c85a02503150249a0780d00808218800c00304001e881c0c844c2d40708907001d0600506032003000381030030311100341d006d015542500c00e145000b101243c4106c445082c50700d40c01001d0041c1c0010002802e5110040244c0c80c01641c00400142410400490300d00c02030071010b20285c2d00080090034000111303140000b0f05048040384885509010250f07800005543c2c01200360b00d490140b2810902c100c017100175000003105d8042c030a00c0003240030481602d0113 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 552709091 1250 552707841 552707851
    0x504080f0607080f0709050f180a0501090f020403020a17030d0501060c02040c022415030106080109210c0206130302040c0c0b07090e0f07020313060c0b0f04021309110a080105 77
    0x42d55646480d40407800b07044d460161012000320301c01e0f0808010703509054a003010f070094010030458100e40c101807902c00003502181c1800c015555900140f01d1807200b44252400303110040421401d0074207650100e4000e8015018040070140c03d0484d81c85c00c00401c100300c031201081200c0c05e0066507550000580b103c5d0288100328400c43c1802880e10402e407002800d515a03c0c4840382300040905010148066400301510900b14504030b154104c40d96202405030f000101b40000000580b100182484141465140c039000c084134036840000c4c40c040e42c043c40d40d00744140c04480a55990700c194244828024990384001e41040c2440c62410605411582c156200341c061070202007960b4452004071a440303554060b44601c0d035074460104401e070228210036a489072aa0044030b241c10b40d144400c01c45000d050f03100a00080f1400f00c84004c00c050742c85015040804407483c065241000c0c3e00050071182c0039440507100641d110320a906201c80f241032903804034009810085a40c0e29885094040d16040750 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 552710341 1250 552709091 552709097
    0x3040c1d010504060902072402130e0f07020d081618090f0c020f1015031a01090c210507020a140a05060606091c1406070509030d2109030504080f0607 66
    0x40090b000b9900d008880380d0381c0e404070b040c4400800314600203240750701044c1100c4201d5802d2200c0c42b00120402d080a020b00300541c1c5c403035036600c3d100d0000b40c8665801042c100071500041000d0359510740141c6902d401038195542c8a500111052044500c0c40c060a410081c0d540540e100240500d00d81e840845680322580341840040980780781030381c5d01c4e03520350900f18007030741f00c052060707000b801f250b000d5104804c00310701c0a070b40e095603a00c0724030002600c03a200c10201d28841c001008009600e02c2000c244030010f0510301c000100148818407003603500d01201d4004c03602d41d40000c0c1018403d121046035984d1000421015807107045030b1b165202d100400c100e0b0075224542c0032500900c2c00a0550b0761170300004109042008000302e0b5030001d04212700c0111900d00c12127207554150ba2080c01410b00c00c42241c5e5655840c0c648141c1054a015080c400580038031407416500d650b081c0803204070000d0801c140a000c100b82185240866040c819584200814016001100c2c000c100101e4124020503840c4c3d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 552711591 1250 552710341 552710351
    0x30720120a0503030705250305090319030801032909071d0c090f121902040c0c20010e0a090f150b0304021c0602030702060423030f03040c1d010504 65
    0x521665035003200d0006041d503802400000c0b6520b10540c0285100f40b81f400c15500252900c0e130000702e400115040840c04540d011a03452035a04080020856142007443c2d01680f070035542c2ca024110407410b01001d040d41c08101e0a400311034020801280c0031005414052443d480c0800c03900340c40d680f180c0940544200301c031021800c8862080d502502900e0081000d134580101c907020082d000b2858402c5039080104107803651540001405103440c4c81c12192842003142c6003610421044500d05642002400490000c020124040402030213a0320385003821240400700c4400166445405015441d40c03140c098840801c50901d9600070007613030042c1c07035410b000c3c0c401404400c0140c5d11041c0211001c0850134000600035240c8049503075903040d9001159420100f143d2100c2e4280e920441e1008050303403015051008000074106040007032881d4050842105070f00c1c82d13145072a8402e502c2c0c00000c98030b0100100d000e01602d4a10100140016900300c510802070858140c0c0c4140240b05880c4036074a88 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 552712841 1250 552711591 552711619
    0x40507020309031c02072705070507110103050a110f07050d0903080a180b040914010501020f0a030c050c0402041e080c0a050d0f140304030b0a020c060f09030720 71
    0xa4400b5140010050034107801d5590b119000054120004011032240c00d500003800203890240030214010614001400203c4183d40300a554001d4106010040200109008070318081e0b0040e107001401d20b00030a4580f902d602c1c100c043c0400303000e00c41e000400000c0310814104141c0041507500c5c414800d80d0307c80d1101400c1540d00341c8080c40081d104030300401000400740e2050001c0e221002180840384240d0381c854894040c1d90304070342c200c0c880c00c0303a0310f1401c5c6030400d400001850043c24244018280c0c0e00c0e00c002029218201183e0007414007100813516400c0050038040c500122001a20440d2569522110380c481911482c404210b0b01c003041002081c060404629603540400c05400090554a004244a0800c2110105071540e0042c8145440024014802144104c000200441d00d55045051403004c3d410007030700e0340000314410001d181c4072a030081a1700c4d9005d08840042485036881099260075440b911600a000e90882c1c10b2400040e00102030003c5661029140b40300e2011036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 552714091 1250 552712841 552712843
    0x20f150402010c02150c0a060c020c031f0f0e030307050a0f0504061403061908030d0609050f06010c02180708150103020a0801090b0109080a0501090b1003170f09091504050702 77
    0x40e80e0190004214480b8a00541041c070358054105030400001494151003420042c00c0c0381d008841101c815072188060320f6669070400c000d41c01008103c000e0070100e14100103107480540040b4003503e019803a1514450001e015503c40c04520107140141c030341d24a03104100510303e80c0301d15100c402103003610741d4421000d44a041940c0c04c4d1140740c0c880003200146168005280c0d04000c011603809460b060303e90701c0e402110340c814002450018000d54651002c601c80034140e5040d03800c6090200e1824041040801e080c41e00c03030b90001420b0910314510046400070604000d0390324a04c003400c080d0345041c048069480280e45108680b02d07113610a04c00000b00c011004e9100c3d8030f000c2800180d000d03005111140e40c0354004d0800010505101030741c55541e07903141d4140701c0f14072004e03070f002d96468189505100082e03241540c000940700c1a81c406a040d6554040f00c440410386903415107001082071482000024122000010000d01c80c02662400d6041c0300c44490076500f4542c0110304002c045808180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 552715341 1250 552714091 552714133
    0x604030b1b04120206070c08100e06071d1228110418030e13090b1f0602030a050f0d050f2e061110020c06102c04170a020f 54
    0x20314503c0b1089224641c003003150503040a0005e45a610b182040000c185108004007c5440c0341040041500764683c50000c5c1090402840c280a01032540240700101151055201034468104e85a40c0c401180c0b050040c545100c0c600d07420001d0754010b100c40d45032003c0c40c601c200c1051140109002c108241c0301403000380c58040b0640e00302140e00300740c507100003805420072200c2048083d05800003074001c00d5143d4296921544289c1c0c202c0c0c2c112090020544d80f10107010310101e08400d11000b03035450088002d40c1c0744505a00c820400c40c0106c5c0342a4480d501c0401c4a00c10903c0340e10901050422402402981d0019243c0c1c544104d840314203080d207410086c03040306040e0401c2802582c0c85142c0b503c1544e1242403441c1c0720407103002c0d0905450f00940e071440500715040d5860002c164a15100030040e452040c80e0700002c0c0482110f12010301d401503492005081030500c01c04110b0305840740e01e480d00e02602480c9001a2281000c00c1020405900203071419042c84940201d0ba8809902d64180c100e0b09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 552716591 1250 552715341 552715349
    0x7081f1b05180609060f0c0a020306070f140a05040303140c1b010e01030b060901030908090d03030b0907021f1d06011e17190206070b07020d08010e15040e0304050604030b1b04 77
    0x41400e000000706c030301d008005080c2440020b01070b104401050780c002410180c0403035460010800700450a40349513840070b000403441c05410030b4686404140f0348090701a000740d10000b0200000720341103a07038802d0444144c900036103c030801c6581c0a505103940540486501c0b82250001c2e50944d0101219886400342c142c02c54000340160385411161001100600200103054841c402d017045031010a8854548003140d25029540001d6080244420010041005440340c011580040c00c48000310b00c20400c4050f4441004600040c014903103150700f9001501883c681364103008000c00010140c0900c1281c40c0103120112403030584036204e48180c5071417020341410458a50181103800c00c003950b18100c202e111070006040720b0802c40e0320b503110300041804941030001a0072449020030042c0c0c01c42511070240040c0c080790000351415420300745202611400f0b143c411501c2d002c10f00c103c40000c1c011100540800f41880d0399503070300c0341082c03015900281d44404004510344041c1015001c034100355400c2d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 552717841 1250 552716591 552716599
    0x60d1403190201410a0509010c0f09090504031103030a0f111e1b160504050c2506060911040f09060e01061206051305150307081f1b05180609 62
    0x5142940c180e0703200c0188090a860101219224084d414600313100c0381441a10003a0300480c40c0d10302120242d095624845207403051041081149038604e030815040421780d07182c500c2c0062160b5071070404442403500300840f140fa034003000043c00550100383e0881c0031518904603081c8440d05450520603007502c1200750000c0c00c4280e8000901001c02c84000038520340b11080007205202408000081c182410411a0b20030900146820419030030075002d140e5014a950b0007c0d41400c80006900d5128050885c0703007410700b0022580c000811010354002030140c00d04640070020841c030400c00b426980c0c01801104194641c060300021128154012441615425841c22580c2c0c0d10b815000d40d100c421a0340340340300d825212900072407641c54445110040707860301080401d06042003014a00148a1595064082e41201405001e03e8100144000b8510840c8890300d040618058041000303003520100950710502d000360b40e1400030b6020300501149034410b140f0300d04451140d0200161403160501031900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 552719091 1250 552717841 552717881
    0x3907080d0e06010f06030203060a08031c0b090f22060e010e160803040509040501110f040303032910030e060403020309030d112d1204081011030c03060d1403190201 72
    0xc1c01d111f5005141c05c06e8024206503140350b111101142103800c9802da510046000040e02c0d80904051701405800c0b14060720380c43e00e181400411a0842d8070020100481c1007030b1074925140b000b0340c01c4011071030280c21000420035500386000e05806848503444194652280891100f8080820310319003080390398880095103031500c1d220520001c050010401d4030995602c019000100c0d43e080001c02d4140e144039240c1b50b942d411340c50050201c81d0361400400e400c3d82c0101c600d040300c8410a504405448080712104280d911240d000c4016160480003400d0300d016460502040640000140403040c00c110141c03285ca0807a02005c48015000d001129020b0b40b1620a018040c2c448400381c07403003c10000039121600785881d0246240984030380518002200000d020410b00900303014116002e0070460f400c0c0300f108008451452030340006450902c000340d000001c64095035402001030130030356001d140240c1076070200f07040315184e400005114080701140303545a01d00d80e2040c811007581c500c0700400520 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 552720341 1250 552719091 552719099
    0x4050a020c120c210c030309031309021314040e0106031a06060307080708070302041502070f0603020c06041e0b0c12130210140f0f1e033907080d0e06010f 68
    0x1046104e1325013800464001c21401541203402c0c00118814201c0d60011903a030440071142107072085039a030000744460310500c4050301781c981c6c101c03481086446003020b03210040c0041002800800702003c444040f50300e040b600104110400551101041e103120070303500306a840100b23220140c07100300c98080000b1012030002e907406018184107504000035140050030140c0340c00400461940713031300311080540d0100724208000780c002c03511032001d040300d45001e50600600071941c0d59102c0010740300500c0c41600b030020900300c1240c42200b0b402c01c0d030001039091182c100040f40f60a16030109509209842d04240040c5100000324144209194050a0415041d4002c0070441d075040c910051080300b080c00300170707007000d1142e0000035140c1d0610b41c00010390344020362081840c004c810030300d01c03400c0c07040f052040001400514885a004401c2103241c03268400d0926609101e140c9a404005010040403902c5018040c2c03c4000e81a0200501010003456551041e41071b5078200c24420245c04882c3e41200380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 552721591 1250 552720341 552720373
    0x50d090b030705070f0605090c280b0d230403111504020405040c1a13150f1103090303031003020f0307030803150111062d04020d08071104050a020c120c 67
    0x4d0218002c1c04950190800c2e50f64210945406a40085060707200c84192009072074456261036809440c004000d14406e1540c8c4000c041017114072034600c03068000320308a6000380780d41d08207000030214030341c0c24080801c07044519034485000b900d090300011052000c4441540c0300180948440301e10404031607844d504e9608202c0501001072007100d440904280024040c148800c0043c0b0070b5014140c41070310380ca02c21040a03c405641e501440486030340c550500754098021080c020144031914082842d1a0701090040c514808c0617000754051000004010300c0740d6000a005013900c1c070840c0c3c950704e105081401c2650b00d40c854000030389442c2040010801d105d10415402d08440d00c10b042c843d105054500c1500d04204084030300340c0d5440034598001c0000d2015004041101311002500542c6007040d4011882d51329140d04024042030000807524103201b0080000c0c800203000070f0083c0a1454550084d8010350403000c0c1114480c032581034100700c50007829094502104190004001c0b240c8660409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 552722841 1250 552721591 552721597
    0x80c090a0e04110d060c1428020a0c0e1603021201170f010f0507030b0a0602070e19180c06020106030305030606030c0712081006110a0b070203040b070b04050d090b030705 75
    0x100c503c918212101e01d20f130b072030380c42090130140d0007110002031000410344080d00841c031400500030300c5c8004000801084654412243e042e020329003114410200034401685400310f14040a8015080000300041c1c200190804506c2214100b4600c400e0a1001c1401c0c0e0990141c4150700b40f045804034018440c5181c1c08420444103440c071012650b43c0703c0070b461441d003115030700341214610315214010010255014080d540303000c1429aa000c500e1898020001c0d00d545160040c04404000600420b0011074100c910142200d14421b0810081034165828040602c0d002c0d4200c51343d070f1343e003040011164010300c10b0348110782d05030f140d507841d6645090070400f040e4401011405901020320904001c18240d030603401803143c041e15900024244032914000306103d95028004101c92412502000040401d107641d10381c1e404912685030703840c0c00d881a411030103207400c980500d0302c001c1580018007064180c01030185000708155198065010400c4031000e0440c05006002d031020404519424410402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 552724091 1250 552722841 552722843
    0xf0609210711010f030b040204180b03070608041205040e091f0204050303040909260d14060d030807020705220e0d0c140c0607080c150402030714131407080c090a0e04 73
    0x1b00803101c0e40000d400ca8200350452003401d1402e8500c0c0180b181d05105104c0b07950307030882c01400f080d8600070008100ba00003c000401c3c00540345030750610701d80604207684c0170300700020001c6820b240c14a8966540c01c011468029000d9041218881c1001140f003124280c03100640511700d041e040140761130240c10511000c8628509040b010708681c2c050001c01092600d10700c079030710f40e100d0f421011001a6000d407640b040210083d1803c0c440e9580d01c1e080b5640b18180d150400b1401640c0c2c8041c240c3c203180d815884180c002d4014004a12a14044a6501007681069200b00640180100040e81d80c4030785648000214802510510120380803884401c51080020100c461000215010902a4203c89401c0b528000b02142c40481041c0c107100144030424194600f045034a4950002507a07069580b086441501e0310030243c0c0c0c8103440d00c01c1e48510314915400240003841a000d100103014401326500f07400a43c020001c00d030490081e0040f02c203a100000c0a002c089410112491810500984 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 552725341 1250 552724091 552724097
    0xd0f021009171b070f050a09050c030105011d091920040b03040c0803210705090a271805330703020403120e09070c051e0f0609210711010f 61
    0x10601d0f0381034420014040034110050403500c05034508000e10085144a4015502c454108810050020202000d40303044903c2464405078442c01e101d500a00d0020151805420814241c03c0280c03407401c044050f0102b00c28160104642e00e11031050092a6240c1688045041c10411003000b00020b01000b65411500440e06a07828581c1c50500710300c0e5500400054003a0301074048030700001200304552950211007424058949001c5d40000f9100c0078030b50040c01c0d02113000112903102307546101c000811480c030024080080307400051101440c0300b4900b0003142d40d841040440b5a5111150040541c4450745031051058410800341080c05000d00074036040070180c0c28803001010400380c40f800d041c2e00449840b6080b08901001c140804c100c4000c14100c02c2c46201c0589000181e40011881070360f100c40d60300d444090754034500290a025000074445d00921400c0c0038003803211004a950081c00781612018209042680380c000124000d690026005841500d00d0345590350082c1c0b00d50b030403140700345 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 552726591 1250 552725341 552725377
    0xf0405130213060e0406140d06270c051c0f0b0a15060804051515040b0d020409080318010902010e010c0203070b03190608010e03030403200d0f02100917 67
    0x190320242c40c4142c1d0700220015a000b4546295800c1c50710504002c0c003e00e01c54803040700004400b240c2d40341242c85005140594511143c06968010180c07008501d11014400c45801d080e070624174281c901c9409024031941c0314880007058006030305000e00780a0340c080301c41500034402e80c444040c1000c00510004000707864500c03002c1241222801c86e000350241e078550301410b04160074031f00c0c580202c1403822181c040804090043d824980c0384024480c410403103000c80c01c2c241900114000c0036000d03800030f4005040210700c0080114002c0070f54420b17154a4409520500e11007c81800d0792030036003019001c200b8045890313160f0b500c40e92000303909a0011b011a02600e0343c1340c40811087c3d100315601d80740d110002003031010566890181d1001040a80c0091150050b8a4041516407101404c000d06204510102c80b9500d03418440c0c0404d20a207a0050310541c400d60300d07010b4804101448c4c041c00601994000808240a07132180461450f00050b840c050545100901503a545c44610b20b4040f0140c18 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 552727841 1250 552726591 552726607
    0xa0e0a0509060613270b01030b03030306040903273b040f150506031917130b040303050909011710020309120313030e03030a0206070302030601050c0d0917030f04051302 74
    0x500b00b040301140b0340500c40514617058172030850702424203d80c10542041210031b201e640c000140c80c0c021004590006000c411843c0640c0c0003000c1d400071000d020010100c0030b017000c2c2c455060703800301d58044040100e4110852800c0c1390903103981020a0f8506030403504505c08da4103422085074003071710868034140192074035141c94a00c130045902e1040000d44590400150b82814884884810b1142c500a20420035507a1115045032101c802856003101c04902c6460182041290900600c04500aa503803603440f400c000b04142c1c0600f84490140003070b2000024545000e4240c0150075000313801600034020b6072100d440180d8005801c10506114545c1e11055488208008501842014081414100c21481d018156101c03101903d0b00c00e4005000d0804150b0300840d40301e030f1000952400595070b617602801640c0310300130358503100c0c1a4400e9581d404032080e000305026041d1101110000000c05404545540c0d905c1061824400c540c0c00384020170070741c180485440071400d5221400f40c245486 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 552729091 1250 552727841 552727859
    0x14090117040b06030d09060c02091506030103140c010c02060d0c050912010b0405010806071b0f060c021b060c0309060906040e0408190c030f20010606050a0e0a0509060613 75
    0x503079058070090509424081c1900d8100864030030000c11341012500c031403410402925450082c407010f401000c00034001703a001007601c2004660203800030402512541c40c0e0400904a404222400d040d5124240030005158056032600c5030032507000f000c8c0d03407402000c0000400035016080d0460300b07000f0180300140055940e5607204090401e000000102c00100c5c8040200380c441c1a07021001903080001405076980d400600c40040c021a841180503c1130705162041291003032010103050700c1c1c035000c07080c0c510a9020548107804174a14002c000c03040c0c6202e08201c0c580c810710150140c03580c420040794100e41011400f070901054014a840d08242d03803250035200781e01084404a90414000078030001d001c4203140095000320280c9000f0314420b81c150b8010f0487c0320004809001c0c0304207000038540342c2032004105045904404028841142c0d1140003500640101e40b0b400c021a1a541d0008074070308242010745c003185c07401416a02d20b5101c40301400081e9001d00304503915901c15040c00719054803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 552730341 1250 552729091 552729137
    0x50a0311030c0706050c0a0e0607080f031017060105130c03150306050601021005060901050d0204020d060e06031e0304270603050d030513020a05060d0609050903030907080d140901 79
    0x4996041c055a50343c05242080480da0014404c510b43c0070144131104401341e220500c4511007200f55100b50b51500b150604040a0107080f401040600740002002802c01c24190207504807000740c2800b031b030215000f40e5a15100d0a0074000d01e0b8000030500c0c8001e40c0f021444c1c00c0300e01c41d040213090000d0008100d50207150702c4070701a081039445540341c030280551540d04008800da042c120100070020303030510400048210030180304003841792510104c3c40040d0344e51641228881100e040d003c114032a81d035074200c45260002c0f0b802c40d1081c010520003903000e64100c0045090681090301461500d420800180c00f141b20074158420320508034001030103194402d01ca00800b95004400070001c15008ac6001425100c1c0280010f41c046c0c0d00c040858016110400c2c6c0d84150381d42140c400b5241d9401c03085400084c107050344201c81003424282132050302940400194041c0465500351541240c0b60025680d5030b800346160700000803030307020783c40e030459040001030034002d41c0501d842c0c0d9140c0d0200300e07103c040740 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 552731591 1250 552730341 552730351
    0x6041a13021207030b060d0807080a1403090106030204050138120a05090105100305150c0d1508060c03060d0b1b0a031b0f12050405030f0301061206060212070201050a031103 76
    0xf42c040e45052013406420101c590f0b104100303c035103240e10052070362503202901a05000411141022444084050040602550800031424500d8481c942540c64038044c0040c1d2005a0217149480000b1400c03010310075000070102c03c5101190072408103502c40341400144084029070150f002d11064103194180d45030240074800091000c207c60034591179103070855a0240440c1c1c011700e1510782c2040000c20100300150141f058502d040c4140c2e442500045051047d19451104540f80c0752051054020201a0500341e8151030100c3d00140c0e40c0b0741010855100036140c0a41c084c0700d42e0b54080002c0d0800d40016800391541c1041a00030042000b60703000350708003650781c0001c00d40317500100781d02c4001741d025001000343e6480c002e900180382d000060880c820542030b0040603502c420018087c41010812030f4040e540b440710701981d0350fa4640c2c00a180b5281e0aa6500405051a4002540f903100041040f14044080d04040c40c0507202d90040d1003c2e070001d0038400c00d06494411400c0d0b594051030140d4494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 552732841 1250 552731591 552731593
    0x12312040506160e0a090e0708120a09140a03080a0e0603040c0816031e0215030c0406080a0207080a110c031c0336080c070618050306041a130212 64
    0x94200507510070402e00c00b003c003543c104040c00105821a075904801c0104aa01029001070f641041d03000943c03d02ca070a821440079485904880d550750701d2034000030180900131b0368070140625100e00803121550385003140c0703941c0484081b0741440460000002040c1407100790901c00c1c01d007451174012888a800072201a1950303c40b02000f000303015803c0c80308040e44e4068010480d022804c5170303244468584403e80301d0814080142c500411515051901403068107450f0710580c89140502d5000440d40c000d02604001500c008041010040305000f50b40c002680f040303090707040200c0f0780c1d011260841507104035401031092054160060b10305110a10107610706c100b4607805040f05040c084e0076920b1100c2e50340d80c01280c1c2c510100c16000081c00b41054401e034501032174000151428456083d000e10000002e0900038113100240350b075000040101100c40d0300b17126090741580d400425480f0a021100646203022045520b5500200107103500d52084200400b58003140058000c0341d81d150884040e0092 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 552734091 1250 552732841 552732853
    0x23100525052709060f031c05040306020d051b0418020901120207030c0302330601020a05030309030307020c040c0c1103070f03030507020a240c0809090703020703030f06050123120405 80
    0x25034104843c4042c1c3c00b002c00c0d10b120009091260102c0d40d111001075242441c020b8200d441c145081c40f030701c200d41c011030700610159251104a480748004102c29180050300d0b0200b0310b08441881030180641d0215058005c100521402008405000e0f500501845040110744841c146c2e00f1031281c070140014602a6407a11805540c500d8040c2c0f624a8030545001140002d401142100314040c054100400100d0441e1440d9111640142e00d00405040014941d002c044100204000000003451081700140c2c02c0360403480c0580c1c217000c2240c03c1070402c0c0c80050020401344020401038082c40c0c58021010701141c04180da109404880c4e40000e40044002030350009100043d40307446c80440c0003074a01d80c01d62400030206e44101491074417028071004240b0642a0b2400180303c0e000f8259400e508014149140c0381c904980000c0c000c0d0310400080300860f20b000e1103171034501b86500c1814241c800684400302150101d0100314201c8502c020400a0f0060800581cac04204843d490340340264890002854 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 552735341 1250 552734091 552734167
    0x21813060f051024050c0307060606110c04092a05190608090102130302011d090106080f15060a030e07090c08190b0f13092310052505 59
    0x201140540e2085444a81d07644ca135252841c0c0c0418408051810703420650707a01c0000c9600c4605500540b0b4000d00303c2d629268000915a40200040400541c031005441c08a000003080104503040302c0c10240004080741840704010400010440c0b159100c014020032060361368001030080d00001da000100540308038000c01c055034000d1826034124003040e00940c02e00c08a5141602a61882c0c4406410800d02807401000c0000710260611902c0340600403c10030344c0c403914090600001a200c451000729404001074800111090042a0400091400340751108101e02140a05403910070091940603541e40001c26030300a11031050010030341e444400580c50182c10b0045903400e40308151180c0c0e8140450b0740c0095a030b0524420192108413040c1200201c601c0e080301c010401c1500c010440c0380001d06080c100204c0341600f0002401c48030444048542c3c1403400425983c003614000b160304c00c0e03618500c40c06a81f51080f079a88458034540b0f103040200c540e14021014a142d1501944100a0300c4001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 552736591 1250 552735341 552735361
    0x7032705270a200f03060105090a0b121b09030619020c160303110703050303010320030114060901050a0f151418090c03060d120201061a0c0d0804021813060f05 70
    0xc5021a01d01c43c0c86030414040402d10009444020142410080005100c3c030150b41da0319040006030818030b40903078842c1074048106c008050b0a40b03900e034429a000702c0c038042c540064021145400b0000d006040c040e2299105800c602e01000e824041c070355002e0001305180c82c0100146a0b52040710003810000920354203014150300c8088000070f003660824101440450400011a411294048680c50400c03400c80c1c0a42e00c48a10050219490b500340301c803800015400d643c0781030007008112040c540c6039030395004002c540c0c000c0e403084010070300e640c481c1042010320885000690020a042100d241240f21f080c0c0c040359400455061441110440012403a040800d500c950101c03e150540d495820443e002882600140030001c0240301e00604410215100790000740051011036648040004500500012500400a500031601c11400c401401030306c00c00c0e0150007581c0207801c3d500e42a9a04a54410184001340722107001200c0a00c1a400601d0a10800d03500040c80e182c002080c0c10119045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 552737841 1250 552736591 552736631
    0x13050f010504080715030204031509020f03010513030c020a0305120403030237060608101406100c0b0a1806020301080114011401050a1b0807032705270a 67
    0x40d04000c0140001d010320000001d0308400e80354002c100c0500c20b00d4909007240607100b1500700034015420300c03d002c0881486500a0340940f882290b6410905001505141c00c03100c04443d09890b000100803090701280c040c0001044090000e0b200144054480c1c80e410304d0f220498034203051041e40040e0400905030b0510030307085a00080c1c042c500d013449040640301802020011200401041c8541d035100b0000c555004c0402007908006641074035016240303c0d0001d0185c001800000d209101c0011230600d01f04410180e4407090340c48498200c5015120003500c5007000313100c0103e042c3c0d03a11036042210400505076044078840e20025a903503040142c981c5c292400124494020010107005000c070401c86030750006e58072000c0c03030310719110601c90208a40180c5401d0b103c40526101c4034003001032201c2100201030590194644d200c448038442c015400600d41d0381604840341c1c03690141845a49086040310b0207401e074412200350f5441181490012140c415507502001c1c90b034407410302034644646124 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 552739091 1250 552737841 552737869
    0x1020c031b01200901121a03190506131e0f030e100c0b100e0c040510080c0f13090c02011a06040810050c0705031b01050a090f02150f1305 61
    0x9000f085046940e00c0c00a200c82d5441042404002c50001a0340e44564821601410302c1c5c42e0030f00003010110039152280034070b1808140070b40121500c1340660b200e003231064540306901800411441c0c1c0d6072001441c0c0c0c805925030072525190b40300140c2d80c104d0120081e0301c3c00140241e01d04500e44001e0b00d0050020b41c2820300803806030001c024503101300c6030040c452460064119010314200d5480d10505d2281d003001e600880c20700c489590501000200c1e00000c2e00a0f01e00589540c03030324a80d000416078590270101d03082051100100154021401d289020300420748040300941c03401d0342c43d00644815a03665080e03400050795200d10300c03000070020203426900e0440a42e02c507072900d4104075405888007141c241c4030084985400200f644064064120703040d150300b00701920340350303c80d40a00c1c01010700c10810701e41c030300d41c20038001c02d040400c544541d120a9900c991525039517038036039081c0001e294076201c9104240d40103101c3c944031b02c007104000f00349542220040c450464146070400c483c022044003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 552740341 1250 552739091 552739093
    0x5030307080121030c0c05040603081c0e07141f050d06051f081b0f04080c0307050f01030b1306090b030601090c08040b2d0610030c020606061b01020c031b 68
    0x80802003d40303107840c080e90450b0140380c4039100c0c1e24a07061111104003d41c0c050f40d00546801000401d200260b800b510601d00b50754560652803421050410170b80c0d03003540101940d50489141040000007920500d0309401c40074041d041007940620303150107030071212011800480c0d4001807015407080700e4071a82014004c200c0f5564403050303014048410310040c1040180c10f1200400215181c9030440b0550140210707000300701659181c166417090915001440b5500052140c407075140300c20b28010031034009031500504400803c1d0342080044001d088000e200c203130010700041800c4d580200700c1c0100d50103041080d202041e042038440030700d4075060059200c501014039161098860f6030b80000156000354005400000030b4841c190711540400e40001070b44ca40f100d4902d41600b15144a52180e032061000700c922488041121100768151041c1c5030300c2400507040480010114940003011300300e14000c8002c520b114101d200703141400c90340141e8400241d98130104125800243d4800b40b09074030002d01c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 552741591 1250 552740341 552740369
    0x503120108010c2102070206040503060702030a090e0c030703020a0314150a050d020a05060f1207030906240b0a050f07050a0c120c05010804020607120e030c0411040905060102010e0a050303070801 86
    0x10000d00b08244113010300940e4000800109543d2001c00f99009000b008007616824101040040c3d40d03940309d203644e1000b003000644002015454080307180e01c00d01c2505401ca2450369185012402940204001000e056a0b030000e07410ba84842c042c8540b1464091135201c0c10081d414023000020001035011600c43e1041c51003180050b00c40740c0b0f031103040300e8059441e01e444003030340310401000307004410703402046a40c0703c8100720515500d600f11421560084004104022544d98911108840203041c1d0f4000064060208241c1580074020180c070500c61404a003808a15605400241e01000b400c0e200b990240004100340030720000014004d041000c042d0011403040d41d28a56014114802ca605001007000090295100e21048511540d4045016251080b01c204064501c2ca4074221090003449099843e17840b50800e4800e580c880fa0360b01045500700b501c0e00d0b6002c400303050000c14007411035403a081808881c4100300304407090540b00b240a162a40380502000b0402c090581c400c0300c0c0c0d000f40e5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 552742841 1250 552741591 552741617
    0x51803040302060702030f03210c030103030e0d030e100503090f010519020c15130510020a0e0d08041a040905100f090c0e150a0315051008130503120108010c 69
    0x4031000c0742c1c0d041d2031550300c80c0b00d680006424502030001d00c201901000071136122108403110280d03440c00001000e95660782b039100440341030740001d0000402141e5280100350051422098581040303201e1300d40805440101000b00c5c00c0600001c6400e004150b0110070300200e000c0900c203050340700ba202c9008001a1034407070a03150491203103041c0380c180e6940c001a0700c1c03880d01c0180101644400615000b201d01d0405d000007601420045405075254099181d81c1030008803540205d4907805030b9a6103091443da6280c00b0001070101d207003000c9079265001c100006404170248510000c4a903030030100c5442e11715241017002581d80c010010200c0a030050001e00c2003110842400e82580c480200004c1c025840340e03401d84c1e068241120385e0368407040041c0c241448008150040081c0038213a5002e001e0b189614000f41007090550048942c407034814940c9450f01c62240c098a9030191181c849041074105944850b070445e4401ca0300382c04e29504000050004030300c2400307a80008100391500e00d800c0e4400d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 552744091 1250 552742841 552742843
    0x20f07121e1e120e090f0109111606020901230406030e0a021f03200d021e0c070f060c0c0506030601020a1502040311090408041404060306140601030518 67
    0x10160501c0801c158640c003041030202c401440d480c40b4050740b0040d00c0c0e1205900b00622401d054100401c0000c038030615140d414100070030010b0140150304890b1400b6403c007585000074042c2c0c07801424a110040c030030032405151004c91000100c1c05040c0050b41c0d5910100010f00d4404080d102040c081000d90181c84000e004008036001c94181c0c1c9800910130780d02c41c440d01e003070080c40c1c40081e6004803030200300d81450314016100d07070040d501e9880800101e0031441050164420303550004a01003030900000d031091616800070b044000742c41507501c0c040b803061030b40c445983d04001042e1145d5884003006012950115849001501039820281d01e40c400ca5959546400720fa4000c5a0290310701101084180e40200048254143e01041800c2509203503403800000f50410300c41034482050040305500f40742048480f031401507410600b65461b25050282d00410003005a01254005658240000224940c2d201b182a0a1003000a400d02424490700040030b90b9400b80030300c100e641075086180c5403420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 552745341 1250 552744091 552744113
    0x5030a030206071d06030406061422050c09130c090b0909070c020613080c0a0b07031205040f02090106170a0b0d170c1204031208041101110f030406020f0712 69
    0x5202d03e031191244184560138800811102401ca811100100511003013199640210080d00c03200c2007560114903032501000100903c0d2030102c1607014151203800980e1205810081d4006140d03403884d480c04408001099903054035140aa192940e18521502c50b164032400c4070000b8484081198107001aa4000411050001e001ca40500090000080840d2078100540340c6003049601c0454201d5561400162a0100c1c032031041c0c8501d50540020405008030401e40b01e24640590780e06041c0c40060b02864004c2a0140060b0384a10702242c9090059a071042130764084e046941d0703042c1d038600603010302c0109a100a00310f17000707003410b1842c540d010380c8420a072a01c01641004e2805c544000e50380041c8162721504510001a000341044170309501c1c0c01c0c03001401201d100d2401d06070380101c0840103c1d070401c3c003075400402c1407007403450001d0b50f584244016100a03140710107403074521110003001c41c655070040d8056005600009070710b0442480a00800b40142401d10b00456450010b0303844034040c1c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 552746591 1250 552745341 552745351
    0xc010e0105040e06041d01021b070602120309101109030606330c010606090f1707121b080706110106050f040507180b1209011b0509062101030c05030a030206 69
    0x1600d00000030b42030b642c881d0008040200300d10403200e80d020700c051b8078174040d502103808568421410719840d4100000001d54404980300c6030302070070b074084600089914660019103200344920030030351002e54585c4d0b10310a65442c5005924600d6460070443c1c14141840c1c00148081d10444402400c8010fa07054003d084800d0034980e440300c00000c5016030741180c0e900400700d0740d0440b0340c1f81200100d4401c2e046803045094441880c0c01c5200f641da6403400c1142c8058a03844407015070090b90341049054000d41401d92403602c1017000c0034010001010107001c2d50503c1e0311005050780080301c100b0603950410742000500440a009001072401c081c08100181c001c2d800b12400307a6074680000d0004d134400c0004171004a00c8940011030300d5520a001080354000c3c2c112241d080c030025010038001ca905104520410b0703807100056080c000d440304107032900c5c0c2050103c0c64101e2810400158800c0300740d403041854011868580c3d66950641c1000340c810481d40e003026000b60b002041540210b900003801c03c0d844 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 552747841 1250 552746591 552746609
    0x117070c06180c060f2c0909240c1b06060a0f030b04020906010504030c0e040b10120b09070b0c0a060b010203040b040b03100e07020a0203060702010b0d03030e0304260c010e010504 79
    0x85c2026104980c0b8481c0b45c004044011820030b203041d0700400480200f00e4580d001c503a8202640c683d01800b58803081b5410150320b034600c02d606124501c5c2400200c60354484030501d501410040f01e40414012980b0030310034001550403007004c02c038481c03900c2e007204000340c0007851115044500719514122551400f503c068840c2504a0005106a100c0d400326000355034810300350090140d0750300d641b0344802d0080c0c400306c401c0240d520004912203913581426003101c400650480381ca8616441e43e500c0d49a002d44400018020407802050340310411300240b640150100040903546801d00300402105c0d03490410341e04540040004110601c16035082d03406481055030b4072035891b1544096501064425031001401001c0311041014080e00410051501c0c3d0095040e07403190303500c40d20201e003203440029460b80d00002035810f060101344264801c8120921a8003141d140ca03403a000e500000340d00507250b040000e00a19440100c82c0000c0c450317094000d0003801c1c84041009030500280107400b45014076001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 552749091 1250 552747841 552747857
    0xb210a030509040f0c0f03050f1303030f09140703050f0109050c15040e0a02270a18091b05032a0f030a020d06060f0e0408180117070c06180c06 63
    0x42c0e40d0303641d0003590390300c0010300d081105010b8a080a880868621041400700f490321000410340200c8401c141c6c4030328060700b0b5120f00110345030760070f500405403022841c07001030341e88812200182141c44e01140702c0c240394006098003442c52a00c0c0e40b03408401c03d0014516410082c41c07500040c0005800c0070205800c0fa03520840c1c03030340c40075200750724000d55024020301500d144c14000d41c13070010303402003c0c5a1807040704402004d00c0d403000800490000b40c5400e80102a4200410031441c940740d41412030110100081040210750b11103010b80e50140103590004c1120140800991400308017403200c401c040f6038181c80c60400d5030f00103080a00d0520003140610044240c07000385030340500002c0c041c0c03030b4001c045c3e400d03d034000e04080008060b140503000066440000124001c000c4800480c03050b9805003000780f134000406072503038980c102084007605000403010708801d400983c01c1c503c1e00c44c9025a07030ba41049111403c1480c15109038007c501d0405281504850200d800c8606000540340c0e141090f00e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 552750341 1250 552749091 552749107
    0x6270d08060315040b060f0f100e01031811100908070302130906020c0d1202090d020d0807050a0b06100305070807080c0c0a0302160504021c0902030304090f0b210a0305 74
    0x3c200441c514080051003c4076007008104141c00007442d002e94001d0710f41901000080c0d06001c410312500c7c140a5200011009a0b540306c0e1045000301081c0b00e0615001c1108401d420030556070410420048130211450b011440003428081e184a400900d58503100d14110b1a00c81c680d516401140070190040161032065034519074250800d0859aa1105085541d43e05200b12039480314901d5540340c0004d900000000c540325094000c2d504628401004425400c1950b82001001c0d00780328004ca99960003032000d080402d109000380d440c024011038000400d40f0b80344080003034082e140400030060501d020240190303190b000c0c1a40c0e40c0152036041010300ca80b0f80255081003800703000040c10746c80c81018250300826601080d00301c40c403400b9030042040a51100d08000c02c2e80658540b120440c0980021340540c28056081201c0c20360000d000d5a25042e12078000b04150360707030544420a183e846203500241410600c21418000883e002265003400380030a01ca80c80c0d44001c500641040004200c0130 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 552751591 1250 552750341 552750343
    0x30c030f0501111623120705010906020705030d0506040504030509060c010902121608210a09030203010606080103050d0f020d03240807030506100303090b030c0d0e06270d080603 78
    0x200035200032040c0b140e140c44021200003072081c04c2c48000c848084069000107118030b200c011150316440d00f04041d0200601d0030f20b280c8080e80101c1e6040c0d400d50748850303012021586034030040c4482f0b40100c01642d03a03031400d01254420b44001514190141c5d182ca02004003003a8008140d4007095000c940c6150389106090415000d414807400c00f81d801101d40729501c4c80001c0000f0301d00440b07a4080c2d04002e0303d030740d02ca01054944007a41010b5011501008800e110054070314000c000e40c041500f89041c08980320b40100742112082e800600c040780345034005000340714080024140700a60f61600f051140f010240c000d40394401c01601c041450b44540101984c10014504104150302030401c49149961700c0c401150358019502c0b05903440d0040e90041058050415100c10541c1d40584030503680c14a418460f09107a0300003000303901c644c0e1003401611552001c5010b21200d49001720300800840c00c0503a00001142c4040c0c403401c00a101c0d0110f00c803131100c030108603551240181d04040ca0907644000100e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 552752841 1250 552751591 552751601
    0x60c03080a0c26070e03030903060601180312020102031909030903140309131406010206011a071707050d0f0e0a090c02010207050609010c0e010c0807140c030a060204030516030c030f0501 82
    0x16203012000340e09030502541a00480d48503842968071504400741c01d1086c9500d070300c6217801a1360107030807640c005421540645030306041c42003080c187e5a0043d690f07496204410a5190501300142d4002007413208191744081c50034444241d1034020401c281349542c000d400300925100061182d462a011080103040074000c2d00c7c0606009071504101d0402d409070702005040407500305004041d4000460401c1d4400901d46050b941070f07000c02021082c603801131a100d81c0069104885a1445461000d50014010050000d0340d104030010107142e815050050460415140420100505030907002c0d203640d1042c1129080b1803041400180511425074124064480c000c006001ea100e500d0601220150544c007828140c00c180d0341f0440303011001d00045960050009001d403131001c0601082001c0b80f44a101007000b440c02d007080764210070a882c0800c1c01c0c01c17501e101c02d17202250701007402c2080c00070038010440f0590b0170f58a00303000181540c0e80c8200781650340c0000742c03403880e6601512003041000d5001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 552754091 1250 552752841 552752867
    0x8030910051e03010f12030203030c130906170d0302090f042307050c0d03020301030b151207121103011116080904090b18010504080306010c17031609060c03080a0c 72
    0xa4222102c5900c05411658000e100b41d481900c0f0708003000818491b1001d61414459265014602d540c07600b0038841c0e003607040502e10680403840900d00040d042c8003481900b004020b480842d038240003100c25030900f000405a01001854010418074040c0d03510b0b03041e45d84020f807084400003403d081610008070301d82c80301d6900a00600e2120309104941e0f4121000d04490f10010044803050020700700c045080e03020a110082c480280350000c81c103e600ca1030013030500218094000a40003409482561074060366500400000c0840400d600c288007010040c3c0441c160181c0c028401c184401031866064410440b040034512200d6211104000309041102c0a64400030300c207100340412420040016401038402810201d800c8444c400c4040060089a00c1290400400e901719078840b401900e02ea1204c10045a940c0c2840360441601401e04000d1401520ba03d10350341d22182c182000513141244a8201e84103001c10141188002507100c4403107680449446004601c0b400c0e24401a146464001c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 552755341 1250 552754091 552754117
    0xc0d050a08040e0415060f0302090a0b090705030907060c020a0512030d0e010b040b031603020402030c0d021209060c031009180609030c03200312060d120801060e01090803091005 78
    0x81c000a030f03220000030043c0101d014000b916452028003c42900303c40062040e045a401c0c1400c0c00c001510307140340034a501030007010300452504c8a00c0d00051240320115040c802040e000302c24400052300c100110b0300030704034a00b0041001049900043c07040307400c070f1180a22071020f1080c0140307075040038000e40c1c90600380c01718180868809000e0301070188c16440700f402d010300d10301014003810346000030b0b0b09604d0071a60710418020364116000d11008c3d500c0280500700708030041200300035018862009010b249100034180a05080600086050050103400507201c00028024440380082c0300740c3d404119618860009200002901d03040c28000c440724004d0403140c5001807000a02d50003502c00c0090610070707a83d000048643c40d5503a158084d05100c402610b9000b400011a14103401504e00c0c0c004400405800b0003010a0f550030702c0001a181940001030345070310040080542001100c0407041090825088550601c01525500d026801076a03204101d180c2c05a5444c0d400381e000c4599004000d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 552756591 1250 552755341 552755347
    0xd0f0213080f01050703020f0d1a031203010302130c1209053a020601060f080c0d051e01060203031e040c18020a0809120415030b09070e03011406030c0d050a08 70
    0x303038599072607140b5050b2101a950a0500168046110f4402c41d041e5440c561101c40c103100c0300f41310003c01041701e812440106d01e1894000e11441d0f40400050400003e10350782242d0720f41c1544140324100d01e10b40354034005072381400403e121356500078802c0c510600d00c0c240c0005801486082c218500490581840c02c0b8038100e2088401319007000c12203000341c02107081c0d150813141106070200c0e5188002d00c183c41c00a240da02d404105c0e02c0c85a08172a400c03c542c08651820300b650000d140044800c02c2e40c104054020020018004d1514000118010200e42c00a9800c3d464034075401e03030352000c1d2142500450754411002504000304034001c44003600c0d440c1d031030005030f5800d942440000c0d440f0002070307804100404005000410f0005450fa40300c0a0307111541d00b003518000e0701d82040300303d40451009041e15240c68500c6a15400011446600c1c681c3d00c101e4440e4600090500b11801c41c41c42440194005003045134a803170000703040c440e6400c00e0b511004241c0650410741d0508000d2080200f402d0000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 552757841 1250 552756591 552756599
    0x813050402120f1510230f040e0702190b041406040b011e15050a02210301180e06041e08190f0507110405040201050903031309061403030d0f0213 64
    0x20b00519200381055000c0501e55210045201c41c141900b031607107075000640002d145003040c42248002c5103a41140311800e03401000c90309140b443d41080000c0c0d840402d000c01d041150103a5009078540003100c0c3c8c0054003c0b0501c83c04800c40000c3d1055000e8842c000e5007022508114025400e00795800001c011755442c3d0400e881e1a83c1c000c0020b10480550440f0380842001c98038200c1e41c003500312070307208241586140005409481030307000028200d080d0b01a500903800b204a141c101c016204082e0044180c0d20340c105505141070300004103c0c0d441c007a00c1c0c0318040d01c51920004d4040c0e0010740060050b0300050018411030350540c0c0700300c802040840d000c02c2c251249004404031148050f1541c440126000040b070302202e480c01075080103000d00c0180141304a09042a50019801ca80185450b900c0d0a1021000c2440c60b03118000029120407640c000700030680c0f81c0d00c10f420160000d81c4201d83c03c12000d030000781d544c0c0590091801c41c03d6031160001c0d11698180c0c1111300b180c0d82c50360401c41c2140e903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 552759091 1250 552757841 552757867
    0xc0c080316060509010209031c0e0a03060c0f0302040501020c0f0415030f05060105061201060c0203031215010e0301020f070809040f09120210150b030603070305010501080a020411030903070813050402 88
    0x10748004451290800d0f0114898010600a44000c180040c00800309464010344c5100290301049003203003442540300690029840720440030018601800340032401c035105050040c03441000303003841400c2600c1404144026030f4081803404101d64101d80a80704800c4840000c0c00609080c60156107125119900104019054010b1400f00c0e01410513200140c1e40c1d40140070543c4101d40032038240d60618001808858000c0e030741d03081c80c00e002408a17800c05c100b6842c00c034031007103081d99400e0032020b150f10005481d60b0301107441501104160025420302c0c482ca41400b105000d200c0004010303240c0420a02d2580c0c460741d200c41511003c0d240c0520015825040110300d0807040034154005024121848003201194090b00c50010000047d0307241c02807510713005194a1300f0140c0f02544c940220720001010500034012140a82a020301070540b200f0284100003c54000800304030354050140208148500040207861131150484000303035603004c0c003800720f8901c87d019820041c0d0151000c0b51041940c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 552760341 1250 552759091 552759127
    0x90501080d020c0607111c081305040b030705130e011509020310090908070204021b15070e03010510060f0c06020d050411031b01120b04060b07022b030c0c0803 70
    0x103a5502900c3c0c002210700c0c20702803584661280a80b01c0000726800c4001e0342055049822403603d05400d000310200340c2e40c1c400c2d02c1c90b03024104080103c0c0c034080c800d00c4986082e228802c5d41e41821070041060503c0c0c80c1c080b440c40300c441e480c0e90420300e41c0c034403810822200a401001a0040c0c1c0a0642e000c543c03220f400700f000303400644030100c81030b10480c404500385075548170345506180c0004900d41056220350801019501134901e448034003030381c24079503a40c0000c2080000000304440c0c6000c03815281054000382035000e00c40c404c9101e613040c00244040080d0100b00710003941d02a24000103981e0340c1e044240da106046602c000c054910020b4840c1000d00070354002405140704000c4804c08400c1da4080642d11030300c520200225007941254015a50701514220495044190010420411210000d81242c0361035010803403060300043d640003145084446c0d0b00749450304292510b24070500f0b80f2040748a0606e04002403d002040c0194402d10a07036011000043c00c0c4081229654110440c7c240c0c6104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 552761591 1250 552760341 552760363
    0x40509070f170d180308160f060f0e1506040e0708030f030601260a201b01050a090c12021815041a03150612060903070b01090614041509050108 63
    0x40100c0350030543d0580709038104240d03403001044000d611410341e11503410300c0e070224000104141461600d400001c0b900601c2081c528001c0b0000900c204034900d900c03081d03415801c03c08080307800027240403407030740d694a0215070031039400d0b41d00080042245800d20301d0038001c0e8210910510021414142c0d03c20034200441c480d54081c1d840d0800e0100507182d5201c018404004500701d56441c00010344200c40ca54000211150540150901e000001405006507800180d0725011042803400078076030802c00b40605034005c60890400c02c802e4201d038581c000d50f03046074052412104913800221047d5a81d03c0190a0407e030b4081ea000c2141c144244010081550f05456500640c207000114603000019810f041e250074000e0301910885402044004800c0340050096038170565081020a03601c1040210920030381c4114001c8d03030345540504203c410040141d02100d521410183c0c2400b0050441d0b03007481c1442740540e40826054a400c0b0481400c000c00d402400780a854480005100e2200064004200e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 552762841 1250 552761591 552761593
    0x3060607140a030315120803060f0a08012003060906010f031407030606020c0103060b090d02280e0c03040c030b18010507020309270103080708040f0b0415030c0806040509070f17 78
    0x60510b05c085055010503a00c40d1880320304450100001180310000110303032001c001461110000400b4000681c03550f110382141070b16a5458804800e880080b2060034a050120915035003103103840c00c0065404080140a141005842c2009040c0c0d18080d4204078100c0c0300d141c01c03840d80703441c00b0480103009120318818000144581c180c107240300e5001c1d2162200382e4000001040c903003844a4140b0507011020f400403030b0426080013580381e2032039401e950703c2c0302d80c141881020740d81490480d503d00420009403c81320300080820074800018a4056458200c039404207207030f601580c1d80304000840c4402658009090b50030b00d800c101700d8a602000a04200c0000c80e4580d40745011a030025030f5658000d41d45400e400f00802c01400840c0c004805840e115201d0710600345001c0d190714481c440f0140d503030b100d00d8641c00c022070244240d5001207000f07a61b409881c81d08001610101c0802040d035480030305032501803a03807400880c8a99074180640700103007418240006e503003541c0381035800c0c52000c022204001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 552764091 1250 552762841 552762851
    0x316080606090f1e030f010501060e0a0f120c1203020c0411120f06040e070e0103020a050108090c150405180f0f04051c050d05070c0605090c1503060607140a0303 71
    0x1480d003001030b14800e050180500000744040e81c18010111074038603001c0d143c41002007940c40e8507a0300b004485060380400d00081000d5150003806881000865000c501c106140c0c0c40070311150740e0800a100407030308070b002983c1d803441d01802c0c40c03050480d49070010700c55804480c02c1501030540001d0070780d0b1400c000f43d404200c040741c5400140300900a600780700302d0b50440b12001c5091034981ca81405c2d0403100060000894800050800785001840c1d4842d0b604240082c00400561800881c450001d02d820300f4110800d01c1e0803207200c0d840307002c1000482c2c4542e030003440c4100056132100a540c007402028007541015680360a40c1890f09004858540301c0f0241c1d803001490300c00402d4921800703954041c0040c1589900761075950030001010441400304003040c4220250709000d4000d0500031060f81d00c403800c400a20703080035010b035880280b1120702c5a00504814111361140c0401188441e014842c26031644c54581c0042d034070f41315444019000340010f103100c581c1c450740401c0c0403483c58443c2d1801c100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 552765341 1250 552764091 552764101
    0x30105013f14011a0403061e0c02060411010c0b0718090e0a020411040302010215180712050f010e0304060302070507050907030e071520010905070803040f080102180f1302031608 78
    0x204000d0707280c130380b10601c2c80103000030000107203d90003075014004a0004816484101c013080c45c11100e154041c0c20069002c04180014015152224400e001080c6880392030920151212801528041c1405081045201075038100c103c21034502d40142484035001d112041c000359280e5034681e51004203074403a524280015256602010443d002c699040e0040e21510100900d61141c011006100040c5410500c14490720705106002403030103403902d01d841e15030880d9281840c500d04046428450103a030b1519240440380640001135504885042c5000769645c0141d240260400032560302075600310190070240b080f6946c1540000025000040444210316034500a140954401c07000903c0860300c841506c0d614444e01110700d0045806140000c1100300b074943e034152600c400703503206801c01c1c1c0010905000000c50329407900c0042450200a5080600c002031403410310041484c07861045008441c01e00944c2c40d0303010452144241020215141d240828040c0c40c101e191680c2000001c0e51840058 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 552766591 1250 552765341 552765359
    0x171005070302040f0803040e0c2d070311150412170a060503010b0d0f15110a0815040b03100504050c03030a02010b01020c012105180d09030b0c030105013f1401 70
    0x800b203484c0130f08d846040d03440c0c110500482e5404980c20781024880e004020003503203005101d840200e60598415582d82d009810300810034928200d24880c2500111481c2c0000ea00f011802e9800c642c01c03d4091003c40b5910344151500c0d581e000b282078211000400700304e0b142d1015800401124000e4000744400900c44041101d0b9010003000186035a90440901002c510308180032000c0369112200055200700e11801443d15400a80c261000030340300c02c0c100311800220701d00c0148240020b48080c0107510302c40002985480009191003c00340e0740b20001001d1200c108042c80da010405410f883c0e440b084200001e000e0300d0304030041c90152042194111065200d100302000505d442c0c41d4078803640f50f15004450281901030034411001d5a00c2c800105034a40921191000e200071b525100c3c151840d40c64074428208005002107484041031004004590b08911211083c000082e001d42c8c80320b0f40010340d90511500c4140e034080841100c8110440702d100340e40030740d141c51340d44080781989a90380c0c0c10301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 552767841 1250 552766591 552766597
    0x15030f061909030807050703021609150503070515280503041b050f0402071a0c070209010506070b13030216030f210504060f05070204020c1e0604030801171005070302040f0803 77
    0xf030000b1404000150894815405030030f03000c0c464130584141c504501d003061344030407030750704030801c01c0360f42d502070a03d0119450044c800403c0b0a07806005018644000102c07900304421003c02c0f08800016900e4501280c4030382e10f004030141180507a600c24103c14000c0198108035800c5880c03030440d05980035021b05290f2100c0440750700900d1001d0104ad02c1003444044e4000010403034541c0e1401481844010070001c0c554400c000208010751038030302134010060a41d40680c46207000320f008101c01d10100341800718203684443d40780c40c444c00d18041450101c0c0783c4800007128001074903501d800801044a22a1105000750086401e006100d0000030b4111001a015000f400440c004110400519025024009040e03906050450070030304030b0740102d4144c1e400702113030100c0d0742c0185c00b05401c04596565940b4082c2840300081055182c195000303000e0807018040c8000c1c41d0586e103100c000034401040340104840a1303d00600190600f108040c0c041c0d080b902070780c000e1400791000031982140010035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 552769091 1250 552767841 552767843
    0x40b060f0a020114130c05060904020d0c120c030e031206030a1e060506030d0905120c0d05160f062a08071208090d080a05100314070e0708011d15030f061909 69
    0x80d681b000e240200b00045e951002c040641c00035000d212040750030440380303d102c5880c1d840e6224440208201030035142103c5004185400341440c00c0c0b117060b800940042a940d02e4403848002c0c4000c0d8942d42c0c0064a81001c031040101404011000c0d5858500260405192140b180c0020701050300d54038101900c0d00f40408200000400c14541001345140107207880007491a1201554070003640e58002c2981102c00b41c01c2928564026149406400b19075903510b002403202208240001d42010002401d070800881c030380d0046c100b49031a02003621030b40c05010641c01d0748045030341d80d40c180d5440c20400744021001682c01180c24000051401c0318080b0741c10140105581d25048940d8445001c03c0c001c1c0740c083d04003170301d09000601c080002354003038900d86001c80312400100311140c50403140c08400d000c010700040411410f00010001c86000300d841d10601860f030100c0c0b01c0140d4500310f802d86031040d07124019a041c49140c641d4003012401181c0140601404811031712001100103510703054440e13481d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 552770341 1250 552769091 552769103
    0xc050a060c02040b120d0804020907030e0304120303060e240306070219111909060503031306120b0918100905030a1103040803071a13020906040b060f0a02011413 71
    0x1501e28014507042d0b2040c54144da005000382c2c00b546803000310368075014140c072040c2c021074650000d12042d4500082100c0c1d01c0240ba02d170a10100914140c0b194881c022841416040340e110401d510815000f40c125801401044480081c54a008462100040e00034206050780d20040213807400c0c54100801e00e503101d0100c41d00104a50640091070300960190741d2401d030343c200a00035482490740d03201810403c201d142003044041490030310b81d03184202c4500d5407207544039170300c104940d0701240d01011020088580314144030000c2d074614540c0b04c0141005c9010154885810401c01032054600403c2180828001084440c0d40e030800d00e41108031443e5101c040e00b1640148840542c40303100c0c8041c01c8080980c03c00792414155a10b440354610b800102c02100d05110110012541e880300f808136552102c4c0d4540041201446600800d072090340c00340040f40510b0701c4910b04005612074a045841c0071900b03829546d6201003030000207000b405072580ca00241000301d404101c0c454580a00844071942100b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 552771591 1250 552770341 552770357
    0x100f050d1e0f150b0a0c08040b0a03020901180e04030507060b0d150b090c030f13080309010209040b0609012a080c071d0108030d050712051608070f020309040b03030c0d0c0c050a06 79
    0x2171015103440312140821034202804000c00b00348110350310060036107070340d4a0b20056100c4026900152000150241e500c03003488959030308018100705880c2d01d42d00240c25061103a031701c1503641001d4001d0702e00d412102d90806040c56038101005485810342241d80410a0f003084100442003c10902007400e454055003410184042014031021300030f001c1c4c1200e620b81d018540303543d80d555924120380084a03e04003d03507010030520749504090060541d04070003104e80524012130383c1c0010b4611004001c00800600b0000e1141d01203450041004c12070503013000980d80c8a81d0158100d0761303140c3c00f9000c0c542c0011084244240007a01c2e202d441d0341a01e650310b01441c20000c3e1846c10701c3c02008028059401c100c00b69511050b0000a8072409010b20703814219a0304105400d04082c0030007201411000c20043c2d261000c0c0760032030340402510b0600204581c04202440d00c0702c000303032030f60140800c040c0650007440f65a01a55070044010106a4401c0c2441042d10b5600c404004009480e4450179020402d21 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 552772841 1250 552771591 552771607
    0x2060123011e0216090209040b04060b0d05180a050a1703130303050705090a03060902180601120506030a0b18070503010605090115121104060e100f050d1e0f150b 71
    0x800c0c1001c8000b5540c4100c580c4205900142e501c102165800007010700d40c00908100e613800e046c090b0705074860f025030b01032006034a44451038005110f41811142126650310108440d25a40110000f074409500225120030296040a40c0c07036020540e0216400c034500c4014440c400301500a0702e210b4032825070b111003088805c0d2025006044010721080803c82d003008000c0d0556100c01c0581c2c040d41c01080001151815807040c0495600c035071810080110040d81041050f07130f880702c485007041e08200d2000c1010344442d030110745004280c1500801e07083c0340c4002c11844024801c42822400781c4102142e00300d0b6600d10525080354054061a83c010040c50010310140c2407640165124808500d4006010000400c502c0300715841d0589460f50780b90002000c22000781d101128402200302158041910307403140401420600800101109000021440800701812a40400204407131940821654603280302c1c400c005008540304080e01915029411620340131022071001034820301c20380c141c03a20040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 552774091 1250 552772841 552772877
    0x9010c180f1208040f0f08060a060302061c0209030d030c081509040311030702041a03010605060408030403030c140d03200307140d02041e050a05060c0d050f09040c0206012301 77
    0x1125003680c040000300000075400340c1700f500a0000700030f00070444403030030f05080c021403c0c0000034100b03141071820403005101690715402240d41001807040c02028043c04500c940001c1d0040c0104141e050041e803000820098041c1c1221880701425558012259921010b03c08040d0221040f40c0d00600b4490000d0000f90241c2d102e182e07085040d00440c0c0c204221580024240c9221401c0140b240c200c0001c50309450030300b4042c0c1c40140100305c078400e0400e8104046550f403800341e440046d040103041c16000c02400882688603141025150984907480c0e450780005d4043c06c00840b050f08401800c42d101070140d00300c43c0c00c1da03000e0b410396950241c20703080d5460001c103143c00104c649000c065080100240c000211030b10001f0f92041e100021482e1460b00e8200210300510768403890041001f04401c49420a001c1440c031181960360030500e07114040c1c001030f83d4060003610840340d0410f180105021041d40c00040241c101c9481044985954101c10408061000e8101200f0b012584111107003111400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 552775341 1250 552774091 552774119
    0x4030c03030914011a04020a0c0b0606121005091528090f050f06010207050102031c1b03051f1505031b03180706030204060e0d021809010c180f 63
    0xc003900d4081a114415242d06040b40450400340107569910000ea00c4600070403503c2ea402480204c0c2e0440c113007810201c02601d80d120a06006050303130710700d2002840700d6031364800b41c806001003886004650b04c2c00100d1444601114010140314030107180010750500401d1006660700c85002d4451620f07040f603c0340b0491240200c112040c21060b00d10710200c0c440441e44a88045100101d402041d2801c1c00c9403034181440e000b078a032038119000303900c0c14001c698002048410271444000e040340700d000c0381c0c22040300074404c0a0a000d5480c1003445036008131a0b150b00164000d02c0380400011000d055007001c42e403000900c8c0701b404a20403030140b812042c1405040503540c0541224401454013603400e2140305c581e842218031000c0c081e2a151401e64640c41040000003400b42c6003801c5241c03506040016115424900d1868410b0f401c9110721402c541341c1148074440d450b041111800e450801401030340c0602981d4040900081107a83c094011070034140c00001111008001c85080078101212a18600c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 552776591 1250 552775341 552775343
    0x807140405190507021605092809021509010813020a050103090f0f0302011b2f0a0209040308010911030f010b030c130303050403030801091a01051b150108070501020d0804030c 77
    0x3410b156407100d8800c00c1030103180e20880c459406030000185006d60282d42c0c14050700054018403036981080801160040d0014054a05010217081450aa400754014007800e4500a4002c800140740302030281e40d070000b808400700300340c03900380150b6680a1407882911540c10b000e90301040e0000100030550280c0d00c01400320303006825603d03075074a8584410080c42466042140141e6403511200007112410f04126000c1142e40742c04a0360812503810f80c090854003200213141d00aa8580c07081104408101e03c0071820f5028140030320074640390070f0180625009101e09003680e400c0c00c601c00002c1003100e084910030110300e070890440742d00f07000c2c0001c0c403500000c00124041c10100520050f601c100c03c20350b0010361003952030395650b900358540184641410b84c800c1e51042e04012459415800407002c81c0c1c0145021300e01140c03180601117640022049404104440c1e01036507401d0808041d00080a5059582000c01c40c1c4070640d9030350049a4900e000036102d00000c00300d0b40410006842000801502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 552777841 1250 552776591 552776611
    0x10e040b0301060f0e010905010501020a034506020d0513150e0618010e0609100e0a0b162003031210030209010608040302100e0a0204050c12041b0807140405 69
    0x464413403143c112503008a401c6044249882c2d4010840c01c40300d40100c6024000a1015108000881d60050300c0c4031078280ca040c90303084c8841c48181e407030b0142e5103405036070f03484503000c440300b0022080c0d2145100f1524015140180502700701c40c4861070142d401c40d61010700304d8651581c42494000130b0701c007541d18034008200300700348418038a00e00c0e600d400147c1556030b40060f51a04104500b0009480c0035007040c04207010748003d000218403940c8661914402620a09018481364503220005000794001d400c146c5002e500492100c6039981c40112401405115811040c00d0144042070103284000c2501380c55459801003040d0141d004030a81040e400020680070079041c10744950000fa0700c140c09030801000620600200018550304000550324130301e1580d0b08220a59040382e050340c4411100c180a030149840c1c1d00407031001642c24088451800b82c412150006003414604030080310b03a0b4152108180701c071040080b9555030042600340c120352940f0210004490480140805424010245024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 552779091 1250 552777841 552777851
    0xf0311030106090e030c07050f060702040b03150a0e0606062a010b03010c2607020c0f0a030606060c14010b0a090f0b03011a0a0b090312160f0305030403031109010e040b0301 76
    0x144620a02036444e000c6035140103540c41d8020a480b41d850814241d01c030a100b0344000700400c1164440e40e08851486405540c04150000e56101007440c0140041113018485142c2080056a800c5544000d1710600007009079a0940c441c01c0400845004e50041002000d017498a421044404030328103101283c100400443c2d41510040028210740c903580031480130036070012180300e001c0d040150090070b40b121000b040410b4280301d980299601d01c5002c0185c05130799055500b210b15643d80e208031005550100d003d07c0000d44452000f05003c00d2658129010a1040c0024008400c10f008168020b00301030281c200e49881c000382c01c0050214452070b241c0440d9680c0350b04503540c40038050160190010350040f210800d214003800400c10455000360010001445001060780d8003052040c24281d041001d2600c0302c1011803018105c03005004000e0942102804503420107030000043c5206a000b91410070926076444070303200075131141483c0d982c0000c4148082920b54a000e0303002c10403548016000087d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 552780341 1250 552779091 552779099
    0x40206160201090b04030c0e090a0f02040b040e01060b090111060f061017070c0c05190519080f0f010b010c080d0504051c112e0504020303070209042a0f0311030106 72
    0x4003617010390820f55060b00342640912a01d40021400d9422a160000800c4121081d40310920724a0a03c28020702c616214440c03003601d50b60f00c0e00aa102900f5131030080004070351f11100c02c609039110310311080c003240003010300c06a5204007285003440b0350900c40101d130540d59107504225814540c04650300520500040c4154042d40204103c1e1082d85140c035100d07040340c6c0d41c0c1040f5002e00c400345d010510a024129030346250814105104049503400d42c0e0304800b012681caa10400c0440f560040806881102d00c104074000c800555202c00c62030a5000f044110302200044802d448418405031807a00b08010140c0f4000c002c2e4000c981c05030260003660301d179010319040c01100040401c241000180185158076400c001440400e0041e001a4941c0044010b8860216000f031881d40780728071060b59600016040d918180111107070154002e01098192030701d458101c203849003c0800e51605140d4001d4026407401400300300e01501e1400603850740440c5103564480d1465042c1d40b10540554036544005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 552781591 1250 552780341 552780359
    0x619230a0305100905010f06032306071407080904050f010f08010506010f0f021c09030506010e060a120602040b0a033c0b0a050a0b0703110706050d110909180c01020604020616020109 80
    0x44d500c5080c0c41c100340303010810ac010f04400c6440f40002c084d0000014480556004001c60000750b00e0081c2c010745038400340c14000c9042c081d01952a0b08141440d0401c1410842500150305a40d038121440c440c0c01d0b10fa010035401c86070120348080c04146400d44000c1154003c1c82c040042d00018812641003020b503c018500311031248805e080421441d55040c410410b05005250151419458102203403401a0019601080c6c030b105445201c4068140c8600f4400580c04507030181c806004c18035920400316100400504809074004024002080042c2c2c07138085071191103c0301300b4061402ca802280d405580300040401619103507100c0302d26840011540c6984c8100700041004161041d00c0d07404505020784020050b401c044101d07000740070140a0250000c0c2a910b1001e202c480000c3c6540f070180d01010240b09040001c0c1e8071180c6041000050b04e5458026600c6011100c2a1580361001ca001681c0d9400281c4009510040038044030400203003c8064a00b51801494007075039859841b01a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 552782841 1250 552781591 552781601
    0xc3003030b03010c03020705120915040b03040309140f061605010501092f07060507030e16050118050a152a0c0b03040302150619230a0305100905010f 66
    0x880200c0c0e151210301c1c0061030280304501500840d400d081d40ba2140a5031150346034100135102c02c10643c004141200207494a0708511003001480b46020369443c0c07600c17226549508111021000240c4a140100399400c4071180031802d0b0101400e40f00300041c1c2d900800c1250341160310116014040072070380d038021420034001c85000b8002d843d80015a510446007480380d000c030071a04101da11080003a060b8a404c43e2004441c0c0c0541c100c14005107a07210b805044000e8800c0001031090351080c1e05448040300c001c070407010101c2e030090329100030000707d0f450f07245280351341846032951160711380034200b00b04c6103103e1013644c445066242c40102d001c03400085807048000080d0307007540c0c4041c1c611801e0400c0443c100e0300010309003040e5810304500d0940c0d002507a880c0d0030040711f00d114202e000860500d489122404c40080000d00899100c182c80d244904041d5041503014881c100c1c1c0000304e4541410b000145000343c0740c00001805c80b0b40354500d410741c094031200008603010b66980401c580c008000d4452 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 552784091 1250 552782841 552782843
    0x219050309030d091a03160c02060706060e06041d12070501020405091801052203050c0c101706100f2a06020d1b0801060c0206120103030e090a06030c30 67
    0x40342c2c4501e051490301c4014817144004100c41c4101081070240d00043c450110300350044c03c1c901201c800c060b07480412020700802d400141642c1c1001800b040e0024500d0105d446103105840420503064524001f40c4d2045180c00110807640144440c818400c4010b401001d4650160780017628017940da0020a110900c1100d030198202c94a09044010700428021981c0201d0800c08000e8005a2100c0d405c042c03068940c3d0007014458000781e5044004800d0150030a0b0703034402090003007007202090004c0c01401000c2c0d010741c90058800c0014090340f034200005060984195518841500b0001c4140c43c2081075081c4507108038080e81c4960303000201d05c6030f80c1600d903200c7c140168171140d914021105035183d4400ca03070600440e0044c44c0558580c410740084c1100e80500d44500346c0000d50000c03880c40d00c501c503945c2d2046a020f000103c00e05402c80d0310340c100344c0c1064451509660b59101c480301100d0352030000906080e200c140401014034003a101a1146040380540069a01ca50030088051040154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 552785341 1250 552784091 552784097
    0x806010905041704060203090d05010e0706050306010e120a0303021c0207061d01141504060e090d0e0604080304090f06051e04180b2d010915150219050309030d 70
    0x108200c00c100728203218516031030fa41d88a1506103420114065200e0140c041d10234014075001d1901d4080c031800350810440240294166600692604002000c5a00413140b69001c03030401041e107145814001544603026098601a00e0302c50703425a01100070398043c5c0c04151040b13400b040510032521030f910040000610400001504c002078a9004140e140c40400c1c003001d59240011802d0a08903402c14580d010240685080a000b01600060010711054001e51042c0c201d034410000d145000040c868882c4d42e1036111090400401c01c1000b41a12460007081070035002070004000700070480d08070810805441c1300229000762100c0203d513400081c0c103119070f400c44990400100508144c40365a4000c840181c18076500251600c51043c120030152030030144811308444100102c0c03404d2100c2c5080240c00803081c01079655083c000340030301500300c0e80118520340c07641c000501c244200310381c070003503112500070707250301840c1c2c4c4407a0300c0b4425941b4068034580000c0180720503d9506021000b8400c926403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 552786591 1250 552785341 552785351
    0xb13050615010206070e04110f130902040b18040603080f2a0a0b04150905060108010b09060a0302100207180204060822150603060c0f020d020a02150a0908060109 71
    0x8288245040c00207401000840305841d90010541d9000c00d525a000a03681840341080b0044e8020800510018641703040c0040042409072840400758000c2c503841081c60600f00b2040e4403103110a00301e1040d03110314009940e042007049900381d110f801040c5000001400082d40956a4031120b60325401002518400400099030682501427648640c104064280786000c40400304200d0943e03802c0c5826010f070509503664005000c201844000001120401c0c20a004c5c030340c84c0d840c3c400d5841d0000e0141075101c0d42400101c40b040d043c007024a5100e01d10081804038018690303024000440e03c540709400031405040c0011540340d400b031203c1040e40401e9800169034501c0d001740100504c10250100d038001d046456000810f565904110313011942100b80f0701603d06070b404800000300095480180207a0400310040e045a410504241c07100055400755070655000d41c81c202c4c0c0311604070b8002544440540201d11564120102034141c12001d42080803110341c45207400d40c54010240d0203040b0094030b034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 552787841 1250 552786591 552786593
    0xc0b070b09060108030a230408160801090b0105040903020a0b07050d0b01021c08092a10230307180e011a131a070f030804030e031f0b030304030b13 65
    0x60002140e000c803654001e001c5550501681a869114507194a003c2094400c6d05040c1440f5200340b640c0a441002a12079823240d90b020604c1e00d030314900b03101400540120000280010060043c440d40c01e50100920343c0e035030b007000d08110040c05106026400c51055010000000d040c80e5001c0740a10003d803261511000030b091a003043c0c51842002c0c43c1150082125a841880c055144254500e941d08100000341d5500040914108009002c0070f4543d8005441e01c8081004040402c0040c0040e505440308a02102c41500e07020410411000408000d000442c00c09894501460300040c1d2440c00500701c400c5078401c070304104484d4000048100300c080c01002200007020407c1d42c8024200d0707009051580c128a4294168050b2040070340c0c0715000c20b107030100718400100710351540d030780300500c5903a09030385040c01404c140c0125011000318a40320b0b8a210185070000e050440c0c1100c8414046180905c0f501c480d000d01240c0c8189500f502c01031001200088604110520520ba4072410412241d00c2e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 552789091 1250 552787841 552787853
    0x4060509070501020c130515090f04031206140409170705070905010602010c170702100618050702030f071709060406020a030f0801030f11210106170303060303030402090408070c0b07 80
    0x74030380c02141594840004000e480c1c0340c024001c841d6000051700000c10f683c8680302c800ca09200c00310a660300480075410000303204d04418005014a000f59510300c84403005080300030841d20b18dc0113860b002d80308003221200034940b0340c02c40070307001d4855000b00e826114071013a001c040f1b0300040c4040350150041c80c810700a10390103102d60b81c01810030344028003214610314409860812030b0f448203d6040070100005510314020400440c0d202d400381d4003000a42e646001c1c05540f000784500080929042001042d01544008140c0c0c0b40310b111010b2862800c01c0c0c0b0341c1d50200300025800069441c460522102c01d8543d16600540002c10340d54000c3c04141c0b11500e001804c00f100d940700c00050006038001400400e801e503c1a032420b580c01f00825034141e81010001e002c104806810900c0d038800441400402c0d90190031903000c95a07010009100099445078143e01c1740021602160075610500008001d031500e10304445c0c200d0700905815142403403a40320000d4001c010f03000f061001c01d00180748800c01403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 552790341 1250 552789091 552789103
    0x30405040e070609050d0302070302130608011409030d0b1f09050a060504030b0408090303070632010e0f1b040e0417070b0a0509070914061f0f0f0e03010504060509 72
    0x4103100207081824202007004c4c0400e0703001d0140f540501151040c50382014002c02c0000090341c5c000b40b0660000d0a410905009040a8002e11215508014000142c44c035070705420381c01900304201450400e0300c007140d0071000300300403540554880c3c22050b1110054054034500030071401217070f07260b41c440780c148014060145c10300d80c0200c0801100304420030100c0d040100064000c1e030b2001d40d1641e04c1e004040001e2a502801e440504103d00d046a8400300726901410300700e500406000007101300304e0b2901030385200d0304240700d14001c41300400c000615041240344a140d1180900d00c4000b852100546003117901c0d04582c00c60131419a19a00744014800812801c0d080d011000001914090195a0300c0c00244405024200015240c4021440d404014854117020b06401e4108200300d00a07801c0d4020800301c00c0e00c11174011101a80003500d1a20102c1903206460050386030100c182c2d90810003159050400c81c80f450030010b401c0c0800101e0b035002e0140c6409075001d5140801c0d1405d1801c0300c282808 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 552791591 1250 552790341 552790361
    0xb090105010f081908040e0a0902030705030d05190924090b0c0a2003010216110402030402030a0b0a021902061b040f050103090f020405040b090601150c1b08010e03040504 75
    0x10707002d00300860840002ca20310141a030030301e045445089032816407078a01071a003050703003400984401c015400391aa03109441c814000c504492800da0b1322014162181e90000c0d403040003400420192000603d0101040440030b01880c190840b0741d50b602c0030084900720461100c021400d200c2042502030740c4052090050030390380700c640e854a11684409a560664148010b12030034003d8000040000d152130441c2c103c01c0040d00075590f4114601c441c00c40c1c0107103150101c4400301c40448421190500d4420f892050303034003800405c20a0740a89030744203040780081c0302001c41d5400f000a400d8010204840007050000d5030003c01840c10800f5081030f80c000803e17250f1507900400c1c0070030004007800340c81010403030f0828200003034181c1b8681040d0820186803000a908541820b061100300581802118403a03520301e01030740d80750790700c880e0404001c4000000200000fa1504c40100202d030f000040100c09503407038500d14912503550a0628252000300007140c810f50000301702042503082a0044a480c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 552792841 1250 552791591 552791609
    0x80a050114091612020d141b031b090a260a030f0c03020703080705070608090c03100b1324060503090307110111120d0b1002060708090a0209040b09010501 68
    0x440c0c100400b20300c1c09480240100708103000030400800c4940202c0312084502d0700b15400355030303591240e50a8405403a0300c2c004110044079a40c0050f449a024000d04900c1010040fa00c92941c3c41d58140d003044d060101045602e218001c12101c00250740b0751007020001d0007034140049801d100d0030200c9510500034041d4000c1e94201000d00000240d10850a140c0f200050030201c19600003403c0c04c074580b005a0300020074034000001c00c0307001c0c03040c0040c00508448540da40d0003601c0da201110951951800f4036180e401d9405500841070500f15504015a607407401341c8000c03801d20000c5554026594982480311080d032003603211840100c3c0e1003000c640070300840c1c2850ba00c0d5042100099980b40300740351000e4407005403000b42c00e089a2250400029421040d402c0f0384c40005050b21155080d4003803a1a400414500300560005017800c40c007041d41842103402078800d40e611030200f80c0341810011311414190141c0100b02e40181d403080281402a0700400c400400c1c0d182004240e400c40354103030007100c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 552794091 1250 552792841 552792869
    0x71b0b10150e01031517031206060703020c090c0c1f0516021905011103010e0709050a0503061b1e030402180f040303090501021605010e2509021b0d080a0501 69
    0x41d94001c40310700181d0030286400114000c55880340c0940010300d410000038680000c81c492440070001000e8070310180440c0410203a5181d5500700481486103d0380140960050441604140741030f1540580c003039040c40b005890312132000182d0b404c01d200d5005100c8002c40034030700d030480b607001885941d0303002c0c8904604240d10044a08060754842c4030b004601694000c0058500c10003c0a4120320345803040d20340299200d58543c480240c0c3c02d4011115100010204840011189070004151084a1001d000f034661a128020720304141c50b0b0510981c0544042004214499403040c03070030001d400304e46241d150b16030415104109215862088106080000c08c051096001c085802c1640151381402c3c00500c01420b854458064003c1940d00410310031886284e20030300406403c100362441d2202d00303032003414060766080240d20f000715590982c017105000c0c0610410540e680140200a90b150200300595541307002c89243c128000d9101001034228420f00074030004500907940540304500044030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 552795341 1250 552794091 552794129
    0x182402060a23040f0f05060403140f160f020604090605040e01062715120605070314160302070203100e0f19020918120a110c0a050603071b0b10 63
    0x2c0c1040001d1121607440c4a00404a000c008641c1c0c0401c8245a0211034081500202d091030f5840703500490f000e034042111108881070081c2103504075001c160041c22080e0600f010070b0424a1004a4440d0494000c00100804805603440780050030050404102c0400e2181c02c0c24207000540b0b100c10307540d242c03581c103240e400d00c1544440078444288141c2c0071260b211890114110700060305c00400c4040c007248100c10701240403500d120080d00c03624040c800c140078035118244214111546159403064040402d00810042c10420015160009140c600913003070002e182c00103400c00d030041c602000c02c2546c2d4000e00742d0745181400030f048030a00000c050b2000081c0c41590507070303035401210000d10450103031000488140c140301c000c42e40c115441080b1513110101d40c040c101c1e44e920080445010410140d100450f04600145040d02041c01070014200305240c03905000709500003415170010b005d250318803419480c8101c082c00c43d4160066501d05c10500b0020103007408141c980e0807058600c541010150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 552796591 1250 552795341 552795371
    0xd11130e03040b25050c090906070c140a05010f0b190e0a050a02070f03020a0201030f0903021e0c06030718060305061f0e03100501050406050a080d182402060a 70
    0x90440b030090f03940580d200001c81680b0149442580f4903d03121202aa007141440f0000070f080c807030304006840c409020386450104a40d03c0300100c40c10000101c3c4009250f0005100c199070300490003048040f12078140580c6d5440e801e4030480141d00b20000e585581c4a02d00303141c800d4161042c0c0600e01c1d003248020b8181410200117680c01004031010644030404a2449013203a4110b4040a40100144c10614407906d00291a4000824281c1c00030f0f050006043d024480b9200380020b840d0f041d0000c103c00e58407080b410401801c00c051b007400c1e9004101321103003181c544100a5108040c19561905100c4140e281c03c4240c81541d00400e0801d864002045896114070725030318400c1c1d40880c2a00310072003120b902101d101d0202841031303825000b00403245c0c1c042e081541000341616001c0701c003406110745540620a50b5a80c03403050b14203540c01860103d11003401220320b84200324506130030000782074a4244d4515014540c0a9140c200148280040520b56051242c00c4e000b107a0b070302c01800f483c1101c01d024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 552797841 1250 552796591 552796597
    0x20f10080a02070f12021510050a090e01091a160504180b190603091103030a0203270d030c151a280b0c06011d01030f030e0d11130e03 59
    0x40307049640002c0102c1406648004250625401000069400700503c0000d48649050034070a041007100e1000c20171058442d0484230a44001030600703e0740c0d92801c0e440001400c0951482140c0e5540d0750074280100b0100409c2c4c000c280c10070b40c0f201003241010025030340c5040009441e402040800c2c0805c0c00007503004021003100783d88044001c00c40f42102d800048020988107448488810402000580349401d5003100f010320740a10110784448000e042450744078403c0030b0070030b40140c00421903840b0b00030400306566900501403055020300710b40d0802041011400b4a030580c0842da0071004070081245603d0011103400400c041400800c00d02c400d002c034180c10801503184140181000c0c603160b0031500c001c0e151180f02e084c21440782c903591140f0391440340d0b02c082030034081405014008110341c0380480d104940350440d022240c055a00e15181c1d00c804c20340e40e003011410004050321420042e6540b18800402a002d14900000b4014010401070030b51802180500842e0601c50690a10303103012081d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 552799091 1250 552797841 552797851
    0x30412020a120e041e0614010801030f03031508011e0c0c0f03080c0906030a02070c0501080f0a05060103060b070c061d090103060b0103270201030f0501050f01030903051b0604020f1008 81
    0x180300d4043c8060002000744c103602d4601110190800c40c4d80301d201101382c000004850015020381c100140850045a80000034040030b8000f002003550000083d10903407003c0e1151441c0203a02a01684a01d00342d42501e1910b001c42070034180c403220356a50740d151403080401003c180c1c20078903030003042aa00c0e0001e040020301c000e410301202e0400241003003400000c807a107034000141815a40c0c94441c1181c802034100383c001f40c401d210005c0700810303554001e010795400f44a082c40020708541e80c100050b4090140208154101078660400043e85c4241070003070032840d441041e140078440d042100003054480d0b07a101051180c0e1802d4030040542c0c488108803819207800250201d8121f1440c001a000741c14582102c0114007040c014400d0007006414400b100c45101744e0f000d0040c00c2d41c0d8540c08054540a0003640d901141c1403170605c10320341c0280d11184400c0c9c0300e8103100b8140020106040d24240c0074544403416500010208411454241101d40f200c00e01111400c00d5040104001014400300800d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 552800341 1250 552799091 552799097
    0x8010f15030c200604122f070b071401050a020301140f0f090106120b030d05040b07030314090a06060512060601110703050105070e0f0111030f090a0905010803030412020a12 76
    0x500c41da0380c0391080410151010040800f034140381c15600710241d81d2682200c0648454404d148284100e034413520258007145096130031704908610000d1010048440305044540300d2003a00c1e00040c0c1001c400014002440c01130340c501c400401000111401c0d241c006103009081d0340304100522020802c40c150840300c0d50261079020741800d8081c00720b0444520368a42681c05800c9000004c0d00d0f0364017135038140354a100c41e0b209014a00d8407409156440152092120210b135040c8802e110111151001c0c000581c040d26012034500075010154000300d406494202c0113801900001c018000240214001000c054481d01e44948001090035104d120182c00a0704010010701d130780c0700c10601000380c24095508030008200340e05017803002800710703030300c2c40e58140c0a446d02d0200020b944d8081c00304544401d000d9409580307401c0c1035240b81c0d5401d43c0040704059000521700d00c0031030403140fa40303e058081c0292100071641c908140c14500c443c000d05064030801c560100c00b2002c00902d401003403180c0c44650781 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 552801591 1250 552800341 552800351
    0x41410090b0a0b040e091c090605030405100903051b0a0b010302220c05030a0507050703081f03050f0c240405040908210105010809010e12030601030608060702030a08010f1503 77
    0x41c000344001106510500b5928404500401c0d5040041c08241c01865018101c03500b04912000780c09000c0c1d0152404404205110820801c090041c4015135100d031103a020f5460100401c1002001c0b91078401c420f400007000410703200c2074001c2000c40c00ba54079070300d40000c001e00d0304980d452407001041404001e00807000440210390080110240485d0791100326020304c80e0f14020000100f081c2c0044540c02d2116081201003811540900110340c411034150340c54989555030305900d07603c0c10000001040303100c03207203001c0040490b10900a84162103200d174042d0078089409400c000100101150007080f02181c410424044410360f000c035070840c5c4040d0350100c1d080e00e0b2814064000c1c05803040501c041410070b00c42004858000580c0c40c140c60742603d0b4414591601300700ca43c201c03903065454618551002000007070101108c800703150f00400504d00410b2954443d502c6504020b01500c0c8100542d01c0400d412802d20340045520b8017620042c007540902c185041d8002442c3da19090260090555032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 552802841 1250 552801591 552801611
    0x110d0b010c0507290906180a08030c1005070504050303040303030b0d080c0a05100e0309010e031228051908130c080705031b030a080a0c1203020904141009 68
    0x3515010310082e400c00192540710f5030380d0944041308400e1098400040c82403086402c0c2034003946003503030070807032002e8015428600504203000070034a90441041c3d009408100000c0d440d0402c00003008001103c0b0054003400c50403002000c142c520140511081c400c05010500c008d480c000f0558040b00e42518010501600d02c1c030106681104404c0c014101000c0007890722181c0c900080d0b4200940d101d1070440d596014800540e00488030303c60a800c0b0290000c10000b099503101d030084010f01e050040a40b80005800100c00340e00f03038020740e07010011101102070081c0c0042501800806554103044c001c1c42d10650560700800150005900e5050103c08404980401c00d004440b002c0d6603400924024000c1d00e0750a1103503183c900e845410b200c0c2c40380300e2601140085030348071003512450240040c40c3c0d1f0012980c84071065000808030304d04104420341460081a088042c0c8a0310048580b00180d540d0807110900040d5807121240340f00d02c8103c0001e201540d902c00314408121520584002150011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 552804091 1250 552802841 552802847
    0x5070f142e12020d09080405011706130c2a021504061205090a1a0a0f02210601110714010806030109031d06090901080709061505040b130504050424110d0b01 69
    0x609881c440080d80b178100842c2c20803a0010003041a51400d0302c9043c245507101e400a50241002c90710250081c0e200c05e00044080403a4108080030500c40c201165003a02e10654000c4164003010381489144118000005600b0503003c14221451424480c52909080000c050082d0701a000c56000741035032400003d05044c41800b1205400d0307406080c00741800502840e86010010603264074004601e000c1071078940706c0e11842184d820010441000c0300444424041d400300d000010b00071380c1071009000303607620031040c244940303409801c08903c030901e1a05c0750703c001044100010f103198020b80c507286280b004280c12055000c4505001c09081c02d81f241c0080c081481e5000724a0361a41200065001150b285800f04a0b541607494203070080022a0391914072504a07101c090640300411400c220070f0043c0c2040a00402c50210320b25840300c84259900042011500200c03400d454004131000c598080c1030390124440f0301030340c41d0030060100c1203607000410070500c9008150001d0b03d079035811107226640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 552805341 1250 552804091 552804097
    0xc15051e0714160305060105100c11061315170910050c0c010f05090f0d0804151806020c0c061e03040f1a07020f0105070905090405070f142e1202 64
    0x20707402500d0003540e00341c1040c43c84000c01e000488042c000e45c1c0000c44c1d14200240120160000c03550344031002c052035202d07100110b0004000c55080132003000001c11118812068400500310b106040c4400462a000200910002505204c00012060038844e00c6900083e401c0c010000100d40091280c5403e040701509102e46140c0040320350800030052134500c2c0076407007644110294003c0c0e5200e2420b40e051a6112041c07114080d000c242e5050208001c16081c002d4101d54409407580050300c42c001c0001c03504034403211401201c2403500021800d094501c01d0100078500d06041d00c1250414110b41e0910119004102c44503c0d41c1070044000303014000190042401680c112246066101d0b10010842c2520821a000c80c00761140980415002005108080c401c0840da035543c2d01150808042103031802e0081e00c2035416104880e004900b15040c507180f1001413000d04181c40d0404442c10601c1050b4129120303c4c4080900c910070f01d0034003102d06c01c0000c0f0a00140c50b01c10840560180c6d0303000280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 552806591 1250 552805341 552805373
    0x31110020c1207080f0c0d080a0e030703060b27150d020405070305010e01060504081009020414090309010336080c0f0c0109090c120b030a0b040c15051e07 68
    0x103420281c82c4889040042550015191900c085d00c0d1800c1d000c032416030b920082d42d140c240e000070481102402050b2000c02801c2084a03901d0100c4081d4081c1c0c0000e46011200d0708103450740d9070b40301c881081e14030308400945812014030a486640341c1d1500c0348000102001025006219204407255010b80d0756050081c1f40c3c581c0c001c8c010005420b1140c2c005004007002d01404191104640001c034031280940c0a68041300e115000804064201e03e0204002d004000320480e0880e1700d49043d40070141c04551454803401903a4000e64507060207070b0005080c0c9159040b100c00364071407000d140241501e03c0c900264031905100c120992883d00e0b03c0c0010b000c0c8520301c1c92848901440710714101901000c9204000c6180998821550644460100007281d416144040201c1e452240320320342440faa07040100e80102c014143c0d5811002c0d40c07030301080800c00312802c9600d01d81c6044140914003106038480340307031105403812a00381403100e059504144901c141d41110110080307445400c12102c00a2803d0389 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 552807841 1250 552806591 552806599
    0x9020415170a050303060415030807031e0c08040e1302060f07060507030c0206070e03030f0d0509070801020c0a14071701090204060504110405130608060106021f0501031110020c 78
    0x208040484581859545000704146840760340700c00c40c41403100082c00c21885410502562940d20340c0005c00c8020500080c0420b4180c80b020340c00001308104901a0003002c0c000d498090300150000c9200f540500300c244a00140104a070034032011030318000076030702540c0d615440c071203054031111724900d03c11800f9503009600c44000241552159012000707004030034030441e000e103c1900c0320302068099812607840c80c00181c2c0721600050003a41300321404d04c0c0c0650040c041d40e00c0c20881f0f01c042c8c5180e038008022009100c1d103030740a0060620003081608000c041410017103051a034440501a2140c58418000d492404900705603c501c00c1b051106d50300070042219402452000e4511043c0640408082a481240b170408000742038100780c002c000b01178224030810f500d02424402045800d01031901c8100e0450b96590f0301060851081040c2c0d0b02820550700105a05072032045070b0261802c2074001002c0080c20080100005100d101c9281c2038850b00321001c800e0980c10240803403030411145d96003a40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 552809091 1250 552807841 552807851
    0x715060f080a06050c18041802090117060a020f0a0507060e010f14150907050a0e0405070e1e0109050f0f040903031506111b031507090905061918090204 67
    0x1808000501d80368103c0c03082c08103000e203607240c0352000258043c00028100c203c12212818002e0300e0a60300c5000d100d0b4458944451038200341c5c0202c0e0425009030050380d03042c0f100c000e400542500c1004225401110004250316240d01c3c0c0902200c1800b5040300d0a051040206506081000b9500010700010002000b00303c12100c3c00145000380480256801c0c000c034030701c0d010500031644290441090000540751511a40703440c08115041da0100f6540c1040000075151000710b90303241d000c0c41c1d00030040c036078544228104103c00c015030030300c01c1c1102c034203034100d040b280d44000c1c0d801400900440c1c500312a0005074840d110040b401e84105081c0316a40185496904070030160980d100e84001940d142034948a140c4954041da61485000c080c4040380c1c0c481d10940180502c54030060180702400781c00d5640b400c0740c181c0316080028041d00c020020414102007400351086910846034803480403205422a1415818060f0014245001c1c602e454042c10400300072642c9142c0103021601c1e400741c02042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 552810341 1250 552809091 552809099
    0x50f0109091505120f1f090204150801052d0403090905190605031501050d0c0803041d1e13030e1507050f121206150304050309030f030a02030715060f 66
    0x1040029901403d4891401d1041151000b1000a00151840c000e04000e180034501c400401100a11102003d0001c0f501c1c2d07000c0400685035405801c400d10b5014400d400c245040840d410b00795000207010b0b1948001e540b24403124060022540c007600160b080300d040c9140c45604081380d0018064102c58045400d110511060141002c6226100309440804000c01c9850300308141e180c40c84e4490384a007100343c0c00011f105a14100040750b8401d48070390762259000ea55030021605540040d48000170f1810000c0d6942038070342101d516a540241441c50020010b28007034000110840058031214442c0c1c2208481c008160080c8500040800004c064102200e0740c1f0b0481c4401d43c0c4091400c1b6070b10b01903a03c6c081158180098400103000000e0401c504126504035203040721030780103186590080d295006000a45078490007103003d2400b034000346580740c0b101000d00d482c1c41d211112441003903000704501417095501005494517990700c10f008502c02512211114043c0000b60030a812241112500103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 552811591 1250 552810341 552810371
    0x2d0a09030c0b1524090603060402070b190e011b030c02160b040305101103040201110102070c06031406010c0201022a0604060f0810050f011b0f120225050f010909 71
    0x420f82c1e040710349255400c000309400c460802220001c2d00c0b940e9080c8408505450400041c56011801810050030904a0b44954100420545c1c00500044189100040544090140d10b919007054070091086916518041a10341d030380c01510010543e50381001e03843c0b28070900034901120808a2480b03040b9449003580340310b581c00751000325214498200810000300302405180116180e4038804d509594440d0019942d5142c6000000107a560802011000070803540f40c1c1c401404155400052505006038070780711111000d07080606004400100318010303030b80007031901c5801c8225051030640d03000b0075507c0266103c120798400c0e403015000c900403811551000d840c03510003210b43c4c1c07050195102c440b0402070001c00c1c1d00525400038200612500c06500943c40348544500b0240002c048030074030b444814500340304000c21204042da080c0c0c1d641f400e960400c802c07040e014100c8038000814a10341c4501207061102d03c02c1038007078441840306005981c01819004020700c840300050004c0c81c1010102d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 552812841 1250 552811591 552811621
    0x20a090e0d08130f1b080d03180b0105010302181503070807081306050411121e1501090b0d0807080703080c0f1e0903030a0302032d0a09030c0b 63
    0x65a0244248003504912034803800c40b0034010403400c0a00501e81610391140d40d50481d0a640c00e644192007009000c0081d00135a94100041080c2c0018082014000e00c0c020305a8484580b000d00600200b06044003103000f1000c0c490460783e003402c006955041d00304401c02c1185481d8401c5074841c4620301c042208000500055100354101e41c0e17003c0103035464400a41d00d45100f6a11080c2c2d906008041400091160b48083e822074041c0c0300c8048081242c40000e100d00340d103c98504059002140404500c64101c0007482e500c250000203443c41d01184003040c0d0070040148500041e10780c031645000200c0d107030165402c0300c0d641c006035016a12035003404d15615562103010114000b0300420000f80182031160305541c00d0340d00000125281c2900000074145214145801c1d40490104021240c80b586e01040200314503072190b10050b850780b8120b146080c102220000741c2040360f032104071140084080e08501a804044d0b82c6002038070981a082c111413101074240020824000d035018480d803a0a040c0345 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 552814091 1250 552812841 552812861
    0x108091906021305090108060408070c12080a0f0504210804081218030d0e0909010b060301090915090201020a031112030a0f05090c061b1005070801082109090c07020a09 74
    0x45038025500c0017800160385007441908210f40040c4082030000740344800401c0d03081d02821020103030b15100c0a000c0910700e01e12001b11003244000644241140d0010981d680c280d0041c02d050341814070748119680781c0280078944020050840800307008200340301d82034030090252101100c20511407414180d00590160302d809207031110382c8010109516001034414490310065803080103a020580512609002c0039003000d105549030b0854006039110040130794000d0490380404603100c1c0c460b0800c600d16480380464050a42e080c20a10f40160340c0021701c424030607915181c40d4100003038a0040a0800d49050007000d40480004140032810040f6081610400460001001151a01c4030343c1540d528140c00410b401200600850169441440412907100744007003c0c1c0d440c2c00111020b2100b01d80040ba8584d000c22101401404855403c100c1185608002c904803466401e04000c4c0c180d8500038143d000340300d281050006040ea0740b08000f520040b81e07003c1d04003090903444644400c054112250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 552815341 1250 552814091 552814117
    0x100f120204080c3a0503070f050615180f1e0109060509010b0a0c060b0301020c0a0c1502120708030601050c010207060603110a0513050403212c0309010809190602 71
    0x1080c00703902da0a0a001d001c1800f41d224680540e1a2042d4590a078801c005458a0100340320283c045234913445034618080c80781300a427003145404e080c24180180b5000840740107205400c20012001202050f0070741090641075455a170740d480108c03020012034100506420516503000008420203540c0004090b40d504543c40080c0340c0c0c941101110a00810b4070120000c1c0b203d900400c0031400035803052a00030800340c000b614140100e1003840c5003403405070048030511260541040322103032801485440001500c0509074458842003c00414000c080001d46884000004601180e02074011180700315620300080d0f48451342800c2003c000c0440e03200907030320004041d401405901d49042c840c81a190024420b543e6107025151120007030034002d0003113081c407104e140c0c00a1503402043c40c5007400951410080360340a801440700780c6c2c100503040800c00080700c0e000c2c540c0b460b400100a89a82000c20301e071240f529500d03c6580c0d4503100306e8100803001380c01894004824481d09800800b01d801d9594 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 552816591 1250 552815341 552815359
    0x51204030501111801111009140106060912080a0216030f0506060909280206040b070c06020c0a06030c14040602070e06180f0c0903031204060b030c100f120204080c 72
    0x2480410314490300a011650040c0300385180910740c0035a09820080350800204c4062881065007c4202c84199100b50780d0000d5603039080120b1102405403d01414640c0381c802c10140c941680d909212400c801e0040056001094450700507200700310303904000700404281e4045580c1c0341400d0340c50100c5000280d40601404000907480d00b00740081c5801049208018200c0051411040030072140c40e1501c2c200c0340c1541c628030f501690717608006d0009040c51006c62641d0700010b14180c1d0000006920007001d640000400ba03400b941c880d1500411115241404100070100072800c0718001c4202a40d030660540200c0c0c0850303400e60004598041d40e01c03d201e494865211803040165044036614000c503260300300400290300100000d122074002109413012130910347c02d900082e06540040106a5030070003070500b0481406400c1c003d00129000a03006000d81740c02d50f9000c14590301614045e50140000700d030b0010030651141c46040c01c8040d50180440d103c0e501c60b00682e407541206815070344648080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 552817841 1250 552816591 552816611
    0x803160809070620010e01020f0a080a0c080609070c021513120b0a1e09150506121b030c0301050a05040b0c0309030a0e040e030d1d03040605090409050703051204030501 74
    0x74604203071001074035210341c1c0086144c09003540d01c41c2160301103480e540351204c40341804c00034005061f0070010103003016101c4025000091080c0030007040750100c10f0a0000e603880d00e580200056030040c10503120212199a4900c09071401c0059800094000014024080c00d942680000d000e4101c11003c1c040c0c070056a8445512190941c140094240a10100030900240a40c0e0014215161458542ca102da0352000e601045403c00101559440c1140300c84090701007d40c810307558000011949031400d28403c1c610300d0341d80c400d240e03410503500c120180800d040b42d070204040036110b44020002e0100d40f0707200c4035400250000751021500d9000c0c040c0841d640c61030034000c1c0c0b80308119810086003030051425040701d503034055042c02600143d0b20b110080301c0301420b01c0144942c150703251020078140b03500707290b02c0c6010704250f941e1050b0f1b03042804148030f055071002c110351480c00c0895011030742401c10709000b42012003545c002000c510540c201081808050f0700a071003101d014078000c125410b41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 552819091 1250 552817841 552817843
    0xd3906050f0915060607030e0604060323090307060c02100e0106050f0306161404050d0b0f0601050a050904200307091508061012140a06030501180209040f08070803160809 75
    0x90f251045003500420350003d0342c581807031400703031851600a2800c142c0501080340440c0296005130801000240c403400242035110700c09003a0342c00c2031300ca02e51461440c40c08542082d2240a02d9000415180d241d08204032030354404c00c4210076840100204020f240c0d91500c07200c3c000c022903c5554061948156001c40310b14001c91464070035500b14152964807001c10301d003281c2043c1203d80c030b081e4140c824031000c0348030f071500305006880ea489044600890f040464242103016802020541080340030003d600c401507002c01580e1031014143d5020549080d6107a0b807100b194540151a05840787c080f040120450303200d403101c02180c005074407240450820100856580c002110296085200501c0c1541c0303140c800c40308644940c888900c000f4000c032041c18a91007081b03003561601d9410351101018400d10a00784144080316400c0034100c80c3c40030003640491000079004001900c0c0099554980d014000d0f039204844203141e120072200d07582d190042c05400200c000903903000001d012a4006004424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 552820341 1250 552819091 552819103
    0x801240b09060318070b03040b060102060906040c0b0d020403081602010807030b0303161103100c0906051819030b100f121104020f0903011a030f0d3906050f09 70
    0x5030180141d85556a000004010300c000118030031151702c1503800004e900d0300e50002950150f80b0a40e1001a1418900c000a207441c80140000c01c590704104d041c4400603c1120002080303031075004020751501c50520070b400080c0101e0b0704c0504032000000311058500004041100024401d8880d21101c2e181c20350114100c89400740c00304d405a0040007103290076140c1e00001505103108411400d88400ba40700424200103401449503280c27602c9101c4034155030381080c1c05801900551802605140507600000883e00c440060140074410103031549685000000081002d1a00400200001d003070903200c8100740440c0c0e106860311450714140214400b00180b441c0511075402c2980d0250717085600041100940c0a12a00d00021004000702c62150314280071b00c81c500d00f40c902e2202d290300400f00a040c1811185840c03005940c2001100703c22150300800d2011a00305890000742c85c0c80042c0441c100d2089041010200d5401e280c04540204084e07500078070b1003144400480210b036103c81d644c182da038038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 552821591 1250 552820341 552820357
    0x30f0408070b030910020d29030f0a030206041e0209010b0d1112150a0f030c0812120c1309020f0a1101020414090411042a09030201120c090801240b 65
    0xb4020316030040c584200ca1b0043c10309080e034145c00094001c107441d6403100c40c011401e00c6c000002107d0322044070f18603050001e146041001409080da420b11980d00944820005000404041400303861441507c0c80541e00310381554080c00d210600d5842d41405031040e084242c0100f6518140800762800d210214142c95811260105448a68030740c580c0141c52601a080800d82010210394005601903a07020b440300118012100501603e00b0030750101e00781198207104e03881e541820800e0480c00e0007003076001075201c500c1e40301154076030511a000451980c100c1d40801c10303042c000300d480b9406000040051504c020039440349031080c0400e0032114281c0c0600d00c40d0010003403000d00d902589080c207580c03040e401031040b02c40b9400260f4040010302210505052200c09048140204c00d4840c080e503041c1d11100c0d2182030060010340b03594002050103031030030400b000304d5440f200844800350241c0e800c1800351160800a000405581c55030300001da4146054030310140301518000394401c036100c22a2486 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 552822841 1250 552821591 552821593
    0x20313060c02010903110f03031824090607171b0607080106080c0a0221041818061a1005220b03010306151a0403020907031a091305030f0408070b0309 66
    0x1031403030360b101e81020941b1002c02940013149014240e40a070b5061005111940070800b078041c07041119414042100040c192000c81111140c2c250784400a542c4240c407500402201c449544040c00d20300702030308407407011508449000104055140c0f0702c02d1f450010710108400100e40003650340721804c4400780703070a00c5a0408a01c442c00440c2e510344c0f08800506010309640102c03495006000b0508803d03081407910300c42ca140003c00c1c140041410150809034008802000348000c1c1d10500a684c04c0b001130010080000b580e0f2200300b1240b15404a00748040100204650619040d00301c005d4001ea00001202468105010b405008074140c580c0300002d903500003a0756404d40e0f08580d2170340014803480c000c03040e04681162001032080c50855000ca0031007284008552111714510501c418500d000d01004145400d0101805040c45d281040165007801280c150060b038131418101082101d1140014000703000000ba0106150b0310940140b040728a0101264016586c440710f45045020584a074081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 552824091 1250 552822841 552822857
    0xb04031715150f0f18010203120601030504062a1202180d080f0c0106030c170604260a0e0a0603110307030f020d0203040303090317070c14030d0903020313060c0201 72
    0x607604000a207035619541c40c03403400f442c03d0a402c0d0851643d8014014000c0042000100101c0350348802091000b10f040038002142002180080c43c8000b80004060504156030b5100042c14401e041c0c00504002c51000c1c80480b2500f6003503080c2e0781c6d2400c00300704240454190081114100361510840713031f440e240d040401130302c00607400c20001c49080121040da0b282006001114074441e011004040741001d04000082c11841c529080e480c40015600119103540350500785070140d10041246039000c1d510044110f02c081100184451300b0308141107500034802c0120303241c00440c4e00003e8850000701d00715140b660710755403050124241c03003214402001851042c00800c4046001b0381103a03098040b11040035040086150845d001c030382003180e0903030020f0307110413804041c9a0048040641286500080800f41c980144040e00501000000034811210315502085005041c0140c0f50a40140f400500c40e040071800c0081d925000304100c10a0380881d0080010307540c1c054288030000a50684480303007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 552825341 1250 552824091 552824131
    0x51522021201051f05060415180b2a0307020f09070903020907051216020c060a14070f021201090308060909010b0a03081b010501050f090915040b040317 67
    0x2500450a40201d821151030900422011001e001d540d00c642e404802c03921366246030211801080e0130a0384814056002000144103150204100c500e10724900d05110601017402c81c4459003550741a4000300f51020b010404802c0c0c0306c00c20050507000d95040011002d10961070134995161f2040200086d84045810000b01150038031000c1d065000d1090f0815030b80300c0d9607980228152100440d0032600041001806107815888500190741050f5000410100d840c01c2480181d5142040c03c1050311803030010031307000c001a2107100007011213082d05210a4548a1030700d4504481411907100b00d00c903c004035402c0404400501c590154180c041d03544410f035842e49411b001028030041c102041c1c030354035120258680d89855044070b005500ca685c0f196a543c00e0404000c1c3c088601100f102d030342c2d90414004020741d80d181c5070340b16217002c0704480f00310468650a002e2880c100406181c3c4082500300c038100414440405d070354500c07460203600e5404091a01c0b120341410800d08464889800c0082c8940d11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 552826591 1250 552825341 552825391
    0xe010e0f01180e01030506010608071107030809030a0c0b0307030e0319030216051e01050106030603050a060e030c0a0f050606060f070b150409110f0604030506070806010210020a03090515 82
    0x92940d90300d40200d00b085803150020030040c00241c0003510f01e548404c00400c051030740a010310780d00c00990302e40090050307001c1070001c3c2c1310403480c40003a00802c2c02041c013078510340e8140004007085d03621a0030300160b2542e0b848001c0c5c26030400c0356140040ba00e0103001c0d211201010085230300405440d01c04406c80a07161105034025080010310001584080e140d040c000b6504010210b40c5080404000e581525140d5040b0300f90b48058110b20105030403c03400300009040000c0300c0b19491341c09a000301e0b81d01000c1c3c0c3e01c5841d6000f03903904051035103d0010440d00740805000340c004580d0041007503440c1603403410300303100c0382d0b00c1010b10f481400642003103030001003070100051503000382c02011404941c0c141d0200140c00e85501da070080d522000e611451040030716003100740700f03100e101c151159428503145855140e203810005100f10b050061150008455a00c284a0110100c030030320000c5441d100c00d800018001c00c007007032007203901d44039001c03104100142e150380f210321941e41c280d04005845000d881003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 552827841 1250 552826591 552826607
    0x1503052407021c030b041e0f0c090501050705010b031e010e03031302010c05010b03010f0605090901090f0227010f090b030f1c09030b09012a0c03031107120905010e010e0f01 76
    0x200c01c05035540c0901e900ea903140d000b80a840000004104058003003601c83d11f0840c1c60310310f0000c200741e20340480c05082d00c0d08818680d08852003400c08a84414003410014003510110040c15814023500354081d8403503d084c20500e920b025410000c1001c0c02ca54140315580388016074400616003218664080158410703490f20b014144514000700d5040c0a4001290030343d880060a4926180c5950b801e00c42410300101c0254040110002444007a8841e1581c2c200d541d8181c0e0040e0056051420100c07140b0549814804000c440b060f00503501e41e5034030030311a942010b5002d81c40c2102d08140c0d942d5294a0000b80840303020340c0403405401c5446a1118010200700c00035035107414058400d0001001c102c200149a104100300800414190100e116101020f81c403408041c01503200041040402c039401000e07600c0c0b0035810f00340024104043c2c000d52221780615200203080d8494400a00e07030a5a00802c0b98044450a81391b1802d1001d8503c01500d1b800c4001c0c110540001d00100651002c2d8811515 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 552829091 1250 552827841 552827893
    0x10801150315080c0f03011404020103180807050303240a09020307170408090306010b040f050d020d0f0f0605062e03150b0414060306060307080a150305240702 70
    0x648502100c002070b107840c0081d880300b2040c1c0c220b04200c0c1d4490030655032080c0c107031a00320020816511031a03d190010f01010f44080d04169480c0118441c0380000b4a44404030360f00b001c0e148e6102d031450728085030307294401c07101d5966451809143c00100c80c0c101ca018141c078003006150700c0c2c220781448130203402500014401001c0040001e039001c100503640d00c0c80d6010704d0041541564a0a0304001d240c9021810b900a084100042200b00002420b02600c201512821a06070207403018600004141c0c21a01401911401444801700c08000d12030041c1745030544103a10a000c1030342c40e80d04008009034110103a040340c0500407604c02c1010071100903031b00000031505001809180e0222205a2050f079030f080030380401c0c40000c06000000169035034000248040300c1c080c1c0b543c0360102c04105180000f90030b078405d0140c09000703d43c120800d40c002d21010500d2070015000650303203007003182e40c070500e03585043c1e400d81045150030940e48035812454410f810380e80040c0003c1001044241c5082c90b03681e5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 552830341 1250 552829091 552829097
    0x9010503060f270103051507050d1a060f0c01060e0613020306150307080406060b1312020307030206210a090c170a0203060a05060301050a2007020a030804090204081b01080115 77
    0x10808000300b00340305480483c071030b14042c100069811440c003d850010200c0c1c0d0b0b6008036606008120305a03503c9401c46016600b04240826180a1101c140c00d228240c146003a07800540803600d996801d151a001d000ba150000f00240000c0e40da464441c9078110055440313581000c4038800e2000080c1d944e40065411990140048150188081c0c03207030340b142c00030f542d280001104001803000303001180c000c090281145207800ca1030f05002589140c1c9014040c403030440a0307510000318bc8107668080c00703d10015600507006039603804042d14428200c021304042c0302030080000002c070780902d4a80c1310b4040880c3c1c0c4200c0c804101802c100150640385000e201c159071905ca40141c010040e1030601105c0d000740240e80000c50941020400c050a403903004107040546454220345503503074000b441c246044400994411342eaa00700f5400400d0341c04060b0740015000320350005000400c1c0385242c1c01001142c201c103090350b02e81d46004824084240007002c5850014201c0c1006000b64083c101403100b03a071000f81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 552831591 1250 552830341 552830359
    0xc251502180a060512010608060609040c11070906090f1103040f0503070813090b03030a1707030e01021201030204051b040303120b03060a060303271e03020a0312090b09010503060f 79
    0x12000580b0488590401c200069000c00e00e40c0c0d41030007400d901c601400560600c038015144c0440030038501c0c0903100000b4800c40c2c80348184000240502c20f46078100c0c05001c151943d054884c1c244d400640341500c16031701e80c2490481c46035501c00380c6e0300c5144110101c011150340b6580362038450038441c208005e0155507078002001900000b600900007081030740705102900a180c0d2612461500700c444254985005c0e400c00c0000b5030304698002c1c204401030001801c0f04815031600c0c40210700070080580004115840020f0815030b490980b55628126071084070203210540d20480501d0400c104001140e0b101601804184000b074000d1143e0700c1a980f90fa0300024552210301e0004c1d14195007074030401d03956582d40308203005240d804810140f2400000441985c0200c500302c4200c044240342c0f03d030142da01c1030200070240c4044080c101c10021500240003403480d40d01d80c1030075102d40040c04625008100000c200140c000300d01c0e0b081c2ea0780c100c4141c442e5821a561f11080c01907101440f021181e10a01034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 552832841 1250 552831591 552831637
    0x10b0607062a0e04060b04031208091e0714030703120e0d0b011e06050906040501030e030405030d05030106021903050412020a0509090a050609071226030c251502 71
    0x300e8040862820b90b60303401c1c0700364070800248000c071062a0400300c0c1c2c0480420061004c222942105091503400345444c00c01c6a541c62100742c00c00c00c9220b0101d41c850031b058100465580c1c0001c580040d1052429003c40d00f100361010150b5030442480001c5c080019080a2902140544080403591101401c1c5000c0e8000580ea501c211030b03002d81100450740409689040c15500c01c40c03218010f020107080051802204c100010905c2c05644034040c101500c03a44007201044003072041e0b400070107014013143d0809006101c094015082405104010b100311840081d100c7c0010030882021501900c401d4981350401d1700404183d10b602c40c0998120b090540006520b44030465428030a4503c0b4002e00044565450300504120340034003c3c001c0356020440500140100d01c2903442015803280c4100503001514040309440030030301e1100c0c48140000300c01c1044220301c2034010403048118000e070307003640045881640013090419801410a40710075003800407907449030b402031201d0320020000103030480503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 552834091 1250 552832841 552832901
    0x71421060f1b16061407050313050327330d021303140d05070210080711160e0c120109110c03041d180d03020f0910110f010b060706 58
    0x24443c1c00c4a101201e02403418460244180140c4668036500516a07091042008010b8003001d800c140d00e110030420300c4e03410020100100c1c0c550002c1d440c91048074003889403d103901c110074007031114004e0022242d820810400b401100f043c0340039503d8030314480e10116012941c0c40d0090580ea0700810340c2000b800e85501c04842d0014003d5101d04524000c20141c0c03034206082480d18043e103010b0040a0000e000142e8628082104003001403401c0d02896071141c1e01125404544150101c40f40141542411300750600c0025100b66500c891322641607071200c80c401c1005100b0401301c3c900100c0150300500c50080e00c0d8025030720f0903000e800c0e424100101030501d141554841e520102c03801008580098104103000c0f42c20740d0144c1c0151000c44c4070f83c08031100949510712044800708055000812222220b500320548011480180c03a41002e03822505000d00601c2815512185602c02d01d11500035041050182202102c0045c100505185540e5038240242450880c2602ca04c41000448001c01007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 552835341 1250 552834091 552834097
    0x80307111005090714031c091a0901090b0f1602010504050406290a02070b0906120f0a0f0218151b060a0c0806060301050f03010905071421060f1b 64
    0x2007510310010700c0e8203000b00c1c4039240c18071590046804003a00059040c20f5070300403440807000400362500141e89540c0750740413900b0300b43d0f0340c000038420b50806083c4001c90b02100040c09504400b80c0b12400005e48558041202d070241103890078003100302b0400300d10242c12921540040c80e206040080c141520b0b00000b60507030b01541c0100d2031620940c40308600e41c03180600000c5500c131003c2a150301c0e2103440c4a00035140d902e540145141820000364840d407a85461003181c55207020782180114904007500c201202c413034151030540301b0300e04204010608080c24800c9560b070411010340504280d200a0038420720312014001207034880018441918005400000007800c4468013020707003100c0c90281003080c111444100030a080010b940c0400ca0b1648401080360b054840c00c4402030481140310b0b0000703015058081d801031190161040000310b1081d0703001092030380d10007100c102103911171500c94424007044420b4034800607030102c004140c1e2200380680310354000c5005100c00240300350042d002c0d03486074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 552836591 1250 552835341 552835363
    0x611070c0f120c1e0942170304090903033321080703020703030f032009030307060c121a0609010e06070f03021f0212060616020d0b040c080609030708030711 69
    0x40700e005941030740e0222145019000d40b0040e090050540c9146031240700300c40ca8028000007d00945030100b040c00304000f503900400070b0710000c0c0243c2800d40b070010b014201c00120b410707079285648441c910034403104a000303840742091041703020414640040c80d400004024040e4080a603002d01c00c2c0301044000c402803001d64082c1d0002c150040c0741d490018030003003a20302c00318209443d00344003800942104c0d81440249002c041d105480741c0c1c1000c0001c0c00c2d07200f20480146101d14048501c0b006a40100d20f030700391958900c4081008402c1e8040c02000301c10120010dd901910401c8142034560040c07142807021040a440d81b414106035646101000b051004140c0159001d0309038520b00350840c03078800c8640d03c810700c015401c0c4100525135866031000030389282d00c42e0710080360420001800f00360701282d240e001091221030810390f08280c030440c502030b02e0075608518907800116482c3d17800030780781c4d008104400041d883c140c41d5803980541500042c00003003c100c0c108964001880c410400d00000f1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 552837841 1250 552836591 552836621
    0x1e04050714031006081609140114120603100c0c06020714031c05070f023a0503180601030c060509031006150e030c01050f03040611070c0f120c1e09 65
    0x381c04c214010300301050042080c100c520361403181000080d4030064003c00c641c901c03002c2d001904148001642d001c81c83c003c11a10303800300441c500d5010141d02d003115018403400e40a55030008004880d12083c3c4514580210115090202b110300044055000341003441c041c121000303024840140c01810360703000101e99080c09080c034081042451007841002d80105082c2000d101680420700080d46800700065101c800c03102d19440ca41400c01c0008041c10078500e803921829002c0c1c24180c0c00f41142c0c000307660200001c1411080315120f524001441030503a6007000c070032944030340b42c0700048a01d988200f05103a0540104c2014030806800303409131f20040c00c00d0455890009010307140c02014a071000c4041741c4268040b82c0d0034001030341c006040ba01021032505056549548505083c40036011044600f100d0b240001203440500c03065555072415600c411814440b50341e41c504562501d1001c5890103403155040c0902085070354448a52480385c14010081184081ea481d601002141c401403444190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 552839091 1250 552837841 552837871
    0x207030f020601050105121504140709140303070c0509070905040c0f080609010b0919031403070c061419021c051b070e0a0509070b0a020115051e0405071403 69
    0x303405120b014007401c001e18006060001c5208444200b18000e001003642190350983c814054a46421030152817950000180003424101c80003410f07410301d8401da1f060b440102081c11046e103804000c0307400154001041449c11410041000751a0801814480130b00c08250b00011381768541d4010740200c01e200351580824102001c0001c2c00c0c2c090010202449200e1900042c440031742c0e041c041c0c968150059890100e0003180ca000c40f20f01c44030982018251403d180c100160b8041d00000400341c091045040700800380d83c9001c240c82d482c1207080e80202e452000e01c4500182ca95007160041220014030403a2000c0704940f5080041c0140c800c20754001400c00a040012200c140c000404007070322070001411241d01c0c2c2020307440440c0c3c0240c104152144c842020036510102041550301510700c1c25240c95449540b000b00ae8002c10700640c1c0f2008000310103c0001d01c1c0c0c41c02650000340d040c1140080e40415100a04000003407500604180034407040341302044074610400050341c41800f904048c1a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 552840341 1250 552839091 552839117
    0x60e01050609070f0f0806010c050a0809100c0b010e33040e0304050f0f040e0d03090201080601080106020604020111010e070308070606050409080d02130911123d09020703 75
    0x307001c1c0401040c9100340420b58a03a010303090791001d8139901783c10f600d1a1000b00754031b8000c0101c4901103182005400c510400e0000b40600403500020400810212804480c0301c80c1e429090794141c210b400040c20101e0440010003c40348800c0140ea4803030040c8000300b0040c0031480d0744c0d0a480280e000c80e9018404103141c0c08003141000d204402c803d0440400440c10286000d001034024406070701510f004180803082c4404c19100c80d00020508140b00341900c42c2c149240ca401001018104002d900041030800821313a01d5010307005d45410f1f18a65405405039940c6e0781c00645210317207005551852036607141000445040c0c2804518003440c0f16031030704ca503130f1007090804c3c0c6c0550742d40f504a20700c124981141a400640c100040703a505561504000d622411308501c0444c01e804243d0042d51b07030030300380405801e640c28808002c00c2c800000f200d02d985d880d02e4601108c22244841183d8002401f4110360540070750300e01d40c440501606855000c0d8449544491004050360000300c802c0300458a00c0e0040300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 552841591 1250 552840341 552840349
    0x50a140d06020a0206090610140409020406050406061206091e05180d090302031513021212040b09040e010e030f071412190f2c040603050c01020c180f06010903060e010506 75
    0x242c010603682300c0c001e09541050306d1000903c44100005202c2c55680c101d5004546640c1c00c15401060000d0041060b540d1b1404083c044248600080800c41e1510401054a032128441d045025010503c040041901a40d04130b004240243c10400d48003003502c0c41c0551a0b208004c2aa55003400341e6625400e146584181344c60204c0100d6204902100002000ba14070101744001040c1c03501101c620b0010950040c5a6081c400310b4252008094400900812268010001803405440940b0100030710301d40032000b1400c80e00d19010294954008000a2a400481c0c002030407140c1c3c054060404542001e1603071601c1c01c0b900d21f0350f610f10080089442c0350781e00703071000c1e001160014a0a0582c0c40c05d100c0c0800a0000440701044044560340c40c03888801140442c840c2000200090010071002c1c1e228207242d40d03540e040600c42d0380103104201041010341065440004080e008020440c00c80d1681c561030000c03100014480c0341004100000000485c9060003442d40c400c01c05030002940742040382c180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 552842841 1250 552841591 552841603
    0xf14060721091e120b06210d0f0512011806080f0a14210a050d020c070302130b1e0102010e0303040c030b100608040303200f04080610050a140d06020a020609 69
    0x1021402c050040100130304049403107071107500c40d4000a074182507a00c1030006800c0c516103c0c2c1c80254031007845400c01c0f401c040002c0d06e03044807001d52269110000d402031300700c3d1a48500501c080724690010010407058000d0550800c070807820a101045458845d0b03407240c41c00d0704440b800107541c0c1c842c8565400303220444400701154440380300034100d00d82c00081c006480505078090440f80500008503031100c0d032b22403410f80d40e03458240c0b001555602d0441040d80d07a184078074082039204244420f10400310071960301c980c104c50513010b05002d071541c1283e007540301c0b4541e0810895040d0b540b03d4903102c6160400748001d5114502c40e003014a441400c41c10701083d0028020508001100b8903002400240d400640c502d0784035909d86804902d0800f880c014040166000c00780c10320340d01d0040f521a40c52501d40d0040c1080d00e0202040fa0a181d441040307040d140c3e1054840c041e040002244103025005482406941d4124080d042400c040d40d05d980703840490380020044401a0030032018440280d500b4010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 552844091 1250 552842841 552842879
    0x31021c05061212030c0708090d080702011107060207050d080702030a0b01140d020f04020d2004060206090115031b0b19020606040c1e09120602090a0f1406072109 71
    0x24581401902000c150701c1c030001d0811001600080346c070008200000c01226041c1d04003402c0d20303030a03404c2481e00108076045102c040340031605051024148071000164640ac81e44140e00602c1d0b107030700c0d21003482409440007a0581d4481e40130807400003d030700c0400105410301e20445414091b50314010424141400740201c803440f662030201c1140142ea100c043c00310031400c046500607511a915440400241580540c403100443c100e541a54003a0210014100f01c6002d0703026500e40b0358484041070b08031540c1d4103403240c05a40004090022644482d020070821006d10312009515449180715041500541800903a81e141804d001e451654140b12160b005001a81c0c24402100e00e104060403036080d0083c2c0500c3d10504e040301e0400248075465400050004d1001811541c85504100010303507c0140300500400460350002014044540501c1c2140c08810a903100003000d20104061a40f0010080c0c0784141c1d12040c40541072031085e251881034040d9240e0542d82e40c544802105001c690f509 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 552845341 1250 552844091 552844093
    0x1014121b040510030b180f06011205040c120812270105070c060b01091701140702030c0616032406030501060306030c121406010303030b09010531021c050612 69
    0xc02c1200303844649401c0c0203001e10342800f142c18420f0704042503c01341c1507441000d001103040c040c00503180e000b01c0818000c500aa86040030590f00c41c01c82c6083d54000e88008000800c960710800c40e403918005030914040c8951102481c1c040040d40d03100740504c05a401010312241107082044100d07001a00da525581c2d860001d10451410310b80140042c1c09084000d840e02c1d03180c90340409035a108150704000ba000000480fa0740103000c1c3c4015000b0711110350716032124411240400c001500001c2940d00d1241080e00421241c0d0352020507030401c013000d03040c0c1d1081c107440320205001c5041d01c14056943c1090000808c03262481d00d07100409440041c0c2c0004241841c000007400407e0810b4520010341c5c031240c1304012070340202d02e09414503c5034212040403900030007002108046e45500501800501100e05981303998840040000032034418820291044041e0442c010071980c1d0b6603403400c00002401c1c01410f04940b088e840e10040e4400c519251901d6860041040900d0011400c03000d0800c420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 552846591 1250 552845341 552845347
    0x30d12050f06010f110f070b0c0d0207121509171809070905040b0d060e0f0d031401090513060501260106060806090408040315050a0b0904111014121b 66
    0x201c0060250032900c41d1403010805910780840514170100034074401000200d00303c400e800e0762000c030749045400802d52800ea50140e04070306000c0c540300141c2c43d17003a00c01031020719043c44015a2401d001e400203d048880d141e03100d2001101040340303803070003001000b906207020390b0345d9020302c04a110b1443d0341d0008912400e081000d00c4041d65210043c0700c03d9960656000071884c3c042c80008140580c03042c40107080504011082c002980c0c040b40c6255000383c0c00040354041c900c28042079068032021010381d0018100103004100d0100a6049242c20204000c42d1203140202ca841720740540d08240c0004404115000c101c000c1c003502c0c034000f034000d840c005c0000c011803070a1010041203034001070003884c0305403000c4012134140080301003140d000b03541c00030014003803024003902880940000c40301030100e586004082c6600e4108645c4480c4a01d070301024541c00c164401d0704000e0781c2c082c0301c0d0707080c02000030400c014031569907071000070090f00350010031901c0c19190100640400c118596000f1418400c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 552847841 1250 552846591 552846601
    0x150b0d0b1020030d05011d0c03040807120c050f0601061808150601020f070609030b060d0f060e0a0b0a060302101107300b0f090708070e0a060302030d12050f 69
    0x141a407902c0200c0d0b18000701d644a444031005145004018241038800e203402c00018850085001100400070550794038440380da5a00070012042c00200c40180c40e009041281000003142c1105001c41c40304103040c0489180e1541e140c40346000902a4001d01c1030340030b00c00502441d500140300011282e6140140100305040c4005240c4440d0603104801d0460241d0000c9040ca07030080c401c4061190012007220043e560710640140703190390034071040d510321340c1c00004505c103418200c10351030382c5075048502c2209200f0140d80d402d00030229940201018015050130764002a80c4070703401350140041400100d8075504500400ca030900000d40341c04240000081050744d801e1010500318222100341c0d00143d102c0f140040c0b100740902c4a0300140d6040e102c40e815103010840000f0007980102120311642000b0740d1504030080c1d850b41700740122001d03548200302c10002e0f189800b60183c0e00091100003c183d55990343d0109151140ca118020049207500a2900b902521480303266484480714403c0162800c1c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 552849091 1250 552847841 552847847
    0x1c03021b01030e0607020d1704020616060f0e0304050406080609071403070306051602060703290d0506010e1b0304020a030201080703060b0301061809020a0f080406150b0d0b10 77
    0x110140c204100c011030040e6000e03680607a002818403181d410036240a4617008100070348a602d48504039021800680c940c0030001c00f58a00c140c8140c0d8041c0030103281102c054445110b103e500d00040710782e00d44070181d00040200301d015010f05002034600460300d03641000100300594940750001000c0e0b0b844041002103040001488504030f0f038000f6081d0040390240740219040182541011342321078100000d000244c5000380f00360324075070129825030300c1940f038a2200b01d06550b5410b10748004401c000c44d84000c008200d90201d041001d00601000c8141c0c401d0360740c0c90070104240d00085440c80d03007108200c4810000810905103d82082d02145140380543c0003407220845404068100b01d103150008110034001c0d031041003c2e0280304015900c03581c0d034550042100021060201d10301113641d500141541290099510380000d0707403501583d990f501d800c01c803905d0000401c1038420607202c98070300400c4004102084041c00c000f2550903070701c0c0c41007410031041d20011030640c1d0040304000b44008049038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 552850341 1250 552849091 552849103
    0xd020a02070815180316141e03040b0c07230102060106031401060509011b0b2208030a1e0e06071403100603020307121a0148080d09021c0302 62
    0x80c03200812904180000f0700c0c5881d60003a0280c3c103100c141103586440034841c075420249054032003441242d54061915a001703100124040000c511032740705020920054003410041c2509160102c1110601581c3e0010f42800392503001c0d0005c42d410300400d190721a541e0620980303026100c542030520821580c00d0b480d0050b207070f0500c01da1080100100300359032160300c501c8910000841c0302299554002d0142846169540c069521071340c922480184120000c1d01c034440c2e4454141c01c00e0b80141503940e812214001b60681402c803141d41d81001d25848042120791040788481110600102040e160080014000280c03c1289208401083c010801c110640e50000c9090369114170700940c0381e8581000c2926038400b500b240c095003900380400e030144448000b080701003c49e401da840c070340e104c0240403001d0400c2c0c07040d104075500e80c9580c0e00c041140070301100f03c28903085040c25012014143ca034036400c9464200c00c260740402e5440300c0340301c0103500d03081403901264081912014804035143d43c020759194 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 552851591 1250 552850341 552850351
    0xf09051305030405040f06270e0c030703060b0303071506060822060f110a08060f10091707030b0108101a0105070b06130c08070f090e041b09020d020a02070815 70
    0x1a854030280f0540a6951300031f000181107001803001c001c0489010051625038581d0a54441031800c8215143e10b80c0004d0a0500031001070090044681584c45242c0642548810141c044c4010410b01c0e000030600b000601c003500c0e5142001502a081203c010078062000d400c55003e00d402604850700301103010b46c0704111130350013480000c1344070010107908050460030701130302e84a00c0c010461011064000c00300da8460b203011204605c1310a00e03841000070101d9054910400605a1030050141c0001c090300620710344030300000c568143c0d9881d41c6403100312109802025158201184d011000700a0780103130400401c000601d04500ca04640009009014925024005454403004600f840e107401400120b00d01c0000c0090144c501c02040213440213005580300c41c0080c101069440a80c1d11030003440064401491248440380c545844452008500c1d401000b8581800e55001440a4881c4020024100741500c05600c0d2068004040d04040466000c45407507041515144d40c3c1c02d101000c0715503c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 552852841 1250 552851591 552851599
    0x80a09080c062505030f0405040f020304050a23011d06130b160309021003240311060702011107060917011b141303110f010f0c021c0c0f09051305030405 67
    0x12400000c943d070b00c6107401003409800b41c000040e40000101110005105807201520103222204101c46801c04911081b5006003003a000751032224009002201c41c0000c0c41c24944071100e90f1548003c3c410308456680c80030417040448030002000441c0140700b83c50388804120141041010340740c5900344902e40090030050134500356a80f201280d4002d600081710319402904d200340d0900000006070040180c480c0344100d44620003020741041c003003112440240d9a02146900c1c0f000200310600c1890f80000b05c049040c000041d101028407102081614020726080c0e5500300e40c0380c50301803990851002943c426030707141d041010ba9046424650059900c2954600e40300c5010b00c3c0050a01e180c9001c2c40320209684180b5820000c1400500b104005000c41c080700c014201c02e0501e40103403064128064030f60b000c02d0110900d1405403614403101268070f0380030300600040702c9503956800e10900481c2c00c105504044400c080c030030318510344142903000c0d0300781135210762010ba5522016640d005034810b00d44a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 552854091 1250 552852841 552852877
    0xa061e031b031712010f030305090906010c08030727210512040e06031504110d050705060d021903061a1c050a0e10050105061605070e04080a09080c06 66
    0x1110503040c0e01e10011900728143c21641030100d03200100300d81c403140d901c03074180036a800003054581c4c044100070101ca605440750b910317046400c404d00200310802058141800411841d280104072500003d5104400d60381c1d59840b03540861400c10003600d034030301280c2440c1c40d640340d05014451070b9982c011000054031143c85030580c1c107403602a283c0b580c1a614261041e1021600203801c0b4440d00c01c960050301c089040c0c582c070850a02240d289100308981c09050680701400101060078404402020b0901800a998880d0707115004034025070b100c415203003110b990000710b07503440c5d40b000054001440490301c0c007403052924221941141b1444400c01030304082d40040c0041d013480b113922040c031081c03243c424140054a00022040300a010340e50b1030400c64025441036240c140c803644034130360581e4001041e040c1444015200e103480b840d18503204458500c0345240102d4102c6420300a5440b56200d91842a560f0600074001411104140d204c131056030b00c03040a00c4a50340d030f80e9054800342d0b0000450b10302 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 552855341 1250 552854091 552854123
    0x111306030f0b100c050607021f02130b0a1d030303130212010f110409050f060a060518030328020a0809042a0306090b010e0f010c080706020f030a061e03 67
    0xc02084030111465000b4814102d09001540292204681d0740c011811b684059541a106a840c0c2264a45e01007460307005122440c200c07406076010f45080d44810366200100d98690408240f207038404100c034004588180107925400d151010952030040741503020394118140008d00071503c0f00d000000a200e21061071440d2040b6a0035882100d90000d080c4040c8a2410300c4040c00d56240e10901810507141c0c14040054046448140c0340c6004110141024040b9032801b074040341e040c0c1003024211082031340880e00c007a55030780c100701030300400d618a03205d00500c0b250700c2c032142c0788000d4120128040d904940703c5140800c000400b40d44280c04113030380109035000110045900e8600c1036000c1c202400d00d6503009402c01e940350b0320101c251040343c0c4041048204460054030310882a42c1000d0740150b0003280082154031511034003228500c600c61382420000941d80f038400341e800078000c0c22507850001c0704008402c1214040d800c01000b083e16502030714030121100c80c03040d05a80c0006807072140040d01d142 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 552856591 1250 552855341 552855371
    0x90f110a1b1b15020f12030709090e030306010e1806041d0d0c0309050a0e180f0d0e03070e1e06060c030c010207120e0607140a12020a0611130603 64
    0xa030442c1e848408a4a01d00601c68000c00c400024001d0840300301c4003d600341c40700b500005034100003035103940c002d09504400391111301a50380001e20358400c11114a400140387c45490184111415101d00038603101d00d00324000402c008120848544102004988141a002050103464201c0700c190307000f1490585e041c62085401060223074034440c40c407604030108021036201000d81e40192003607540000c100c4d03544d0104801c507005809100031648100000c40c1e10340d2854000500c4403c1c0707a4003920009154021200d04119000700c6840100701c00144481851906000c050f01610802d84408884d003001c02a41c003040d023041c040d07088400425400303d40c2d42d82c0c805058803050380610048a6507a1000400745010f9001801c04071055031040c8031026125001c4d075a50100101c000c4d0001d801c0000c0c41d128058030144445445810380501102e140c04504c500d501c6122a403010780080c182010246040300803039040b00d40c00e904080003801001d61110515031500c04846c0e441c940400c00000c800281 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 552857841 1250 552856591 552856637
    0xc020402041508040308060a050a260a050607090e011a0703020a02030d12060f24210c020f06070203160302011401090c0206090c010206040b0408090d0b01090f110a 72
    0x101461070b440000c070441c15610075002880380d031103075407440348a40b0341d4000e00414100d03034010550f105030b44000178000301f03203124100b03120865046080c1ea0043d444164250608150740c3d404e44554000d10100724513583c00038400e0004142d0007000740b110f076140540348059122040e080b00c0c0c8002c000500c400605208000803c5280c3d001425200482189070010b440d902542c4d075041912030034000c0020b044001d01c640e08080307421400c0c070036180240403031421030001f11043d4001c050080d410368110b40002032844084a4281d42d01d40000c01c03003032002000e03142403041100c90a13036a110001b003085556000c401d495204440501006240e40340e4035059014000c0380041c0c1d0448008240000341518403604810070209280d020348019864400e010342d25000e448842c98096400304000c00c0010742c1c0303640a281d228dc014a045814100f1a100181d80e406032030400303443c03801d80180144800e43c0301e07108120780c802001c6010800c0d81c0da100781c8001e80c0e01a0f4079a1000b8000c944148101d8180001d0700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 552859091 1250 552857841 552857849
    0x190503151e0406230901060603020f0301210812060405090c102f0a030e010c0b010311060f0a12060b12040b06010201020912030403030f03050112020904020f040c0327080301060c02040204 82
    0x50880114139030b900090141400b1500c4446560800600080d02e50003031003220490031250400c07030701c0c1da800e221400e00850503030320715460304a101c82e19402c0032130310390000341150405001210a490800d0402c000940784c000c1c00c120200e80289000c20001da5600c42d40f00c0440703c3e0341c03c190840c174014200c1a4640c1c041c2c40c00c40700569104082c0040391030008954445618420f4840c00007030040a40110b803000390701e8100600e400544001070020680b54101c94a00c80001450300b440c1001d03110760700e840c40e00b242c4080300204030440001c451568250041c41c000e0842c190b0840d09190500d10b41d40440c1c0c1c8003920252a14a501e400700e01c059100303404646007000041c1003140c0c59500d6400ca20390301e43c400d00c0b0030b400090701d0400580395180b19010325070484890105010301c110550302046540c4802510807030f032103202c00f07540103100e445900030001490407035240002d4007600c021602c20380008006070b03c0d9031f40c0c40246080c80096201800c2d03034151191450180880146031021400134800c41d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 552860341 1250 552859091 552859121
    0x1020717090310090c0f140a141c0f0f0b16050f0703083412090f03030e0114010b0a1409030d0c0c052e0c0209011206020405190503151e0406 62
    0x30102d18428800446a884281510a008041c0d40e4010740803030b00c00d95450260307000c00c0140b1580c0ac48502e115240c60307440d028103a6201d119240e1f80c5e5440411039500c1d012140c10b50040304200b06140110007004001c00c5078180980341c0100403580140300c0c498030710014144010000807908802129170840300010480c144058111004e03506666500505010000060a09801034032507100701c0c007840764400d90040104140b00082d0350142d025050800c000301c2650350fa89104101c1000c004040d40c0201151001544e43c0c04890780d00920325052012a007032050410050071030207450000b9030300e42232191032031300310034402e4146090030f019041c1740d0103103900c48212540030764044140003600740420040501000c0c2c1e8001d07203000340d4521041034400b0b54050414001004102c0fa005400b40d11244540d60041c07406484400044ca00c0c0721251800341d001d403a8100074025400c0400118900d41c02002c440b2001d450a01c401c224200104c1c0907150661a416010508018036070b005441c106402030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 552861591 1250 552860341 552860369
    0x150403050d02060603100608070302011110110d0b01020a0b010308090a0e0c0a0801050d0c03060e030c100204082a010311070203030a0e090c0f03220b0901020717090310090c 76
    0x20000350f40321426206180f00c2e014802c0c98200440c1340381b00355000c99030954003400d4080d1440c4c0065603000308203100e0706880d001d464542980b1820f180b144410350143c1061746078036115403000d8801111844070445041d0b5008140090114288840060449900040c900e59440f8008041007003000c040e4001382c0018450b00c00d0050502d5000e000d406049881e036030b001603a0380c2e91000c00500c11056240941001f00c40801030022070203d40080c40007002500031286000c2c2d0306c0000a1030019420380c1d14000d582c4c0403805203c1d03520180300c014002e05095050a100c05403100801c0451125002000d050695038850740401c01c8009060391071907a00241503d446405541014120360750a0b4082442441e0081c0060290f07039030340060302e0340c221a003914241940d031858003525041e03540c13528482c0c1c0f9100c0c440d0048002141400d10520511a80b00096207403101803802d840c00f4102c2c3c0882c940c5a210a0042114a0b180000d034030320120203120700803900446a05003a006410359403c045441c0c1408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 552862841 1250 552861591 552861613
    0x1030f0f020604030c03060f110703030e12070f050114060a0603200409090b0c0c070909110301020f18011d1e03060a0c020c0415051003020d180201020d080c0915040305 74
    0xa00c101701144e00480b070520540511514100458840c2c82041c040c5800502614010038030030b510080c0c90100d14021100901c0082c41f40c560240c008a0040303511030206402c680405c03c00b0f0040c030f031301c4000d00e03440d40c000d900f0700c5400550024443d005480425507260980c0c2c1041102c01c1e507010060360203103400c1c0e80d80d80d1182d40c004007400482c00d0560310100000c02107580310f170302002100e2920300340e070700502480c0e8200003e040103002000b405640103024000d28160030b175001e20040ca081000401c40740d0b62424040c0000d944031400e50285810b0002d88820480e04075600135403840d0000d02150005c0000d01e200004800440906c0302a58041c440c4e0420040d42050b95030080392001100c1d000c5445e00e0b40341c6070410007901d50fc4501510000110700c410400760a062a801446a4041c10050304150150208a00300d4810b0b5040d80c030354074601c90301c0006550b0184a603000480c4185061920352038440d14420b198407684c240240280c14140c880c0707000304c2c075140a440255502c00e0a403213a006070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 552864091 1250 552862841 552862853
    0x140a0b0c120f0c062a090a1518060e090106080a020d1401050418050a0605071b05010b1002030315060c070905090102070c08070303021b13090506090f030408030301030f0f02060403 79
    0x4420400f00d240d21500c03012a940700d200b200c031940010b0030450808142e04003c20070a0b4203400c0a9040c83d00034982080201d181403004078030042241c260b80c1c902446044c0220000203001c0c41e079001c0014401c966000d29401d8a59020080c15603034103003883e14464407000d405078020b10580036080c4180d442e00c004035001104404800381204c1044030280852440c81810a4080039102401000c580c86010031000007149604401e90001d9903081c082690740220705840c0d6080401740048400d0395590700241c156240c51103510501c1e071510703c0218103500d0070740c8188002480c0c800e40c2c5840b40c400803500f0071036880108001c1c805070264410900041c00d0000d030320390103900300d40400c035680c8802c10b4010406000000783c0070206d9405a00074035044011001a0b004081d2a03200b985c0c02c6501440ea040103c0710900500040f9440b0300000c00140c68405505414007248a4101d683c03a0001c100410002c03100000784c80c1541e0304420a04c1d4028082d10f82a240c008000500030b40180c404075000040c00a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 552865341 1250 552864091 552864097
    0x50d0f03020609030c03040e06010e090a0c0210050f0a0b0316030b01080f030a05071101030906110306091815100323010609060b04060c060b040608030c0106140a0b0c120f 75
    0x44203070215441c0b901c880807003a0f1280600e0724400300550080c40100700f468416100c248d040a8103040c0380854840718004102e0680d4101c8428000070380315107805010365410020401c03d0400100100410704000366031198002d00540102005a192181603510b40d0b4140000260020a03840c0c81c10855a64607010424203400d115031304a50040c1847c9911040700031007298016400c980d200e51400713410344d5442e1952031251002c10b0416944030801000503c05100e00d040b803400b07484529880785000d80c10401540c070000c0c40304000070031080c0c403156103010000c3e0fa420401643c965000f01d59a401c500415241442e82c0094110700030425401d0310013000318a0b001c45420031000a000064032580c02e2016900c080c8241c00f10b41004100800c0070034420700074840080d2103000045450700101c0c00180946160b0303040403005800020702070350080002d00c68000103122030300c80b031101d90303162100080c841c94013441071000c0340000091f010032440040c480788041203d1040d625480e403088848592a50b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 552866591 1250 552865341 552865343
    0xb0a210201080c04150f0306030609080720100c02060c060106031d150604020c011808250215091903050d110309030a120c050111030f10031713050d0f 66
    0x3010100814075410710501214145c031002940341d004008008001c4400c91880300003801050354034280400015568005c403c1c3d04d502824041d911900d8074141000611451859094103500c444800b44590b100c9441c620b00395000c0741030182640d1002c3c0086401441444003101070b40c01b80000210701c498165210742d199220752400c4200d814110340d0390310354881054a00c80c12040044000400c94030f0260020441c0e1040e207400414480c107410b102803840c96400204075161440801c11825155945524403104001d0301c0c0342851400203500071440e4039104130742c4541c000c04001006116034807280b50303240b00170f8004645400314694a0404645415484203103100080e06800300751501076001090311804075005001d807003007590941d51140300510446480003800070000c140d10101d5000e100c4e941d0710000903469079590386860180746102c010b000300020042d04040b642400480e001c201c082101c49420f5240540c0ca43c80e5400d11550684250f00440d4000344012111080040000703500d5072807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 552867841 1250 552866591 552866597
    0x9070b0c03040914070207290a081f0302010905040c14040b072f12160e191b0e030709060b57010e16090513060b0a210201 54
    0x4000c08410321340c1290150b0341240103034001002440130010350300410307200d819503034146150751603000d00101050b042040001c000c92500c07410841541e1040c4d0044040c841c9809a0b0501070f42503a002800340704440c003070b0500450b070781e0342240d9001c0c2c01010751100c0351400d20040e94880d5921422044660301c11002180c007150000704940014150140110442c04000c0c01151038180900520605040c248951405889071300880785c020116503d103070002c1c4c044c0450414a074a40340e9180300405000050414401d4a00001c803100010301003900184245540351044840191400085c0342c4119a001200303a1464500001400c0721000014420040c056040c600d1803400303404080f6212000015440302c81194034038808135091191201c0041e92105082003100c01903200044e0b08440366000c03880c005900542c108842d00030501240300060012701e8052149140c5101e0410701b100020303800810303e80c1c450703a00064941d200540784000d0141c018003201c128114865641070200441400e80c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 552869091 1250 552867841 552867851
    0xc0f0c09010e01030201210213030209060613122607230607050c330a0b010e040b04020c01050c18041a0607050708070905041509020a050909070b0c030409 68
    0x4a081506215040b80d06640c16200241c0c41c1da0010350b4009126078044909140381001040a80001c6c4003412852500e840200486c0c0c0c1503205000088902030500c0d032040505210351035150014005e14030a0740c2d030304006200070a802d85001c0500d801054594070140a00e02c080b00c1c4c002001030054000103003d280410901c89076084840d0020b9500b100c0c02c6403035000705002801c45400341c0c0c0200b402001d464115401403003004400381c51a003d550310321009403c81d12041038446542040301d6041030151408114020f007000c0040d001d5034034000038a001d241c44034480d003c10307030310b0354103070f40803005100c0c000d102500e40244022a583e0122013404c0d840d0900f00442c20160034284294524442240d0780c0c01284040e907000c001268003c013408440034400d542c00411861001c1c84940c0040c40840001701d03681c10075107030041010300d2171000c0c035136803925014608016a0362255080100c8805640003c0c40c0d4032040c0d8118140042a0040c0000c0100002c0120b01c2c8a00000188200e03210241c003040703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 552870341 1250 552869091 552869113
    0x30403050d0f09060c0b0609070507050f01020c16080c220510090c110601120204020403050d0c03120e0303040b0709050a0f0e06060901270e04030c02030c03030c0727020c0f 76
    0x405c03442d000005001d51201200040035030411902542c0c2004080c04c0842c1004c400303a07220351a21100aa0660301d80c4d40204203e102c840c0100591400f4604441041c22504d040c901019500c000d1081130a10826042410a949a0305960304511051110b4424425031400084111545a040c420a03070424509100301201c0da10904000e0607000a010150074540d01c1c15500c15200d101050090b6405a0308202c0000010020000031218001d40d1b1559100040c5500300505805034840c0700441e55401c013403ca110407040402200d9009900901810b841e4036100001c881d000c0407501700c1504003c04007008110841082440412201580640003250343c0352000e20200d0b005e00748016011851500c10141001c1d00315588500ca03e03207904007000801c2d507400036404445002c0c1e0707069002c103c00040321002d506007803041200c0c0c420103800561912555940050f41c400580c400c070b50801241264410140d28044103003c4a003111660554952509580c482c2e111800d041800506104e4403217454 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 552871591 1250 552870341 552870347
    0x40603140a1b05071b0e1f0b0f070501200705060a060b0f0706090c090905010c08091e0a120503010f06020705060a0e0d06140118110405040b03030403050d0f0906 71
    0x91101507524041c2144202607080684a40d003101c40102c81d00807514102400ca03410400e45e960081c411040c550700300e0300704018500408180c040d0018403100b03040c81c090101400b098129184c90a003410020354650480c200079006212845500c0004161103001510340004d61000d08030240c0180140c1c0e1013034a0300c0407003004480c40342c45503004001052001c069001c4103034001d070108a001d1030011807101d0066a40418030005130b00500c01c03e50b603c0c01c00d201404424410007540420604100c007043c24898003480d911000d08041e1035016450000508060300244001405184d02103e404050762840b1000740c05070b0002d0040000f9a5402d81001515904c0003814004944c0050010b51801d000c444003200c07001600242e5035005404c40403102c2c00951103210b035598582041105818035410b0440d003505558000c000b529110382889921020341050004031011124203c500150a1145ea03000ca030271130140e030348080c180e070040145111040750408105030700c9205079600d00c03814646034171041d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 552872841 1250 552871591 552871601
    0x5070e061204021507080408210304230f0a050d020606011e0507030905030d020a030201050a0c0e1c170405031608030d0b0a08010c05091c02180406020906040603140a 73
    0x184038814180302080c00740c104844010014165400c603e07141181c1c60310740081d207505c036230320180f0f40e60b210003500c50802c0756030900700000f0303180c08429504e90308140c1ca0f00072444c1400c08004e401d14406441c901d40039901041036140707951400c41a0750401802c2d04100e80c440070290342550140c040c000004080750f11130980b07616220440d07025010075806404003210580c0213000d04034140050008040740300e40d81082545841302d11603000f8074400201c0e01c4c6c000c0c03d40d0b00142c100158a418845031041817500515000815281034a2441441c9c41154101004001412015080b809445070098210031342000800a444054003160800344a54900085070b03c8503126411403034209005071010781440d50410080150b0082032981d0641d121800203003100c0d00a502100804c10020385040d00341090641844480b0551882000000858011441d200320380080c14003860003110004007040402d505507041c0c410003819180c1c56544500000d001401d64458400c5480b12420011303850208500034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 552874091 1250 552872841 552872857
    0x5310b13090302240a0c03051302040b031c110f06010b0702060a0903050304170601150c080307140d0501030b0a05070207170c030d080105011202270613060305070e06 73
    0x80c10015005105280c0100308000044046004d540c2402c540c0305107071009035480300036290345607503035041101690017100c00c02070865060506000820904180007820a041590141c1c0d0202e040d07014400040d06021911030140c4125881c44800c180e0181c0c031082c121001040042210000140310803110b5603160240301360035803090100180b10042c2400005040d85008500700a540c00d85c59544003030840e0896040701e0420008110001500c0b18104545401000520020f182d8080c504800404800074054080c040010000108100d0b80c86036400040240384002c0850f201d0346030f240c541025102c288009d07154005920081040003019108042c020703441c45c3c004002142c40d200f4040301000b06d5280c1d8980c7c0f8012284220a036440500c05100c1904459444122541c100707400035044500060781d032582c851043c424000110041c401504c1c40b0b03540011815485a6040009005403041e8007001ea0090300f0400000f070301c143c040d08030600442403622a2448620400103004c258060003074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 552875341 1250 552874091 552874099
    0x120803010306020c030d05010603150608010302030d050f0d0207030306051314041b05130b031509030d050a0902040921030b0a090f1b11120f09100905310b 68
    0x4000091681d401494204d4035442501d040030301c8291402c2c12510242c0c0000042500c40c50360000485204800c0317000342000307007480c80e140e5042d600802d030b50360741540340981448000140700c1103000941381524441107920f0f0080d5038a0780d080c900240600454032425001310191441600101c055010310200c0d40d6440050188542d913a40360080580b4103d640000b5050180741c000c601c5403510a181d40640320700304008128981c0c5101418981070b050011040032a00c140705000181d00c0200c116000002c42c4c540c0400c09494250400c0002c080f441d400a51040c90800340c1c4003082811088821803401c61001641510600c650aa003941c08034004a94072061112003030024501d0340e0700c09403081c030704548002142400d14110302d11586425401501240b0038401d54890b600301084103403160102c0051040c10450007540000b0305004110f419449018469192a01580706050007001450024101404540c0101b181d0004c1750044180303242d00b00c001c85c1940803a020600880400f504041c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 552876591 1250 552875341 552875347
    0x2030114040b060418050103020906060405011b11090109150504060f0618030f0c030c090c050a30060501020606030109031b1a0f07030b010c03020706200609161208 72
    0x101008018407107040720651181d0144800300d110301700203040350318525280b071340004c181d4190300420100e860004e00c2c0c5840382a0801080c00540d078040c1c80540e1900030030740e85030030400700303860b20010540e10341d0000e80d0030600180001400c11800c0d08000300c000b5041c0c4609020b40d4584c0280400e503101c500442e04020204c00c000c1240620840c0310700b00411503510b0084405417281e952054030710041c2c1090321a855076100600511904100da90001d00e0b4151040058409c105c1000c2c000b4002c0c59140000e106105206c140300080b410750306010b00c01d80c0354000c2d4101b50010400d07001005103014050044c4102c000140160505102d80403085401d41c4804131100141c01006004001013502241c00000903200925114000c80314203010390380c0003041000510f002c8400504455502e1b1701c132410090013018250200c0e4002c2030b0881a42c413030b460b110f07810040c403403024400e02c000703c1000007561260404100c417111002c20310080303004026405011881d40e424041000301003035940034040c0c403420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 552877697 1106 552876591 552876629
    0x30901110303010e01090f0228030c0203090a0e1b19030c0305190506060702030304030c0e060a0f0909110303030f01300209101e030c09020301 63
    0x300d80214103540c50440d0050b0109410f100704402c040c1d45d04a2130300c0c003400b141c040714865042160140340340300b0041d5801840449002c0400d000071f11380441c41c2d915510100484011400c010445140c013400c00d45e115003400d5000c3d003444c6409070040c610140c107a0401000d054284007800e469100c2e84000741c2d025041d201e00901c041c04041ca0a0204100b804850209041c540c420320f03030000b03c2d6629000814400d00c58008044e5141c032010400000304141c0da54200301344c8000e40030340f080c95200c14040c815070903228007075445610f880311820b0020f1040c59006003c240c0c000c071041030b910403200c3e001c42e06640c4141c580c40040e108520040c000b00c1181c4840c00a00703401e68028000d070305205c40c20881d00c2c0b01d40401c02803081c1e8011012505105076100c508015084c00099041c0c00f050040d1140100b90240c80203c1d42e8402d00c0c00f0001d810a50b5100fa01c2c12140c1c8014041310300d26030 = true := by decide +kernel

theorem cover : BRFrame.Cov 552697841 552877697 := by
  have h0 := BRFrame.cov_init 552697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 552697841 ≤ n) (h2 : n < 552877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
