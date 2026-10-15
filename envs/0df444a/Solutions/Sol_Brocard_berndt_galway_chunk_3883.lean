-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3883
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:57.225966+00:00
-- url     : https://prove2.me/submissions/9f09f740-75cf-46f9-b31b-a9b5e3ad0d97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 698201438 ≤ n < 698381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 698202688 1250 698201438 698201453
    0x409060c020616051303021201060b31060c080d0e072711040513090c0806092109040e10050103050304060f03020c0c06030414010908180409020102061501090815090c090103 76
    0x904c000b034002d00d01026100d030302300400c1d08404040c00c40c1c015070f1542da44076800c000b44c80901e00200d46003010100046200400c0c40c0004150803100d00b9599509440416283d141311540704810b04001e8136520300f0f01920141c4103002c13050003810b1401c01580c2500b000d403c81a1550300d1441c609510f9480c201c14140300719100001e40d0241d40f000e07580c207541d20319000c01c80c0c40203004d08800070700301e46030310200061270250004d00343d0f208483c00c2d800d40321170f812180d0728591409d40900c400349035483c1c10b02c9241c0d0941441e070b2041d11814400401c45901204c21140310044803000e0b007040c0c41642000602b401580d03000380391440f55840701d02c3e04610b48008031028a4440d48800c4405201d81c40000102c1d0501880e504400c0501200d80b0082100189500c0d01d803040394014080c034050b2070300e1901c0391102c0d0b1803d8400d400d266901a0081c000310303a16540342480607a28140e4550520a0030000841d1402d405c000c100c22400b10640316501504056071401d2902d241c40d03000c00e11404403800140300041c00c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 698203938 1250 698202688 698202727
    0x11e15081602030903030301120512120613090f0c030606080304060903061a0a0f1404050105060d0e01180f0512040b0d02030601050d290f010c0305090409060c02061605 74
    0x1140000349000040000483c107620403100c54541c58480400003240c517407080d071510040d1a205070202c07103054900c00c4d1000890702407242251070602d48000001c0146c10040c1c08041c00e031148110010300c0811681d00c60404000450301610082000c0c1c00610411a0034441ca10160503048011030030301e45020001840101240402043e65440700c0040041c0d501c0f04058519134000140000311603921009880c41480441c0310703000b110740419010281d1801e007841480e0680381d010b4410381c40c00c414050710300b003d042103d81459466507030f032100004038151410700300c01941c883d0303207001c000070007609000d89008446000f44c1c4d0007660800c0100071020200044400032a060300300541c51ba0741c0c0f100180c074603001d959003009105051480e905080311310040790300044520842e004a2780c8206100f480410065481c016001c5849400d812000c40c3c091406030440e004000c10101e40c0140c10380d12242501c020203040030142e03000300140154241c06070b9181c0c2000401e85010f90510220903038603800c5091 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 698205188 1250 698203938 698203951
    0x8030f0109181b0321030f020a301109040501140619050f0a030e0d1404090f060b04030b0708070e0f0d1a0f01140d0503040603020c070905011e1508 65
    0x41c01007106244080800c04001c5401c1a943c0c5d0910340c04a0080303070320540d1042e4101c000707031402c5504056035000f0310942d510600c2945da215085401c407500302c051030400512010740012110823094119442d4003840301103d482c0d003105521030301d0b0a41407000365141030b0070406500301a0f49a01c0301e991150b9080d104824001030082c440d10100c00c0c1f080c0d880d4810003800c00c148a40c0000d0301003a964140c0c0110650010074000c4603c40940e0600c11144e0101d48a0036034020281007000300811102d0f074000340142a103001d80000c81c03651b181010542d5602c140d2040396001c1483c0204031000350031162444c0d2048003810180b8640d1001400036000c07040780301445126503400d4104100303110b480e09080490090b00610720354a414107000c4074120140c240704c0d8a11481d0108224030076414203086100b06150b01000440c101801c15105402941000322513a01d68031418400042041041c00b800c0d0007025101c80390404401001030500076544a500085452040f07007403440b44556210320308503480030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 698206438 1250 698205188 698205203
    0x30501051e061c0b0f0f100e01020705041b081b0a20030723010c02151e0f0a060e01050108060405090132280c020c040908030f010918 59
    0x340030700004616018030503205440700c2c0300c0d0000c00a1403d05622604404c0d00880d840050035040704100200b00b00b10180c80e5401c24480d6001607101c0d130052030709240440050064880b0903450300042012200c4070803a085000e4040000020305503003000351590017078580b101d22040c1d100e00003195510f601c226002032080040d46d1701d950a8134480c0070344030320080c0020815a55608494207101d881551068503119440d960550f150703e040805110749040300030180c001c0c1401980130741e01903980f0f43e001000d040c1b00042210b20b0124188455140751b201c0d4498610011850400c61048400c4400d01c1e001030041481450050010b6070304020480da006074100d6020409589003500e00b4090702c2c50241e032603400d124201c101465002e5000365141c020262a070201032645d18154900340140140d03140c00542e1a010040c04006402a000070488071411700464003450809000b007001c0780c90000c415a0300c03040120a000d07900007612005401824407400070300600407030000040d09900180d10050840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 698207688 1250 698206438 698206489
    0x908121c0c360306021803030c1b0f03010501031209090207020901030204090c1e0305250e091f0506030c0901030302030313021807020610060903050a02090925140103050105 76
    0xa0701d240320003820b42d120401d107a000e0350b5501d180c41c0e4043e4012120303860580c902c0001c0c1005c0c9040010a969600403c04000c207051445907460f09000c014a5065680080e5900742290068500b4000d0324001c500c2501138290341e4600c40310061041126402c010038490041013810090307030f81d417001a41541c0c0c04031000201c040c41c0e0310341102182010703440148204402001d03201e00014030b09045c02104d0003a4241c59070302d604035a50201c0005031074010b1b2200d058040d820311011114100b00359100b4115002ca841d10080c0c200d2601400040d0071b8411391103030300c0d1803c200e0141000c2c030401406000c180d44200301941550350194880c00028005800e02810038040e86c01d55851340e03090104001c0c1200d13440304c1400e00302c0f8004d480c3c0c07070308035052000d00002c01400034110307105550035401c5a07048009407000002c0741e42041058003001e070080c0003500c285061600c072490190a5504242c60f190019151145045c80d00c10140c3c0d40e03038507980c3c1031500c4c0c1401007290751107601240c000c0c2c0264401d840c418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 698208938 1250 698207688 698207747
    0x30a080601110a050601180506090c070203100f20030405100c05041223031801030911030610030501050108010e060a02070503160303090b010b09100305070908121c0c 73
    0x11148880420b4965100303003080001401008034405041c1d4640c240135018001010303d8001c1a034405990a0703070000c0720700001403040008100501000740c4010140c8078200c2003085620150340c0740040e50020f0681e9003408025400138000b46006881805e800ca508604d0b00303468003031716800c6595645441c5500e070280c1c400c1d20ba2003241164060203813514120b5828075a0704045103150040c0721800640b103622241058900030000039a80b0209101c0d08100308142140d00442c00307002c1500d0111034211048402008030380d81407101e54850025500d000c4c04403461814483e096071b1040c3d004425907403629043e684480400f090040c2c1c86000c4100160b56003c0924149155214000840c551405e10503020390801d44c0c1508254189805031840d80340301c4c0d0701e03200140018840e03050403d6000070f40b83c15101c0c03e540250001c680c007051a044c819100d42d51140c1c1c03a07061500c00c45141a102c10000f5806201030b8105120462481d2081020845002c4104000c1c01d01d40c003401080108010301c81e00c9203039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 698210188 1250 698208938 698208947
    0x80606040c0e130c1404091a0a03080d2c0a150c0c020f0d05010e0f010f022514030c0f060f060a0b0f04120c0503010f05040213023103030f05040305030a080601 70
    0x5c0032071160764075030752603940c8085801480041c0706407450514041c00c0e0051490a20800340a5030b40054401d071a10f14400c4000005007034040d43c150f8000031640e401c803002c800d01800c40d1010000c01000d800404010b203000d54040c000d0807120f003002071914040760b8001e40d104442c1040203905990007402091981c00050078401490b5000381251701f45240c07202c824001091500be5450050700a0001d01da004803054141d000305900c2100c0d50240c409501c045010004400c0f88250103030f10400c031013026802140741550320000621100768084100034440344410420540d0000194040f00480d0901000041030004540300d00c050405001c2510000070801c03404640090000902c45500015207140c101074082c154410300d4483d510748032100303507036020380d0051501c140d41c014401604000f0042240000303400004030000c040700318840c0c9030b100c84201e41c0c0c61000d07101f9810f203000344c9a165103030040c48003402c16108406c0010510041000510000c103884c0040080e0420300b050343e0b1207400495 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 698211438 1250 698210188 698210207
    0x12060c08041509150c0903020a080a050d05030717090127050d0305270c01030f05060f1002030f070c090501050102030a0806010509012708010f020a0e06031f080606040c0e130c 77
    0x1102c040c43d104c0300440171070304400f602007103901c246d450710102c03641c40303419030f840302d00c1a50f015000380c10032520510440c2c860f80c02103602128906000060803600d000000700e81c40e084688a010360f65402209500302c0005054401140780400258441e09480d038442d0303200e1091039904000e040c0c9450200c0c054071030400c1d0000030080842c1d50f10380382c045030285045e9914507240d071841c0481c1c50851000a0125123015545c494107000c0c0002440d21107003c180f18102d81c841d03482000314042401031703c1681087c20000d10245002c0c850401c0c2c1c13203082c4102202100c43c10b80c012415036104100b0f0400064000041d1580300c0000d00340681c49210210040e43c40705480580d10101600701d40c4c1c1c10302c002c11520403e100f5a840341c40200002c40d2560780d40402c902c02d403030180340800c3c0303400148001403500c8002035521080003003401c90301115030045000e110701583c0281405802c12000c200143c20302d403141c1041c0115501e0001c01000c00c0f040400c2640340000002030a40e6100da21050301c280c001c40404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 698212688 1250 698211438 698211473
    0x7140607171602040f0902030d0818100f06061e050c030f0c010507180803041208040e04030c031704020a0b070512130f2405031305030412060c08041509 67
    0x65030b5103041d119042c950745440d081248100e1602811008004e524404d0009455001c2c0c0188103564131000140c881d20030042412507200707601200049510028030006c21050311000c4045103a10714110b50401355205a08414100040c0521408220181d2003a10036150b60070b080030390707403040d110a245044d40300701c04a00924080004001d421200d05501107072080b4070340e03034403020000c0040007540e440c405a0710440b0787c40da00900090124460010102e00500d209518151805548220600b00345208840960108045400354410704d078200d112a600b151001d10410b0303840ca01540000c0e0990443c0c001c8aa4215011071028204842000007001c0407131038401032626011200303078140d1019a02d0144075201038400f4800101000604e89030306005100601c460301c0f0304080d8108032407640000707140c0318104401919120208070144000c0000c0c01040282410703400c854204501035a05100001040050000400000c52100100c03041500084000891000780b107040c10045601401081d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 698213938 1250 698212688 698212733
    0x40f0605041211011103061c06050f01030b1b07080a0203120f0a0c0801030803060907020a150203070f020606030c010807020a1a070801050105030c0412020a09090309090e07140607 79
    0x140814420b6580b80c0e40b0071100b039640c5035000e460700c660000d826500e03114006500d80c070003480440c015141420150070307882c00301000c4191240c459241c0320141c0e00143c1b80c0124030b81d04e0030014014000c0000c03019074450b86c1000604524444043c1040d0240b1502001400480000c03941121840c8280100c6080c1c0052003141c0341d060400ca050088015410b850000100e45004444003c0f02d00414649040300c1d04002c10030305584d158418007521a00050241045000f140891000a401c0c040300c450024040540140c9900e0301c2d0401414502074240d00c00250350064040050303a0350001411040c1c503c080ca00741140d911144401c0c0e2808250280003011020351403d400d4a81d01090501e0707200320120740d03480c1803503681c03100156018801900c441001007000c000030b20020103c20b08601440d88064410810300340c1d81c1015400322001844220001503400200300440545402503844080340c04014085092505c0c1800301030a1605440c540600000300320b00c024041031004034081c8803402080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 698215188 1250 698213938 698213941
    0x10f08090d18170601080c0d02090f1807090c0306060903020f0d060b1201090b06190b1812030306122a0a090c080109050c0f09010c02031c0f0e0303070804060503040f0605 75
    0x8005031a0442405410305c18820f0500047e075900d03001c030303030500303101e801030308130070311038681e044046607030b120003003a0120304c3c4484401c02541701003c000d148003c2c02428000a40782500034802406c0e07170420f034482e208010f20014240b01581d1140900b2a41100495450441d40154a840300c0540552402a0b03400502c1c607644407042e007411f41240034160b03c18880b000166442504200c0c5540004014030300d4100c6611342480080d00f15001003800402300081e00c01e80c02108800507007248412105425a50004814810a4240042c80d10342005001000e04100c0540c0c0c0318030164501500c540700592b0001001c4074841d074885044040c05001889400d02c6401c08108025050400c01e2007580f00152620000a004110001c1a00d034103046001200345004d22800046651803601001030340e050158810102005030014100707440c20001e40c8458aa00e45030520251140711030240382c3c1c2c06500100400c0b4001401d050482c4d0548002d8240300341c40707417150b00b0003200c800004071005000d640b8060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 698216438 1250 698215188 698215229
    0x9052106130303142e0902040b0403140c010e060a1b06021902060105060702100e0406320315100e041a010501020309180703090203030d0605010f08090d18 68
    0x1d1280d0245000b51414400c0c42c0b80aa0400f29a5804131000999660042c050710308604d500310119038a0021081c00c0503469031100b0940f000c0340d000743d104001440700042c0420412440d03051130020942d10a01524a001201e0700192000349070200f4144111400615498106c0c01541502c00114607141d080d12a01d0851420b20001d502104a42070803941d00882051800c1c030025000781600c0024050b50b0170f09000e6824802d0100310619810300340a410294900d07607407203920031480181829003000c2e90b0300da00c80e0001000441140344403070804001c000c0491058600051554000400c49622440307551a9660301c035400e0071641201e500d540682c010701c414060f81c0002480c10408500441600c1d907a140f006990300d01c00c8402194100120b80e0390b80c80044008400c1c90b500504508012401d0031a0350700103804c40e8440c48900e00000e688040910503944d001826079810200341c00c000c1081d08003d00403e030b90394050031010042001001c80b54007800390747e14009005000030305c103001c428841d94 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 698217688 1250 698216438 698216461
    0x2041d15270a0201180e040f0204060501090e0c031008030f1207080f1504060503120414010c0209010e041a01060201141f12050715020a0c090c09052106 67
    0x6507010318842485400401400c82020380c0400c0920000300140050b40d0164015141c040b0603211804440e0740890b00020003d225079251442184143e01181c440c05861040000300d07145a00b10f00d04129090a040c4041c0e0328440c401e0742c220aa0000c2180c581d0740d050510403588a064200ca4000d0001285078aa140e03002d5010380b81c0721a80041190300d030b907100700048444210444110340940300038004107201300d80780020410301c4d18000e0b0000c81c115454202081c80d184083c4d2203412507640001c0c04010b40320128050341c1e003203002440e240c0c6103c429074001441d08181802103286581803040402c00f00f0400c1000140da40c18100d02ea0050b80d030303403400e000c0c1c020118803900034601da114200040c0b6070f55500130100d02c07595419204210207420b01099100700b10449804541c80c1c499410081054290a1003115001c41203a0007407060022a01e0f20607542e0f01140d01040400d03040050b1441b00642220170f0106480781a02d03050949005040781c840540c03504001d103e49400340c6c2e0305018180040707 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 698218938 1250 698217688 698217691
    0x80108010b030304141f1d0f06030403031505060c0706090902210c07021824060d0b1915180303022802090c04091406090411030a050f0c0a091802041d15 67
    0x1500c0c0b071300d0302c0170320600c2886008c2c0e4408020603480f690400c0080d001034003a44c800e2204041a168541e41c4503100c1d80070a80d00d0b03200300c0d490140e66004420402c0a5079001c80d031038001e802080010b41c208081c01800e1202c880c58003e15841000a900005850040000649030056001001d103018002d642c02401035245090f120f00c84045104542c0d91180140700c240345c904074070b001d0000d83c40c01c2030320f41800005020446400758000c032002440c00d08940c0b0788040001900c01400015909100f0701006455900c45240640c00f100040300204040390700030407000d0804018401002c5814181b9410300e954a1040500960180102041c4011100d91401402c103449040304104161040720350348040e4154102c50040d4003840c01c9000a000416072001800c3c8508041d080304c1b141410f0369240d03803c000420408080c0c5904c603e9200d242d40c0341200100e401040c030000304000040c078541031032070501d108500181c09039440340340407620140c204072824210038245d0203480700714008000d175400c542c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 698220188 1250 698218938 698218967
    0x1030305480d1e03020c06040501051e0f011e050d03020d09090902090414030c060a0c08011719050c0613090609050f1330080108010b030304141f 64
    0x221030000c91001000000c000060b01030680b200c980490300700500d444420031100a140800d1780900c191480407008201c4036001c0c500c40c4c4000708071490041c0501d40c00381c224800140786646c40c0c1003400002140c4a00440c195290482100306580100c041c1040000c21540032503002a17000c804842410340c00300365031820001c0c664800005a540d6112641a03842c02ca03c007a6001003800e000c1800900c82d02c00f10106000000c1c142c9080c075119440490030203004172546041941ca071114120a20391201d401030250010415080b10844951441c42da1903044a001c001d034482041c22007000c1c8030042050440e110340003014145d03620480030030700f40c40d0b800a10030303580043e06209020658481d03034060f241c855802c04030b00b05003d60f200e2004c0d44c1018a803140aa581d4a4104076108034030401c0c200c038921a1050560510b0810054040101454016030110030241d16182121100e80c4c2c02000b110216035592000a0345070b954500020040241c0f40314404405074140c0c110b21140da003040c1d02c1d060700c0e034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 698221438 1250 698220188 698220307
    0x2121e130f05160e0708010608070909050916150806010c1e05122b06060c032003030c07031b0b060111030d060801060503100504081204230609010f1401030305 70
    0x26a40c3c23405484442e0300f40d03040c8000c074040e40c109100035009036203d640e000040d1011156501024100b9106070340e00361300304490400361a9007500c80c6c0d81d001000c1c0ca8000400f03213040800418540c0718603e0301418000c103203040c602521a5101881f01c10003440140742e036800ca080d96544031301035001e640700c16461415800c0c80b442e10001d80030314280d482a00d040301d00a40383e80b0030061071903a04894a01e0b030012280c00e805103107043c0854110082014600c80d56440c0356032036a448140c00c025040d404100d043c00540e031090910030000450144442d03410040c02e0910149200790706412030b05502801c10b046480c5490000005030070380c4150085421681d0075816241c149003090808008d40c0c0c002c8038041d205420401c0200782c410b641410056106001b1700103030750b208150080f944104901b68076010311960140081c40700c145403c1c800e90320035205c0540d041004e10300542c04c1900b0108144405010310901181c00700c0c4c03801d40640380e00141c09500d00b0f80b072035810100302c424640241400c2c103031000c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 698222688 1250 698221438 698221441
    0x30f151a040f03030509131a13151502010207020316150c050601230607030305010f050604050120010209211c0e0d030e0402121e130f05160e0708 64
    0x192220403201907580704280b40e5412410342e10160ba170b5902200da25074000c0d16100c441a8060314030300c155589501141c0306030710844520410040511951038110b50304a142c0b4071244490200004140700f00d42420700e002101070030044081e030090007800c0340070390103005884540c41982c0c2e044410000b0b440010b0390001e182c81a44108640e00060080020300c145d00c0f003401405800b101c050041c1c20300140c006103442840500020070400e4000c00000c5002c251690018040c05d100d40c200f02d0080c1c10705651a506152400700004c140e202c004450000410400c0303500d0924500a4041702c2840d0800307000c1420585202c503400d10030646075501605240991700941e0300860300c13403450000360a5190380d1071407120300c0306040140500108004a00b803010221400039540c4840c0003400b03240440d50074000700c919112800c4180854405006003440700300c8000c1201c03000c0d001a58002c0c05d034015009504480b8140741203454040d60341d11512840042610000d980d00c01e1892a1303101d02000c0e0f41c0c20006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 698223938 1250 698222688 698222729
    0x31006080c03040b0402030c040908091002120d09021903050304080d0c020a05010f2007050111010605061c0608060c09040b0d020a06210501060207081b01120903030f15 74
    0x2010001e86003020380e420200085000b007003105800b5600700b400202580d03070007104900000c0464034440002c40d601740002c103603803c0c1d5280036000783d091100140003401590182c000800103074401c41c400e10400643d41c109440654a13045800411b4a0000007206441900d07401d049980ea00544540c0c01980305901103207640c1441904400889039000d80260012400c100064540c031a101099134108681c1200302c250702c0c0c144d00280745000c0d50700d10140c19460700b0500014000c0d14101203148403a0b0606004000c681c42e03039803c036800b04040a1110380500d5520088001410295005050b02d1103070200f84050384241c48000c01c1d0040040382c0402481a0710402e10400b40301e030a502a51203004040d00b00002c0707004146032024102903c900784051003040b510081154020b0f00303c40c006921510061064200c2081801020501c000780d841084030440002403901c4800800d212109450f909140d0816000350051002d100c203440003400612101d054802513990a4440d543d000c25015084021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 698225188 1250 698223938 698223947
    0x1706031f02160c0f090b0f06071b15090509010815040312050c180301051b0c1603110301062108090d0b1305061620070f0b180121050402031f02031006 66
    0x207400e51f228004ca842c100040d503005030106860401246183c1e01c80a500d107140d400240034051002e088010650100401c00390640e04254012907085006010301c4000252160305a1000c4981484554072880c040307601400c00581e000c83d050510007841041e2a015015003407205081c443c40c660a248641007600383c81c400c0d0760070b40e52880c0507861a04000080c80003001e014400c4370440d50085101490301300c0c0601c7d40d5001b030383c810a20703060103c064902030081900070640d080e0300d1480d540c0005402854001103640c018814180042c40d21a1038484003003030643c250b00a8065011480c000c0b00000f1240e0700001c045545000348000542c032051910903410f25902941d4418034102e03606042e49101c19800761902400b0311907407000144000e50020744801515505040c40e40712141c141401504242200d80241032042c469070f149105080050582c1807281c1d002004101c2e07458600211742014000446d440040e81c00c41040421070000d50001c1d4041e00c20900042c0d03000e581c40d4001c0300c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 698226438 1250 698225188 698225201
    0x50d0b060a0e040b120a110f040203040b070c0203150702011a01050c0307080d150810060e0f040f0c05060a03150f0501051605030d0c0804031706031f02160c0f09 71
    0x30100b0002001c81d01c20342044e5109005052002e402c03107039854580c2601030b24090321440304951011600e0203e4441741082403012002c2c41040c0c0b0103608508141d9110a00320702c00524020410410f181c0660656504014520302001000a004030f24205900300078064040382034030306907a07914503840c1d10b6194812012226084004000f440c00d040180c0e450b003c0300e41c48140b2014500d5100c011711803035040c0ba400340c0c8000706840001824420914184403040d28147c1d0b001d0501d840405040090b40c00030818201d80c010703405480049400300901c0c0c03052040415801c0300303800c081c01049050082d0382680c09125503401204002840550350404507200c0002d9005060000d9001c0c4540c0b030801d0a008400b02c0385070310070310941e070030409102d4001003229241c001401c0024180000c0c04145034020310300380c0b01522030000c40b070014540103000c0380da170398945454820400120030942e81d65401941c10f031000221216031581d10b4000e03c0c1000c03010400c0b2400744003295402102c00003a150034510036031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 698227688 1250 698226438 698226457
    0x110301030609051c0e040b120304080c1c0c03320d09080f1c140a0c020f010302030f0c1803031b060f0405120306060405090a050103061d0714030c0907050d0b06 70
    0x5a03601c0000005100140c07e240c403146408c2040040300201c020b00c1031001c0c02c081c05001000348070407801d20080000580c2481c541940300f0300c0d000c014801090344502400203a94001ea89000c542c2c990300d036a0010002d9108600741d850b50044454140280082080fa1055860342e07101c1d0007042c0ca55280b9601e03100b00d00d240440c99480410071003242e00e0341212100001c0e50b2800c141d01400e1802c020b07110182d02901e076801c00038403e250384000314038011030070700d00491082c42d0460562401080c16940190064110f0708048004600e14030000c4079103c609a491a01905480d03e80b46003540c11364155452a24140c0c1c180111000078550031101e80c003e0b172146802c5001404100c14100303527a40c00d07a10161403e9008030b41044040340685600304c41034090350034980006820361550405034105d6040c4000c034501c8021444004035480e0780011510203030340e51115414081e81032140001d280c00945408a50440f0329042001012a0084054006001b049506028030740400e01008000c2c0310b0080b62 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 698228938 1250 698227688 698227697
    0x21602040c050a0c412a0d050f07060503060a1a07060203070509101106070201050106120e0106090e0607031a060a030b030a140c030c18070c06110301030609051c 71
    0x181404141a0811004408201110741000c0c00c030b084409680e0005102c42c9030118200440065405c020801a450f405026441d59800010300c480b12030110310345035014184038440030701415040c40400e0100301d0390b882240b07003140c10060b40c82002404541044a01501c41c01590600065406008080603442d124055a00b031500708259500d100a4200bd00340904100051201c0012611008600c402d946890f480e0010030300128030740107192000007002d00c0304690401004006507070300400d000c0143e5008030000f20b51040031000560040006900000b140350514802410784000440d2941c052030782980c0a025030054114688000b5031075103055130300203108002e030354005842940030074004e40d001400d6500394940c030f444010360754294045541040c0c0000c01c2040c0d140c07030108075400409100ba501195001c8100710061104103008107101c2c04d000b09000c00008000c0b80b07034044410f00306105c990355101d58407800c050000309a1040d00729150700c18070303c0b4030b035500d8501a000ea402d000d170bd0340c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 698230188 1250 698228938 698228957
    0x50c0f010f09260f070614190c021606030b0402250203150118020a1b150b19141516020109050d0b0103020f060d02040306020903070623070312021602040c050a 70
    0x61304080d511a92080c2c0700130b5941c60142e4056106511160700032150b941c8050524141480d00200701c402c070300d40000c1994408038654415100046980702103482c43e060008500a1000106000e80b260118415011491440c181d0400c051204044005d41c0250104c809401c0d180108240c849400c0c05002d50b00404000d0205039007160303400500c00794640b480c040000c0c0d52825545400314101d4407007103075042c0d158902500205030b03512450303011403421140ca01010f03594086c0480110418011641540302049603210251034001e04195501c0991780c101d81c0d0703080c01c0500081c460035a800c040780080c4d0a1040000d1902d031182c808080341e0307004403000146910350760802ca440d011000810340c100005100c03022a150702440038000840c0900000360361625510100741c10450680c10400074801403005100f000c0d440c041c0c0c00e0140d02c0300f510307443c0e40c0ca100718241030380c42c0b92650345410728441c00020521545111080c030040342900c20b840c00d03c0204072991058600380142d15400000505010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 698231438 1250 698230188 698230207
    0xa0207051612020d0f2f010c02060708071b0305030a0207060306050916091703030402030606240901030b0406061206061e050f0708030103050f0d050f0a050c0f010f0926 74
    0x800072144d052107410140b860a03842d549015074248642c071803c61282d64484541d1076400800106508200b091070144000300051740010500e000d0200301600070240480c1c03000800c5030300840200c450819584502c0c000356640340295a941c41002c02200500441400255082c040e0003102d050f5180100b0054856951034001c00e0b01c6041201034104009200c4000100705800380c0d4111001010351001d10790b00c0c5024018549088005801180550032008001c4400d4036034035118964001001151941d038030603000101e01130400740280c40c1c6d000786041030020b2082d42104250200d81e582020a0014a507241400c0d5440d44000b0004c0341e40391466440c0046040c4500010602c1441c83c101060600382c0c0f80d1500046600242c000722081e900c43c81c55820880030400c0080740302c200a00d000c2c1d2520078000c082508a01419950724240040482c0d5224811010b1000544580041d00200844000c03c00340320064001c4600c280e4204850501381c00c01c16502c40da41000d05004902c0300c40c03400c1e80d0107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 698232688 1250 698231438 698231449
    0x1d03150a0f020a1e0e040216020a300311030a1709010507050f071b030501020c071203020312040f0501090303021e120f06060d0507050415030b030703110402120a020705161202 77
    0x1c0078100802141c00018800e86d6503600c0030f841c80c1090341d000e01e4100d002d50f1041c4004030b80a500101c1f094040d07990305a030002d419040201c564234030504001070030300c60b901e41646c9a081107410b0b00310a0002080800000d03611080d02c134190311005000d100d240e180d0345800ca08032101910700c280054800c1011001c90390641004182c0140703d05200d080112680741403c2510065400441c0c0311f03500016514141ca804000030f50191801ba54010104011a500a9641d10800301902c25030302188000900384000350221020042c1c1000003809062181d250050080d88070486000f80144a12485501041c1000c20740b229408100104011620b5407070080b801c007440100f03c10782c4800c04002e222982c0700303240646405207505864558440d030820010182c0f070a909440441018a00900249140c0d80020318034100c0b41c100390001051341c1e1080c0420043d00c144025800c551540d101400114840c9a0080c10001c1c0a0f406440c40c003903940210355000010f07803042c0c1b96000d121032046405031401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 698233938 1250 698232688 698232737
    0xd030807200601030c050a2112140d05040b0c04030203060130080408013603022a180f0106050c070f031101081602030a1d03150a0f020a 60
    0x6a1030a601c010050125061508000b41c0048401d00c0004d001084681071642c0f000028096040780007150b0720741088010340401e0450790160440d88845022546a030181d01035144802d00c40c0d0035030f079854100008490180005940455494000700000780310510003800382e500f9242e005014110030391901c94820300700300d29008584900d402403452815106180604d0718010307441903074060380350f600d0f080d501821035005414050f469001c035950a9403425106c00c0540303901541c60400e40c2e0814050608911703060306203d030341c1c001d85105ca912103c82d06902558007015401200c12144a08000c10709031003041d810340f800000c0ba802c1d040103000307150280b0080e00d0175090358000c030380700c0a588456108c5150010f5006031411421050707140e40c50350780001031b1640003520301510584e2007000480295240728120741d05041003011900e424054400c02c07000007000c28000c08a50f150200110307031b0500f1400555000c01c0d07641c540050341412a142c6e0080d5120b2a02170784450003c0c240801151084005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 698235188 1250 698233938 698233967
    0xf012715080609062208090103020c25090f0902240708040303090618081b0a0510020123070903151508011e0908032d07050a08060d030807 61
    0x1030340580070a2098040010500c242e494100501c3e181c2804042e40100b412017020201c800041440510b012078160350171680180020303c0e00580e21000d041d4100c1c14408000c00c28140c20611060305c000041d41061024182d4215040402c00c1c80b40a0701c50700d00715456248025045801c0000c0340c410101254084801070b82c80851070b6190088c25034944200d03031b00c607400c01c40c08213120a0082c441d065210700c144080384411080e0440150815071356035550302800480c50103603412003070404a10340350048400d004000140000c80000038650000e4040c200c1c0d0f1401244150526082890800c0440724007800740c003180c1c9982d20982d06607150f41e0488542c000c0114911a180e01c46401e0b403074880300004004040e100d000150400480507842d8542441c491030b194581c2c1001003000c003217040b070300440e44c100d605032a0703203800c03a458042d40c2d547c5110381012242100b10300070304106a20b88c2040c014416200e0300d076075140c0340395106010803944004401014000070ba4000c0000c00042c00790300300103841e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 698236438 1250 698235188 698235221
    0x2100507050604030c03080f060109030605060303130e0103023a29040203060604020406170702010603020303070303050105011701080a02040509160609030210020c010804170708070b0f0127 83
    0x555580722149042c0c0107490440014411281d16070506500000c215003140d0b4042e000b03882800c180c0300081065810b4040501215a540d010a0603a58100308035200a158030004000085d07850040940070a4240b000741d008250b500d441c22424041e00c20070780e62250740907840c410328040d140c00190440188560444000d440c0142c50320081ea100c58580c1c04044400c0c0700c0101c070340350070310505007080005008103016600501c4148130082d00442014044071440b0403c41c1c2c1941e5030f1030200c2c09031081d0b03031000e509404000f49800c18998107822040c103848007a03c88650118002c030503040350610910849815811000c1a6001480c140c0c04c01600a9010802c840089000314440074403410b03d98880c2010a40444040085082c05540b8041c5130b046030020303200c1d013101100080d0403018001d06c024100100310805a0848240030191650a608403134030341d0b140c0da000e1901d6184464142d0310104091a4900006441440e20501002d8000c0e645805629000c0003007010000e0610705c1d08648041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 698237688 1250 698236438 698236447
    0x303061005030910020f0d060501050307050d0908040e04050709060614190905040e010608010b030f06060121050c0d1a10140906160b25050a030b030a140c1c021005 72
    0xc10713540c00504010010702c2c4009a41e01e990b607420004850041d0702850500500384104100680c101c415104c8090b14000c000c80d03803034018645004d551049421807864260014144400d0000000e0560191118600d041100d81e0702c40d05d00b9104801480c4c0134040580c801c0040c1704c0d0f50740c11480c114009100c2402d1186c902501c0f4400201507400d07080f80743e0400c2c3c4d59035000b00440e10b42401120302c103408c107402401010b1508419143c1b00c0100800250510803640054450500005003114100560120400050a000480301110742c40441c0e00000300741050700080c464260b12842c0059800018003489800c0d14100027541c9400038030000070b28ac0d49007403100c0001521070340000e0405040c20364900382c40c2000e5107000b82c00020040d0a84043d1103481017507011103c20707c0e8220750844a142072660312003100c8174045010b8501201c4194050003010703804410480c3c2e94810340d2258600000b81d40030302d02003601740213a040140c9044401c8104603800100903050180800d4209030251901d076191 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 698238938 1250 698237688 698237713
    0x30106050c03270a121101030209031c02011401080d020d0e040b040203100306060b0307020a020405061201092102010212150a03080f030a05010e040b0a0f15031b060203030610050309 80
    0x85500d6000c0101980c50859103c4030350b15008003000040c0107951140000c1c5051901d8258803804420720250502da40007036a050242e40c07c0001080324801200d40c5440c41010f81402400380000c480040820210000040348614000c1814002d10845500030004050440382c111040c5019054150700603030358402c2115035882d00d0008502c55882c00210308006440c5140403001c83d030007640702400d96101030041c0481c242d40070441c502c40302d8040350089155210540015000340402c560050558070300005e0000300188000d8114460380340000040108002e040186d090b8410310310680944540c001c00640c2002c4003440714110b40c00045c12002503251030303503180c42c0baaa22182d140b002d941d40100c2080700c42c038558043c460262201d51480d03442c4e07040503a6000311040e4054804180c498480c21924400380f0140c2c89022048c0c00c65052a00302596418002d088031416010007402c0500340030081056400003044a0081d031001d405090700304a5032104507025000030704403c80e603000c0d05100c00756 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 698240188 1250 698238938 698238967
    0xa03080c0c0709060f050102011401120206040f031406061f0503041412040f2102010c02040b0a1502070909030903032007140f01090e010519150c0b100b030106050c03 73
    0x906074a4500095a03030070035690700c845c01165031000341113a04110920030044074080006044692040e203228245d08284009002c90195401c24030b000d08805400206028000300d485c0305603222901920100c0e1200824810020701c01030452001c590009070003040310b80b15200442d889070060349194010244c4030321207410b0003010f00044404410104003800f002c05410040401080c200b1840e031200001000c04000d02407941101a0510070031520800075915240c1000440003001401084070a0319003103a100f24080e50300740d50005114400020032234406034810130302c029426442d842021842e50382c0484102020b00c6000180c040071004454402d1020861000908401480384220360354400600c4055280f040a03030b410411302c1d000802180e240d01d00404c0c10359806075007203650400b200d40805c0c071040103944001c80e032a001c50b03807840c1025489540c1000e810b200708405d0f40642c40e0400c480d1083c00a90180038040c2d80c0c1000100660390040004089000751803050303e0400525040303005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 698241438 1250 698240188 698240203
    0x18020c0307030f140c100f0f1104090b0306040213090201023a03052703070c0b030a06050a1809171b06090115050402090402160c050301060b0a020a03080c0c 69
    0xb8007080d250103c100042c2d0b0400300a403d02681102c1003820000c0b1030603c29a070303103002902259015510000591442401d03040108000ca90403024070160f60440325a04042d4054841c50b0f00151074501302e41070701d1074041891b90140d60020541014140c01d600680010414100205d043d489840042d1101c01c2081aa407440054a400b004d4000044001c00c2c110300004000d11104161900c1c040003007452581c4069501d50024046440500242808440c07031840744140182501c020040001940e003440001144030b80441c682c01d100c200c1d0754a0900004003100d02809000000c1000594100105503005003507e41c080c9540444000450b0300c079481551096130551044018201826141442003085a03041001c000007080190701e109068040100b0074000e0a1085400050354840c0703035250380645450182310350038120002540c0c5010b040c082c04622a06000c1e5003481000110207600e80240c0320500226000f81c09100000e035811a91844001d1401e03004101c18072050352203e404101d100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 698242688 1250 698241438 698241443
    0x50606041a0301031a09150402060f04120606062c030703060608060601020c09100603050a0b0a0b07170405010c02121509010c03141015020c030d03050412030b03030418020c0307 78
    0x780d41e9504500300484040d0040c4030f00080001c1d814280b0514481c001100b0080c4028560300d130101e82c075148001142840f90181d000c0c0c02580200c1c004c11618284214440564420032040000603581c003000da4403108a41040c0440c0981420038819030381100581900000004050742c071140e0300c1c0d50b00c031400c4400d07e8000028550204007000b100c0d580401144802e00800c440078a501e2a0141c0c0051051455000d41410103485001158140c000340d0800407d0343d0740100040e243c642c036880f0905041e0030154064500481c81c140c000f01005901c0210380503180180e40b9140404019000d002103405c17510031100c0103108021074010940c15034005c1034001c400520002c209406107920080a40d002c41043e00341c032019400034865031000c0403e00600311101d880035004038100640c000d0307040240c241c9a4030b426000d40300046003070a50652049101d144101c0041c04940d00466086003195102d8141c035825500030841408810440c81000c590005004000741ca45162251554119040030004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 698243938 1250 698242688 698242739
    0x5070e0408090405150901090b03240910150501030209031006180c090b090f01021510030611090a06030e1204140307120b060913060c0f0906030e03090405060604 71
    0x100302d894a82809040d8001d508184008074901480300000c5a1403010310655204036900c4541c0402c0391400e010038050600411803611001b500070311014a400c4045800c03a456004e1844185586a242d1096200c000b003889940d03d403071820400150029030003404116454440c10000e59044092030142c1c0010b840340302c1440300c0c1401107264101c166883c4041840500000e11002d00044031140180c0341c0e00e801c2152002c581481120041c5d0030480d002c1c04114044603d8810000341d00034220180c0304683c07040004100ca10060b00741545a80500000d10303901030385804040000300d110790800d07403010304050290742c03039100019a0b01a15512590040c00c4030281d00d066110285018410540205840700240818513038682da500c0541d0b900400980c03080902d04041462441080001c2114551200c000c007d60742d000c100150420000d25a080c0020740400700200f00244a4000e4001060000c001141040b254104020250074018040c0e90022814440042c0f42c0c1c0000300c200c100d0200d059103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 698245188 1250 698243938 698243947
    0x91202150a0f32090a08100509070909050316110a14120111030406020703120207051e0c03030a0302090409060c0f08010b031006030f09020303030a0b0120030a0c05070e0408 76
    0x1005803000040300f0700d8640c0c600070707408140540d082c0711450208040880d81040c0c0c3c0c80840310002003030244c1d00d400c104951310481d2250245010581d2110303006800007000c9540b8284e80345030082c180c071100f0b00c0040c4507030801c0c0310503980d100d070481c1401882445009081241c03003281d00421000c09107584010041245c60005465500309009200c08489203d4004e00148005595031062440040c10041c1480c1e0b0000d895014107114800d40d1240081c001c00965841c203041c200301d9547c00c101d44900381242110103004410a800040c01b10b00ca000250203141084140d61094000350002c0040c00c1d00181c44e2000c0c280081e03164030402c000c07200d003520754050100d00c03410300400644050300580d2040c03a0400a00460040d40e031a403400f00e9000381780c081540c0c2c80c07100860014007003540e4000e401d44404414070401a40c0382e08a0355089600ba0399031880e05da0062079042500c0080084001180c2040100e01900382c4182540103449005504852510b80e45035020440032100300c03000c1c0c4101c0300210717 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 698246438 1250 698245188 698245217
    0x915060a121529071b030506010e0a14012d0f030605040506090307030509090a0212040506071112070210170c0d0b010c0b0f071202070c06020f0706091202150a 70
    0x350b030b5040c80c41446442900f810151a18284144151440a07202d66034000401104040e15407000001d9030707002060f9520395a4408403a44401d03c251a181005420541c040700c419000d1340c0b040b07049600d40c012243d058124020700003d051410b4802c241060761000c40440d903071000c184603400540c41a04006117902c1c10341406030410a000c0d00109640d041005018003080d40002550142d18040b945004203448815221f8000e100c0c1e0000384120014010420060141c007042692146040741c40d14817218801180b49902d03400c42003101d40680c9414030450016003001154820010710f07508001c00e1f207a80d0140c6e0703071724030301400c8525644048c00060f6002c040712a0340290041d4030400c1c00e0980425070300b50380c2c40d03d9000c80101a08624001c080003d84454170071600c01e00200141e040c115510000350410300d080744454003880000d80302e400b6610741c80d0040000c08000b00c0d03180b9030f94041c0d4242441d443c2c0710440c0b039500003660b00081c0031191406100300d02e0700801102e0003584894141807810b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 698247688 1250 698246438 698246459
    0x8040219050d39030204110c0d030c030b0109060516080f030a151a1b19030c02030c01110d050c1501080f0c0a29070b04050a110915060a1215 62
    0x140700d4403414003d0252440a801829098016039034100c8001c1050400640f00195500070341d5007c101364401e00541c0889290540d00c080085041c0741d0342841011290301c0191075400303180c81200c2c00100e0800c0b0b088441d0b0b01001c00c49181c20320540c0b605260850b402c16040b919082921240c0d031850740c3c0c6007000303030a4003590704e150001c004c0c0028001c660601b08080d26894014030b010440301d002e60030160214088103200c09103408146c1ca0740ca1075540051b042c018516500a00100d00900c02d490078449190b02806040804d11000310050845507115201240c598100b00c3c8801440d02c111070361710ba0100100c17103c0d980a4003502c001405c4009100d9600d81c5000c0080b0030355800b80e100035006000d641e07442500d44d4042c554084004044848007401440d6034801c15a024000e41260340c180410070002189982c04c1d140142018000c3c40c115604001c421802500d9800d060a5643d01d685501d0034400050f1021800d1030400304418801c440750b007819122940040040d030042c1305020704c10b11459 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 698248938 1250 698247688 698247743
    0x3150914190c1b050708030a020d090e0408070f031202041401030b040504030915050c0601171209010804110103090b27010603020f19090f290108040219050d 69
    0x4101c0144000300b040480940f88507052400400c110141c4807482c002e0207802c01000d8020015402181e6907040c240800a45910032990250001101d038003000400c0c44054074441d00440e088140980340c03081c5540c840c80800c550304800c401740101108440410000d500c040c1005103030202d074001c82403c00c0e600040c00c44004065161159180505100101e07500064010540307006010000e201ca00030082a112801149460480f51258000119202480c0310040790100c8080080302c105e4a010300048445005001805002401800010703010602c240b8064900e2103060500041d400c0c070030346424440c154102c41500200d04152070801502900c4600b080b0b02c036090100030012541150f00180101c425005a07611401001e1890305104500120500040c06420030400844100c1c05503407000c1c0a80340d010074404000101c0c05413084000000c0d01c110104160b4409145039a5a07082003030f00d40210403207004074008004c0110b882d171210201d4800303160207481c0749440c0800400d603106801e4030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 698250188 1250 698248938 698248981
    0x9051b0c01270b19020405130c09050d0f0b060609040e010b0f0a080601092003090a0b0703140f0a1803020c1207120f0302100606050c0106091b03150914 67
    0x3101c2c8110400325202c3c00e0f5007600145640b80200c20980c03908041c4002c1c0c0105e4001c03641c0300000c40703c40c40c0030365401e40c000306401a440e2600340c5c103950346808007c0d072008038600c0500780895140d1380d80c00064500ca140360b40301c1401070841c0c1c240b010000114084850b010040c030b90580d1b503031050807040e1900303054440b2001c104648044801d800d2181c0c0c0350300c0d20410300c06da4600a0b2a50b406a620420718058202c543e014000810703220300c5c3c0305928503038650701140d0642e030145c0301c0404606014401d01a60b4092500100c1c40007454903600b42d040c46042d00180a503201c5695034046042e281d0a41409003006c41c060f0340104403480c220410410080030742c5034000040d600841d0208050890010b000d155150407462242a10602d070809230f04090b014202d05602e41e181490118020703030020003030640900c1c0c05000304005070301e921303001c01150b890740100340d04080600542840130344260410445040410a40303010b40381d80314800026a60300c10480c03a550841c0c43c08100030702155002c1c6c40e11040f03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 698251438 1250 698250188 698250251
    0xe03030406020a030305090a0803091b010e28080f1605040e07150c081216030b0f130f0c0c152702180702030c010605011809051b0c01 59
    0x107151a401075556040e00900605143d115000a0007070002400300c00840e07a041410aa41c83c604401c4980c0c072000d024002d0311800c0402c0c40082d04a521881110304400c00180010318819002141c1c152070141e081f032002d400c54104007000c540c800b4140302400680b061a40103100c0200310701d240d0196101c0319008140514030f00107100540200c005450011548103e0801c0c41024038a00c0031100003142800c05040080002054071010401200301446144101207010390516001d404034244c801c0d80c0b41441c1d004c0440340003001c0510384204204100444988000703030b5558603d0001e03068540c801000e2010440d0049082d00340207404075400c1e2001800107040000c0c0801d10100e1195401a070722005100003000d101c2001c40d180e0049000703120580550003001c0e48ec0400c0000d542e030740071161041c0d0550802000040365406441082c000d507000300981d40c402400e050583d001403200078048540c01c9011604c0000d0300c10702d14020500444400d0001c80e99602c0aa0407000440c0504480c22044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 698252688 1250 698251438 698251447
    0x6050909062e08100f18020907260f07050304200f030102191b0201080f0a0213030b1b030f13080d0f020403020f01030507140705011104090c0e0303 65
    0x180c0441d02660041c000381c0208a40356180302291542101034440344200e010300d040100c1c01940c00a801d403a182c0208800784007940070907424500b0303142d81c40314103140391440109010041c60074050103684004103203040d0105821004052042c50909501c201140c4c1104007400303140e240d91900e003944254581040d03441c40c107180c0d5400a80611000d13101000c014031440c60300302540e0381c441c919010380e8010029510f038000c4036240d0100c2285240d01c1001305400300309500121108814003003100346c058417204029a070750076004c6010ba800a000c004540e0b820051003241044902002d070145006c0d201c84251440d004400386180380e940f12260040241c10b1080010590445940d1503001044402018542e20316243c120090301810100742689810030039203151445941e8041e200702c900854a5902003440d071001501102c4099a10800290b0a030b103048071181944002000b0032031040300001464442c0c0b0b203c492281d04680c0010a98644130038116542c513610401c2c084a5900840141d441c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 698253938 1250 698252688 698252701
    0x80403090e09030f040b090f0a0b04030201050d06080d050403060b0d0c0b07020328051c0212180a030b0f060406050907030f111b060106080f0a02070807150f060509 72
    0x203032440c9108003080324403800c00140c041c410500680780303d44400c00f0300589403903d515600201d034000320200da001c0c0030311000058151901e00044400c44401c043d10b03625190464004660795407190324010580d03a00c4200020f0310b4002000140d1505080381c0d01e032600c039820340c9080d0f0b059400112940748503d0176644207501156903141c42f0f00444181c0099603558121031710119080c202c40c0050440103000c181100c001c4100428030403010107103c1c0c402e0318030312041411000c0c881c030794481d07071100140d0003102c0603001d00001600901c80e50b1010310b0210400302c400d00000300c4614254108840006685003809500030b1010000350308551f049034103108540c105030116051900080240c4201511142c8104580c0000d60103203050304820030040303a0f00c1040300902c004038020300154107100e1180f6400014002e110f0b85116000301d072170400d50f100c5502ca81e10762502039000400246c5010f8010013100f80001c21b079103003001d00c1c440300d180007103801061004c040342100c00380e074042030007401c018080000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 698255188 1250 698253938 698253947
    0x30821060604061b0b0f091e0304090b061209010f0e061b09190b130e0f1f1206090506090f031b010603020307090603060b0105090102190809060f04080607080403 71
    0x1a5a9030389044e0860110754102034903110800000074107008404001e00905005403003000e40b061081c00d00f200e140c50001c0f440740c0c500001408500e00302d43c00621051012002c81d400a400c2000010320306401c1c00002240802169030540c0d151425030b55403e144200c00c0c000d8044c600000c000f072405004240360000d4020380141e84000e0301004914001b625658556805006089450861701000c1c140d5455024101880d40b008034038000c501c002e2080007900181c030a82c0d00e0b1084210050f00c4080b519902c01010201c1c5c040e000604d65466905070105400c4220781000c2c001034080e08000ca084800780c20302c6420010b02810759a8550030039051180c159400104035a812505910f09540045141d1031882c010902a04020f5050182d0200040c0e4008190008415280507110410285640c000151001e2060202041c0540c2025840c4444100c1c0c4450700140c060041d00300310315000c03112000481c01c0c2c0c000c0f20030b43ca4002d0007050074054410708102142c0c0c0f1440301e08083c0d01a0809482c00780 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 698256438 1250 698255188 698255197
    0x10504090b0609041b060c17040302030d0f0512160306081b09040c0e0705130e0618180706020109110a0b0306060304060f090c05030c0a180e160308210606 68
    0xa01683e80c08011074200700201001c0c1d9081040b090840b8402138036644000d02c2c2000e4141e0a0355803c1d080c1080f10008400710341143c0407240e00800400c14401411030a51341d4401c00015442440000e1040000754a0f0394100f81d807040c00c1d45070a2403500c082011003c1c04440c0c05801038007503036203d1000c9841035050044036200141007250007010940d124034000301d42450b55000320541c0004071041c0702885030410080e00301c241c0c0d0718010400c0310f038942c00c001104c02c00880ea080d90054000390341145c60907414a01a0300200c000010146a0300328140c1d04c2d143c030802c0e82c03104005070b41d03420302e40d001c1c02a10300200b400814101d800c15070441c07070181119140c1c040640301c58802c4900101140401c4466449085114001d000034494454103050110682c0d48502c00c80d406801002c4445800740761101c1c800b0140c44020300d07141507404651101c0c100801c1465450000740c81346410030b002020034961a640110b1242648540d01c0342c007814005039815070100181c0300100034505000007540c5000a84 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 698257688 1250 698256438 698256451
    0x5101b050c0c030a06050709150801030206071e050d02120301051f0c0c0311090a0513110d0515010617090706081b16033e0708061e010504090b 63
    0xa5141d640c400c040500300440394124a0b41842400b00d11020805107400c075501c610450784600360101da591001c03000c00c09605002e0000902c2c10300040c801482c00c0703070280080381c0c081d101c2c071341c04441c0400b40030b40603089440782910f01c0c0d801782c00681041541004402c2031107040758065400c41d4581000300b0303c9003a05581080030070500c10342c0c03103000901c500200713a0740e0382c1c10180046405543e0b0414004580d03440340d40703a001b0518440003c00c03030f101d54000e0350b009103940d1014156556640d26020503174211b42c64001e500421001c032007008100d00300510100c1101000c011209549400c0300904020300e440d5500c903104500c10304002c00a44081070320b00c12100700e4100551240c1e240d43d05102e030802c4100307001400030400b051503c04404489205400e207442501c2d4042d12034a00703032400800c5080c10381c60300c0e2882050342c0b40c0030102d450802c0d0302101150860480b0503094482003e2402e00703e0860740740f02d401010429601521000c448036500504003079400300015880c0d9240c034408208000c115 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 698258938 1250 698257688 698257697
    0xf040603022413090510050a0506090f21061602011107030c030203090409030201021902072603040801020729010b030c0307020a081b280f060f02030f0405101b 70
    0x4141d4030082c400e0840e204886020204400a5281c25440005040580d025109400c0c88100801c007410b04450180560b0030042015040050040410003940c036402c491541180341c90905140c101c01e8134024001e4402c210002d400c83d03203082e1068026829015400d0380c1160f060104990348100c40200726141e40b50146041001c007000790400fa40345108110700c181d0082d242030740042c01c0c550b0640c0034011070a5180001629080d900340c0072603031000940074144c0545c0021a41c0703c00880004002100c0000e40c0c420340381019907a000c11400c90f0032440c42510408040044a150040703c42c0382c50f4000031029034444003039410009003602e61302004000c014040b100001003003000f40204400c00050740e00a01d0f2603078a41c2240c0080000c02182c400755142e62141283c1c06444c0109d8586100c8201c201d11102d29101029496107214607a640b60152402903450f401d010602c54140019440340480d24507903200b900380b034900185800001980c14007201c7c60002d14109108014201d01c001d80c025241 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 698260188 1250 698258938 698258989
    0x50a09080f220321030b0f010f020a020904210c0807030c060b0307030327080d08191107030f05131a0d1b03110a1b08090907020a020f04060302 63
    0xc450398150020296100000388494000104840500c40a070103c2d00703480d41004d40c0b05400801e80076255442044c5901c200802599106540300d450304d0b5200810314412a045c131070701e940104007110420764064800880a903807041010501411415100342c803498004201c8401e52183c6403a401820340040070420740b0241032043c81040d4200c5d04100b00002c0907184800d669141c090f000d4102c1c5028254803a0401d400705a100c10041050002c0758070380c0000e03003044520300310100d56100000340401d02d84140181503005136031882c8a45010801e0f00340d10075507078200506001d00480c40c0b000c03070300c4100f02c0700f080000310308001240c1c0740085481c0e034281071a08800040e075024403805180108410346181c1300502034003180303542903815440040e8404000d4450401c8189072035204004012021500040ba407420030105054030308016802444094141214880011559901501c200c0c2c0164800c0525600350300d80180c1d00301e06c7d00f83c01c8504001300b034959408106501c0c810150400090300b00c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 698261438 1250 698260188 698260207
    0x2f1006060c0503040b030a290901170c10050f0711041505130506010201020c01090f020a0503060f07050306061603080f0c04080c040b061b0d020606181f0306020f0904050a09080f 78
    0x102300c40001c5030b03011001e04000c0d074012541c1504510818160f8400e802c803800004260703505148441070100d443c0040d024507400381c000c0c40f200301184440f14081102c100f151501d03541c1d039103016218141c8100c940b01504030202003000700f036071024003109207500f000d240200b0841e41c07240404a021940003c0c003140a65603000140d0080c00b98054041c010350801e200c032410440d8190244030110710880e1894030781600d074400d2582c2c4500840d0404d400399000c80210742224000d40285034071140040006281c07200c01e201e050078006411074202c000c00c1e0f1540503c002055042665584070204110090a29280030411951480b105580e00d015650b241c8100c0c2d80c80d02c4110403582492000c000661022084195181d9034250184c4c450707005024100202c0d50918209480f4030100194050b00310305038480c50000142230040a01c1e055010040f418000005101400a00326480b00703598020f44036202d01e424481511801001e2400035494070100c4000554103d00303640c2003a254103122510ba00c2c1c8007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 698262688 1250 698261438 698261441
    0xe0106030204240b120408160f0f1103010c120b010309080c0627100522030f1103071208100b070606050f09162f1006060c0503040b030a 60
    0x50304040c0d046414200600c1804090458811409042500005050b6a035051a8540340648843e2080c1600c00c500401c001c1001100030f040072100c5e82c4508080161640c2c5c54090340d0a828204554420b5000c0411081c03100403080890406800c1c0c000340950030504d840140260a8910210841591080e0f1400d56901c00e5020100c1c461b40031b51100d55482d0007511460b501d0a00715511100320200ca001c10500c03010b00302100e004212000000c1400f41441c2032040d01404008200c0ca001d0548000383c401a40d000440b10b1400c1d0740070361a02d40040103900b100030300a03182a00503000c01c0d4010800000000c0300040c00104c0702c10286059803a940b12081035402180e8142d12560148101050360010b00c80c2d541d12100840e5000c665014088420800b488550340084404881400c24484400c03103050040c800d42c02c1020003d112211100014912050084a14120701015611210f0b0100141c2d174580300c5c0b440a0603c90030070001c00c4140360b03910741d070fa4415070155107249140800401c40c100500d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 698263938 1250 698262688 698262701
    0x4140d08040f032d1a0c1c0e0c0616060b010c080d050103020a0602070b030a0b151804180816031e08010f060903240902120a1a060604030209150a0f06090e0610030e01 73
    0x440401e100702907515007d017015105076050902940a8041100003910f0601e00320380e41500303042c540c188000c502ea02ca4200410f014103001d0306101c0c0031140b10000511210003481b409003031800004441d419401845241c9110303400600c00d641c080002402840c0b42c80081e6a070000803440007086809810010561850481c40910b840100c04600d0170501000958014030a007400d0f641009034070442c14a40c03401c05940807000d0203694040041c481441d0704120b50b14040c50090070804007040d650149030388048518022580020096401444880c1a00aa080051206207404584a802c0d6140c000c040a10100e80e005130403451005090518290340159a019070018034800303004000c9010261500790500c0d0484d0308100074568a001140f80840590040078050942c80c20035041d41e003409441034000c0d01b071030542108120405002d64940a811024242a00601c122a0f1034244046c6c03989a141c2c02004181c20580c04004027510b84080d40c10f20403130700e85000302e1611110401503004051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 698265188 1250 698263938 698263957
    0xa0b031005041b06020601180203070f0e030c0a090c080c0304022115041a160f051c022a0d0f0f031b02010509070b04140d08040f032d1a0c 61
    0x8010004229170042210b50498400282d54200c0401c2020349000300d10040310900081745130140070300c110b240315190760303020040040c046450f2101c072a40002d8005841c0d80c400c1d45100e4440c000201800c0d88090000d400c80f402184050660500d540000d450a80400340504e030048000b0f2403804519040081c0f0512a9010030860300c1c6046c94207003117204031201130748204c0200603c0c3c0420300c1281d00c4034034481d902400381c0d180905407042e5402103886902a10030b0000b4600484542002c8400c644010042440316200c40304c0e11341a08e2046d4940c076407141144c0c0c1890307000316417111703c1030b600a07045410106051819010030403940390b00360010040c104c070581d0fa0351000c3c0c0c8649515030301580701d00e0240140034111044650ba034210000c592040740074100401903050382520607411320440784400148110041800c1603180c0f000080108980e90050b54900301c05040c1150520360b040e14a982d4480317400b15411030f20020b0300d031406925004400d403143346036860300040800c40000c0c15585c8446 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 698266438 1250 698265188 698265233
    0x51314012003091c03022503020414150109030b0a1d150423030906090d02130603061a3a050a0507090b0d24020307170a0b03100504 58
    0x7940c808080e80d41d81050051a01841a41c0038800c1d0528142076245071007541035000341503203c0d14918000800c5034000944c000301803c6503010005903070f40e0041050303090044036140414945980040610103082416505101c2410014404502160a020b07404000c800c404111080d04031402c50340b04006154509490040700c6540000702c900c2110302e40941e0081c100c01159000d0811041032519a0320036584007503004004d1202c00e810700c8000b910021500501c42d41108d12150040307000c00c407503100a401c220766900010f01c200080b503c0f6504444001c0c00c4502240500c10010031a8441515045c0300e1030510402d010340040c2c000c16403040c1e140c40c030001e444011805417a10030b0760b40000308000c491038000c40c2d00c04162004284150f400c0b481d001040d80241e5042c0780c58018070b40c9401c682000c0d115422002460140c541ca00066006d407105644403a000f4150000707110300704001510b58031300541070000c2c1340f60a9400082c511255682c0040001e032a403035510340050a15849101c04604c3d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 698267688 1250 698266438 698266487
    0x1407050a140112110702121c09060207080703080304030e150a0203070b1806070f020102071704090f0b030706110a0506180d020105010e1914160f05131401 68
    0x1d0100e44104580c4081e00d079001a0705070300c1e02e00c00c1034401109842000d48014000000585030503020840006903542c1a04c01c010002d460099075800501d80080200302070004c2000b00540c100007020080651a001e03012860559640410b40c1c0f0014101038200903050140792050340c3c1d401021860042405a900c0d628800110f002c2e44a0308100c1040e14000b1001001560710408000b50419210b04807014080303642e640041038400340441c82501003199800d20801000820b81c11a0591075154040342503111483c0c211000c040e03480d000c075446040d074201405901c0f0b030748000820005031011070805803411081085a01e18110540d100980188259018030501e070101070501440b22441c0342c00d960f00d00c00e181c00103a080c0c840a02c19412404122800140741c8540c480b030094480c0503880011803664081e14480c4005d00d01030714a01c4200c00b442d20810a06900196440d00c3c0304880d00340030707081c2400444400008407272846034000108441c8030032a03003070b1711030480030ba54041c2411061022 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 698268938 1250 698267688 698267699
    0x1503030d0f060f050105160b090f150103140a05060601050f0909010e0114150a08060f0d0b011e06020c040b0402091c020307090912030c020705270c03040f1407050a 72
    0x41e0015205620701e0905058004c51075500c204121707284100102440d81501c50341c2d545d911a5002e00400102c150f02446107400240e1500740100c0f002040f000c00c89080e29415410301c1040d00715484001551a840348030114000740740840c1c0c50ba030001c024200781d51900c0030401410814403400700300302d074803800880003c1800b0f01e511007018180d450f001c0034035640c0b200e0b0005001e1610302e07a80540120200070f01580742c081d031050030386550001c80a0107104580201002041d507524a15008481580105006010814000148150905114440843c200d18200c001382d19140051003a0f40a9a144d100c003050300d88842d01111104000a000c800c010004078a00408100200c84228424040d1010010707a400c2c0d61301403000e0b940c4e00680d01820f451000642500100300002c4104258050480000b034143d54100555a2203c0724180c429107841c1001115000c002004000c11040e0350240305200210380050380380814982d12135034201806d007100040c589480c0d01031780510b50181c083c80c40400c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 698270188 1250 698268938 698268941
    0x10801020c062d1b0d1b03020408060103152a02010b010f0905130204170d03060b340503030903090109050a0b070f0312050c040e1608060f040207060c0207050907171503030d0f 77
    0x146c5000d48408140601c0403044102c041e44541c3c4108551317a80a10018808500810030310460030b242c140c00010b1950903074446042c0d2128050700d00300e1491950681490003502070181001c00c0d8400d103041014113038503400c003070072018190054a00860b20560314000c1e0042650444011740460b1904c4000d030342c1c1c0440c240b0703030712180d440c43c0400207410910b000840e90006c04c2036801d2500c190740101d008008018074060290600d11104110b2440340d1442c0c000300b40240015402444141d01031a910203100340050080b407411390003035014140e82001040104420015940080d81c80300e0814410407060408540b14000d02139050110307854131047c0486e00300400024400c0b10400600050140da0b090080c0c2901020b070290072003c54203070000101c40d403401c54450300030804001c1c4010304255445d11413800300c1d02034400040159009010601c01454401210f42d84001e00380740000030303240c207030754001c4040f40b01805410080000c005c0d140d410780c1c1c06005031090030303c49100800403203640405103030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 698271438 1250 698270188 698270201
    0x301060e210a14060103030905040c05120c0a030b0901050607171308070906060201020c0a02060a0306080304090501081c02100c17040b0406050a090830010801020c062d1b0d 76
    0x4a81d24034880b049180b2803c0402d130b0798100c9130191100d010340381c9880c3c24000540440e01c0c060b030401204028040a4854026100b40034000c5404203988442030700300090211661710300c0389031103800d01c90010002907480c803040711403455000c15614001a4039100b10f515900030fa08544000d0360014502095041e0001510411903059040c180040381e40c400e001d074200d03c03403e079040b0000d0700b2018005002d428030380002c04840d842d51034000f0b803050ba0b6108103411a08240c01c909000c80c1c0b00c00042100220400070a20203400f1000c84030b4103078100000c043e41d0b40311440340801050fa01c0381d00440819004280000d025241842119600d25040c40c002804240840f000c031621444c020120300401d46c2d5214020380719a110340c1301441e1400d810f400368419802aa542c1c41010b20a5460410116111080070300a00d4200700241e1200300314800c0c103042020003402403000d20781000f40034500303410040218414244036201c41d40171791030f0030050600da62410302420801110014045411079050740c00079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 698272688 1250 698271438 698271443
    0xc0a0506060f0405240105040f0906090c020303160315030c170f1903030e031327021c02070c0905190b0d021f111c0813080301060e210a 60
    0x11458205001c00300b1084074426102c0c8211344091704590f2401c0c50700111400103507541410302a0901d692014201c40300c1d03071136421030345d8a00d8403400100f204502c180280368030080d040c0041c60640ca000d14100e00e0008440c0f002d80101a2504800d09000046008540c0a503401104003000e403612001c1000c0103035880c41145110340300f403044200390f818011a4003001034015400f40c1c0c641040d661000c03005468100050951800704018000d00d000704296407100902c400c004c0110250904c11900050302c0d901d000340304199004106481045580f607540f40c0c1010825000181c5070200c5080641306054035800440e42d05140905000c0b114184601c40e0b0551409007005108001a00080c01210340444400079086000284440e9400034501040300c100203a62800500480806919501d4803110584500e0f600c0311900510200e03560202c0b0082d409072802d50002e011a4803982c0709645448140729140821074443d10741e2200e1350714441c2d0810b903298211645040c1e0b0980c0031500f034450b034940004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 698273938 1250 698272688 698272699
    0x803060d080705010507170915060d05100c0c05120f0910030b0409081917070c030219152702060f040b210f04030e0f0d02090a0501080c030102070b04060902060c0a050606 75
    0x8e9071b00300000411f581d000c89d00c0700c505840398031034000b441200b103504a000c4805000c1c3c8491220038006500c140c0b9003074921651a101908881d082040c100320141c2c524900342c0350304110100b150400e0400300c90310442e0580d042c440b01c45114008500134130f200e03182c460384079043c260f141081c051820040e1941c81c444811320070a559030140c00b0f5821151105030301e40400b030041c0c00554114007030200c41c0c000728040c1c0140c03103071030603510301001d001008003404852100f0406644400c010f260712032086049140740c040407900c01c0240c80c402030802c0c0000024442e24000800c12204503541007520028407501c070b81c580c0ca0300b4821421241200300594070402944090001a051090201240c8d00403070b010380b01c04000e24030800501c15100903c3c000550003120b0980c1d0400161186000c0c18800c826498000810b035060031841d6040020341c40740f01c0d00c00ea00500008002c101640034080e0055031140f030000e100f03c0d4510215110b4040d42c00b04030b4840c05900015018040042461031155800311070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 698275188 1250 698273938 698273941
    0x3150a0b04140607060b150d14010e04021e1002010608060604050402061e0f03040f050105091c05030a0f091a01210b07030e010c09210803060d08070501050717 70
    0x2004501440c0b0030541d80e400007070b03400c044904180d80203040c4180211008564403505074003140c40003a801d45c0c89040b1070400140c4620381c100c04c0c030a600d80e1481101804a095141c186140b080c0600603002030301c619001100000110000d0142c0d012400020780800c05a11251202a000300818801d441950140500290301d030b141038811a072155a00401c0329040419140d8070343c504c3c1d201d0b80f41080d0202d030208201d9203401c8045d8040c42c4250b1280003000e1482b03e083c68018251000609590610350051022102041c00b19810034100e00681c80c0490f00ca554441a10024201c0043c660003010700d00840c1e1024403c803180e0b05410070f5041e041c103e44503662400d80c14120f0750040e03801942c01010540e0347e00002d860300901c54200c40780f4500400c2c8182800182d5003100d2602c00201c0100303801140400c403080300485408030624200c02007000703250711501c501c3c00504c80240910b1144030f036030203003004010490b4240c80e00d1075001802004070f450100805800b51200036039040b0585d16100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 698276438 1250 698275188 698275199
    0x507020a031e0912060e2d0a12110c09040f0b0705040501020304210c080d020d0e060d1d12120117150a0f050a06091d0a020d02060d0203150a 62
    0x40a900308011950f82d6440a4070381060b40c0e512102c1400115503031525407101c891001800c1040c00c0702001c00c1407103c440111941603440d0b01600444080045410400c048004070310f10549412110b070003801c10349444181b490816040401c5145480d030702c42296800d000a001080350000f44c1c5030320070940c402c07039600c90400070b480500503403203a2401603104100a0003482d07a072115001640c0e840000600d014100c90340c1d00c4960713070425001100c03540d1007600c001d16804c0c0d040005e51040701c090704048042c0d03003400c40461a94441d128260f8035040c0c6a0b00701c0a8046003400003107268012400c151402c41d030913404d2855045e4081c25800460205840010400f00042c501586401910100410f05d11640003580140c503113009004c0344000ea45c58260001c5401240100d61050b0142c0e10000340c803d081c540c049045411951135524002c800652555032688002402051660111502810340d04148000b60b028410416013080050000c000d000c08001411f82c5102000c4085996403262501c44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 698277688 1250 698276438 698276477
    0xc0a081c110c1908011a01020721080a11030a0e010311030906040b060f060c0105101202210109120c03020c01050a050f0c0a0807081305030606010f0e130507020a03 72
    0x12000d030009504646442d48541c83c01a07001c481d46555a80485102ca64684c8080d013102c601c4030b50211020000307034001006680c1803022402408403c0c0380d06100341424252a2030541c5002c1d80145003200c0000c2c0c0c1444140200ca49000301282303542126520185208000c0104000c804080d02203400d05e05403040d40301607641500d104068090007403c09035602e80385c2440c002c10241c083c80e0000d600f4408942a61a480002c00f148910000041803504050361444045500b9510024109180d44103140c0181e8442c880b044002c103c5158080b04a02c400303082500405804c80c0040c0110004445240300136088900d00a0f110301035001e440c4000402ca0056a007032107040038400c0040d80070001120400901006490781000100880d140740d02150340301c1e0130940c40354030141c50811011508a0400c10008250740c003600381640a0040703401c0c4140003a043c0005d010048003806500591075105072225100f488100ca000d500030300c49400c0140020303450390550982070700010790310719040c0d070040b440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 698278938 1250 698277688 698277707
    0x5311214150114040b011e05130509010605070201120609090c0302030114250c020310020c0d0c0206040e060d120e040b0604030b180708120415081501110c0a081c 71
    0x200c07440e01c4003083d503c40800c0000e050001015040c080f4172908200b41c1c80d0041c1d00d00b400c60401d500c44a0b0b03110303d60200750300e2625851340120710035903460380113102c01940441950314080e4282042c8086501c01c05800e000380c6010740009519918051040b002d2140102825089038000c0d4002c000e13440954502134540f59084850030800840b2840550000044981103109035000f440c0103141c4030300b10360020b0301340354041c00010b45c1c40d90045161290482d040c03000d45106801d03070038081060440341d8042882030080f84541d0f42218180000500c654580d403034810075181e4071004034405580c3d2104c0260500b90a81503850107289080c5d024192810308108484c182c03a00244403c1403607880c2d800301c0789130b18250340480f0020700410f1400580004100320105405d451000b40c10303204c1c1d091601000300a80801c080004010100080c0300b101c1b500e000c4e849034000b4003880c10400d05131305072044516000f01c26010710340022007070100041d207880110b07920a030a44d1003a80982c004501e2901180c0c491207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 698280188 1250 698278938 698278949
    0x1f0c030b0123040e0a06080105010503070e0106211e0606030b06040e0405010207020307080a110a18050402060405030a030221070c060c021804080702040606053112141501 75
    0x215251081c141d60350704030051007805080a02da00e0a80c0300c40c00e03071800e814240d90402d081a107a01040c80180310a001c0c1c07034090103040c0d0007026400d1510444a1140006100d008144280885400451402050b14403504040e0749024444a090714442003daa154424030320311207850f00c1e20125413288039000d41d05c985503004006504160410341040a6100040c0044035130f0b41d0308011000050301c0034008100109103800103086001440d00b4803900300145a03000c01c2c4a401e0f000e400348654625800c90380302c200061a00012555a0b40c40885c401d40302d15088180d25209001c0b0001c10550300041007000034103e030300306104d10b0381c541d001e4241602558400504150300c2c0c04e800c2c090180b080103504a001c1c00209100354440141240320145001901d0681c1e100d107000900205500f41030141e03d0092070107103405482e10100c08041c08989a0340036500d020745030311100c031581009a29074074a001d00071040c80380e0105110307450500c00700000f029040c1d14a0043c2c0c0c4060b03403c6407101c04424102d5a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 698281438 1250 698280188 698280197
    0x7050a08070905060414090a06060603090f061d010e030901180f06121514010f18120804080709060614030601080a090813080d030e0a0210030c111f0c030b01 69
    0x40c10b01a5801c054800280352640042e641c1c2e991440e4080f85441241c094900701028140c06421824060160740c10380c1c00a42c203041c10310002d900001c0c10090340c00307d40c3e80c00c4000010206010703200b80c80905071104203403103950700380048014030a401100800480c107090b00c4500e4141d0304500d00070460243e912402e500550025030070401c041c01420384a03d400e615500001d020000d0300801084d0705215004039110600c00c011000c0c441d600b0560481240c8198201203030702828082403850703415038034003440c1c003000210701c01601004010801d440c044c0542409441c000c68503500848010702051203420001808103043c85441d0003042d084900400040c0d4442c1096070ba40314042015086000044880c2c0b98200802810220131400342000351031528007a01c41c548040c0001401d07140c108124220303d412618084005075280c010301004030040d4203003c9082d500b805015504110344135805810f50047c452951900c6030103008018140c111040200b0415415400c04c40440e40c80c2c000c40703400304 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 698282688 1250 698281438 698281453
    0xf0f022101180509070b040605070308130b01060f031e09021f0f0e0a0b071203050610090e0903040302030708070927030e04061a13080d1416080a1107050a08 69
    0x208003d030425503202928a00300e50b90300c0d585180350002944036600100010b8004180d9030101a400070341d0b41d4100412002e8000200159110150f0310030041c0300722000c2c0f01030b0a4014080c1c42c0650041030002d0780b40820381491100e540880e0340a4440c030303c5e04038440d0103028407104184200080c203007445a110350f6501002e20300c051059800710010003805501a54201c000503030028941300402549103ea00504990510143c0180998102401ca80d208090140311403407010340c88031200341140c0001407083c849441e843d802500303501c110b80010350580200070340440c51a0000400c00d049481041c1d0422104402e1880c4200449002c0d04003003071241c20fa0300409c0480d100312481c9000d100001d000091a88e80e51018100c41c1e564903020004402c4049100281c506000345843c009108050140007011414000204000003039940c07460800e9021078402c07103895900130082c200c19400010165203100300600900044100000300d083c2d403044000200349401c040e140d18044a038044001c0c44503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 698283938 1250 698282688 698282729
    0x2130c080a0c020a140c01090501030209010e06090a051215061008072105072a08040e040f05011118030c01050409020a0e060a030b0307080a2003010f0f022101 70
    0x381c0620b2000908511036a001c100120318035224160740000d5560003000f0005032500050302602c0d081d4002418540b0500c07400c891a600000294002c6004070b070aa9552149200060320068540d044642c00120307102d90500004070000344d440701410580b082c0005540e41004004102d403840070103100060f81034020881d80c9014081c10750f084003040012004101c0390000a20440c0c000b1540c510006e2041221040c8004d403c210a1044031001e030701c2c409031540b141d269021281301d14411102001c2d2000000350510039034203444500e40e07500c40c00038001d40100c1c1d40380741482d802c0350b20f1014109034042c00100f824030340000c4d91500040c068445a08203440e1200c980d00a4000300d5008081c0100b80207003030181d5555000520341c403a00340c1c40008030075509106051624065401544095101d040e11002213044500085407000c140002010820000000701e405040180208003106e410700920318443c604a802802500e211103890115032081c0341090740c0c81a0b02032050440e4849522850000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 698285188 1250 698283938 698283941
    0x3080702070b27060705010f060513092303070c270b090f060a08060907080f070602031911062809020f061b07090519110d270b010302130c080a 63
    0x24501801011356081180d01d460341802e5030b51064807040c0e510b42c1d8420900551070084a8903140f10064a02001081c0c8150b0703420450300e03e001c0680c0340703e2035040c1d511103ca080c204104d0f01c6240d48003884040d42540c440310180040d440e40c540d081e0912012451112500841c07080ca845900000c0c00c08407940c803480071080741148040d001e5a0000070540020a030140c0800029001da015400205001440c00391581d042c181080315818064002c0341003004495800025030740030038042c028088030304c9082c050507548600c1c2c140071b010850280d04200405810244000103075011028281158400c0c403100c00000c0f51000103000350b0022840c400c0c3c00c0d050400c0c8000e00164005c1c040c4c0c401d0304810400085180100e00e600c00c00e0f125840d070080024481e1250403c007219601400240001d6400c800950014001c01d5864030103156a0031071250310700720000c00c48141e8107003c40341322002081800c00d03500c64034090105038001d5400d9074003e078000810384640100199507a46d0810340741c44002e130440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 698286438 1250 698285188 698285257
    0x20c0309010c06230108010b01020f0703080a090f06031b18030803090102160807030e03120a0c0c15020d02010e060f0f0907050405070f081326070602040303080702070b 74
    0x4581c01e55a04061032100120f418139145510f080002c00165803400203050f0030368044001c400e0440d0800b980e000890300e00003444409880d403200c6903036217800215404035424185640184403203e0200300000d042901507000b012240d080f0000e40442c0000301c502606c86aa9542d4038226a00000d042040800ca00030f0185410403034803000549440100c031b00e800d25002c14000f0a482c9801c0000b0800201a003200d004807816100303030060482c220108103014281d01445542c1401d0010070300704131080103103000c400c1014104c11400f161030100200701c02036403250491154009586405000040c0c41c1e00015800d02c240959006d140003030350b4000c8660307461000909240c20a104294000c901aa85d0340103072845294642c1c1c40e407948000c0c44800810354180600000151550000d885020841c03050f02d02c103a0581c4482c8120007034a1044640210344100000030341101e10106001c001c03da405651240194415401c551269454006444540c420213070495800c40b01440d500c950514041c1c0e604 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 698287688 1250 698286438 698286443
    0x504090e010f1a091b1b0f010615091a090f15161a1303081005130504062403060c0c1e202103070c0305060118020c0309010c 55
    0x1c180e40d1581001e04090f0781071800c0d0300d84000d80a01c2c003040350313003402c0d000b103980841070b0b0f21a020302002c04048401948210b107a9000085000032844e8800031b000c2041c00b1001c44408020007506944600480b123032a00c4030103000010320780c41d2000610700d05c900034204401d084007030710610382850384d81042000d0081c1c7e0003182d00320440010020b000e003650405040b04005034140c50f4958201441c02d4800403850740514501100084140b05018246840e0814040d80c107080440068895076007444640307240e0f51003103910440f0101c2d09141340300c00c1d410503070041d0310928090044140d10401c0c01d500440d00b161500348148600c804101142ea00c0e0003565085040d400d241d0100e6220b0303100d605240d0940c0a0a54213004952501c40400403036076405600494070980c03000003501080d00040a0b41e240f541f142d10034400100402076032185c18000c540720f080d440060050200e60324a8020b48401003440391011100f040042040a0b00e80d40c000c076000840f0400140d0300d040103140040d01e03080f0144005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 698288938 1250 698287688 698287691
    0x4050a061a090301200a0906140304170f0a0512151309030909020304080702090708060a18020c1e0d020d0c03080a0e1b0301050c13180f1802010219030504090e01 71
    0x4003840c0842a1740b040407005000b003100b940c2d071500040c01400942d41d9520060401020003102e000000d800015250055070148060002001d50b06c0da40d20035002c0d02c600e40307220380c400080000715285c0290080401c013003024000196a680e027200e580075421005861a00010038603800744040403154840d4400d07030310074140706401d02c2c3c076400e0703000880e00b088800311203030407001030707168154500a07624642c0403600e0b14103d9550315104022554410b0f4601c11185800d03000c050107018000c5940541c1e44884d00c1130111501e0480b50700707004455105c1c0c40c800c041e640c050012030340040b07403010131144e03420000c685131800e43e0045940e08490b041c0b00200110140e5554018021628409000621640e580b062090046d00b81d0385040508440c0060034400c40b2101c10000420700d204191120070495288002005080c2e151480701c0014282c6500103091152070040645500c0da8003032030f40c54195001307900319503400b104d0301c15151086010f80c80140100c0c1c014041084100c215802c10070090000400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 698290188 1250 698288938 698288951
    0x180909140f03040e1f0e0f090d050a05090406050607030c14030306030a12020114040602041401020c100e130e06070921060b0118080d110706080a0225030201050604050a061a090301 79
    0x464805c003a504058288801c8100b40705502c0110300c2107640002158000c0c00300b000480b40c000d0010f22841c0c0c171040502034040b036814039540d2681d0150740248409844680c1c1c030820752400401c45119514121548980b4110310343c199a030000c01c0d00d00c1204040d00401074034555844d80c5d40080a4000300d1000c540d00c0345d01c26001026061001e600031403003504096152401c00e02120394070041010320604540c080a862022a036842e11207803000256400c0a01191080320045500761040940d4003c10300c0c24540c01400d202d900048140c49440d10340d40c1d48040a0b03c44021644400d1410138017286041301244c4035010401caa07100b2921003105040c100109c10703d102560018500f10752008010f500051640f0008580000840c011018040060249c843c18035030040c02c00400900101c012590100308112009501d111411042c2c03420201c05900c0142443c009004e01400c40f801d0380610304010104200c041c09001d01c0055a00205d07100304085119003001119400030343c800c0398107640703c18 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 698291438 1250 698290188 698290231
    0x71104090204020c0a0203071205060604110f030c04030209010906060804060c02071a090f010801121704030204021603180b070605130f0b090c0109031a0403180909140f03040e 77
    0xf0040001e00401000740c0ba010b12140105818100568452000c0c0c941000b01000090404200c20b50300080841e0001501c0c0300c0c4008186980c0650550540014000010300c44000d000c030014000f20b0b88215601c500603a203514038241695080e2207114040346492010800040304d41e002244810107a104a6000c1d969400710b00c5904942c04841d6516000001048012814005030709094072000382010f801070b5143c88155150701c40038090203130400100095411640c154141141d0040d90000e00554807400f5901d10025602d0b48054200c3c08035000104004a41d03002804110481702050001d600b003226036101d03040982402000361101500b07002580c40050410325001d9211802058100e0345da10341124278900d001e050400303030b5040c41403956041002880202c08420024220700c250240c58550307180c1601c24100f40e4002030414802c540c0d004c1429000c90344040c1d40a80108898040a0840342d8119160000c6c00807176221a00704100c0ac0c800b10040c42c3e80282c00c182101070007103016007100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 698292688 1250 698291438 698291441
    0x3091103161e05360f01141203040522090501050609010909120e03032b06060e0f0d2f09070512010311121213120305071104090204 58
    0x503000c115841c000420a00501079021650002401101e540701c0419081400042500418603a810300c40c00d074010301159154100f400d81100141c6840d80c0942c3c60038002816250304400b40150000b400415034400018a002510400b041c1042c3c3d002d545064182401d00003440402040f040070340798244c0c07101d40c0800191244c8024a4040e1000242500307005041100761030060340302e48413490521800101180a140301880300e005141000c40340303070711000086411030040050031100042c0307000001c90001269041074010301c01482003080455105c1d401941c0c4d03080c603a000990071016003128030413282803e260440005000c1c50f03003040d0b81075001040481e2031914005041d01d00e10204042c5045091010f0901e405c02c006040440c14142e5111a880d01035030140300c06030a4081c1d1040c540020b889030030303142c02e001c0c059030255003682c80b2980329442103a03c54081c403501161601c02c00180f20600030000c60420743e25940740d5142401680301e0002c03d49000c2075503940590368205140050365075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 698293938 1250 698292688 698292703
    0xb0a051b0706020c060903130e060a182f030103110f1f02120309150a020c0a051e030705060f091009060507030509011b14070218011a0a05040603091103 67
    0x100720151343c441c1015072140c1455400740000c1000c1d4010f1058103e0312016456500550b1211040c012443d9142d01c006540d00340305a00c03034409a030032000403521800403900003101100420070085650300000390440b1111000701d50705060f60f01c0a10050001554000e03a14184880003015a100b050078a00082d00c500300100f41000c405086c0100a10010340500241c4028609003c80500718a086420141c452400b0a56444501102000544070710599815030752002240811030704601d03900d1514950b14101c404440c2c505d040700300e0882486490000c01c880b095940203020700b44a40b5400c07160840c0090140c103e040c0c601407444210310302e2440c0e11508002e14001c40011886051400014049610203888461147d0600f248641200e441041c000040718035403801c8803803c1d4075601c0600041c01034000c000d52203030302d0822160445510141032810380b2040600728841400c1c00c80480d4082c40307900401008030308140800c219103030181e4008210f45002d00a8141c1c00805900000c1c14040c0c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 698295188 1250 698293938 698293943
    0x30a02030d051b1902040c090b0f070203100209031504050f030a080f1005150a0c0b151804051e100c02070f0f080709110d0903020a06180b0a051b07 65
    0x4180d0854800100d080b64514801c00340290400000a041e01403c41300303c040041e00564986c1c003030b9000c292198903c1d00080c81900d0030192a0700752040c4100c1c0c25409004168401c7c80788034044014a82144202c2c1d500503001130046c0b00f610b08124910b0f2000100070029036480c0642c0c800034116000074070090502c4c242c581ea07545128500941254a000c002601e03560b99403050120a02960726103d8004030b0348200c0e64032080e2120b141000459003024442001040c82d1107200c1803190f462101541100284c100310360034402d446c03424807503000040701100c0103816070784054106044a58140455650614160192240030040c9480901601d503110710180c0183e20a15041081c41c0310000803101401c8070a120240851034443c0c550780c2e07071103c0e000f04011281e54910180003a00004203c07107100c43c80500600004640e0f040194954180600641e803150400c034030704981e8a0031043d1071300c08a41c00010031104d0b481c0d141605008150060a1042103191410030202090098020b804945d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 698296438 1250 698295188 698295197
    0x60c140c0606090f1006031805120a0215040c06030f09081204030e010f1d180106030b010e220b030309120708070e01081b03072706060e1806030a02030d 67
    0xc005041c099a40402003481510134100c100f400581030801ca00e035012620f6525002c44c03905064a04a00e041201e00c500400602c5103440c014800d00254001d0032030030160380c00707983e031f40940d10300b04038900d54080350020250040c800701480980e000e40d009080300c0400c0340700002e04140329600c4c48400c2d48070000f2140c07264131071000c000400d0351003d00e04000200038a80403c0c03400d20350001400c2d0712014100340700e14005542000f41d080c2c85450102801540e0031150713860550751407002034018800a070595000544040380c260190501030030300b5000803451780d058607000d4030120000006000c00b495496060200b0041101c1580d25a15071030410800140580396607850408000e24140d244e900011241300000010440e884011482c440340c07420190000104410010010f070038812130350040725400403140518003c80c0c80030b00321040513001c407110030800907499032800e07658410204520b60b801140c58a001441045c400c1d071245c0c09c000060212924004c80b94002420030013a13114460005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 698297688 1250 698296438 698296441
    0xc08120f0a0c02030c10091505070f0e10050a200d0e0405130b060d0302210405010e04061406071a04030804021018091a210c03070e0103060c140c06 65
    0x40c07001d100d40307016860305000a510b010550489980c8807004070400d607801e40e50b641032100a2203845a4a4001c0241f1210204858078149c038014001c45103105030100025404a0900f20501300028040710111480c3c070307420300740300e000c00040740e09003008042c0300a0000011901a0302000403c900502030185803205c8100032100704c203104c115013004010320140f030300c103c4c11400460b0788542129040102511034009206260030240d00e03000e00420340310107589070300403550840c08400c405071086e01d000342d0720075414015103c01c02c400d4808030300840c869091441c8102200740f0b0034078000c01c4464441c4280010506c5000c4500d05803240c1110b0940c0411140307010082107140c101415403080a06040440b11038414240610050004d800b400c45019983c44c035468075003082c1c40c074482c0e000000a10381c00300480380c504200c1041e404007400e41028890440038454603d400f01c0e0314020740b1404002802c140e03296843d100050999018031905006000100400c1034030350400501c50030000c1002051507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 698298938 1250 698297688 698297701
    0xc1c0506040f0902060f0304140f0607080601030c08060f210105070e06030405070b0f04030f0f02040e0706020c13230105150412140f0729190c08120f 66
    0x59640040c9035145040c54441083c0040c2e031054152120608281c5030141c90742d6071860425600404410305540a1040c3d1080d6540c0c0d03500003038128492283c55403202460b8075006c0c01541581c0c0c4000d00080070807000400250142040c81107200c0010f0028001e262902d070030440700e14400300407090500301d070751030b80d0400c42d40a40049100d030071420141c500b20310b10329043d110252540b00e140104030076041d0006100303400ea42c43d1415034000e11f80040d0700359003114561420a0b420b8a40500883c001c034142015082103483c0855410300f200c6840d0090820300c001e900400000030074a1010b14a2160360f030391071180c4106c0c4183e2001c0c88040d140303a02910355040c2003c015000000103401d01c0356800810090040c1c40304801e50780111503000c803200541044035801d0500f41200e069401090b4070444400103110312034207141009111b80c4002c10b180306501d00031003502074410b4520005980301c15005c2400703041d104000d1440410b00500c1d03c40e00780f800c1e6811070a0203482c1514202040f4600703809120300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 698300188 1250 698298938 698298941
    0x3030b09010b040303050a0c03201c0518010809030c07080f0f19020402070f08030a0b0a08070303050403170c010219020f06042607020d06050f0c120f0c1c050604 71
    0x740208092050915107180d400400610640b41c07d001046802c9007540101402051a0703411640350380c0711107100100b1844106d035141c00d40c1e28041407140516090b44480c501a804442c0100460031001803580407140054038209005003582000f1b11081068400225083c0901e401920b1044040e012000a40c0b0a942c030b0300c455101c0d0030b032180c0c0240001c00790000d180180d100c1955816200540c0f55506414500707140e58010360050710480700001085a903001030740c068001038404546200c500c64071036a086a451940e4000107012030410070041c8041070303161039913040400811b0712043c600005040441e00b681c20170303460000001c012488030165141c0501561441204490081050345442c2d210350302c0401c035003000852640d51300c140d6a0340e50442032080720f00b11f94002c0d10291074050b0529104d002010100d43c072410314002e041c0402c40c40b02c06841201c60303400140c0701c85000d03a1942c0d040222203500180441c5a4080b04005030800d0340c5c00b0800762400c101100e000041d440c5003c0041c0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 698301438 1250 698300188 698300191
    0x305090c0d140d03060e010b12070f050c06040b0a1a090f04020a12080a110115060e01020a020603040b0103020901080d1d12100e011104180221090c031b011209080f0703030b09 77
    0x30b403800414050300c0104103c0c2e0b2700b142e0f40711000d443c22040842c0100800d8841d0b120754544010315000380c0b41040148448404010300031410954104400d13503400d1952151000c11a4215a02184403800316010b1141d5200c01c0f9081f43c0014204440140d82e14240851800d00e09011640a10082160b0521030b42000e050041041d0742d8000303000c0e060152082e010009441d016000c240006283d103040075910810000c003a1340e40c0989143e0f034a080600707000b00248030921041340f08a12000022403841408203050036254070546542c040d0081ca5522042104034208945401a070b07403015602e030001c81000302c00e140c00d8400c5000a60b4032080c1005501390b8128811503401601d00b00010480500558042080d102c59030720016125086400c0030040310145c448041c400c0102da000b806003030704002ca4201720301c0201300c1c1195001c2000101d40c010071940c900d80940070503d0814803400b9420726400c0100c0703045c82007231030524000741c1500c01401c50704100800d50000e80e842600c0c540038100810111f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 698302688 1250 698301438 698301449
    0x160209070804111009170c040c05070c060503040203010f05012303010c020309150d060824062d060c030a030b0604032a0918030f0305090c0d140d03060e01 68
    0xd40d040c1c901512030f451009031242c1058081e41ea180104803d01d0720450104000d0564010f00d0f024244001000355610340c124540c5504c118a0800307601c1040d030041301269900e0f54084100d51629252240503903082d00028070580e015501c80307405050f0755100348521401307050540e01c404411014000b0800010b1112055603000e03a14209001399103d03000802e461485500322901e01207001d0005950b401c50084800c0036500604200b8089902c2c080419841c0510300d01d02005807018458040c1500300070419503500740c201c1d40b40d140300e103011228003419440900c2d1100d503c02d044d0480c0408943c0325884a03028400503007000c100b00e000c240c0e05024441c8201401c80d455400c02d811500c400b40502540c565440049460000800c203069040e0308078001031910160800c500c5c183d040040051441d02801100000c85c0c411034000254001d1041d2030007050024020180d1501c0201404000d4640140959400102c1940100b0180007001580312045081e40c0c08280240303403400d1a0700c24034041e00f21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 698303938 1250 698302688 698302697
    0xe0310090b060f0a140d0203060702031b010b06070228091d060c0d02160b0112062d0e01020d020414120f0303041b031b080d14040504150b16020907 65
    0x9030711070f64510915501780c0d541d803022074450004020000b84180700e407440c000d4241c01050204049282c01001a01c042d212a2861854410031030038a00c3c22131358590200c962000b02881004c025060603280f4400f03045188440c5940031b0503c00380c000c40d000541d0710000c1d074a1380314281701651a029500e482d848800000c0140000d080001e888211801685003580351a50b0200300c1d1060440c0140103072078000c4e0006038140495843c0c01422800000c0108280c40b05810302445000391401c000a44031000b5101c82e00402e1000c200e041000038241ca00c0304107010b59020701c0041c00843c000d1004000034800141103080350301c80402444880009101c3e50034607038210449180303c0903030101c1100c3d445035004044012003001d03a110074640da03c1d150005442c0043c1d070245211090075464640055034054001c68603c07000c3d030036048030345081180c02e0442c1c020051100700300c50f060540040400b9520707120350b1620700303886041c901c50380d801100400d400f00c681001580154100302ca03245410225a150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 698305188 1250 698303938 698303959
    0x42040c03020703090911040312181715100503100e0d0206100b0310170d02010614030d0e030c121c03140601050a1e030b01110610150e0310090b06 64
    0x18041c11300b000c03c1c814039407102d444030140280245017000310b5000c0c5912480d50400340c01c01d01c50003000d00705c00404284200c0c1b0391107000700d0124a216000841518090001d01d0720036403403088074104030300c060100785401c803d413500450641c0e41404141e0052104132400145a040f00d41c2140c034100c00c80c0c89840030343d00003006018256600600c0070007528010701c50f42e0b54a440ba144400703d80f031503950240348a44c8001d500003d4401000c80c00403411705041d8000d2141d15112158000c0c0761041c0c1450342c0e455809006014a064012005041c04160040070303104051004004203106140c0a09442e41e140c1016882040e542100c41600700f0405003464104070800d51428440300151003c0c003820b05016011a840407040d22649940d45520f94a405025240e0684000079001d000c1c00048140031070661201101e48000014105108010f204a400380141c03500540c402003040c43c195200420489c3d502d0314585031400c00800c103c89000c00e0f00041c201e8151306003c02d02400241ca280d10a030102e10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 698306438 1250 698305188 698305193
    0x120408071e030f060e0129193606030803090c010906020c0126010609080f030f040303121e021312080904050402010504030503040f140103020a02060109050a091b06081e42040c030207 80
    0x85985030321270f140c405008040564000000c4080d1000000b2104541003560220803c4008e41c043e5000d584108100c1d07031424100c900554640c2030501414006900a80e01c1c186151311030143c82210f02c03124012400940d10204005070240b009800100105110f031000f0030001c182004000020410310001c0c500303141041904c08018891480003900704001d645107201c500e100741d404540148808906034070302181d1481050065004000c03024039402002000081c40000801c4e140b08071070b444440d4074039005882c1e040100500780500146c3c1000707420b12001c40007610820060019113088020100b0440c0b91407460030108814a105904141c010320001101d0ba03000600c140c1954103408001c00c9542e01c92030010010f080342d190190900014484204000504a070343d002620410b43d20341d203d03507640310700700721039207410500e0f11106001703240009602680300c1d50a500110400b25900d021080e42850a803280d00c8034902c120f4030711603028030506c028a42403040d040864118141903040442d0358 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 698307688 1250 698306438 698306459
    0x50a0312030207030e091303020f0c01080f0c070203030d1406100c032a210503090d0f0203090a080606030f06012105120408071e030f060e012919 64
    0x914039005154010a0640405000b07020301705160030050f08203001813070110b0b200c10250321013030804c0e009401200c801600d146000b14144465800603118400180c0b00e20300180b040140c020f050203150901404214010b139024002082706130030340c0401083d40d0b504a040307051101d030003812080c803070b89012014041c91500300824402e503d82500784010f0254401001c0400900c0d84075003400d45000ca20b20ba003042260b600711400544600b41d020a130000c0384444203075494807042d22000c646610802c100b491041c880d501092803201c0750b00c140d0b0300b8842c1030f6001c20703007a06654000c14950b41100c0104003a07030074100007114000031800000c04c8030b549020340072202c0c00d040e0200315540b0860401c03281c080c4102001200c0e800500c1591841d42c85686107482c544400c4907004003902610387c02c03440b0902080d002c942500350390b0000320402c6084082da0360100140004500580300d95202e0301201854003090a00c06203110f42c0c200e2030500307181d08030101306280e0100e130300710001c1e1088800140300e1032050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 698308938 1250 698307688 698307713
    0xc060313150605030709060905010e01030503041205030909010b03150d120c020f090702010c0219080405040c12060807090c171305032206030605030a0b220501091407050a03 76
    0x10400903a1207058008403040540503030380200e0b405100c4c2c0c520009501c5215400041141c149550411150340c032823014981840c030a200c040c0c42036005000078010041c040041180a51091080301c1c40c01103100042842030201368440001d101021082009242c454441940510780882c1c80260541c40796a6000741654201c103640200608462480c6c21901d41e820800000e20008000c54028070f000c0400034068a00460504d005000c1c0c40c03007050100101c940014580382d0711004003801e050810041c04020880510000b080003820321a28242c8410b61003031101400c4094050721009040080140035100072010500c204244003258a591910701c41d0000c0e04200c00c0307006603810f41c80d80d00b0941d00d18041c00c80701702907141403141c03c0381ca14803c12100c40203d9100703071000d01802e41d40b001003544440c2101405030480c070044002034040c04a01554140041000700c400c454070380310351104c60031105c240300300b104d014401104442c02a0003c1000340d004040840d0855440d074203640da640c600c0c248 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 698310188 1250 698308938 698308943
    0xe01060e13020310080105090d170f1f030f060911120a12051210081e03090d02150a03150504020a020709020307031407120f2f0d090804080c060313 65
    0x180400441c2c1390104e0070050350005d04003403000303000d6070a00b5400a81c03180350000c40100818840440206210107508880e8403070a030160007420f2982d070708201d501011101c2d20102562008803400440000d1004d00d46105440c0a00340c001051540e6250088031442001180d501ca0700020200c0d00500c040000c00d12040c9501031a081e8542401100c01d44850049070f0020403031202c110308110380920030011070800c0b5640c3e4002c5501d00541110207441340c0c002c003a8100199001040405581e09080b0091540c16101608403901c00e8801c40d42c1d4282c540081c50b960000a482d6616038245462007000031018080c1240e0852500f00900c4000c4c0d0b8070f83c01445001c1e096500407001403103945c0254040d407460002d9030360002683c41c0251008120320745140242c030001d8500440040340d45864445c000c0400c004c0508806416075440c0d04401040c407080002c41980c1c0b0420080b403801c074140c0103c403222803003001034a48503828941e2003800e0191701070460380039080c14002c2107811907544207008078894 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 698311438 1250 698310188 698310191
    0x312021002030622020706050435040909030e040e0309091501020a0b45061005060702060c120403050706030504150b06090405190e0120031905040602040e01060e13 72
    0x810604125003c1e0040007000f8200c1f525080070001071100e0f0f00c1d4614084007406d0211001c1c1d0249107036408410344141c824010090003404140030350700660f070100c000300f4080c0c140060150524800141503035400e0603660123740021460007158284071820580200064604100b584606d100003507075994244000b4202885003800b080c00d60008070403981c203100340e680005004031541c62492184502202e241c0050501a002c0f00c130181c00007244150041c10201441001640b4007401c00c0840d80200c00305a901210400c40e03031b004030700f003004882c0e058000b0005550305c451035130a2880c01c140c102c0d4400018542440100702c005502d12001151181c050030300000c4521550f000700ba02030041d80c807030b19046403614040c045900465100100300d032017203c40034010703486900072007800d980b00d2a149003041d801c0000088040081d00025603488506002450001c1d4000c01220702a100103a806131011940003c040c00071201c48841603000d08081c2c00c1c00502003c0d900c01060701c91700000031020645 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 698312688 1250 698311438 698311489
    0x8030a050f0c0106060206060f06030415021b0f0109120206040b160c021017011403072c0f0a0609020c03030a0b010918141005010f08041b03120210020306 68
    0x1c40c002600d56044070b420007080140d89668000c2d585140564029102d182e070003442414900d0850304613032055501601401d400440b51007510080e410124800910403075818815001d0441000001590200000040743c1035140341058003004544d02c4641e01150068410400410300c52242690001c2000030b50600c0581c410100300d07407c4180030002035001392103607600c0203460342c0140142c003105001e015108003641d94020921050f05111519501504800010014004131041c000c9983da6901400343d140c0d894140c03c5c004c00d042c00c4445800419080040c045c040441d441250040d06e0303640011481d20352080c481c9652800010100c18a440d00c8141c02809644250074141c0105492400e0481808075040c0d1900508000c3c088e0300034107540200000e8030600d648000604450040c2c40b01204040a10350171241414001d0099540c0c0b030314201018080100e90303140b000110300a495000200140c40d034004d081c05242110b10f55071310300520a10606a4800f010340061600580d044000d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 698313938 1250 698312688 698312707
    0xe28051005070507140f060703020609120414150c010606080103051b010801030b0a1b12202a0d0e040f05070527030d030b030f150c09010318080a030e0708030a05 71
    0x1e40c802c4101585e0419008230b0480c040607000540705000c2c118a1042e588a65082810050240150710900c80b0480c980700041c000307414180d21030744880c000e001009282040c80d00c1164207640d259070014000130301010040060100c14004c0d642c002c07100304040f08480b03580c100000c000910601000d8500d40e80040841e00c1e18410b030b4006c1003075803001d01c00d04219184041c4094074a005000c1400b5000303040800940b0b42c10645540ba08603001d500300082d003407a800b91100314685810745032620905041c1c120401c5410030421000c00300d801f095490702d241940c804140029502c442030001496070400c800d03c640c00303401405403850640564202c56604180846103c46148060901a0103002d000c41c000034507030b03046e000640c001100303030111060283c58001d0a0368824001c065443d10309841c401155244003d400149440d0805141c081074107054032003c950104103640b4129140003000501018042d018050b850011251784082c02640e49008207198803845400400001c011000503140071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 698315188 1250 698313938 698313949
    0x1e030717070b16143c070b010306060918020f030102091507120f0c02061602061303051c0813060e0a0b0a05060405160e2805100507050714 61
    0xc1894000412446a052501c5a440e0714001c000c00c1c080016450154460048503800407940c5059881041081c61064458990080080366174440c2140d0603400840c8001c008040180030600c6c0a454042044c1d451817800000315080c66000c0080b040c104030500d80d100d21600183d801d0325406540b001c0f210110600003e0082c4039031400e159004142e07000b80d200141c80000a4007225120384845080030140c441c06840c07001c01d140500c0c0001d42d29070026001410400040c003502d4509101a10040d841a400150300b0740200c1c9440104416564041040c40010031181120b140d0301c60140381420a116070003029800300030303c1c2d841e41f1a0411051020094a540145401140e80d01a5054a04185007106031a081514a84c0e4400c2c00c003400700d80c0d51700e050301c901c0e40200b20107412828400944c1d9015211281401c64644e444144803188500c483c0400042651400b00c41500d1030320350f41084d00f080710002c12031105a0400c9020700090700002e8000a030b801c1a62080707507003400541c1043c0000795 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 698316438 1250 698315188 698315197
    0x1020c0f280506040605030603150f1b1207051c060503030a030b0303090d0b040b01050301060b04060c06060509010801090c0807120f141c08090a231002070809031e030717 75
    0x240c01040004001039002d502401950003440c0c1227041d1401c90480c10401412860166020022074000901003102e444030600c5002f422104803801608050088212081402007203c4030004144005411803410804402c1300e80049040d00d420010356042001007a540d004188800f02456a00d02100c0b40c2d40d5410000c0c0d0300200b600801d20001150246081e00e2000703000c0d00c1c2284c941c0403110012038903140c1805090151450f071000a81000d01e030440441c0e032080000b40582e1060b0b40e0382c401203042e4507651042d6010303086040005c41d41d103d051400700e50110b2030381c3c80890075401540083c060303030401c0091003000c142c0003001200030715030b6410720782d4280640c400c6000c072610a9041c281c81c4040100030a110201c00707901c40342c4655540703195007900c8001030a030003005103090a601031420f21400003070b440600380c40c0040300c80300c20090300844101d0b801000e05684284000c200000e8501d8208130400c40e014100009400f201d401e032204030703668000ca050080100a89000ca03070403140412007074a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 698317688 1250 698316438 698316449
    0x120304060f05130303050a12020f0706051905181204050906060a120212060f09090a060e01060305071805070507120302031302131508010e070e040507050603070e01020c0f28 76
    0xd0755030394924006d0019400001810082040303c40181da450b03020344251180c0c00c0d884080d984c0360604641e503884c01072100602410345031410204880464a1910410348202091b03c2c1c8641e4585100f811146840c0b20090780114003c42000f0502c40781d100d030024160001d0703082d00c01945403034500790b00b640c03500000f101c8030318202e10126100d20344954000c44507020300015a81c0f03941600b030803014807a940f501140ea07107038154442803c0360b0020f1910380c00b8060800d14080005038407a180d0340c690b82001419841a0300c442840b2042e0032143d102441800c0e00040c450422518001c0650750300c02c10041311070509018194080005401824604d50180c0100da0040590760300700305040e440401888001403a81c10100c01c6a00070039102014858142c00003403010041082c00d00e01003020703c0101e001801180c1c00d0103106800035003629404069401024140c448814004070300d400289410400c0314950b104081c01480000244c07030700100d80b1811800c220310300a8544000319020308004d03160703000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 698318938 1250 698317688 698317717
    0x60e040b0d0f17180a0b0c030304111210090605060f010807050a02030d0c271a030402310b030a031403090f033417070f050304091a120304060f05 64
    0x441c14022600c00c4100e10102d000c585c1c60024544501d642d041c0f0740035078502d115541c1d00070004074011a07000018002c00c0e00c002403031a20180c510340303126401d0880d078400700d008079500c401e129000c0081d1030042540c030138001c3d03038803a030800d40d06000248003280c040c0845040c84030019807040140d10a00446941c5800c030101030081001c0c0850042201090765958a0209002065001075012344000c000841c0d200d0b06101d50603001d8240b662040c1d60028104036482101036090410044802000b500301c07078421811003120035514644603060f52541d4507564400d420150300040025080030b00b14408403858000300f5101e982e0a0300051401c5515601c01c00544000b003600116851150802001002e40300c13213009042005503d64011429520300007040d0380e24400d46441e804040e0030141c9500b5015101049803c0055255141183d009800c00844283c840e02c5045d02d4000000420a00d590261000000c01d100030a8254890096006100811031030003079000c0300038492402d81c0c01701e0026155 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 698320188 1250 698318938 698318947
    0x1407020727050c030f100806060f01050d060e04050d0e060f0a300c02011a0f0a031a0f0c090f011d060d020c0c0d0807020d060f0e0106060e040b0d0f17 66
    0x2e400f000c41e04201c420a21130790354800000c1c0401d42444d81c00782114120402450107458600c10411b04500c80d44016040010030302c440c610801c031600030040180300c00a0392055a041c0b0381410303402d000d402032400c2c0c22f002d00e003200182a41c5852086a103070a894040840d250044094100c8038100244844a080e80c5612643c000000705110719949040c842d28042018100d0304400b0b03420790f40d5a48282e594a040d618800d8017a00f0140e032010f21004c0003c0203c43c0d2240c1300e9a030581440705050100115201c2c80080240300c22500c4041c1d40c0005405a8050610820b20300007024081c198003d181003000005c03941caea45207104d0a080c4880c001c010320307141d110001d20341900000d4000ca80384c40f807207118052924440e410701a04268100d0b4001518514014140c1c013070100903a800d0354100c803460f6441c0e600702240031162050a080710700d110008140740340b41000c001c09409074442031a01c90b07442d02e5501c45a5903140c00c50203040300d40c44dc3d8000e0312407580f030030443c800c54040104564180800034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 698321438 1250 698320188 698320201
    0xf14100512060a1205150a0e060a020a020304150f021b06070212030d14061f020a0308060a0b040b13060e030a0b190507090e0a093f02010f140702072705 67
    0x140e440c4682d0b46001c0c506c12666a4a56600581c0c82e0000c0385605a002817001c500701c1000c0340c0081c68205001d00440385001d40e41d24801c20300d0340010740b40c0d0700007810340d2030b0071003880e41d041c405d0040243c02d0384900a850904440010401e20400030300900c0340e0b124400d22515020188107407000b006415204005038544c80c00d081442420496140b44580c509004031518204000150200d008055006090030401950140c86031807005d0085030303218010750400120074140a000b40080c050118040c0d0301d90401031601c5192851a801900502c210801c0080c0d072a1000140422080d81101c0c40800350b40b00c5000b800761010311740507203500c03282c140000c01c52001c0c0c0015602040725807a03640e404d010b68981122400321041050000e09a00802c0c00018202c8a08110001e542c0c0481d08108600d80c405480f090248050758511009030b515444400d464038020320035005011590360441d855490801002901d0b182c560142029120030a18413001062480d0f0042c2100300201e4010445801c054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 698322688 1250 698321438 698321443
    0x1f0306020310141e060703030603150c0f02060115050a180806010e07030536060f27070b030403050c0106030501140c0c07030321060f14100512060a1205 67
    0x80c0142c201518050441c0c1c841428149019000e038128500e0320310b43c60313841004110303442c0c0c0444015020551541d03001700200c4d01c201e07004010b413004820006005840c03804040c082c2c1c69070404100964102c10010021440741d8240404102082d1820750b03030324a210b900944250803404002c0c0300d810006040800e24000002d030080c10380700a071141113144e40c3d40798070440a845088401c43da4449280041d1015400d1070a8080e210f40080c0394203040c0700d5040000c031171034a401125408449104001481100c0301d0030071649800411020030422210b4a4131491070b916141481103240d107034000000141418452000d54907400100c0000740241d540d41d0605a0180001c06e6448100443c0800441c507042c11041c00caa0354200340304094080d0b60b00e551420f40d071203086203120003c1080c40429103c0e003c1558451003028040a00030a400241858680310800a009045a009205a50b814040250404141d6801c5440441803800c3c680c1c998000c90f80308400d59100000101c440c1140c0000c20002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 698323938 1250 698322688 698322721
    0x40311030d050a020901020610241106090a0c211b080f010203010f0b071122060602070e130b16120f0f0e01021c0e0a051501030c0803121f03060203 65
    0x9034200c070115102c08100c1000c001e25032064200580480c901e82b125520744c1c0c84119180b5185042945070203000f5060f450400704100c808855030703008110071408018040076031750050825013039054801c0d060808403210842072103a02800d00c202551220541c003100800003405006188140d541120554802074040e41080c06074103854a540311010803075032030900c1a544507a4102c1c207402d1694100b030050050485010040d161111240d4405101c0000c1c14081e003c0140050340c01442c48071b1401041c0003c00002422813525549407108000100d0303001d6495641044200c09143c291811100e819581d0403801c0d01007a40782400e141c42d030f800d50ba0036a070109440640c96081405512400c0d520b8508030310070490141304103000349016000031a107607440007400f46e0903481140d00901e0251685440d128500d9003000d601140d02c0018020808410804030062080400550420b00d04c030038110208480144400c070781c041c41071b6034030310300003c0c0004200085421003411503a0341080d40d0794940300400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 698325188 1250 698323938 698323957
    0x305040f0503131706060a0506030405010f021b10020a020a0b09070e010b0a030b0a1802090f0a03050105010323060106050d15060302180d0209070e0a0815060406060c0b040311030d050a02 82
    0x4e60b404445840c0114440348038100061071860303a10b05003020482a50030144c4140c6840d0359524005809001510040c00040d21400d80d021f00342000140c9140b0b80203548440e13500c440d00500042000310780008020700c0190340404103000a54a44c0c91035880c0c9402d9610040d080c3c1401c0c400042c00e00005c2c001020b4480300f99030309202441100081c08007440d603611910f100c1000040d0044100c0000d40e01800350b40c9001071854018259050000f001c200040c1c00076680d43e59100010401c004054542c0f140700e8654450b80300460032950039a580700d200502c2441c2c14814009022951403813a544034280f001d144a011080607926847c00030001e400c10b1031803d68200424414800d240b4100007003071040c50b40203080711081e035140e22044500101000185400441400b000b1031810810311403a444c8060080750701c41a49482c004100c2514081d9111105020504840c200480d0b150a0907e50040d01400d01c030b90b04013024810249180300380d021440a440c07400090090700c0741d01d5002040e8154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 698326438 1250 698325188 698325209
    0x10b210a06050c03100e0f15010306030f05062e031514180d170c07020d081215060f0901030c091d061207060c06090302011419050c09010f0305040f050313 68
    0x548505140e000e00038169056114054441c001a04e60182145ca235461001d041c540400c2a655a558032000340019a200301c8003908544200100d03440358000f0310940c80115410458464042c6140401c0c02d4101c3c0405403c4400d10340300d119a8603c0c40d0041e00d0780c0303514440711907a0341ca0200b02499001c5d1b018025091035010300c1030140b80da144180707143d071045010a01c3d02115a00e851050706038960101d4022030b0000b102c40b01003004a841000501510444403086402c0c40c50b10501042c0b104003103a00f424450101401000a401c03001c07c16030b0442c400a080c0000c050100000070740b40288560700240840c00d5032080150384031142201036002e880283c8151880203492a64140c5a0f015401004006a1150300d0280800d01075040080601d007c3d000008096095100035407032880100c442060803a42000402c2c0c000016104a5a0090010400604240e00c4000080c20f002078030310b00c18201921840801c0074031000b90b842804090384102104d5440e182500726020414452140c041030a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 698327688 1250 698326438 698326471
    0x9050a090b0a1e17070911040f0f0f050d1a07050904050c03060d020d081e0702210c041109030307030e010807020a05030a050309030d150f08010b210a06050c03 70
    0x504620488500c484000c0c000d00351514280786075140c01900d41c04582c130b110b1045050000c0c000c404d038031810380400014902c040d0340f0b41c2810f4150000c1221580300c12500c0e80c40070001c00000149000c96030942c0c00844403480c0340c82c803c0c202140c89911108944c07008003010014407140c42d81007401041d030441c0c2643c0c1444691340309951a84c5078002180c2c4281c010f41e46000c0d820051405000500b001d601c0749260a0410305007032a05844010b5510040528003000035294003949815030344a440c41c881d41121f00b00d2400c9200e1200d44030105495158001e50325a030302d441c01c1022001c152000c00c413001c0d041ba525681c41e801c0003000e50421503045400b10b002c02d8003013050703148045500c1c1000758000000f940350aa00c02011149588004d114405500007800202d40c520034030702030002c10f959030500106160342410901d1460b2111360b4400c2d0742da80c3c5400c50808140c0c6640049c11444000152059600c261031030400381040c40160004110618000411648aa1a10113907010306510074051000c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 698328938 1250 698327688 698327699
    0x50a1a0d14010f0f051804050f0102030403030507090e07140a14180901050a03080703050a110607021e0118200a03080c1605030c10090f031a0907180c09050a090b0a 72
    0xf90300e014005c441e00a051007102c002600441d40642d030300036229804031844508044002303400c90308103407001c4001a0f03d43c010302c20604d50240b019000b400740e0440c284d020b41001c00002d405d425110350380341e0072006c01003144105540100c0c81c2c90711001c1c0340074140c1c0c1daa1130182c80c0805020912161144904814000450340b401c0c900038520540390710165203490071102e61805e427204d070810612007040001c0740d00484201c00e4144801c90055001d0780091481c03810303001c0d840315200020020006583e2401094401e00c0c21003040c081d0075a504560010040484d540102c0e8a40c10000009074022801c644000100b040c1900101030f107034051000d0380c901074000d01c00c1c407100680038441c3e40c0d41036002000184071407078220002418003026051520255a41c3c0c0f0100c600c1e00150390042c1da9500002c0210700c00c0712040e102596101d40c0c0c00024200a40c09c01800f141c80c105514210f4017420742d0b507540796511038001c49010002d0680103110030005503440d4020005000c10348070240c0994103403c0005031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 698330188 1250 698328938 698328959
    0x5030102132d1e0f080a0605090102090109050108040f17130e040206030103020108130b070201091401050f131a04060e1506090c0d1b2304050a1a0d14010f 68
    0x248000c0c0000d09030030300c0d20f071480081642c8200e0802c0c0905042c0103000090350080c65802e0030080c42c00c007016140c2e458443c18000c00302c0744024200c020a900420450316030781ea04c908503230181e880c01d00300b0504586460402501c50b002c0e54000806d840d228030b1418910f420102e01521403882c0703103c4481070745501c1d80c0003003202d00402d0310002e40140003400140010f40c0210242c96000b00d00500394031a001568942004040c025251600540d6444503c4030a021009107010010079102000f4402420281941540340d04d0040080458881d151266070070014140e4201c40c80714a100d4520f040c0d401c0506260004009810307114401d0301c09c89100103e080400c1c3c51a500c81e0700014039103902c50781c8241420fa0300b0350229070986401a0b48444021401b00710034465402510307079031340d21100305003c8501001518807800401144410503c030801207940c2c0c6034032441c02c1d18410f0000803042200901c01c4161400380e59011041c69003044280100300c1c04000000e0b040703c0c1d10901215180e5900d050703500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 698331438 1250 698330188 698330249
    0x140106030302030d050a020c060c090f0603010f090b0607061b080f0610050d0b06030c030405060705181c0203100504030315050f09070c02060c030a030605012c06040503010213 77
    0xc026800504c448050b20040d9800164010714a040151401d400b0100550801c0c00850b0000505030340490440d0741410711204103d45204242d4034146154105800340c98181190b2240e40200383c0c40d104080130a44511098462080e0b1107501400cc010000d13000d5142545002c108070006445103000446079101508017a000360f00c09000c0c0c000c8481002001c940703590000d8803100e42d65898088054458407244001c62083c0b02c00600c80e0703100c0c2003e00e001c505105c00503110404204042c0800b1a081031804511400401c080b0b07020900c107000f900704500b140512100c0694140100140d5600c44400d5400940c0701c0c034403c1d50f0820010311803001822004406004064005044480318035250400e0001b85400003032505001318175000650001d030f00359003d40e151031404d070808900c0c02c68481d09130140d030015080c2400d00e804d513070b41c00c002d200140c204d0040c02c0306548d001c0c0700c0c0c0c10071043c2c03140001c90b0054000500255500d0800c00c400c1028003006110b50400102e10071200c0301c0c03941c182c81e1442c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 698332688 1250 698331438 698331443
    0xb0a0e010e18040201110d09030203150f010b071e050105040308060301051b030c22080120090402030403120f02070b06030d020601060513050a091a042a0311070303050414010603 78
    0x1c84810018030510140b04400600480c148140e01646181c0c941003005580c0c80b4980d1551000016030441c8181410110400e10101444000b0402c1c440d40f620000c141c281540d151483e416201c0803907040c903a000f03c2100c00c4900000d0030400d80c2505001042d088a8401ca00a8540a000f0780f1454181401c0f6074046074110070340c0c15001d010300181c003117a0005503000f0860003449424180b40b1141380e60910b861907034181654030000320400c4515000c0c0249a880658502c18901a1410b813108002c0f61264008a07072086900100080400d8015845041e1440219208124081e00b60181000a60001c2c0c41a242e4411040000710b9503d800035900300104402d5001d001d81d41d181c40800d4820703070040309090041114220f004074076a00c0300404000100704500300411f10100c503044050403c1000c0d91504e02070343c1000d03007503161044c40e5030010340900003d40940002e54180802100101704405c40451424030014407035003459496004175000701d025000c0d40745c660520483c540e00b2a402072000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 698333938 1250 698332688 698332699
    0xf10031104090f2a0803030702060a020a180f0801061703070b1b030403030501030b180a03120f0905100b012d0519030c0306210b04080408070b0a0e010e 67
    0xa504040e00103810062281c98141c03054001075450b00d913a16002c0103501c045043d03111a0181d00e030a045030480043c0f0052015501e141800600251103841c002d0905007040e80010b283c140852040703084c502d000d00d000100e07810305500c3c1c41070740e01020100d00c140082503090036030100b000802c0718001d03241c010961005502c7c00d540350b03644681c03004004180240b0614401d000b6aa1070411000440c0306520a9500141a40c1940760490880340b01902007181560066425480c1c1c400c000303920002d15405082c1841115820706112002d064102c0c3c1d031004103030400070300303030100800003c3c00c1421094840f0103018002801004590f00300d5a100307503201440196100400c3e110002c901102100907515015241c210180555006004850b4007100001c0d500c22000050b250f03d48144e030068201d4a10a4541d02d902038400340e0201c011b04d1024060340640404142040303006802c41c0c1c01803010409031003103140d4851080c007036074001500c1c800100300c0c0c48500307001541c0f01d6856011100c000401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 698335188 1250 698333938 698333963
    0x271b120b0a1703160609032303042a060314060108100b09030c04020a110d0e032a150a090b13031e02044d0d0908120f1003 54
    0x644942c0d007600a4803112207000030000c00307580740d01c84601c0401d040c0c001c1c0c03400320f03125281e4a070040c00d10341e6000c8401540000601d070080120000301c11640c00a270801c0c41850080e0700c201d44000001c80d280310344605001050b4000a03800d405030401190800c0d0328a4140c0503607903100055070780c2c0c00c08440c1c001e9090706198007070000045450242c00207010103402c9a0740c100c1d03450007003422603000b400b682010916515000d411074004001c0042810b5803454030503240d007048404a565005140150302144e0514000c401c51003c0d0f00c01030350240840180245a107045101e41c031070240d4030040d020000900c0700b031004501841d0300c10407661604650000c222805103141c0f900101407004014060702c0c8406021003101680c0d0300d02681400b64030003000301484081322404052480f07107884155010711800121581d044003644115403000440c80d030b02c20340c0c4040e1402410001c0602e0080140046800f040d4010045c00c407104951043d240c2100b000b40c0d648a00701e50703201c100c4940c4030003400b070040e241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 698336438 1250 698335188 698335199
    0xd06020c510711100524100203090609040b1003020a1e021b010215090c0406050f060d0c09080f01050604050109090f080a2105070206060910271b120b0a 67
    0xa603581d00094201040d01d070b00f036201305541003d5880c103964807203035543e12080359500e0309003401c81009610011a100c1011801c02c100194503070042c20801440b618000c10343c40f41c03030740301d58111854070040144404880c0d01c240314013030001d421a0b260380000901c3c401d16428165507070300d0b1020681015400400508060240001c80b4a400c503509a0460185050020482414a036880c0c0070b19401805030840a610710b00780802c4a10702d601c140c1c031600f014819011f00340c443c08202e4030002183c0101041d80000703808159050b610350b62107038400b03215032a031004e007260040d48a64000c58003141c0c20711503a640d034040e980039150300d0303d0054074003c0a5445800002c42a0723000344102140c509140810600c01071420054400e00b10081078055121020420781da64103000c05a0300440440d120009800c0070303034940c46400c0b814022005104841c0c61081c490340003c0415181e4001c00d1030040c44000c480346a00d106a000703e0508001042600048910090700781c0038140c9604405400950b00034a080d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 698337688 1250 698336438 698336447
    0x50102061902030703060909051b0312120403111203070f0f050307030e1e03040306140408070b06040b0607050f07080601081b041506050a110601050d06020c5107 71
    0x540121300b4075a8402000504140601410074002c1c0a000a4400f02c2c0d0034000c240803101104203e18820340248400041c4403079000c0982c1d07030680460000070000c5d80d42d843c1c191036880700d000a0400c2446031100d0310b1224580580294400d941540e07501900c10075010086e20300003016011000440c000b40300180351984203030304c900c2446488108a400703131801c180001c110b01c0c0b041403010b0000e4100050034001c0c015503000322610144082001200f5140648444889015803e8020040e410049c0404c41c56036484e0030980500790010000c80c0c2d035801c98074259555440c4000116001c2c010000c0c001081c0300d0104a1504a0708040c01030a01c2d4150401c240343c0702d50b05a00201d1380596a660070340180303940c0010720806400680c4400d41d907100c0342c0c02c4c0038100c41c8014030142025400400107014980350315411240d070907440fa00160312030b6002034401d410142400042000c1c4c81808400f1014501200180405192100c110400d400e00d4440740a0f020710000d181e806840304103802103449a0b128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 698338938 1250 698337688 698337691
    0x90b010507030e131d070311032b090b030f06030615010519051b01060503251a0702092a03061e030a05010f051b090d020910050d081305010206190203 66
    0x1e45030014854044031030170080042000c2c0090b2036035121040c18801c01002c21200001c1e02001c40017400c8800113045410544210350052180c480c940001041c145800b0b074125001400c0d80908880d103900e000320b01c1703200c0c0c080300f00c407800e00c6449108041500b0034688819001200c41c1a502d01740f41140002d6008405c10b840920201000010002c26601c17404c0c1e20030b42e018a00540c000800e2180c035000c00c01d850b040821000207400b070000a00303440c00c500c1821411003103a10f00a401d894003140c1c4503c40d0640e00960341d020313400818039400c000070000318240e0040340e18200d190001030201c807051248070500044801580094003142d5180007845d03031408000164600030119500a031559035140e0030f45030310a0628000e16120300c00e200008482c00170b00d00d881aa41d8500c18204111080021104400500041d006000e0b40b0081800603543c030075064054400900508085c40c0140340000d4640e112800210b860b40040383c01080e19880421030b60b00907885c440d42403102d0316000751054020b610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 698340188 1250 698338938 698338969
    0x418080307050405030a1a010602030a05190504030f0f120c050c04020306060c07030f0308010e2503020c0114040b0f1b09031009080a0305100f060c050322090b010507030e 75
    0x14184800130f5541e90130040c5a00e283d00c211030700d032401030740010091510320301a0400c500390b410030302101480d603611805640384202c00d0501585502c1e072102059440d40300e182c201508902801004c1014401d0891400210303500c10307507142401c600a10011640d50b13040d00c1c40100b56030040c0c003000000d46072580143d0f40209004007510315001d84d500c0c409151444660080f240e80211140000c1495000b11949004041e100140d09440c5010414410701050031403140301c00c0ca000c000b4513a0405d00c41c0e810340d00e800c241840208140ca103900c0c494903c89400300c0f02120700e80708803030005408284010070351b8041e0003000507490403014581052016074020b080065018454041d22880040c0030b402992402801244869520180b03070000078140c40d03008014101900305a001000702c8a05030646100b16202481c00ca0903455940c54900d046209503244000901c1e040302c0c1c81080410b100e000c0f0030403503080c82d40c2040b61011490055410b80605040075010400700c000b2007545080610b1986810031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 698341438 1250 698340188 698340197
    0x90108120d0b0d0b0a0f090c1e031202030903070b070534031a09010905120906120a1514030607030e03120f070923060a021606030b040b0418080307 65
    0x845a01c0400c03080031014109480c01d40e02007050105d094214428604000692071040c481000310b5107074110f0f260380d18803c140c89880501c2400e428030440c000c8003005943d100036019207034007080134001e5a0390800b03007580b0300c01e0083c8040010401c1040d8102c03141150310002412940d040700803410090240e4502e075144810900910002101d10801d1500c00b9601c038150301501c3c112550f1010100d4007000b455520280c2c0760100c0c034000b103000002c0800b4824110101c056031604803602084050156002d180010103040d418020034212030b800c0003c040e00018018080c041e0348956100100d4007003c0c24a0f0513402c0180425100b620a40005052441840407039280561448400c90500c0b821102e200303400d21020140420694444100b0f0b008024080e80d100c508801c0700901c10120b0b000c010254411040028150040c600900c041825115400c12103440700c0d44e01c0d03c0160240c12403003501131090b403a040b0303e010076207401e1103110ad200806142c0d15008040740d070f40d0340c02e86a1000d00302c5070a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 698342688 1250 698341438 698341451
    0x7120809011e02100c0e0f060c0a0605010807050f060a051c060e0f060909070308120703150f050910150e0a0801150e0106090806071d0d03050304030e090108120d 71
    0x402e032840c0e41039419415401010a920030361503c000301ea00c0b20141d14100411540300342020f5440e0000f18400000889401d81d5403c45142c1282c604a4103001c000d051904082c000180c291000c03658908985007520400e000c0100c40042029074400c0744240320100c1c2c0240103801091700c2c030802090224801250024001da101d400303980c69920216030000307503c0700305000c20080d803d11403d5542c001c1000002022443e066544148a601950485040401d000c00006194cd4425017055042041c1c0103190721b40503869904001c580400f078054039001d1600500452100c140101d030020450381d0780d2085403004400c00300100c03520710142c416654012140c08010411460070300c83c928444203060020031030280b03080a8407070001c1d0141e02150130702544000821110902254aa600c10786c40e2030030a0428000c40114107070701996240c01030b00800c07c400c4110406410200440c021406502c801e070b11355100c08104031206400340104032007038010407030325407003940360102400001000c4980440e21 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 698343938 1250 698342688 698342717
    0xd1e0e030f040e150916110c0117100e040b0411180115020a051c021c05070b0a060803030a0f0510050123090301240e0609040803090c1801170712080901 67
    0x5c4d0581070340c4035000183c3c400c1c1d040210940088003850396518000c050942d001a00001a205403182c0000c614000f00042c0003600c0315000b54508009014403800000c0b0385e04113410880848501210203c030b110500c0500c1015a01d0500da01e01c3c0c1041d60004450030307903824400c0400c0d410240017640344c01c2d40304c1c440c51040010028040b902480001850084000c807a0501c0245840356602001c020300e400c0425504c07529920000b1a2215600b0220844040d12449095402851030341c0c081c100600000c81030140541150b080844c01c00d08200c401d010700c1c1c41c3c6a00400a10815108039130214007048940c082090440814450341d14200c0da465040218000100b804d4806551102c450454101c48081c4a9840801c0140141c04400c1c0ca0004c01c0c50700d00c0118800b188040c10241003007901000080c0525001c2200c3c00c003c2001030803030140d81e07084603404c1000315000e005041001115500403141e0040000c0c1c0c0b40100c0e80160b903070005084240e242c95540d680030f4070078141042002c0350740710074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 698345188 1250 698343938 698343949
    0x50714070303021f020f031b0403082a01050f18070503070b0304030212030f04110607080d09150b090a0b0102120a09030515090d140d1e0e030f040e15 66
    0x214020f401422664000443c01d10313041d1480001c80288a10500070000000040025a54800c1d090301448100111141d0840618080c075440103010721400121840342101300e24068600310492984d40350382128140070142641c2c0c0031207628520462880c0042c441c1c4120780c02d00b002e00691182a00d14550719000402c0c1000555000310003062070000a002c01c25a042242200c214a07040081d4114180f090903000d0251003e0406030440748581d52100c035a503207075022264800d81c407001c003d6032150350902e024003800314400243c4142030108002d0031600e909004140702450010140d18042e50348130240002010168015811449241800d00c0341c031000788002d02c444800da40302c0180c0e0915503d081d03494100d0548000b60a111444103100181200040108061400d8280103000010000015505000d8a052500000d042000401441c0401941c007a1044441901400200c8814a11580da4030500d40c2c1c2d0040c145003008204010341c1c42c1c40b40140c120800c0008807076400c000f2030011341c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 698346438 1250 698345188 698345203
    0x30c020f100c110103230720060603010b0a05010906180902030f04050d0903080702220f022701050906070c091a0f0f10030b030a080a0201050601120e0607050714 71
    0x18080b0328015000d006215014900c40303220542464144400383c010650303240c41d6000641e01c65032044035030004c42c0c106805020f98145005c0c501101898a06ca02e601e001d6544109a620a010b0751070102c5422446c00c0c420728010a071281a1525901e0a14040f02121000410000c43c491600c1c210800320f80071a0300e0004500841d241a20310b010b504107403d000b130518a070221600c05120703111a00b0000280e0003001e882c07400d0380499241240a400480d41d81c00201d0107403024560a00c4e00d503036212240c500d60b000d4045088007510020a05140c0e082c81f140250080702d010340440d0042c809440280341a2004103042d40c4100c43c13658500e40ea0340600300070750303140070f5500300c80d540684c0407070006040656240c582d05a044902036801c5480030046880321781c02000301d000301758640503807071aa528104600520305034085a016517492000e040203000b041c052300d09034001101c0e5100103100440328020004410303030450140000303844060041c0c0f1140d00c10103049541140c1903403401c0c2280020701060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 698347688 1250 698346438 698346469
    0x60902040f02070b10030c0608041e03020f0d030b030a0f140d030b1806090a050a140a150f0f0605072a2c04060c050705060705090301050a0b0d030c020f 67
    0xb68a40c48545803103400c804c4014011005660034504c1000803c61407402c0d4400c0f5941340c00d051070903032540e051000d42c0100c2500422842c500456014080590002e034104012075048142c403002400c4003021402da5210a04240d8542e01030070081000c240c1c84000b036168540f02e0000958104118141c0d103080c422a002c4002c040ba60300c2d0344000003810900d1818840b031005030000d488500d00b040001d846240c000c1d00106d070380b6035580d0002d000f80003960b0104005c1540c000003c2c049281848460010b4030850b03010300a0a00140000101102c0450703c1c0c2080d142545180e0420b00d040800031038090300b020398180c4481011840c3c240c5086000100410100030b0600082013807400c4c20751a25078110b0085031100c4e000d071035030140c0c2680401040c4264000fa071080020400c00240b03070003201c0d14096084041c00c00e0240100303020b0225001001000304904c250028007441c0d45001030401116000c0c88039075003011907644580c001034480d905215405100a1060549558500108181480c2c1e91000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 698348938 1250 698347688 698347691
    0x1204020616140328021504110d06020306040b03060106020303010905070e090403051b030310091d15010e0105030a030807051615270819020c03060f07110a030206070c060902040f 78
    0x4821980351608100c0c1381020303004500c0002c901942c0259941700003078410490410306000300302009100256a9404680289220000b181e5401c22500a500c00d50b005440303203181100880031800d001c59254126801030300614150303840e040b48100600b8008207000100041a0034440b41507980554081c0914020364a903529008440c451981400c40320030707030603025401801007044142012211030300351000c50101041600100e158004610641d40d11702e085809002000c0300380441000b0250704071100d25003a4950b69a881050540340c00304c03502c015000810413000604160b0003000144403a00020013011042c200c2615130f102d03c10b442c105d215600c00c0e251100300440301c0181c500c80c1caa852031090407d08104195035101c082c0d00c03c800d640b1520000c4019403002e401e0090240303908150300503064580520300341d030b100060008212620b40104242c103981c0742050704001001030075140d26800130301250711100300a41e44000700b2070003111442c1e140c1c05a10016111809003400c4840c41400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 698350188 1250 698348938 698348947
    0xf030e0604031115060a06050a030905011a090f01061b02010c17030106020d0504050315270d11010c0c060b12011d0601210809040f0504050609010b0612040206161403 73
    0x10282000340c07540010248884c40340030301c00c150b03481e400e88104440c00d03400c0030356a0301da80d10400e0300a00300c2500302811039440d01c407800100924900307074541100b4007102c08000e0341d542c0081181c85088280104d800240c041c40079049105280b1444c81e140d20700504207032040c2200e0b03944898094034501c1c0c0300409110084010401180c042040f1320907000242400e9040c141000f0100c1e9884899601403100902030f40d000c81c2949101c41040f0b1302c1c4201f181a900c40301180074801075034542056101c4000150b100c804101103540610480d810050a50f1340d01d560922592030b6078024144003002558403400314154038600305030920629080000c0c0a40f031503c280c6e5403960060528030141c0c0700040c03650345004c800a00c28040c1850a160310350019800b40c8400d0001e01040080c048051882c403098600000d00041c4200068030300d2150a01900070700803114014248015400f6035541c3e641c4ca030b40d0081c0410b006103400c002401984408040d569200d01d0262111990700341d107072140b001c19400c0081d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 698351438 1250 698350188 698350217
    0x5160605160e0103060b0904051b0705031201060516020d05191b0f06080c0a0203070c0909050709200708071218050103061406070203010b0a060906080f010807060f030e060403 77
    0x110400c03102c6600342002c01100d840c0940c1089203200b82d003030043c4111343d00e4001407400320181070883d00300340c1c40046064603841e141c074102c0c1c0e5a0740f204461011091000000007030145c032440c2140d0003107416006a840c16000d80d401e0100b842200c5508603460b0040c02c0132081511840c00e20501c0580c040d2884d45207505800010030101c0009800134404403603020820310110303402050850300114104075040c1e0303d0145c50003c078250700409030010802500f01000154281e00ca4100c01a0300e40284196004039940c1d52307003d401c80e03a406400d40101020b1030100d02c96410f501000d09207032401404000c1c58043da981d65000545c03102105240410500d064650082801c001c0a40140000b8201040038506108000480b20202e0602a101d04000559181192400e400064080b50068089a401910382c00084d02c0752045d40180303800515940c2c009410324035840c28041c1281e0743c80024110150074404112407026007203030307890305041d107611140c4810201046954410b40c0a5541c4240242568 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 698352688 1250 698351438 698351447
    0x40915080f0105011a0a032d050c191b02100822020f10030f05091501080a02180402011101090606081b090615070512030103020112020a210914010b040e120702010516060516 76
    0x901144207090003030245141d2200c0c0301d00c950200503a0cd0400c00050b60a0032804103400d017840c42300941122204800000701a080b40c64a409500074046604c07244d283d0060102c0c0c0003900b9038001e0340c0011504844403160910703141e140701401441ca80418019400345503442591000c0d01c0100003940150480c83c42100d2108405024281c908081d080310745181d000140d8010348031001c6000e42608001080c1160f00448030011034400000007404183e00c0e40c02c1c1240280141e01c540011402904805403400c041c1c1c0d0402d2886c1c400007010210726071030380d03414054015142c41d8401c044440402c03103180415020008004414080d2a8403642c960451000402c07181c0c04942e1051400d0041c015584800c0d0450015628811180100522000341450100c0948010100030b005c00000c0c2203000040c480c103401c00000c0b080181c400f488100d400000407941c1307600207404c8600d001030600c0301c0e01c010341c4150010803150b56524820032540200c1e40751282100c00940304010a90881c061b09a00f031a0003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 698353938 1250 698352688 698352691
    0xc090a0b0a1202010e03071211010509030a121b0c090e0309060c06091005090307300e0f061e130902040e0a0e0111040e090102040915080f0105011a0a032d05 69
    0x2070b0042c10031f062802140c42181840c10a0081600d429580601c090b40d202c0e0b030641d400c4240041c211490007025050250840e01c01203140c0d00003c0b40042c0b41c003140c2c4a142c00c0c110b078083d032220444440516000c0600014842c42c140088180010001004203680e440090100b90451a0140100781000b0461911300480c1c400500c3d40c0904000402c42546030100644995540113079480b010404290700b0201028000100c0c0c001c0c05c1074090741d41001c90390016251441e02c00c00d030b480201c203202c14410401c0382e01460710306183c0300d0301004a40c002c1c406520058000401d0303400c04091390700d484104000c1070740c002c1e4001301880340345601003005c0340314180120380443e04200020401030144511081e11403055000f004210044040814603900d02507040718000e00e8404810400a1b50605442c8460741191280b42403900c0352a4041c10540b00620a1b035040380c0c071a2100712502015411111503e400c254028418156034104c441d4040704031000303841d00251110b084881d40b0a0442e200e904a440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 698355188 1250 698353938 698353967
    0x71208041701060609271b08060904080301260d0f030510051e06121314010c1704061b0906200703030e060f070303090209180c090a0b0a120201 63
    0x601c1420441c640e0014101c10a40d40c000c03c41a041c0c101e12548160382001c0f001d010b0b01e60314a0a00500c960f20700803400b00d40d007c641c0c1d960b1110a6294072040220366501658040c007207080c1000100480048480c00229000120303e60090416a000c426402c017022102c030100400c0310749a01d00182503040c407a1075481184500740d08141800c24010a04003200b803c40c3c44440d0080c100e038080541d442c44259901da003000700c680300b664680f060340d004505466141c2201c0c1d5521040008113000703418050400004415034900450412401c6042140d030303409003042c0c078410340c0c3d05d03404210402c0280d0004060586900d80c01402c0380f411100a0100507a01103100405210911001c0302c00c002007407020440360103141040c000c40701040060075521401e02e1900c011132002540100301030b0160040c01d0101d008a40703507901c5984120720150700004c0c01425484503040f05089030030500e42204250b401240b4140d001074030300c45c80b03c0400d9984200390000010019080340d851304540e031041d103501140d80d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 698356438 1250 698355188 698355191
    0xe0f0d0804020f1f050a03020408010e010204090c0c08030703023001050a090207030e090403140c0a0605181c03020d2a0e01080703020c12120618060310090203071208041701 76
    0x22544800035541c550384c8014080100000d00d0f04403a61198050f0f60140c24040020049091684103440c000d6015228028107142403140500c0e0250140c03c085080c6a00b1a458910303580e2100c80031002503000b1000c2c100c2e074a0482043c3c148104280040d169591040d0701d405041d54100b0007008405c160303640c8680307003041c0100121400640d000f0a8030307070548001d9440e10401e1b206e520b01902c48084540a940c0b94003808500c4000c40c2d0380c0000c14210560080404000d5500d90b507814490304290242c5c4605640e00c003400d00d016104800c0c04143d46000d80c1d10b00142805401c0c0000020340d91008c405070480d90320b0002aa014100e190f440706503110060500d0322000b40c40e03c0000c0d00d5400024100b405140d0302058040c851502800b22a041d0103007c2d100550f12143d50b4484c0705100c00945806d405203050303000000c00d500d40d20030440d0140034002c00400c928040c08100902070542e01500304d0301405020300000d00d071203041c0c040344070591081c50200d0300d540c01c01e03014003900020082003642c0780c1e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 698357688 1250 698356438 698356459
    0xa0f050102160609330b060c0d051306020c01090b030402152704090b070c14030412150e2d0109060e0d020607080103020111031e0a0f030213090e0f0d0804020f 70
    0x785c003440c0b400b0148410b0110b01c980313200000521a0041324141040c0303001340094884c8141c0d000d00203090b00031034405448074103a1110740c200d81d01c1c16141e02450209603030380c10a00510b004030740030715405440240117a072070030b00c12445000c141d000502c110000020300c0790100c021041510a81d540c2003800da07020040b619050301c60180043d4003501c3c200c20310a8180441c17040c0231079080d00d5101481224101c0b542c03540d54080003001c412074030b00d003541c00140d150544d100403140c50256585144042c4002d0050308403000c160b501d024138102d0b99241c600c46490044030003034000c3c001c1c00b103d00d0013180c0c00100700401082103414070002d4880d0304c0464202d40104142c050308508e14505403502860a2518041c99188644c41c43c80741200d03001012003c024800d6003c110f0000030312400d8102c1e03440c800e905102400940070b900507940c2a1401034160fa4042c00341c0c94195220b192031110032001c4480014540071000d0800040780701e0800042c10240400007581000c10391040c1c200019503130b42120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 698358938 1250 698357688 698357753
    0x180b03030304080f0f1305101e0f030f051609080f0a0605060109031b1e0b07080901050708030703021206090106051c061d04050c040b01020a0f050102160609 69
    0x8034030000300010040350012442201c98074801c0c06440417181202012941c2e0116880c0ca1450302d082c61140b18490984181d040744041c0c41001300e15043c211644c0c00380f4410b0282441034440c0303e0102c0d500d81c101aa0360b015410806028080c06015010500d41424041300008004121001c103400032283c0394001c4a0714042c0c00c0001030702480f032079040b0500254a8644100480f0740b00c0890740054402080340f61101d403005400d500c5241180c0c848005607812800360214084001182e205d0500c04202c103102980c04219404000c04002030145003413413501e03820340d446e1801904203988460010768081000c02d5036501c000403507034200d20200d40b078501c55031401c24010518400c440350001d81680f04000d91040c810f0f030313401c003002403c1106c1e240c142003084062070720b00392501102c0603070f4907106444001e002c9080a101e40340c81800c040e4098840c5583c01e03100c4c014183d0b4010401ca4041d0750801c140c050740c01d42e911030074050724031032800800c85483c181002d100540c200d00001481a0680c80300821 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698360188 1250 698358938 698358943
    0x503010b0108280f0518070f030201080c070605010f0810061503091506080c030712020d03080912072a1818020607030201150b0405210109021009180b03 67
    0x20b22050510b00580d0f40ba0103071180348000300320b038800c020145041000e03200b5900750035000f49125581100000c82d030002041855981c179021441a140d2543d801402400917504c81d86000f6440511103c07118079200b0307195030342c1d001c0707a0007640300380d0702041c2404041c08200c4043c050310f0301d030800510b0140072690900701252907044105181100307050b5200e01e152b04210f000320708490118040142001103541d2480e00544920000c0b89961103070040050101e10060120010400d454001c2c02c0050468040e980640b10408050204200c07441855046510480d4042c02001214440c1603210000907544c1c0c1c490000d4030307842e110710003007172404001417108804480c5a1607800e40c0100c00451000c1103c00442c0d50641e4019000c1d4014000040b4070042c15015085201d07941000384401c8a000c0c0d98020844040c0901e008041c0c0c0138800d403006030310420284089408034056080005129a403580c00a410515000e4550001c41d24010041061844070801d80d60300040100c4244120f0305903000180c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 698361438 1250 698360188 698360191
    0x20609070909030e130c09090513031815090e010b030f0a1a3a1707020a0b07030903170a090e07050702130506041b0c032102070812010503010b0108 65
    0x241010764402c0d0200a1501c40d5010200040000c1c03c0f000c0070280d085456000390015900f8071011854203030001400244920400344107216520715000034200c2a0340441e680c035003020301101e041311100e40200b0200c10b988440321502c5010303110100070038900703c1030059600051307000401118003807007081043d044121625500c136510705000200c4907940c00001503403d88160b003491b000100c000d6014001101001e40000b03000136403101e261121540700c1040000961400018041c00741031030b0f28910a07110710090000c0c46d10003810884070039210f403a1440039401000007900010341100c0100b05102c00c8035104008a118031556502d48041c045c0c004c0d041e01568811030031080311010000c0c805034480c82c00c4d40c801c25030085c4031003c000504003005024142c02e1318807501c25468801c01e80c04000c282c4000181202250b12502100e24003510280d4162407000a94400880c1503211314824100c0d0303100408100d0f2044880c0c64580c425007a0040904005800160181e03140c0800b4443c0c03a030304105043e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 698362688 1250 698361438 698361449
    0x506070809070b1210120f060e030f0706020a11060c04031b1e03110105030123040b04051009050f011d0a090512040608060a0e150f06070b01080d02060907 68
    0x65605440341484980703850200d40c000c40000001240c04c0041914000c4143d00407619151003c0d40980c45100451581c094102c0c000c00c280c0da64005c5100260040e0000000100c11205036820011b007600f0444403503102c0f0004803422035000030000740140e04000d586a4005024000b03044514003d50241080d02c00c0c0e010180211130920505240844040c6800025000034414801240f92801c11105484400d00040b039032512100c1d06036a003540f0030002c0c0c0b4100c07400922100d0035510110440101c01c0000e0302c0d0319402c151950004e00594640303000c1d0794001e407a1300c01c195141900e012500e10856102030907800441000d540100428144003005503200103540c1607003581912414160402003e0551004002e03000c0c1800c52241c082121020300200c503c9a240c2a00e02e98400c0d00b003002400490040c00703801e960301c20101b80c100319a2840d1100740d59000d003012254001400000e00c2a03000290100c50b0001000014040d03901e0521242191010a000070700e03160070550000394464900b030045 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 698363938 1250 698362688 698362697
    0x90924040e010b19062d050d0e0105041407050906150a0c17041d1b09060405040e07060201061502030909040201140c0105070305160212070309170a060c0903050607 72
    0xd1001d961801e502039101071000401c80d02214500a0034040204001c1c403501c000314400c4c0c101d28203128464298150140001140c401b07408142404c1170b00e483c0c01c40e249240c1040d903070b501743d9104400309104050140c5e014001c10b440f401c56640da800c1c0b40c0074141e0042d901a031130842c107000b81511840390751000075803c0c160070b544420030484119592100c01802810682c0c00d07459486810041d2401041550031080d00490740150384400016148016a0a82c8080841d144912105c01c06100586013a4000130407891034540d03605d0001d03044e00c5816040c0c1d2542d0304880030070000c5580910404e00280030a05c6002003031102284023a40fa0701918046600803109400040d0840e88280d030800001e0300383ca503c0c07a45600b4000009c500030001120f258000c01e00e000d000c19100710310f1400140055010f580109816807140035090540c2d0008a802c40502404403070103d03001031514610a281ea0b4410010403019084c0c1c100401514000700040d800d000d0411030500201d0004503a0950003941e5007071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 698365188 1250 698363938 698363951
    0x30b090a080304030f020c010e0f090c0c0a031d04060f0b030c040b12060f19031403130e040302060f040c050d020316090603020a081b150d1109092404 66
    0x1906040828505004091107000410802019007146010f40200c54540c01c0783c82007aa031741e00540c2d000d004048e48560010001110078001e19004549551240c0b2240806080502c40040940b0f4400186401c4001c1424415000c140e822684c07e0040000340450301802a00d1900208a81070f0310540182d030b02840c40040050855905035040f0740003403807851100380c1d036940c2d40c0210302e245c11800e55a4134480d00e0282203800040c58130341c8036006148520030201205078616a60005483d018510966031400f082c41351212100d143d4255030020100c81c0f0100c0e00900d41450300a00384500245944403403d0440240404101c102d1804001c1d00e00075945010002050b000003072910b400b8222011020484000101e85407000da08004126071080c1d40d565880358075030a8880e15848034502e80d200516802522000301c0c6040c12002c03424036441c08119142651542084066603803030544c0000541000801d180325082011202d6404800c0024441701050601a070508000c00b500701d140c4107030f85514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 698366438 1250 698365188 698365201
    0x170105360c09130c02030307051b07030309080d09240e0a080d0e0904080d0b060c0706020303160f09091a030f07170f07051009030501020a090312050c07030b 69
    0x5086252050003800d864014940302114001c2640b20000341030141445003201801840e15000c3c0c46500ca100b50061401d682d1400801c07100b50308022062416404410182e0625810620180e00a103010b5a01c1e10301480c20000041e150400c140c00110410068103003c02c102901c000801051074000e00c01c02d9003510110700304840c5080807031516540889418800291003c00050300c180744a1113840b00801103020004204285000311805400e07201c04220450482d001e81d40305014003000200014200403080760114a440065041003015900000a0000e80364040000702c0400c802441d2107400d80081100050101905205811125031500003000c0500f403500414019040086c045403000000c0030070f00e507683c4100d441111009800b1846040c01d032040031a051056004400051005900c3c100522000701003840940c010000c0c101d1000c03000400a00050100340007507034175020020705508100c10502c40d2001e4131000d0202c10410080a032038040303a03400803660044401c3d100369940c01e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 698367688 1250 698366438 698366509
    0x61508070906050927160f0306180906060b0304030203070516151101021c0614041b0c020102010b040e06060a0b031033090e010b070803040b04060b0a080d170105 71
    0x3d401c1100d5000c1c50608002038407921301111034595200d540d44000e07480c481c0d07c0540441e103903801090101c542e442d140e10703042c00e220f81000700c92511030900000c1e89580c91a01250f03036001a9000c600580000658400780300c4208170b017404106074083d2994409103480d812160050b041510075040c411003e80d005040c4000f0b50588041440d4010703030341e04a82054a5000041c615402445410760922140d16180d051074410020908405000c090703c905407000141c1d002421207000700c0c1103648409120065458600461200c004007900401807800d0031020000080807542015000c91000c0c400c206e50051081c400c41c0460b48018400400c03030464400c4442c20740c001d401520060095030324035000c05940110400100d0390006480e84031662941004d2826200c0c0ba100944424030030b001050204504840322a0403e02c50000055120100d001181603841c06500502c480d40106400911007600440343d140b88259030300003808198144030008840039100c0341d14001034410f00d0490390b0200a10b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 698368938 1250 698367688 698367739
    0xf0209090430170a0501120311070b1c0b010309031d030703060507050318010c090504020f210a0e060f04030f0c060f09290a0510090615080709060509 66
    0x2c94054803195040d070000c1c0004070410b1024007003400510024046100521070603040e10481c83d0080c1c05e400ca41c0d102224003001c140c00d645e1b003078040c5440000300301c900e4400070480d282840d40701c55850006850200304903821071241a041c541052940400a0b603c004000c4508516036642c007149580407020900d402c50503003004203940c1c40c16044c400b00c95003281c0914482c80e102020b9003c401040ca60060a903068010004046407840b2001c1c0a10f10707181d005001415560030943e0f050006100c8071961000c1108174161194500c4010310010008500581d007618000c0d80042041d42403040c0018a0100004d202508002210000e20280e038400c0f003200e5113258004c1402d011182840c041d5000130203a2070821100600c004010341d40c0c04a5507840740e205101540000d42c116621070701030b01e028002c020304650f800900e10802040e2551148a11400f40c0307006502c04410844070100502403c00203819002445030510040200c0c951140485502c9541134401003003a80c070398004000200071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 698370188 1250 698368938 698369003
    0x708030c010f0e07080a0b06060c16060e0109050307050405090f1e060f090606010c03110f0a110303040b07110a0312170a02131a0d1404060f02090904 66
    0x400600c0d00340c0040150458850764402240810900c0e400b40d492a0b6a00500d20680c1510b421161091010907000d241c131603400ba4000c0d116034584041015101d050640000c0280c03000c001c0c0030424003c480c1c0c003a580390f00320002802e00c10714203130521000070f965070110f01c55580300e26220400145200c00a200031101410600e0071220203224603800501d00603d05c5614108611940d000100f503003088001c0c1c2809242404041d014549598004680102c5c16103c1a001d01607a028a8031251200b0403480d03c4207503c0c0c401a208045451800c8081c542203201098400c1d03100740b00501c01002003c5c210781e00c01d6402440c15082902101c00f00e0b400008607070000d04010b544038154192243c0143c01c036200d410200340c4080d415914441c090089000b201100072080b24600c50621000880c01a03103400d400450051a00b0555101205020307145445180600c810054082c40204250703401898618142c14409504020054000c42c28000c00140048d0600d68400c01100441c0388043c0b142c141c4030b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 698371438 1250 698370188 698370193
    0x209040204030f030e04021206010c02180109020a120b09190b060301090519060f170102070b160906031802011d1809190f08070812010914010602010911060c0708 71
    0x5a6a00385a441946004411380c0421035010041503c0d1419200f22038200017450f0400c03a075038a5010044559405884003280c0101400150106906d514003400340244202403015a50701c0599100a1208001e50000c681b11410b100f80c0300c129036111508075901c282d0f01e0010010071203248085a0242c03120044440d0040380c0000041501d01060704600c2c8940001a10701181d05200c0d103249080b60824400e030b414044140d002400701c1d6000e03188090302148060005810481644c070380180e85101560150300507441c187c1020745890b0441c2c40500100880c0c1401c0140b80c18000b262804034200c41c0d4002d0400111024500d0741095035260b07032030981c03400f07009821081092016180c2005003640c005885107e4090513015500d04014004546940050008481d107055520075809070000c040403208141d060080e07107015045824014001c1010000100d00b1707103e48a04240c000c401030f0803810071a410140803c7c003003038074842d0400002d407044c1ca0540e551440380110328140b200c190007000150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 698372688 1250 698371438 698371447
    0xf0303110d180b070c051b030c1c02030c031f0903110f15010b07080d0b18100609090e1902030c300c09070309020f131509020f07080d02090402 63
    0x40301c081d52a640801c0c4614401c600c284c9407120309554003200d0720001043c651002c2000039401340c0804c3c0b4598842009801c444540000c103000804154241512100c0d0746041c016880961804000a500021003500542048000d228022100d0f0404103518402c80c1d485040e00c4c01010300c03400c15500c459807414140c4900840c064480c58a4007001421030a00207003c0b00003141c1514030b07408941100d588110650303d84010040d02d07901801070000955445a941803241d1a00c00e480b011661092414990701ca109600300200a821420345030044088586802c00700200502c000400b5511030035411035025412600340b000030710307000850240c030380c0140354030303a03a03515000311107480c00408800c456070a14140c0303010f4401030b03496003510280fa0f4004040c0010a00700c1c2e000341c4c0907035400d50000e0700007902d6505100c04614180da49110003000d1595a01801c0003100c0300807080405880b004100f54600741090808800314004d1030342c050940c01c0009004504850942d0454005800140055444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 698373938 1250 698372688 698372711
    0x60e010f111f0c080901110a1d040e03251e0213020409151a0f1804180203100e0319020708071d1608011a0c0f06010906060c0f0303110d 60
    0x50f05240703c0c007501180e09100031848421040c0100b0f05003041d1006154200080400d04503864130030301340f04c200880d00040c81c2603401d441d107016820303403000d104c80119034a1a10205445070901c1c3c6048021001400402880004800090f42c140060f884180400400a240000380c004441c0005260b0541e10005000825003000d070000808890806901c2429640d1200301c0304010420082521178520300300507100a00c521100a81800c03500c0185000e28900810007241c202c4c1c1c1c01c50001d21103100b01400c100f0440c501002010421002042c06001001c0c50201c4503907203028015034107170a02d0041941c1c8462034800c101200c01800414200c0e10344542c2c1c2c0b01c4520541c038060048054038150840080d48100e0340c19510b12180c4003640e900800b5030300c0c04a04090020110030018900c1c03e04100e072813080e0504000b0311b00e44980b0300d4050700c501d51400d44148101d540703903845002807111594460340460380d00039000c03041035054100810840b104e0990a0054400c8900d080d010300c0c41d002d0704404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 698375188 1250 698373938 698373941
    0x504110901032006190f020a050f01090c150806120a020d1103160b0405040207170a030510080f0604020405070903080f070507090501080307150f1d010501060e010f111f 74
    0x11031215403100c580c09000070424010244590340405c1e40c5030305901503241e0480d100d129020580e00d11881aa0303482c03030107541d55a087c003a1403080c1890b076a4441085034244204801c10b84000c3c154124030504814441e0009040041d0040100d84100e690020b40e00001c1001e0100a9609030300504a081c905980d1030200e149002204502d4041e2144007003070442c41c1e01e40004082980d100e00c500c03d09192903c2d0403c0065400002c049a0710314420311100d00d11407032400589050b2000c1d131030101e02403901c10b88403103400300d05900c0800305900c03007586840c007060b010420503040707501034030003146941d25120291050001c0303520041400200041881000070b49002400f0410300c907100341c2e480140c2e50f06480040d200203028466403600100214000100a42d0303105200794456100441c0c8098800c414000302c681039800740b88603008480500150310b40c28407500e8058049400c24000494982c00000d0910040a801a0610060102455003105c0030030100c46003500095094003044540c00c01e620 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 698376438 1250 698375188 698375213
    0x90f0612030c03090b2d030f342118020906180124030c09061d12010c091505040b13030210170f0402060d0218030307030906180f09050411090103 64
    0x5040441546d000c0340c0034105d00100da000318090b8007030f0442d540310352002d411502050016966500301142c02e000380d45100c1035801c0c241e00307a6030b00e4000d040e40500089600505040342d8000489260401c10103648040d881d40246154050780d8140482d0746a201140c0c0c0003002d00414071241003030f00700000e10f41c1d47c640080414040400d0345549502c00d00381040c2c059400340440080815511403040c0211841000300321f82c14100c510342068030f5208c6c1404035200c0c0b8014103403410681d450703081c002d1505800445100080510380508201e48108000040031070040c3d000d402c6001d140041c0c1101112409a001005150010507012030160140e10241a51145280c50155503209c000094441800d628005121b02c1d00a02000d240c903421418860080d03000380a84144040d420340f04890944040025120f9140b09844041e241c0d410030b080604521a03040400101252a800030b00451601540410482e038180101049a494914103072203040ca0003030340b154020300020000002d001c004111038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 698377688 1250 698376438 698376487
    0x2190f0e0405060703020309190b0106030606090b040605070335011202180a060b03090703051c0207090f1d150108240907081006090f0612030c03090b 66
    0xa016280e45110100c0340e240100c07800b034116040800021003050080d0000d6034000001c0041c1c07280620b62160014400150140c1a541f4206100060012071340611a05016013001e0a05000580c64589040014842c50254104200000c43d000c02014061249110300f0f202005500895504286040d4010041c008150301150401000000c4191440048041c1c003500a0074600305105031014000403150060a0700f0700c0b140c0e9688000035850a08809540070f07600c11000b5002503480c40c10018984213514040006160805098080c1503800148940484280190100714182c10f070171820002d050150400c10014030764440c0d4007140c107000c11a05c085070350f100311136a40c50f62a05211541c68948014035040d00700c200030790704203215248440603400907180d000c8450b510f440304401030a1030150002070300f007642ca5a5060111840380e010700d8054140c0c06004100051600c1c0c1c030101c1d021250300c2c01030244045200c00c0028544605111005400750480c502d540d5041d00396aa40c28010304900b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 698378938 1250 698377688 698377709
    0x14010905040c0609060c020d2105030402030606030715142b050907062a0f1217040831060207050f0607051216120f12050106020d0c020402070219 64
    0x1c10f6803409038042c4001d030b0312503a951480d4100c003a424001e4444000100f507420b40390084000c48890070350400c21544006a640f00b85e26802e080c81810316011014180c148039400c02c00040c003001c40d01e03900b004442841480c01210202912035501030703a00c180d4800b600b030200c0c100140482190032011680d4111f0304c139001003040d5a42e9010858881d040c0f8041d140c00202c00c6120843c00c2440c04040041c01300084044030506130203a80c98040910031704100f19420403121031445031103508034100243c0d034095011828010302d0642d880d15200d115100943d08440c1c0b4082d60b1400e038061412034030702014444c00003903110548039080a5540e40c820f1040340c0c8540e02e001074941c9541400d500f80c400f059408001001310000401c3d10360019000501c1c0002e42c18140588140402c103044ea0261042ca07031922080740e40341c20420000c008204511100241034203040040008540c0000d869991455500d0542c0ea01c11107440098064419950041e6000041142e495841c1c42c00d101c603035040710001c012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 698380188 1250 698378938 698378963
    0x905040c0302100e06161704060305040c0806070c02010c050118050106090f02070c0504240306020a0e06030f0106081305032710020a02010e0d06091101020105090703050c131401090504 81
    0x211024511301c13140170f401010510880d00c800c1c1d01608200c0256200b01e12034412400030078008545508544e2018002948840c188001d01100403907100c0034050b000302409591502e40801b618204100c0b000a04020100c3c41c000b0510000f0b42c005c02040c0c00c840a000d0f9100401c2c10310502802c424050390811b903161040380b03860032505108903030b115607016402000071450320040000401c0402c80d050409558061595408081924000e02544c480d40e00140c8400c1290001841c0351a2008110f02a103c00c005104c448184024032a0444819181c19015a070360b5500300c100f02401003c1c02030081c803003c20155500c60a29281c8101c0030710074020346800001500070001041100c410410160704041661405075200b40360040c20480e01510035034808207a40d80d40d804440c20380c030007605c41440702e410740306583d80d0a003e083d030801c5101000b80009411a16503075100c60000c241c1d0b605c545601300c0240c40b0032a468000040110b121a40007043d582c1d50b08204020381400c440440b02e0b9a03c048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 698381294 1106 698380188 698380219
    0x120309030d0f02071e0819051207020610030b090a02180702060109050613091a10080f010603031403100503120a0801090203070e06070c0905040c0302 66
    0x900450756035004060600071915030100c02d03440d09004006150200c4e40c07288042c0b0403031400752404000015035145c02c034840d114035101d0b103070a00c03107413184400c9058005000d8104200d840450b0031061b901c528049071295801c989916900318100c8040c00420781c0b948440754085101d03022220381001580000c2c1c01d001000c00c0c1007060000020811084c1d9a041c800e86005220070081030209041c0100015951024040d0ba00da02a980e60902800d2107040c0101c0c4100400041c0c3c00740503403d0288c240c0103040c406000b00b0804d07218460a1500091051203400c04403034256840802c030001c00c13140400113a10141030307008001603201010402e03907018000001c100c40c0001182d41d81d00c400701006041070700144e21003080e140c81407040012140e00221070280342e03202121082d6851045141498802d170b000d07040f1181080c07800b4200001c010010562505032402100d0030320200c074804 = true := by decide +kernel

theorem cover : BRFrame.Cov 698201438 698381294 := by
  have h0 := BRFrame.cov_init 698201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 698201438 ≤ n) (h2 : n < 698381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
