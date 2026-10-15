-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4796
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:45:22.331647+00:00
-- url     : https://prove2.me/submissions/01674659-9856-46bc-a821-722c560cae1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 862410071 ≤ n < 862589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 862411321 1250 862410071 862410077
    0x10605041109040c12020a050a12061d13050336060f090a0806090604031205010506071217180d0e0f0603100305030c07090c050a0918180c060215090c01 67
    0x20303c04c0a0815101102007448000c03044d440000d4017900f445c1c1100140111a00950b140780c845403842d2501000c50702a8090940030210304900f0001c0c04455400e207650090148840b030b05903020941d1154603640140d10b81030355210120715601900c2106e800c850f0207419160480c40d00140da005c020480901c50364030950480c600000d681415070702d90701e40c200d00625241c030842d6103514003107010700d89800701030b50102d00103881d9201d086204d1300d182c010036042e41c80040000d45003605076521100700d103802c16a0308081c000c45852824503000c8428030345225080368000d40c1c2c001d200106d0b40c036003403101c294000014420110b50005042d10360603424400d400c420350745c45507a130711640310141c00011680e200801e20300c8005004021900041602c90864000900034402181039050569030f50048820440005076900d5081149800041e02e04280c5410608001618092038049a02d021000d18059031440c0b91840f00b00101581040a1484a0900a011403190804101d0a901d0303020f032409043c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 862412571 1250 862411321 862411331
    0x210c1f0f1101021201080d2c01050d090609050d09080f19050c0303031005030705090103031704170a030203011d0403020304060c0303060e0112050705010224152101060504110904 78
    0x241441c01d6048410301c20300c0100e080d19542e91440c80303590f1030301d040b0400c5000481d00c0c8080458000301d41c44c800c44041c95849005800c5401e50011180da400120704c495030703903403900070020200d0664031605140d2401900a40440d140781507024010103419400b11207103038403042078080c10070000705866101c0514003050365001540760401900e8010140221a414000081071008901201c2d11041c12244103a003030750300c12907640c000c11081010905c0007501050700c03125891611600800080c0c0d00500c80c07c50815000100b600c00d20740794200380204004260700000612505464020828041c440004503039040c1c9442c1e54025128004c500c80c04007803288071005a0300f054002d0b04503c000e000804058803040d84d642134420165403540c6015519800741d41004030303ea502c041104203198064800305840401550300544c40c40c000180020500780c1254541845130396090b0500c0d01c800c140d61202000c1c0742210036810b08580d095030040e4270451419141e1100c44074880e0689010201c12540011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 862413821 1250 862412571 862412597
    0xb0132180402040e03042304020a0903030c0203010603061b020615030d081504021918290906031005181303080601030b21010f0603050606040b210c1f0f 67
    0x10213440ea0311100d059074003002c607011030540d4403011800c054100303a100c030801c0c100b051018803080744602403441c00000d60210082c00860b000b0020181c000b4405000001c0306d5550f43c44490494900c181d0080e0403c15505800305075941c10004160098525944101c55080c10301c002551426803800c920140200c403400600128800300034141340400142c81599a0a094031240c0303c001c07801e403200301c0460440001703068005c940c0326500c41a40d40c40050004001441c5042c6e0301c100c51000c6042d4480c1310108085981e54442101560145d03c64000401c4190700703042c1040b0003023000c440010f01320803d0604010284d11024201c92203d501410626065210180120090f040000110f50082ca0100c400c0b01703400d20603a62900414000310003000300c1c041e1000c42c1020703140d040c480a4081c2e40a240881d00c0c40c80d069000c1822104000c05c1c000031541008104c511340d4402c40502c03485904400d0150001d803c000c80319045040e12102030703064a81031090701038542004160184204141446261 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 862415071 1250 862413821 862413829
    0x80306011b0210030218040501080c10170108030715020a0210020d091e14030703020d0e121510050a141c020a09050411040b01080403030509190b090d0c170f070b0132180402 76
    0x300e1299100d011a0180d6856883f003d90300e42c00b680040700c640c120b0f18002e2844840510030394220481c55405003e58440308205180a500042408010b041d40d8000c400006002c4d02c3c0907900480302c82d25010300c000c40500308142e0180b03a2106440340c5800400400000a41c0495848403442103820071405003200800424903555260a50301000d21a4443d1080c00c0f04072030071218441c26040c11a01c000d20740320790503c10b40d60040c3c0300300c3d030b01403100703052100a070b02d40f419204a101141b02c080c9800303d80c85800084500b40943d10504007255a00c09100500c4040c4e02043c0402d04195000c2c0078a8441000081100308002d101130109135450011510014040c000c00c504002440c015020880048c1081d0400480540350311f0301d40e00c107000706121002e000701e00315400103420664928403400c440c1110007260340002078140701c0300390401c010000120315000b454007030806400700c0340710030b84e0341711903150112044035580b1201880e0700c0c2640c0503030740c400c10071075200c50200100c0d03005500c03a44045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 862416321 1250 862415071 862415087
    0x60e010317040312110607030b030d2106060f02061003080301090b1f05090901050f090f090a080a0c120306050303030601030902040902090f090d0c080306011b0210030218040501080c10 81
    0x1c00c0304e5464505280c0040d80134000069542c1031070255156525441c800f074045821150460b80c05400c062900c4522901955a4008156900d055400804808000d81c0700301c46c0107803c010085080c04480440b201c3d030411544e0341c0044a1082042c05d0b0b411510b44403000e0005225000030580ca4281c1043d058071000160f007020000c5800306082850030881c040c01c0364020364076240c014115040001054074110582004254024040e1842030701c0341c00b840c2c2c603001002450560b06104400301d40b400a00ca050050448005a95903211051054a002c40c054000c0084500402d0f0030148240040e50b408021260040746c01d003800110f05017130341b000c54003600c000740c1c01030760021001c010841e104085501040c414601d042c00d4521100e882031043c0e440840102010307002c0358041c40080c01550007030b444248035401c440b020f8001350307503c0e5001034030381840e44416400298000c190003490040072038a0340f01a40c812a02030200f0f41c1049204c680c1c440f0607495103440f07401d0399100081c500d4016810303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 862417571 1250 862416321 862416323
    0xe0c0a0507150b180606071b030f0b010603050f040c06030e010609063804031716050706021e1b0f03060a050f0c0a08190632010201060e0103170403 65
    0x40c0d140500c41d1400c00000a01c0f00da40018000c013a0200e03281e884a1030f0036000c82c0300d508010019420080c1c540c99a0340508403602407100e0b0380505800120109480c10740044429109503115034a540c1010001020b88801416881015080c0c0052000003006040c512041c3c81591030006032054100380c5150141405a000c0c016070f03440c00ca008200c03d410f622200c00200800002d0182c42001100c20704016800034518801e440d50600061000404640100b10080034a504250420182e440514464104510100d6255000d80d0040014503014052003900d49580128510602440b0340119103911a0440c01d24403e1445075000c00c0c190303224000c2e50350031880a0119150f0f460003402e210020203041e2415062507a492000541001c180401c0301c40303040c00f681c0d803c0101c1d2948401c0c0c61919a40654107400c0e65103816000c55079414644500c0d900010802e203580d15610101440c50704503450b11900e03070440e4108003081c8800e07012242c040341100e90200d6072007000201002a81c45074022500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 862418821 1250 862417571 862417583
    0x10e09091c0309060e0303070c112101020315060903070b030a0e0a03111605060a0518042d020c030405100203040b030f1f0807050d05032a0d08010e0c0a0507 69
    0x36001c025a031552014216500c01c1208001d84450700d40602d50300c0c0012101000001c02010f6914001003a501c0400041c004c00b40514526140c100300b82d5260014040803106039a501004110264941d020601d068120a9038030914200c13a09021030748a64080c024003020500000c085420560301794000c4403107201c66000c0e0313001154240340040a142511580182da071196611820407564080450001c0b03440c000d104a24281e0682e4040d5031942109a01503440c4400c0019804280c0700c600a1544186e141d040e01454190420790350b0520040c5180303050b200510601555000005c000100c6080d50021101d003000f04440300340480c0b40d88100d410050400354040288a800d06c510641140035488a120418000c071b002030340300402c1402485a600e484e485a8400c01103410050b40002101e4060000d4a15000b400b0903108111000364149450212038211440710300d00702030200c1000c54a8910340406a54900f05003880341440c081d0494580610014000085078022011120a0b940c404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 862420071 1250 862418821 862418863
    0x1009171303210215070207050409290106111203010909052103070807031407121104080a02011b0b04031b1a010801111e031509280b010e0909 62
    0xc1810040c1814040580e0140c03080300c0301c2d804c2c0b071450810200e114048035030040043c18a08401c02c0081c0100160681d5007004a43d004c01d4070000e0544030040e04411074400502d15494260003c000c98001426402c940d00000001c1e200710000710204c90450f40c203c007000c0f03a0a00b00341009414a452410141c004804100508000d00ea1442c00380d84070300d400c1d4540304510340d00c3d0030090b000d541680842420044661000480b90360003605e04040320522078000049030040c10801130300c00c1d40b0a8010300556403158801c1002c6690101d20410021521000d607162100c0583d0781030f55440c4040c03c02014843c0240500c854901c1256100803520b41000e010b0b0f03414690040b41c2d1a0041c000c0c0030381c3c030700755003003400309078003205060200c40401d451a00c8003d866a0f401000c00f0480d0009410301540c0d0680c0c1088120640d100c104403405040080d010000f01c0c0b5045161030540243c00200d0581182081c4880b02a40c0c6c004041c0c090407001079030900c2c400e41c1c4501c0c0c01400e1441014290807089a8a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 862421321 1250 862420071 862420103
    0x2031e010b0102070e060d1506050621011d042a1d1605040504021303020d080307030609061413060f06020307020301050f15120109050a0308091009171303 68
    0x1504030803220741d000c1e02516103154450305000a0854102d80300b0b5041204003d00d5000200c804240b2481c16420b20000100c6a448400240c0d035a03000170041c0d0f0500c1442c0c110b913100c0340c0820205900400b0715000342d514001c00700d6124141940c0c000c001401150034034900e04241e5004554401d80c00d03102e0b6044054031502c0e01c851400c01c44082e1a0900311b101200e0000b2030703a0602e6030500018000310745075181001e180c1f40c1004081e6120881004400d0400c090020040c1c544041c1001403520503500b02e0b8880c03400003401000c99080e54401c4229600300300c400c2100c100da1291a401c03180c070507110a9001c841d1b01e071a00014010503409034058080341d0100203100f0354040041d001d40c1d071088000780400d803100209100080c0042e5140317418a40386150416a92070300b82100050030010340700218501081c0d0b00c4071400c21507480b80c280d001c0f030800d00c01c00603000420f0064070044010341c40c0c20001680d964541d203210110750060380000302400076a1301d0303e00750380c00781c9070008652080c0c00c082d207413901e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 862422571 1250 862421321 862421323
    0x120c063210091407030c2d020c041103180106060504152007090c032c0a08180a08030715110702041e0e07080d03020a0e130c0822060902031e 62
    0x100c1d4004c000030b2804440c1581c140c480c080c1c0c1e05d052546149042941d0205002051007501615800380a501c1203440700c0390f543d2124020803214403c40b9040d2070b03d1b460704000d08500e200e0300711000321099160000520801c0c1e0440141e0341511410030700628101c034410001c0d11040d0184219680407012503050601d114400105c640a41c1c00700300007808003031142d0006400741d910144103203141d22500c6544042c810700660014001c09508403c90fa04c00c205a201c21006611050342254035508040021800341003000094009140f00d8008500e44419910b550190705440380b04030b010144c441402815400485040d0342d48190010f001704807000700030b030120401c800c2c000441600c907030411140b03441900c00480e1120417103001c04007030103a03861074002c00ca000f54071100d000028400e0740c44d00741c0c40e50f46410310000081001110001400780b60880e010b82102c2006010780880d0080b02e5804070042c0e010100300c40d003540d115801080d2061980300280c00d0442d07408180380072404420b40202c815030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 862423821 1250 862422571 862422611
    0x10e070519030206030105060708090a1e060c110d050705030f0703060f0c050d05090102130e0a060f0b040b1b01231003032703120c06321009 62
    0x12620701550303160000e03000250600d0780c031000c3d60000303003400100b0107801c200c4020020b4910031840c0e54075110702c02e80011007500c420342000d80c02e0032039140384404c110f0b840e440c404060170150803c82804c004958568040300c0e04008101d016a03071000b15881000030400048000d42801400d44a41000f000811652581c01d44000c1e04c486041001212021003203114034010000da40c1e44081c503104001400b003024110150003e0820765080100401e101d82898600c405008040742d8242c241c14071007281c02c242c60341a0041641c2080c1d10600b040207201d540200c904466002080e6a1030ba0490a0b805c180c022038894016031550030001e041485410103104000e800007101030030825901c60040e5249500954000100420210124205015114070703c805299160780503c401580e180c0c0e40e2800408094049040460318004a1108024113070241320142000c10314030107484034200184081c614007040ea95000c0c8004800420100051801e8071406882e1100091060300180302010203400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 862425071 1250 862423821 862423829
    0x15170102280e012102070804090f0b0f0d03030f3905040603090f050d030b0102010b03160e0c1608130509270705092a031e0a0b03010e07 60
    0x190705140300052000000500d102940c180d42e00744803030707120100550340120819036400d003c40b02c18078940d450945500007403802920910b4566212442d06940e241034074084505c00c680c0c0c0c0d041940c502c0c010f031150300303882442000807580900c1654060500354001c4c002d401800c204642015102040b440029220700c0b4018800710b081e5180400c3d417000480e03946040011200002c03c100700400c0b04e00c0c440c0d00003400d490f0144400303034001031040c0d991610b1f010b104141840805c1d20780811981a68088c82000c2003580e0a6024222803072012500705003955003405100d030185038203c00315030710380340c1882616500940b050b4440c10f000303118101400d4507002445281002040c5030004101420822011400340d24000c103040350b0f180c050085026141c081d02407032800380c0308003000050700c0e0360340c0c2d04a280160800c600c1c22a59105410340d080000780d15400078080c460041003403210701c08600103040b085114041c0a084561203242c0072230041c202128103541d242d03003040c001070445000400d80c14116 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 862426321 1250 862425071 862425097
    0x40f02010e1503010806090705090f0a0903110a050c041116020607140601121511030a0f0e01060303050310122316240206012d051203120903070b01030615170102 71
    0xa0b03640c0d2790030868001e80455022000740c5e040e002003410f54030184c05c08a06c4a00c039052007181075085044607894003400001c20b40300b40d0b100c10390302145400e10344607003409140500c0c00249425034113801d0320801512208001e0203a80c000030f800c4107100c500c4410812110085003650071550f07442ca0f0004502550081c1a510340d403500345120a401c01d039200e04000701090404282c1142d4455046000900c0032100d4203400325120f000020f02e50030203201e110082c1d48241c48140e240e090a05000080d0007040e0888165003800d80d504001042c400345115035071049000314940c091201c003003d2400e015403046042c40f0000902d00c0454545545070500e01d2060300758000604080d52044100d035904820311030380c0d03170030b0042528003200c0c107a0005541d00036801c18000c0e106441e917036501007002c1459410421400350000701c0c20100c2c3c92021248180c00c080410001c0d41454469103921072400070610006080c543c1d41c9590400c85032441c07030340c4001041ca040308152000c0034040114040d5004040107584 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 862427571 1250 862426321 862426333
    0x50303180a120c0516090c0e100c1707020618130603081905040807060201090b070203030601120b0f090403020706140f0d0c053f040f02010e150301080609 68
    0x4900030000d6010181034010100116001c030181d41075070000402c0c441038449004001c2c0300d81c22002c49a60303180007400980342c0080d0240340d10f0310050816001c41100c51080300e5024020114a07480045442a15040a01440440000e10342c8480520032120000d40000010504594020100000056070002607a1060ec103040e481180c108a5116010040050500b030188890112080c03000d40c07a00c00a60034101c2c6400d4482841d2450511158000030040c1c1d10744030030b0410070280025280e00220280003c0d0b045040010028051200c803001c902d00056480400040fa60703501e0f107a0320002140581040000e062908009488038035600039000400c4000700441460030b040c0d4120784401903080444e50a14005440c0706020f03004944a1104010080c4410700c00308000d80c112810500111403000482c100c421904804075400325407107541c1140c4041000041090030221245040e030910707100a91001800014031104000781c401400c0c2c06c000300000c14202d8001035030502a07030741d180450b18 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 862428821 1250 862427571 862427611
    0xc1503060902311e03060e030c030a0c03050d0f05060321070605100806130b060909030d27060b04060b07150911101706030c24040b07050303 62
    0xe9100f2180c80451403c01d1461058a00d01c00211207400e800601051441180d0ba5031403e08008811641c0442c410200d014100208111486450703c1d0b0107086000d103003040c0b11252940c1d2240259540581801141c000c88400c05101c2d600b01c0304841350056040082c0d40f210502c0100803d021140d85000b80700705200c22284d01603050206014000e40301d001482e00085990f400091b203400781441121000e40c1c900440e00320300511115224040b0a229500307003602a040400d041c00001d000305000c0c032440c606000342980044120b0700c450110b800d010410442101a0300b000001c0c02854580380c0188800b000e0400c612600580307840201200c050155135200c414520f100d1169840007418034550641c0c046440c0c0c2c890304003c450b14015038002c90b1203500340300459654400410080b000410b0121300181c03400005022a400c0841035000b0302030300020002181c0c0b22210003002d2410b4003212030040c2d6601c010360b002c42c0e02a015070480030307884503d0703890a03695a0b0020380e1846a4035940f0700c0590 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 862430071 1250 862428821 862428839
    0x40f0c02300a1d1507030e04060909030c060506010c0b1f05040f060e010819140a1a04020102160810020f1e0307090b1c020a030b03010c0207060e03011a0415030c150306 74
    0x301080c4e044d4034141d10b42502e0b0380c0d0030741d4820100820190410b454010014102c1290b100310754130b182c000c2e101d0341005032542c9404000c98400034400e606001181c482007000c030740d220030744907400070174040000511030a0740b40003000504580c2c403107a071050410b503140c0280c40468110070708491810706110440d0740ca6286003a00c40802d0324940f10001d40301c182c6071020039221001c5902c500c0208042e11421078454035040c2d030100e0129550340305075002505010440d41d0401120403a1419144d84101c3d540c2041500d61319040716111184503560040f80780000c05008804032900c00296211a8001c1c040c0450340c41c03a6508221200b5001c10000100011480b045508488007510707001103441c0400d1207100c07a20020740040b003c5000309692058011507641702440360f103040051540081c03282c0f51400d1802092001034000d1540603904000b01980204445c0d040142001012240071441d03c0810040b10340b842100d51026205c86170700c4100040883e14890280803401b1070b070750188003040e101e002c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 862431321 1250 862430071 862430089
    0x418230d08090a020433031101020615010e0102010b1207080106051504030308070522170a0f02040b0f0a0303032c0a060b060f0f0405040f0c02300a1d 66
    0x41460390090380542e0300500e015403100011040b0340c45200c2e10721b0055a2041c00b880680000c0144040710140280140040d4024080c0704020920040c1031503d00b5040c01803017001300681c02410f0103100002110268002e401007600c81c4805046040401021424141d544030644680c907082d5207010004903460414041000c0c41c450351409851510b4070755a8100e40b0b4020040c40d0100b0003000f400105a803244240040018004055945107018102488401c00841d03103d1340343d0b41076000c07155034000200540001110b06404840005045401c1c070040349114a581045591040041ca404001c268055000035180da070440600200700310f943d0318041d450300d506060a58140d00506007880040c80981000c941228042d10050410700c8913075488500350000311460380b01030740204060000c0d0400344208440c03828440c4080c08415a00240a51030380310a1442020140c5d290000030800309031006400b074041c5034404003640c0c0c1d940643c00280740844c14105d01140120822010741039191901c8a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 862432571 1250 862431321 862431331
    0x4060f060f20251205030a2f010207031404271103100e01120309140a05031902030c090f07080901090f030306060f0215011502010b060409051e0f060418230d08 70
    0x661415107000400c1d070b21048d0f0b05801003074419002004090303010300302d42004521100072001680301d20540c41c010f1b00d080000101e5a032001d0003444200408007500c0b0200c402c0390343c2080b407500708201a1000a018014020071211015400001e11030013043c02c0b410501220310b8640012002d0340ca4401000c0c48280c100000740015484040c14801454005600d040c000001004a0310b000d5683e0042030a10400008000c49404481c00500642c1810b001406012070101c40d00c05951800102c18174a580e0041c2880d400c0107060400a10321681c254407849109400488281914002e803500801504450060200240b03a80f0b6001e602140000f070f00c611018021054a040c0343e00700784917081d4412150001030119902c0341c40d22102030702d41c5001000030701340001002c9424a4404d0f500080c03820181514503a4200d10030130040000c01c0e54849982001045a000c160b82c0c807108020720341d10b14480c0d00641890350280c007a4229030312103020380c50380003044404d81d80303c9201140251114441254 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 862433821 1250 862432571 862432573
    0x6071a24150c0f0a03031a1c0f240f06050f0a031101020304090e071a04080a15110c0d0e040b0306061026010504060f060f20251205 58
    0x15604001c00c0008001d4a101c81c05241140c03a4807405401c1c49207413051041042d4046581c98849000549803903d100c014001c00b81e9150200e4194118001c0d4141c90310071000d40b12011041034082000b9131303507420b103081e0041a14103a542d0606c1c2030f05400103202001900030584d107400d1000405080003485103210b051b0080c5842103242c55512000500c2020440b12411800b0800c03020401c80054800c6901c3d035942c042c0108285824216020202c0c1000d64003501921400e000400c4a20700000b5800310b4035501c88460319407080d414070003c01400c4420303880c5034580e0780401d00e560904000120b0201d110b01d10b6a4154618410b00c00740400c0314220101c03150560400710028000382801c44508102c1d00c2e0074a070020140030418221482081c64508607030704a07a0045c010880d62030079010b0030000e0030181d904002c3e07a514248000d4010075040100300c0c140280c03440320300078a10f01c480355503085190b00002d82e91a04122981c3c413601c203074000b50b41c400c0c000010001048034090103001e01c0c1103540c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 862435071 1250 862433821 862433839
    0x40e010f091832010207030e0907080613111306020604170306030c04020c100501060807020609070b1611040e0c181006051b0a0308040330020906071a24 67
    0x10410f010b41c1030030251203a0f480b0444800c040f40800244010441c190082d070740c078003c2d03040307400030041c1c0e084020f001c00040050b80b0b8140015552400c42e0030303001520701c52000a045002c0e20310312025014501800c07071010b4a50031b000400304d4022810070300c124415054041d20494648520a01d4002502d85a0b0181d115120341026030500790b005105052207a411582d20452090791041611002d822600001d05400240b2440c01d404000060300140d401024003c981d0030070505580134010090307550505000307075490209000ca448803514043c50040c1083c810104a04081547c0740d00000f80c89001301c03079401441408000104605004080c070201c001100c1d0320f080c3c1d0848041e0460300410f80744521400d40d120000c0710030040c05a1052003078854100600c0c0900b0064106100c60450070401011800b0107074001080c6208000030341e1b1056001a00e440381c8002080c003d028828000349241849015562030070320a0364442d11400203c1e20a044a500c803100c108848540d814078290049100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 862436321 1250 862435071 862435103
    0x60503090124090c0306052e0804020612150a0807050a0b09030613211e18051507141c0908070509060609102c090a0908040e010f0918 59
    0x354103d030303076613090b1480c01045564840300080c00000c001e030b120b845c1c104011006400c80d001e942c54482e00410700e0341172a02e001c1c5040c2c0c010403114458045c45000990701640061804c00c1d400c1c01d40d0707000c14006020101d000b9281c0b0101c076074804243c001ea03440340400000000f00e03048100121503403c030001d000741c46141c40d451802419409464400c986080c0e00280c000c0032213614041003090051507544401c0c007007a642c10311810b0201442000401c0002c9219450400d40100582408644003911212450071103601140c0c2c00e4090894001c00c01c1c0b101c0c245060440a0004030b048980700d49404104040062007401d42c4c40d208030380b01c2c000306a0030004d810042442c003000c0c110b50249000d819149004440c0c00040d158442c01009a000301d0807010015001540000d4103013510b10300e590168030010b40c03036400039440180c002c0164106c0307910760026000b0805250144c4005100c1d0700941e00c44e550311580490485003203401a110320038a081320080b000540d004c902e080c1903401041c002d4440e216 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 862437571 1250 862436321 862436339
    0x1309140a0b3c0d08090f0402190806011206061805030105010305120f090a03050a0b0114030a06020d0603050609150a0506011e030e071e140102060f040615060503090124 74
    0x2040120700e02c640d18410840541c035a8030342124240e10030003800b65100c0185040100e014090f04a16010702d1051001c4189448840c0d0079000c40406402c0024299072407100484406000e032400c2024581040d200284c0386070031240681e4001d00c03980081c0c208607102c406140c01c8540900c0083c3c4070790701011181e205000c030440100b80407031002d80c20728542225040411960b0390300f13074000c440c0d65000a103040f090003c0b440c401405402d69007040c03241c071045800042d81c1c0d0000d0fa00050302c4940c0c0066003010b00840d9612075070040d075014090b99003d01d00803150340d4441411a42180b143c200c89030005151040c0e61080505c105416150f034080240203841c009501006021010181903441a041448060030040c2c40c0041001090f00c902626003004003c20b20159a8050350158018079a9035805030f0b0003249040d84107160341004d1495685506111000c2d015500a013029800144401304903142d124005510900500009000c1c08030000704e803d1490703c105010301310000842c00b0601c0305200f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 862438821 1250 862437571 862437649
    0x105070225030206030103030806010806040e06150d0f03031409030307140a052a010c020c031506150c0309011d01090306020c2e27081309140a0b 64
    0x1a5141c65851500da5000c20b030702d58003c0e001035012811306010010b20390f074801007440c2e1016096805001c0d40690800c0540d80c0c0c039000d03001d542c80c100721048000090311002208401c0c00d41005180c0c1c0d020060703040207001000200c01402c010242c8100040e00031000204607801501f86596800302060340c43c81c1d8101d07a40108901a04000040042018881c811111400c040860410030341440d400200800c0c2102c0c0d4049200e001c0d5088640c40103655980402c0e6030f00600307000c4420300c415695040000e0900c0d006122b21307280354900822807296090002010344004503080c4c840b401017056401d5103204401ea400703015400124000e2041c1b0009540e600a00aa11951030031038a000d441000400c154001c044e0040080b425800340c0c0614142c06806600d840300c2d603140c0ca240304121502100c5074a0601c881014002400028222071420000c1114000900700030008003c403d03920712042541d464190380b41d1018034103005198800c1d21780201c81c08e0401070030300002c241121010803070807001a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 862440071 1250 862438821 862438873
    0xf08130f0b0d0218040c0906020c10051611030a0318050418030c030302131202100302090306041b0b040e0a0501050901081902150307090e0c041a1804020c0a0c0801050702 75
    0x4c4c040005030701c0e91224080c0309881921034444510303035424004000e24259440e05507d1188003280c20f1030800a4002e000c036402402001342946603540e40d824a00f011010b09429107030180705010010007816440a00da43c42c00104a8410350080d54130810001902c400180000d0904914038226000901518070300c50400d209040c0036044c0169042d211088200a505c5111500707803903c10307002186800c802002c00b0b0741c583d050441c14800da42011031f541d0b10005000400801c0c080b1021080c100452491400a007007500701c4076a19515203190b80c06c0f45609840ca51401e600305000070a1600d001d61a060580300508000e01c4000344140780300030380c9031101c80140e801041c81145c02821070303180b81c01144600c110342c541140f501c1ca4a001c805000400071b221041c1c01c07130244018020300c03002030302c52548107195141407505c55265000030304130b20200d0060107078450700c0018000d1070b2603408956150881e000d00c0c9180103444e40c801515080c1e6404481440041e003055901c15417a030840d8141441c42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 862441321 1250 862440071 862440097
    0xc09010905031b091303080408210c070201110a020f2404080105090d031b030c020c210c0409021c050a0501091505070c120f020a0f08130f0b0d02 64
    0x9503100080303800d026450f108442142d1214100c19482e0514803020754010580c0240e403504984107490040020102a000030080000000c03103018416a4001c0c0c0034040c0c1e04103101c0c05850600c00c181a08035072145004a000c9642080c0642da212804251a10b6560f006800c03054180c1c281400c02241c402011220f03548580030055801300c3d520090003410103080080e000007441c0c104030745090b1506040900c40340030503040c81000d4101104601250a811401c2d05000c43c0c01100144164189141d42c110365810105500c14408a6403059006a08035001801600d208007401410301003a5100c80001039000740b00559040f0240790b10705900034074039001e501a5030b84017603183d548609440d51820b007943c415411007601d000d20a024450150002018200505840129a60803203021180e80050080c890031155001d82103009010020001d5403200140c0d40b485441d140401041e003000074004100380b06060081f820825006081c8182c03203201d01e8103401c258403001601c5c040c5d8483c007481910 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 862442571 1250 862441321 862441337
    0x13140106111501030501060603050603120a0302030c1b060412030b0109050f0d05030d05060901050f18071b03020a05011401030203070e0901021e0d111312020a1a0a0e010c0b0c0901 79
    0x10b40c01c80300810342c0610b120307030000303c6d2036450040010161240035140600c2600111002c40290100108071054150b603818007584035603d0950085881c090345001207100ca6014041404900c00800c80398802c07482440800304400c02c0c2482101141c1c0442c1032a400f2400d1a101405a440c040c80300b560380560040403002604899135600e81141c1019080000664583d070500c1b10500e407030840140900002c0d201e46042d2480c1c040060103031440400035402d240d00503000b08401621900d451034025505c003100991140070341c54025510030918500380d0701c6528003003c3d4039081020b010032604aa80040003403ca140c100301c0c0e100b07055400645180500c0d9801c014049016020409003c070b00c507200440300f510350605590f40e100f501d090601c42041c0320400c0140411844010010000b81c2d031031185001600e01240c4041200c44a03d17403c500030410890680040b0340314000006d1500b000655601100343c2c0c90b600045d0340c00905918002c02d801342440c00901c541c600f4001501c0100414501001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 862443821 1250 862442571 862442593
    0x20c13090804060c21080a02030a0603080f0d0f0510050603100e0712050901200a03110d1d0f0307084608100501080c0c0d0306051314010611 62
    0x19142d01a520100116003180350500038004201c401160241d26071002464040c0d51181c01407008800030150110241d01002081c02c45429034005006550700110302d80d500c524048081130940c1018408006080c10204040486400341c06002c0c0208000014100c6150800341040102e800042908448204000c80007803032244811790320740100070903101d1241c13450001c008002a1003000340107040980c14800c070300000c0304420b45c0b031041001c41d1141151310b644040d901200500321800c4402006100070a0500000d44158030000a64002505d031003260f441c440d801c2e5484181c88a42170380c4d190000e000c00b8001c82d54841c0181015140910318507003c4e17100c040721003009101d0001001c4015000f10a9a030390200411420340d200b081e03400c0100491178003080300c5ca405800c41c040c65040003004404103010b2001c2c101a00c0080e900c20040c0c07080f10b82e05040090003428a4803881d803060459403280c080700d004a120b0140740b16291050410940c1c244101900d5114001c0803280f96032254400c403003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 862445071 1250 862443821 862443833
    0xb07122001060f0906060219080a050c061503010c2c040b0909071401030b0a05040c020a0c12021008061f050f0a0905030c010e010903030305060f0d05100e0d020c1309 73
    0x80c0500b0031030065080082c01c0100c042c0c1105c116410440556100c40000405502c0001c0c003021800e134040c2e00643c2c6d440307108130300316001d00400c48121005c3c1708a105010641200714010601c45038150001c20406c0c4440c0360486084956850200402c00075201040d1040c4102c2503422082e0f0340030300007040f42c100090100f05401d2040f9000c0c00d40d81c12010b400d01c040b0725131100e0001345580910b0244034022089001440640c158482c05214903516000c0101e01802401078014840e0089540d819180d1758416100c1110700c400d030202d224209421300001c85d28024058240100c1d00604051003401c041002e041401e56901c05d46c000b070101c1809112910031415005114442d072a5890a4401d4a0902414901090051485e05020b0101300258103a644142600c0459030035280214076900c50700e020418942d4040724454214007044c00c810140100065003241c0807e01850421084401c0b018841e1031b4282d2410001c0160820704001c0001d107000c0c030070311003006104c560014078042596240 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 862446321 1250 862445071 862445081
    0x603020904030507260d0504060b060a0f0e090c0f0309120a09030b010803070203210c0a0303061d01031127010e0115050301030b0a05090c03070801020d060b07122001 73
    0x1c0300021000280c207002c10541c000044c034010841700c00d00112510050100790b450113107502c0202c20a0b55440050140100c940018046a00103030415588052401004040c000b900007118049160022902a1400c01c45003041c41454201103a0703003004030190f504059940060312094852060901038200083d130303803004154010b100d444450b100c511f513113410300c0c4481c0140e0002d61a44c0041c4000c0025880114540d1500c0c0c1e42d410740b4008840c0346810309100350143c0c0440c1c003041c0c81808840d00406406611440c191a0341072101d075092440641d511011071000d000040c8804200c1c5c20180e09418840d010380c541603070056038011400f00e071003c0c00145800c2684042058008034004100e40750044100c00c0d6503150a1601754070310360440e182e003804240007905800426940e0380000381a040140460400228024243c0d00da2643e25007a060103034000821420007549401400280003003042d003155006540610502403031801d440301580c9170260303501481d540c40b200c0011202c86032428420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 862447571 1250 862446321 862446323
    0xc0209010e09100b18100b03010e04140c13020f07020d2015031605070b091c0e130b040605180a1104140f03030c030a0504080c01020d05030f0a0603020904 68
    0x41d10140c0c603150896a140800018425010030f280495154183c0c40e1200255407614002d031100616071140350100203090040c2d40082e280c2040840040b41e1403d030629003902a5016040191041e5140100103403501d000c10401c40e0b02c0083d4814894078a00207402038001188403264190601c8102d07004114811411201160314480b000e501c04c4e881e04804508440024007030702c02440302c0481c1d2514031014407000c1c10715216116004d41c42110f541c4550221583c072a48100d00e6a25405c0607201d5640d141e004e95040041d84540201c030340801c40c801c8030010240e0100625029030402c9000c41c92000300308a40700d45e90010749500c8003140300c1d15800c441c85204400c0b0782d4400002c1c90010202c0084440400a03442100b10400c410462024081500038480d5000c840d40403103010410002483d600c02c0088030301c618040441c502103134640100c06801151380031400d80f504404500c3c01241c81d074150b0b50b60a400b017681440882c48030714011030a80d5201e4824080003070301940702c1d000105008812a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 862448821 1250 862447571 862447589
    0x100e030d09050a08060103021509150c0d0809120a030b030703060c021f0203040209072712031827020d1b17091e01090c03050c090c03010b03160c020901 67
    0x1c0400c941d003408501100200307050300242515504550004070307441c0025003400a8031401203105500d9590b0001c40c031f4801138000051a58854501003619154940e824080b0701140606000510720301f0701042c034410000311595103d29020580ca010703801000d09040a580602c01c1440200000c0c8a130301c954280808030750000c1205000d083e250007009411300451682050050041c41b0058456001454104590b800e02205248107005000c4544580f040d4a54466041503c00150002d168840696981c001e582e1050204042040c0c030303a0240d00e510645041c80142c0f00b86072401c800401c00c254206507412000b52030041c0c4d027080342e0242d035550b0a40410a441010b08665a107801c10f244103000442ba00700d003440c5d0f107051804581c469000c261080700e144040103401200320800e52080060039405034800071842c2d164200103070764940c800c903528054a29a00401e0f030f1240aa02524101c40c04140001c0c9166100b11540c41a100000380702418040007042001c01640c42903102406450810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 862450071 1250 862448821 862448837
    0x50a1115040c060923010c061103070e0306040507050906060c0723100206041b08070e0615070b0114060d050a1e02070305070204020c070e0405010c0305150906100e030d 74
    0x10402c90b8089085038000410301c810b2080070801c40d51404c013900004600601c960007070503e0a00169818035102c400104944e28003210041400640800b440c014482551082144159001810380c1c07a0000c2c0d401505551091b0b604000a1400107280340d44103202600c140d04050b00d100341e0b14505010ba410280e00c41111a020034408200d8a44a8105410488012045100c102c2000c0d440c1c1c140a00094040741e50704900c8003041c024980182c001301900000c40e008590344112019032410309458041c800d2801b40c019448031200242580c01c6075801800b55011039103804c010521482da4442040d400a40501542ca0702805900c10203120300c4204102282183c64141c0441092204c85044001d20388140f00c800c0100380c1c4501070f10f40b001c0c1d040e680141e8420003000000e10b003641c99400504840040c8081100708601900104034558540e141403103161a214078201d000b49040c0724140d0801c2d01a0001109884c0c4803444d81001d04c01d174100603110b040424042800d2013100406080821661 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 862451321 1250 862450071 862450073
    0x70b100312080f072714040606050c060c030603010f0504050105040209090d120f0906020a0f12090201050a030c0e09330f0d05010e03040f03060c0e0102030307050a111504 75
    0x1c1d40550220103518142e1a1860070450100c59507001800030001c01c42d84640d6000c00c419009900c041c40e082007240b449007aa0740c0d031001e80c1c1110b00704140a0145083c000000303000b034081d00540c0ca1010003140540300c55901c40c200388005400060000ea07040d03480c1c050b0480007100900c00d03d400381c0d005d8800403400b0728060041c8008028060200c0c1000d40c030a0007444801503121907114210240c10001081c4901c80d0100341020b0105040c0203010144005090581c0c1030700111605048480c5407600315015040381d01d034100708c980da0344019001c42d800b040100d001910a40c801c240711200760a0040800c807108000c51703080314080b0740d1a07041000c04c0011207050440d00c1c40d1142002c0242080004034480038000c220030329401c0150b14090041c01884a0401500303410106603043d05100f201c2c0c41d181e8414011282582c54801a02d000b884c0c400e500040c203124400b44051210180c004500d952950130381101d80340d2194400c0d5003004100c0401c1d100320481408a44607042c0301e40064029424a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 862452571 1250 862451321 862451333
    0x31b0519030b07020a050d0c02030a140607081003020a12020d1202280c0b0309031210090e192604080c0a170c090c04151706041103010b0f070b1003 65
    0x80902050f0640d07000c000a0000100c1c002000765604c81c45107400c0045007564030219207007580880c00105072100c400c85010f162100020301a11600140d44c54443d076884034404180f2900843c0406500403d01d1101401900c0c080140c1c9600c0354805403c8030854070090700d4040c038100911500d403006800240d241c40b108000401c80c2500c10018040011070384180ba50f4520100c500c1d44202081345a000c4002804100140706640c4450003410080d00545083c8500250101c0580100c00303600340740511001d0074090005894485002104012000100548800d2103112403095103030300c41c26651080040c00f07903208014100038400200204428410102040404041908034210510220000e6000407100050041d80d04406031034221058488001c6440e8502c11340d00300e887e0341e41c8103010b000b2009074000d80f689520700c082d000c0001e5a856101c20803060764a9042c040480c2801803005005051a090041c0480c860f000070851034a0b51641c0c44808042046580a2030301540b68810024011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 862453821 1250 862452571 862452593
    0x307123609110706093210140a0e0705060f0904140402130b010c060c050c1c120b0a1203090306050610050d1a06030a0c030f0204050a031b051903 64
    0xe8101000c2c4000c070108144030300180641c0001520450312036804009201c54640055200200704d215034008403501c4208140707903141900031344500e1041c9100c0c60384920061081000d400d908081070b034080c4e201c0d0750b60b00020f00100b0b00a10301601a80c0030018442d600c001c01001c042e4400c00b845e40d01d803600c001c20041100e607000c403031000b0390303080c2e00800005a81c2c90980d075119440201c00060302c0310301d0800484405c103606400130f24041c504104009850380280203040000e03819030848203246840d100080c0e01c0700c40038206801040313403143c82003d2004250080365144c580a404c60855030313556441c0710762203400700c0030503404502c15000078001d0100d1401480e0788281c041d01c030800c0707601c482a030044c61032098181030100155680e80e1010981844203081064a000600440d203a0514403a00001400b0701010312000c203290588030100c59040303000790b8045807802055200824955242d1000d000001d08181c043d103418be82c40440c041e500c100c15000012007502c06900d00c0303410344c0740c031040c81d003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 862455071 1250 862453821 862453829
    0x162a0819020d022715131109150d0906020909130c06050c1f05010614030f0708091f1506020c030631060b040f020909190b09040803220503071236 64
    0x7034100b15a1a002d4540b0701e04a0b00648d10540c5c0c084100c41c1101d044c100180030f4080e1211616050050b000f0504c0201d402800008001b2039120096403602c188042c4e80c0d5488a000400e440c24406042052502690240c03205503040010340e035580c4404100307030441301500b1120324421365607100107210ba40d40c030120807541025200412031079800d169802d00000700c402060001044800710010391401018092410b0032a00c00c24401001401c50070000302801e08200307180505c031942e60b00014100d06c0000c90700e40c0c448010b0f001c0c0500c4c1c0c64549203440d00c0000e1010300424070202201030940d210300d5800c6015228010080014180c0c071072000c1205542d90303846180315a038014000c00006030741e60b00403990050725003501001c065540e00e000b0400b0304501c81102e0341c8010140300300414081110001c0d44501501070385022400d40385102c0c014000c086140103403c80e44140140000121000d0080301c011000d070604241d02e8028200d00c103503034201c1c0c81910501c00c048e8101000116003503c0c41c200a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 862456321 1250 862455071 862455109
    0x111c0c0215011e050904080f032508010e090a0b040609022e021c1e03150608150409121d12030d05090c06162a0819020d022715 56
    0x40c185a00d40c1f19080c0500d000140740d01d00000301161806840c0c01d660035207200e00208209a48644030b401070316601e0240304440a03041d111000807507031900410040e90305035210b02148099291038607440010003811078101c1e00700e41c100840760310000d0194080324030141403505042c0c0d0041c606400a0801c0080c1d81012481941070007100c5e071003904000c13071400d03d010140d208008480742c0e501c103c002d40104604001d0742c100c0c2c010041840c551003010f192244450707202c07681090940c4401d000c01c48a140001901445140304044100c03845011003000303c030000901e2942550340c45d8002001d01c0d110140469050380001882003556032180166a40002d00c0c901070010b000d0042c01048091098101288480d009050008101b1161110030b03412280e818004004c0e85610311354410018a4500450300f9a20480b103140070490203404d2080351446d4060804140040e00c2c0d4207001e010001c280100e20300152400c1c9a044e00d401c00300e202c5114001e4050401003034007062040c0500c1500c880010001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 862457571 1250 862456321 862456339
    0x90c06070f020105030901140112110a050105030c130b0318010f0e0c0111030409050901060806092a120d050a1805100810170d03111c0c0215011e05 65
    0x11400e100020307101e0301c2e020700b0a10350317070340d50a480c0a006042045407507580243e01c80010072188003c0443c3d0070b08506c105822429168081b0800040320300b107100d850b0004108100050300441010050240080e1010403000c0198841c00351360100e400c02c071001740003030324180b648444201e42402420b4003001d01940c10800c0f04020b140d00b42d00c9810341d102f920b042c084509201d00401c04100111401420110b60030021800d1014405018115901c100c0c0468410107001c00d240c0c0c907020802010003400e00320281100d441c0310401322902942541215800b01030480b0341c82a070310040c07000b0031940303810b90348265541d03c000001804030000d203020507904880780c450034421502d40080c0b2032041417103400c1114281c1c0d50b4100c1c0c2029020503420100d0007004520080c0e05080000642c42034130407103510180000c10030340035030310303214058865002103101d140580c084050401d81c0c07002101c0c40d410b20686924140c08d41900b1003041c001c2e44100019100e50040b0080c4881c074900c1350016090803114070783e03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 862458821 1250 862457571 862457573
    0xb040b0f030c04020a0903050109110102061f030219080a0b01030b180a020f0d170406030c0302030903180a09020c0604051c02100c05040f061d190b070c0518090c0607 73
    0x250b80c2c2c01c0140341078021a40054160381440c01081408000e41d400030013070041c08003d261550752800075410711800747c8030b1800850b02c0724214000103d000005801c4440b181482c40d02001082c003c0618404100d09104801003003002003440317403d025501413000c110f610352451034840013944e001401c0420110001170b400e090320303102090048000b03030120f81c47c2110b40f13443c0e8002200e15805c1d000c02441420101201c22140030000050002c03101c16440812115004440030f406030b10044680c00840c3c2c0040180c00d500300c4e581c010070345101c40c0290590844079200d04407042260300c010413507075855002d40104000c102d0200608440d05511380500711182e0800e40780655a000580306c00d800e000d4445201818581c4208295070080400c1840c02d942d4680d44c46000c0e1070b11110462004c0e07441008400d0003000d081012007108546029449440314918101c070000321500103040480d1107011301680000c080d036609088000000c840d00b80901d55060442d402c5143c00e0840034658000c1d041400014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 862460071 1250 862458821 862458823
    0x30e01081e09030d05130620090111010b06031f080307170703140708070308060a05090106050906041802031e0417030903160b07110102030f010605090307030c090b040b0f03 76
    0x6120446240907152040c845045004484c14035902074600000c0210307110302c030508112628052101008104540203070b01541e520344a8807001c09000400c80321007154482c0c1e440c031040140520000172940890000100940e0068078042c1c06101a003c809102c161620f25000060940500451400b038079039548103204840c100e803510030481c000c80c851082c9400342c0242c00c04c1703a0003807161030f5a440a5151a40190300205012340008a09000041040c00d00343c2c010340540350010700070844d40c3e103010004c8030076030300c20107035513420000c03d000c0020190501e44d00300f5145a00c0795005601c0740380401703105a5041c24011260aa10000d4003800082090600d00440b42c810203030f24203513681d0350081850715610425076010300d403503001d182da4400e03c0034a42b141c0d8060404ca90310200200c000c128842e003030703002c10340381e4599880100d0010032046008100800302c03010003400b0345a54a50b2501e6104040b00164440c90b411500c1e00515040780c50035100d0480c0100044800042d0440c011002ca = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 862461321 1250 862460071 862460101
    0xe070e0112030207030507060c0c171f0e15010e0c280e21010608011a120a0b041124090f0103020c01231e0c0304020409080a0804030e0108 61
    0x2491881d0764406074014540309202800295411408031750718555520310040050380c0043c0309440000c20818041036100901103a107200c2c1c02c203c001018940300c1810a0003c1c000c030000c1021040342d076441d109908090070710009c1036481da0201305290940c50800300c0580e25000030040900d41200b04540e841da60a90450441c2c0ca90303a210f100c02942014003000c1e2178541702e9203103003640300091100c0928082412061500508034200081c81181e41d500800c0303003030300c00101c04101d0303c00385ca600c14522410210042d4000800840484007440020380b105101240140e44c01d0301c030754488480902082c02c2410b0050903030000800300783c8403401044070074007180c050031203440d100b0140f5290100d42607109405680e07080c01c00c1f00c0200840e110f06940880304003850314101c209030003100f00141c035111400440c00c41e80d0345903e21402055480c1c1a0380e0307032681d20042040342c0c0680c0c2d83d002800414024405031002c035016468a211a0600781000386c100c006c2008158108203502e800c010f6840d00c1103040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 862462571 1250 862461321 862461329
    0xc0703030509010b060712020d0905010c080903030d020a02060106091e0b0a111006030506060d0506071209080a09180507021f090213151502060402060a0309050d0504090e070e01 78
    0x2100c0e1600700d00c1c58090408001e030b40745e1040011984905100c54078401c0070030010a80c00f151818900054103440c0c0603414464580072a5401d1001c40c08550100003e0800380e00042c292458108824048803c0b60040300c0c1600041c1e00150040c0400d035042a528000b4069401841a03001c42c90149500228454000e04821020104650f20454024044018404e590000740d44002c0c1c62040d43e1801040d8a1009803210312601000c10094100340c205c1c1c920b565001409009650707500f040a9031307803540441c4c10300c003420340c0c40c69020046040c040140071415805d5841c10703400303440c000d407002c0401003480d200c090985c070f41400d00042d5a000964500c0301600c240702c0b84184403521120000508800c0e00180d0404002291096540d036190712098059110181060403141c85400501304500c2c505e0618025a02c2180410054501100078085104880c6800b041c03d4a49a03111418140c2d10910300700892004101441512501c0c06100003064a0000074090a03180201240110b54180f00d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 862463821 1250 862462571 862462577
    0xe060901020301081b040e0f1c030911090c121612020903070e0711070f05040501061b080904110d050402131a19031e152306060903010906051e0c0703 66
    0x6008901611560030046100307030076509580c08c9104846902c4c0e03c441c89022458032101c41030000c1c03000c0a00a208110885401c500f0311040000e111040c402c100c1d0010300040740c400d90074058280b4003003c603607034144640940c098404000c0c200003005080161182444454680144140340030b80c1c0b000100501103a40c11000a5400d448000e01a14a041c01d0040400300340610760f0003140c0380012035131070011581c060750204a26a61440c084076038004520542005081d06a652404680b000c1c0103032240380e0008000042c001c1440003000c0b2a1750225065036942526041040190303d4231b00c040014a80d007100c02807103031040b86003e4441448420f01c8440c820b03038208042004040302c0f01a00c0b0007541e400301010340c028001c580b406017a0601d41300104c07005c611044d0041c4140c10180520410329201484030b616810390050026403000c0000d1145403c01c105011485c240d80e024051001a1400f480300081c590801513803451009610300d0300d00155400700802d0002c24201d0804079840c49030185 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 862465071 1250 862463821 862463863
    0xe0c07020d14030c07031101021f020310050a06112a0105031f1d06010504060e0f03210d05011202101b0b0403050910020c09010b0903100504060e06090102030108 71
    0x1160031903020060b4500020a0320012965841d0740f1000200c038410f89000d165503035190b81c030f00401280e84071211029247d40300911311180f070110038035801842c1c01c4030a2191403c0b000791500c010aa00741c403681e00040028000700600c8126400a010f030040030103880206104194021401c0c40e90f003d02c1300545410080b00000298550341c007008c400020018910501500c0c40d071310206403000c5082c5e600410f0500811202007181980503604880c1100c0d00e94460241c0b00c071610f410441c00c0e500f282012505070003003c0014103801c805c0000142c43c0c090b071b01a141c2d180e10005440c00200c5005030010900042009562070160b580e4084000d41ea80a920b00f14400d800c40400c031039294114086c0040100c006002807108140c0c010020b800d1780642070324150400d80c0140c808036034403c0d02001664128595200501c82c3d1507014004028149000d0f045404e08407098800c4811034070708540c242e400707694421060315040024400c0c95000442c17540290306650601e010710351200f60141c00b040d11a8811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 862466321 1250 862465071 862465073
    0x121b06090a0b07051e0a0209190905010e1e0c0402090d0f0f140d090e0702032205030705060a080705030402130c0e1906021207030219110a0e0c07020d 66
    0x5800c48440050240110710015a564400d030403540080404035494056a0344d0400c0d440900c4490911010603540280a41c030700c9502032100110000c0c2c048040811010340e10611202540582c6014030b00c11400041c0e00070410300080d0030040c070007141031204005207060759a4410700180c0d40c00307140c4003118011380d12030041e80041d5244608140042071800c100f5110424404200008901c940c02075080351503158142032000d45a1002441407804a01c408405002110b4a40011a4130003510b00440b460102080202e020101c044031035516010f041141c2400541000d0200380d00074001525054108040e10070050201180100850100b08007c40080c00355960204600354201d06220208101021490003e0000e0f4680100e140180c11500780d050b454440490200e04a4601341e0250040383d00310103665144d54001b107015000c5202c0e408100644040300d0380700c0080144076040c0c032840511240305100c4018815401601c01000300010801d031290414101d59690380c0c110380b5000c0e00852 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 862467571 1250 862466321 862466329
    0x603010902220308070303110909040b0c13090515121f1112100803030c0a0806180c03010f080607090603020a020f0d030f291c12031406121b 62
    0x720060042515440440042840f04c800b0081c9a9280a03035418408282d04c0c1c243c0d41d00f94821240c0b20f540001c0350000090100b6082c001440c0c0107075449401c2d40c40c1020340341c41c04443c1d0255810040c100e07642c900c103005074140644111284041c0584454400d107000c1d220303080e2590243c0c810503207100b41d04030103403205c840240d100f88401a10320080a869082c1144200c3c039441045501d024043c021244c00306041c030000007a207101e02c50480005282094654080f180003402811064100e510791546403400c508115480340f1810a040009880b985031400722628106d481d4440711780d5030800400d100d04150f001710030009550075424050ba46000300542203142109030065602980070b0002c5e10080b03186e058000940c01020032000f0f2003008801e490a41c5280c40c415081200038840485040c442d05010184114000b415040d0903810300035503c0e549007414154410f4000260345041c109a910a010300310741e0803040a48500110805410681d0340d00c4a0080c503a15101c0c0750000c21a030300f65030b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 862468821 1250 862467571 862467607
    0x60b190509090604023709020d05090a020f060703110102030103050a031409010e0907020a050d0203030619050f09100b070b060109120b07140405060c010204080105090a150903051902160803090603010902 89
    0x46c07812003025030781c00c4100000c0d0094002d03200134038200008a0400c000c00500f044640750000e054001d071740c060404102d01540820400c4050050410a2503584102803001e1802036001c1e0018100c481494600184042d440c4480190f64440905c40c0d000c0e10b0b640a2500f408000b401d0301ca99002ea12801410303032030400c4050005200d845803a2441e5035866001c8051401000306890300c1d40441241d00c81c801c2817440354000c80b500001286a43c0c06940741c103100e1150401d0003e0100100d06440342c40c5292540e212540545020b6003450601040b964031107601c50082800740100c00b0840e18603a6415141240a840301c4104001034518440842c40130048500504c401407106940c1c0b88011001c85c00f03508148585c01080d46800c000600011000ca0642d04565011a020041070241ca0707014004100a0800f50708214050055446c40c1501054850800d04c0c84d400400c50a1440205000d180017a5080704240350424060810651503000559065595031b1300003689480e0030101081c2403103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 862470071 1250 862468821 862468909
    0x41a03030c0109030e1002100209120d2a02060706050a0f06031505070302090d15062d080f0a060b03120a1119030c020409060b19050909060402 63
    0x101000070000c10a031815071043c03062510030789800c03101020f82c81c04c12070603007a02c01070000541c01c1911440d414000903801441120b000601c0502910203006507645040800722601c0302060720008a1003200b038800c9109a0000c1015040304032010707080e8085210f40c06034090003000c498883c00460b49805c055000740101c048030132010001345940b81000820958510003082070b4030301c0c00c40441c10882c428000c035a41e50310003410b2000803920726a14003009500c40051800d000b03546800202c1c40110700e01a00c45807803442c51b100c0601c06ea6001c455a411070a40e401219940c2c04521070094041c8049204180117802004c002188040b0001207428144550a50710a01e5000940c089040d904800e0114503082510201d452121064064682011240c0c1e4040c000c140342808850044c82c3c10f4100d0190b107445604049003500201c80891b000303001c503124425105c80780550920103400d29403800d542c8000c03ca07004010f00e08041d008111081c6180031200110010b91407109070801c20500000410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 862471321 1250 862470071 862470073
    0xf0c04031119090e0703030305060406120b0403091a0903010c0906200a08031806070c15050a0b0d03030b01030b1e0904022205180c010210020a0c020d0f02030c1905041a03 75
    0x10f01c113840e550340c0b600c0340ca000450200c0e01e00320105506040612666041e81c10101281030b240e14162038002d20000010000c038100714000310041409a038402c080b052444030460075540b64a1200e003018256034540050b00d040200858040010903445144410951001601c0d52a6034901d243e0031418002100c5c000340c040c036030010a220000e8a62000001d1407090030003900c00644071103074111510b03141c1c001d01900d88010060b0040d02c40404d94800358101e812000c001503411200e0001c180790301258001a008642d0b44d80700d0141e2560527001d4035120b40c604440d1403910a9040c10400000000c1c1a06180103400e5500090115210024000c050b447c03021104550200d6001e07800340036103000c8815620f2049800e502ca800307c0c10000303001e01e000c00140c001d4401c00c000303c003620000307400c4000742341c04005a0619442c00744e154422000080ca004001480c00103c0d603006152500c1c0c030b0204030b41c4c06191584049204180c2941000c000d4542c00c86021405014000d44050b0030384200170690380c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 862472571 1250 862471321 862471331
    0x915180b010815010b0406090501050d2a080921070804050a091b030203010303210b120307140309030a062d0b040b03030306060901031d070b030f0c0403111909 70
    0x10000d0a0511140c021007410700f26038a40000030303010b00892081c440452603a8105000641c0914041c0c020782000c0100042c040101d5043c41100c240049148881c10704450014202c0d10b51140d80c1d075a000e4020030050842c1d9035002c069110129560309086034400e400302d548402c00c40c5101c1110010403009051104a54545040340010302c01440e100d00e404100003001410303030b0300030f00aa9040743c0e090348405124160504131061000c00b9584141840d6580cbd00030080140d031245100c040307541c0310030003d60701c07046285000c40c00c10f0600c0f100c107092a48148a4501c031642d00040c000720040e0b1000f070124440480001007001182c2440b12100c444602680c2001c01004550007003c80034012034040c01075287c04030902d40c0700e10081d140141c02000800c021889540203030005000c4114402d002180c103086140d443c1c0c1418480e0b04644a101070020900c400102d11034402a005099000c040e4981440c0da0f032010814095050305a01401e440c0c00741680208068030380000074080100d040c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 862473821 1250 862472571 862472579
    0x33b100f050c0a05161e1404021810021b090f040f110a060302120a0908030c07020d060203040b090f070e1501021903030b01090909170f0714011e0915180b01 69
    0x4440e240c1d4020392121003454070b080c041031a01c40309600111f81c148007044072107044580c28407010350f00c10346040c0c0c180e2481c3c1da42d0320380303989800034000d07594001341e406002e04401c10340414401840c064542846030f00b9030f5040c0b202640c01085900c3c0c100d40e2211800840448600c0c0070f07411460349100e031075440344010100254031234048d00244041c0c46c0320041003000c1e41d030f40c2c40c02a0854048100152803d00700348001130b50850003400420010b8001444008555190380d10600ed81e4021582140c00065400a1102d1000300b0017021000404130380c00343c00e01909182c0c10354003100000b000f8140b01086148019010b07402400ba0480d03440c03042074454100710480c2400b4016150500c403003400960f44d42d4000406500510904102c1c41e4131040781802407058180d103007000d4010100c14040003004012000010b84821449044600040b00129140030410f000e0b600c0360400c0f00c804030945040c440c05000280c12040c450800212041000942507117040c075019000c1100740004100d0044540041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 862475071 1250 862473821 862473853
    0x6070f170c120a020a090302010f02030405031b09090601030f030807140a20010216080711190602120901050327070f090b19090207033b100f050c0a05 66
    0x102141d00202c2c0b061030382c41c1d600300c080807071003920304020001d0001c12080c00190301c00c1080b04001a40c1e8411281071035207600000f8203014440c080c0020202d03108800140d0703401c180340c010b5448400e2074003810300c0d0740c51901c035094100140000202000310210010f5005406503040e007090300c15201641c6d48418404c100039000301040712414100042c856444015070030140203e0381c0c0659940f8030a1629002591000f02c0b40d0000902102d9100c600c1820640d0341c0c5819080707800031100d03151034481291a003032019042c000f10a0814005070000c000307094481e40c109044039000b40b8401b0303544440200d4076054200c4001d03c14080c2035240940000002c010481c500000c0544a94505c00c0181c0c080b034004001c03030741031070310541300a11054801c100800020f5a018003171040c081d082c200041402060004c900d1412004849141c0c0e4445144200344250b94118014602c01030314054a03800d203540c000760a80d403403214040300b000f10005c0c596a0094052161420140c3e101080703d04441c400c3c4091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 862476321 1250 862475071 862475077
    0xa060915050306270f01050916031e090309151805190305010c051e0909240307090501031a250201110a020c011103030103200402090a0b1c0e06070f170c 67
    0x8002114007400049448c2c50b0a5298038011080d0b040800003221001d0700903070160107038007400c403000d220707080c614454a00d450081d2750b0720511950b01c0610b01d42c28040b019a04090401c2e54070200300c8280c00d500b0310005c50b490100240d8404480d25140015884001c02c9128844d0300010b0980d42440c009404413504400501040030403075010301140040000580c4450060040d038560141d0580c000c5580155249107080d1019101c00c0c3c1c2030071480d214004a40340c41c0721a0b00940c1260f555000402c10300614840e200b24928007481ca5000358100380d0900410101403100090b030400441c034101e05000d00075486101071004d01403d00b51901c8032100b0203500e400c039240d072242c00300784c6001441120100100840c1d0603213074420f000c0101c44401c44040c61211700610000e40d0856400c000310029607a510000c4c070300401e81c00880b55a10822a104c003120740c4001401441400d0030b00c01d90f00f81088001c03800d1503101203103251548001490388800c0340c801c0c1100c019996020200b03000d01035540344403002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 862477571 1250 862476321 862476331
    0xc0f01060e09010c020c0d0b04140d050d06240e01020c04060806180a0f0f0206121005130c0801050f0d12020d03052d09010e0f0601050a06091505030627 67
    0x130451920402c6003681c541c5425000d05074000f00454004000a0b0080f9a450f0003d0150181180076600e00242d03a01d001111600711005c941c0204090811071a2806a58003a1010f0b601c511125003607040340c1650072500500090078020071b603000420302d900c04c00c512082c00000030400d0102c03a40d19110710381c54003029103600100c400b07256020740241000241c0d121965034807514031401c2115603150181c543c0c480304000c0f48c0c4100204000c107240c1d00500001e500803614409201c400038540b90800c003e42e072981a22300040c0341004615030b1071075040100325044400a9407082c0d5094501c81c0003a51f101ca10082c000c102c0500981598442940022402850039036924100100e4491a0f00d01d900c4070080c0d031000c0c01084051909184518901d400140c0000410300049003060102c09090304060441c40300e2030480c0e00001c01003100380b4024400000529040c1407412a0508041d40c012002182552080c00c0c4203002010070001c1c2c990303900c5420991014040b41e8601e1900381c0646a0074801629 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 862478821 1250 862477571 862477573
    0x10b044b0221010506041404140a051608060a0e090c1002030703020d05070f0609030c06020c011e0203070926060406050609061806120304080a1202060a020a050f0c0f01060e09 77
    0x81210100036502e15041c0e8000600185c1410700d82800440d40700c83c0c0c00c1440350000d485081d00b44503070100101c050b006444919000c500c92030400b94989100750b00c0b811003010800b0304400d0140c0c5860b001000070035211001a00c0441380d941c9000e8901d00030300c42e0001908141d00144482c10948c1c0840070b001564842e5090b20558000d030300c0c04940b14000d01c840506042101403017400050030981c0300e0f2801612070f060a950b0100c0c507466410407a0402900c214081e5100c1546d0300904894640e09040811601401c50940c00c0c540c00080c00010640075801501256020b41c41e104882c401000340c51403403200440c2c00610301071800c0809003c084d07a20500540c0400c0200c0c0c81454004040f80010f056140d0501141d91241e00704000c40002072902e5072240405c000100c1d403407401b4002c4007100b40c0205c3d07070040b031003910f5032000f80703002c00003030582501d503205120038a2661381c4407048032004d525045005482d41c0c28489118104a032011113501c01d52319000000a200c0d500042c1c06100701c1142c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 862480071 1250 862478821 862478857
    0x12030d02070b0901150603020702030c0909010204080c04180f021f0302191e1b170315010206040b0613060e3103080f040501061203050c010b044b02 65
    0x3040f2142a40c07018200802d145011050910003140b10342e01034061680010210b8042c200d801c0b010502c0400c058400d0f50f11650000740c103001e4407a0401a100c60f144051740e01700504d40c008801001d901d03e00c480001c20324031010b801c0b9000c3d565180350144028110411150544580c144060005c0d4800d00c0100e500d074840880b031400341400740300540d400141d480901e015400100d442240c000d00000b00c80d6500c2c448040d80200440c60068a04000318101e94565a490038801d421908848941004a045600550070000020001e4100304c1d00201f06658a102009964607006d0244c1200c0c0c202c0c02500306003100f00101c00c40c140200c1c0d5101c0c4011205c41036450082650118030508108000c0e0100b0013203004103c18180c000a1554400c3c000c1000285c142e07201c1d0000e80320401113600036000520081180351171800c082c490140c275079030101c904100000c1f522a42c81000001080000c608003800007801c400f03081002500300c04603003034031120f02007803440114400c02500145140144c2c1c801d04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 862481321 1250 862480071 862480081
    0x8190605060f0d061512030504031b050a0b070302011d1f0c05040513110c06010303030510030b0406090c0317040812090f061309090b090d0207060f03020912030d02070b 74
    0x50b08884820340400b0300180410001501c1d184080c10142c01c060700d003d1072480000641070000e080c80d9a030580300390744084d5070b685035017000c2800890702800d0301200c42242500300304642d0b8110a1030704035240305070030326156003e46c14244e0045c9080ea0b544c039a1012a5446042400c401040c03114000d1050000e402940300395021050480c0c0c0f0031084c40c2c002c2002040244018504a0104450301500c1800460110b541000c0c50282ea0006518074506a02030390040c400c140e014042c6543c04807010460301000d0f42307181c544101104020344003806c00d0f80c1d10010303c400d11401c4451180510b030040d40845019542c0c5e0106000c6a10512500026008181ca524075103240182200c0c02600014080300c000d02c0c0d004c0c100b00187c0e000c0003c0c3e1034a0200800001030003503450086554213401740c500c4c80700340d14094190742d040041a89074801150454081804107a8001000300312440c541d2500585800004012480300119910502c0c0742c1d1001050007201c42c09650010189d0500c550520000340e10340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 862482571 1250 862481321 862481329
    0x5010c020a02060d090510020403081b0f0c060d0209090f01170303010e04030f0c05011b030b120a03140412080a030b09071425050705010938040819060506 68
    0x8010000c3d44081c00700088506507075907800804030f01d4020350550741c0860260301c601342207a105500480ea0300034080f400c1ea20740718101c1003c1c45c00d440d501c3c0240c0128101048100e440701c0d42144100d1049e070b000b190407803a0300104c1d41502c04030b14015000c00340d281440c0200c1c0c13034401c5c4244601075090301d41401026541d8400700540e4102d40ca100710045045d01c80303940a581e86072401030143c2c20460707424000c1380032039400d014042c221681300d40c00c1901101011001402d58a1810100b03001c2c2003071b06c0c2e2a0801e01e2000907610007064141c5031a12507194a45680700c000d01c1503070721803c8100f41c42d001c40c030244440300c0002d0500100c161000c02084610760b0030701011440440300300c00815001200d9207601520f803001440500e00307039038004401c0c603100c2c84e02d0304a102c1c28000c2a9020b034880c43c014007582d6003010020014010301600468480a26968003020700d0200b000e603031680300301080d0403404109000940b009028040c0c16074880c4028100b921203403c94414040d2140b80c20000481d103039040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 862483821 1250 862482571 862482583
    0x106050c1c05130f030c0e0c030a050403090b0703020102030f1524090909030d0e070503031b0715050715050403170403141c0b0301020a02341205010c02 67
    0x4034202600d07401448600c140d250000705004102400410031481c00b02c1c540f0840b814000e094160000c0076000d0450604100151050704a41d40d0407000034140300c0c0300d40100041d2030303110a0f943d43c0030038503a80c1c1d1303e8100c0f03140115601988011801160302810941c041d005548034140b5940a403400381d540340013941780840403540c00e681105a011010400c07000341c40c0008024164210910716100702d10300400c1c0d480c00121280400380d040400e550030314010f00d01840030440980700040c00756a080c80b00003030f00c83c810040ba030120000b981800c0e0702c5445041c000c0300d004113582e001181c142a800400505250b210002c101e6101c40207021951310070220f889160f000f1500741e0384104041c1d91010705503640c050040c1080e03007442108100004902c40c03403002020402050103058514040b46c0b07000c4000c0d00c20000e0450311136401445560320380c0741c2c0040d0365148060045162441d42d034011408074030341c1007140301e80a05801e001001084042100c890184084d10440c0200710003034201c0c9089132120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 862485071 1250 862483821 862483837
    0x106210218011d0312030402120c0f13111602010f0c11151c020903071211090c04092a081b090f03010f0e0d090612020d1b020f0105010605 61
    0xc0e210354440d04581d442641480c03c0c044644482c010610142c20020380391440031341c07009204220000c100804c60410f1000300c044210030000511100300750f07400003a40707143d541090711b004064003080400c10b8241900000701c401000d2001e503a888a01e800c41d41d440440c02003060380441c18409459101a201324808103005070040701c0c60200d00301d0300f8104401c503d891500c2c1c0b200c071902400030040f0700d48a200c2c040510030070700b10010b0b079600300c0400389402d12915610503010415690003c90110384441c02082d5812400c40750801d40d640e54210080240c01540c1002e41d0f01032510300e4400c042024007058849408001d8136040509546000890b00030004907821216940188003202e0030003207500160010300c1d0018902e0300071200c8580130908503100c0040c00c460f1030740c03601600d030b240c44400c0c07000411900b010701c0d004c0c81d19810300e0006008202c91121195009600040781c2404000581c0f09511813449019017100201e82c01038025607030410741d01c0aa406520307081c00041d40d6402001251244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 862486321 1250 862485071 862485097
    0x303090b130639020f062701020a17030601080f01080d0c0312150306060801060b0304120915080a0e031813061a0c0609011107121701062102 62
    0x3030821104880034910012031030120500c0c00c141800311540741060607450740c078800c0c034120f00e0140d60041001d121903480d03046000351410842050003103061485944c030f80c04402ca141022800c4440102e103000c01d81200500015449a410443c42000200131409110243d0300c2260b2611204c0d103120303007c4020320074041568090000841e01c80e014018500b500350003402c010540d6a0720a000f00c00b5038148031511003144001510520800c80c0304c3c81204041c00d81c03000200595414408910f1a034480504090701504d0700401003d0118400d226883c0034140d60078507441d400f02a1040602075100940d00c1090b154101100d45005030000004c2d030303020401c05504030207100313050018802c00b14140d40c1001c103490385904000c540c403282071103410749a09130140b0342c5503070b12603c0003454200980600918902e9042c41c80b040150614141941d41c4690440c86950394000c6101c0c040d500048080d580eaa10111140000540d181e0014078503910354040004e000052414101154124440d404c804844 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 862487571 1250 862486321 862486357
    0x10c03080901090b27010b0307051201020409140f06040504081e0d180c0b03010323190302100c0908070e090a050a12030b0d0209041e0b0a05010303090b 67
    0x2080c40380c809540c100c0c425500004525110b61030711003009500711841800034407194060703d00b01841c00202d0382e41254050003084055410000251034030b825104182c03041060400d04019880700b94120740080c16055020004620820352404090004407122201103284000052803400c00b07020309803090b0ba000741c180780743c0810144a941c40d400c18000810840e038050000041c0b035481c03845020169454030107600030000e414074080f10301d202250000200e500307081c0010400200c0d20214952001ca000326206503140c0745008441c80c101c0c2ca00d203130080b5003400e0300c1244140341c0c010030b08001d403068000c400e020307500007424151080301c0300380716a00c0303a03a2165108100300617000d50010703000050780341a1211070754079440d524a8000c406605484030403d45820102d010f425104034626001c0c141c4807504e10407141c3d000142c0c0e90030020405480d0458040c01265403400d0310000300c4105911100303c0ba210704000040704000e1a003400200c0204400c0703880451100741e010103841d07143d2840800041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 862488821 1250 862487571 862487573
    0xb010807050310120b040507060f02190215070b0118020702060f0702011107080105070219030f0809100e03070b0c0f04120203120c0f0c0415050405060f040c05030103060b0f010c 78
    0x74182c0c0001d2104040c081c981e5404a00c02440b815a040803d029550601050a1901b0401d050003c02c0d84030700c0500030300403406942e254000c26190002805061a0b901641490010648111407025480b40c1741c000010850100714400c1c0005045c3d0b58241c0400f20724580c1c03001000228490240302a61004e4184080c15106000a00400341c00d0710600d07202c80d82d02d03044200e0b01c0c0740c41820341002c00300303945074400c0040702541000004400817500c211581c04001580f00580030903105000c02040202107070000d50150000c1095031140c1c2080c0400700440c0312500340c09500d90308039200803116404124049940f907003814040d101e0700f500507030b100c0d031815240a43e424550804480102c0e018040c0140d03501c1c808080030094960409504094a010b80740c2940c05410101e0991015108502c0c1540082c0e04401011084059910554001605855610010300d020f6803103291950f0050524014101d107030b51000165040f81e05c581000c0c004441e0410030082c166070f091075030070b0000310005c640030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 862490071 1250 862488821 862488827
    0x3110f04050415030636020913171903060b04050127230f01022e020c030a050c060709080a030818060907080f1f0207020102071203120f0b010807 64
    0x83d01e80314034643e111007950759603134400548900e015480310413400001528000c040c089903000c405002e6008000f0503aa443c0c3c006080c0c550050040c1c40302040c0c0c04484030800125441408099900144941d181d502c1c0704000e03103100300d80040c01000641850f000164100d104000d840a41d00140c46000008000420f905c5000b0079400303448103144120400001e008500486000c000c44040300440600d07001801070040c03614803640030904550220000d900e15100d03400c11070441061840303034200d041c01c3c1c914441c400ba00407100c0110941c000020180c0306d50b5008001801080d00d0141540c910351341d100f10a0765034105520901496130000c042c010002841400c0300d40d401a0500c1000b20f408800611440ca013543c1110315603510342c0200e4082c40540d07000c10214403e84070040042a080d500601501c0070440c0c01241070041a0300856214211781c0280503103400341064440007034010361581002444a0104d481410a162900c1c6c40082c2e100500c0c0503c00241f00c040e190050035482d40350040b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 862491321 1250 862490071 862490081
    0x3010603021c1401090b030c09070e03071a070c0501050a0906082e2625030b091005131e061b0926060708040c030c120303110f040504 59
    0x107102da18080a003641544400c030f00ca03080c040b0050402043c81513060002e10011a01142c1d42c1e14842d03401031a01072085c0c0d50303040150b0b500411902c0c0c2240300f2903112012915020040c0c100c1e071448444080841c2a01500784042d0000c9402400703c0620079a0b100c005480c4ae100391800700c000074031004000e1100e9401041d0709500544554103e10129010b4428941d0181c01100b0301c6c01003403011a4100050852178096180d030703a0440070f82c012301603001d11046980301c0e008040506210f1031001c0550780c00c0d02681d004401550044107144461030000c0b01191507000300300032140032500d080041424071180ba000d003070003d07500c0003072414042000c8030340c0341781030110101c00c0380c5103130702c40455811101024100040003c102d840e20410641000c01408140c950760954524140c14044030308100c0300001600340d000302c4030341001070310b80c1c0703c40c00c01a148009580028014210a040000f00088001156270495002e55400c0141203000921944584206c0c0344550aa600c02d010a200600d801e03409 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 862492571 1250 862491321 862491337
    0x21305060a121121072c0a0207050d021e1207030302031504020417060f06061e09100905091f0621090803011805040314031816090e06010b0301060302 66
    0x3804083c1003901c0b0010b1800c0b07400c0f55555024495098510304526020003500014241d04281c6e50303004040c00c0c090101c0c0a13024802c456410815102203142c3c0f0600f030303040307a002a810901f070b20410030354128060340d40d5000c485050740910100c49080e004c034001050400c00100e43c262410f14108054038110040d4102404140400d00004040d43c119603075880280001d003502c9074115104907041c0071726800d140740280602c14100c4d140702040700d541e450004407540b10b0000000d9420820008081c617402c2d010380c143c51500018541001e02c03000d50425128011914211503418280d52810b03a80607070354028903086582a012500e00344080c1d0300504d4140c1000c4500c401d20b1040103500300c100d1058411400c03054608050020042c441048020301503080182030070414009410b150b03500400443d0541181c82c0c60a00100104580c02a4402c480030113460510480d14030126000b2170a06d0200d180c81110125898000c01c80710510000ca0854101c400229000f400c617072800005074043d60200807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 862493821 1250 862492571 862492583
    0x1e01050f012f0609010b0607020616080717040f2c091501030c140a180b0604080a0b0a051005030601031104060803030a090c0909080313150f0207021305060a12 70
    0x60b00185180140d01e04036200b01d00041c40d02e0304046000a00f15542d00910340c2c012a0b081140b800580c5865049400181c201c40c03601d4410f4046040014503801000e000412048402c0c00e1216541a01000b50055070450305c0b040d070041d5564500310b010100800e040d10b00340f81d0401c6810b4031034001c41d085141d02200c1c080950b05602d035443e84403012103000360808c450418032044d0601c02d080c08405941d00030041600d01600e0641400d5042400c0c41180c49044042500c40380c04100b03d468490548004110003005c855010485140030800960104c842407003852415000991060f040c01100007120380240103401d40d44d0840d20703154100d5007070034900c41d00a5100c510010300030004000075803207045a0038002414030380c10b207441400d000742540100c0e140d40c240000d82010903d041d08580e0481c005201d0401c1c081050718013100c0b1103c3c0b07409802450740c0b60142c0b2501d2406c0d87d4000b414440d208550700003a0020145240e41210019640680c02c250702d00c40c14007034441c1c03030441120120b010318 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 862495071 1250 862493821 862493867
    0xb0303220e071205072001050a050c0c06040809030316051b01081e090c09010e0f090a0b0c0c150a0c180f060f02070302031623060901030f0b04020703081e01050f01 72
    0x1454420484003102e001b4250380c1c2d03640301007040100d00c1c0d1140640009080829600d014452580d082e03503820080c2016217440c400191030103055908008445c5000070112100c10095003d05040381c0710301d403000b84200001030404810034550310032640b181c82445c684619060b00d16041a091460020013892800c81d4801c400c0400350655601007007500800300109854001c1c505501400610f0b030300640200425804103840300001100d1000a60384035456041c004d4960000c43c000c03e00c5c02800c0c1002c01200d4140c041402400842600003040340d1025844d02c142005400740c46200c1240113104168140307980ea41e05200b03407445521200c151220a10446503041d40343d4000a0521803940345d000814141d004040000c0d41c502180111405160b5600c2d100000400303012942c94822440654105a941d40250150020b1780d4020480b070380002c0d0045489043c0b0b4a4050300125044d41c41901c1400012501ca1088070a4102141a94800361071003030620b08250042d05c015480d8810140310707000726 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 862496321 1250 862495071 862495097
    0xc2508060907061b060f05040807120e0607020d021305010f050f01020c0a121407120303050a050906010e090a06051906170c27040308150f150a02010b0303220e07120507 74
    0x1a0007824000d500a827030060340c551561034003002c480e85003410f99040c08905d00c40e064081c0d880c0002e40384c483d40c0695245002d60301601c0000c0c440300711081d00c4440c480c9040004140c24450340484000e507403041d01e0300690400040010399035040d940d0320140d40721411980a000310045601c3c103c440300c0c071807404100780302d038220720481c103040880d081060502c0d265a605414075178140a22508121103190812560815844190b1222814064444800c1094010405512040201840041d009101000b290030610075100f0554503605690040c01e0602c0300220309003548800940a9481d0140240031100c211014403151301130031303024140d805501d07042003842c00c0c3c222809548a00d00c00d85c1d491046181101d402d40700c1e1030074900aa4007540c00c42d40c8038400c54690b45075040342442000400c5403075882c1d04800704e014244100b07140ba0140804120011f05004e40061a0070f040664502c9800c0643c075505d410100800440300900002c030001e8606514190552105401242d5441c001d40c6201c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 862497571 1250 862496321 862496351
    0x180c09120d0201050609010e0f071d040212100501030e15040804030618030306090203090d27081011030708040f0303060b040f0302040e03041a0c2508060907061b06 72
    0x5507070700101503511070081001a140007820b01d030140c00d4600b003040581c1852110700c0140c19000b0411010b12080c02803400140044c0c1e40c0901042400030800e5507117040d21003403000004000d0301c04085600c500e483c013241541c02801100718001c4008001d01c808420300218030041c0310040d00a4451003010840440441c000c0e00450440400d52004c11303a0b0f480c01860000d0440380c090380f2440d07100c0c0c814001d0005540002c036100c2125003941ca0845c043da04880f001c0702d01c1600021000716440ba410200159800c004107100601c8000040200003c03103542028003045d200c11689800003510020000b000a140f070400007044600030f10f0002402c80d2210350301945036005422250321426201810011490300c0e008003600741405a01540c00d02c0c0c54450003030b00e8100390303d02180c0456070200d0700d111f44074020881c1c0404254071f0820b40000e208010b007034455039039a5004417482030088a000601848002400f84120380c100c0c2d403490141000305ca440076112141180440c0e220b600c907810810405e00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 862498821 1250 862497571 862497583
    0x20606010c141218040b010f0e130c0c140f0a030c1a0109051b0f0406080606071707111906080a20040503071a07150212090601050f180c0912 62
    0xc40f045605a031000319804c034020072210a50140d109500708103030042c3d01d99012040540c0c40700719052032003105440b1000140440a180c24011030b0380c0c60f12003066440f03540300031021354003402001210601c0802c4071616846a403110305081d800c0c0d212008000009200315080780783c55015890380140441130726081104082c003a4809004240c5420030300c10b0807080c000800b035000b1440c584d00c520300411807041c08a03e004a106142c240030400b0005100d82d200c0e00111441c090b40300c100114849002125101c03250440c0740144c8801e84112040342c40d50402000340e00201440c001e0b01d100140c5050700403100d988004084240550310751900040101c5034204252014040c504900d0302c1d94141001c1c9454a00f455001d106081d882d14803141c15555008111210759411019a101d461069010b801c06032261850440888070810104090840d010820905a40045803600c160807100c40400050000d088000408640310b04045401000c0b407100410140350081e201500011422640e181040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 862500071 1250 862498821 862498843
    0x190908120f240438100801090f1d0706030b06030105060d0e03090301090809040c0207050a03031d10030b030601090209131a06040b0304060606020106060c0b150916170403020606010c14 81
    0x41005100c11810712046188190920080c4c0b603918081754034100040c420301c01032088403d440e039038001a81c203200701500882c003149600349040c0e1507040c80005241d030780c036010701c9414002403811551801a2038030104803030490308010842418070106040300070003894103502080c613500c420130002c44592000e00441025a0040e0740705034640308144140026a03442d107280c1002c41d00000824001c95595024001c15a0380510b480f0040e28401d00c8100c1902c00480035641c0d01803400401516910340c5908800048601a4242d80450341c1e40c116010a82c0078880340313254015420301e0340c402c403041960700190300e030349086114005015129002c1085580581c0007880c2451001003044248070441c02580c005014030303c020041c070361401074002c00d07219100c4d0340141040c1300c20011400c8031080b42e22014401d400106507aa20303042c000410940e502600254102240c03003c4810308030aa10300702850b00c40c0340c050300680080e50b98040115645840d10702d085407844000708088148074010401d8025007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 862501321 1250 862500071 862500131
    0x9020a0f091d0d050703090b120601120c0518031501120209070807021911030607020d03061a0313080c0102030411040605220203190908120f2404 64
    0x40c0e0074544031509a90850390040e1154200c4010a001d03548001140e180043c07080ca095510b42c90145800c4031410516449011030b208041074424500b09460000c074003400d0240c80e035081d02102001c074902920100360b49800894010701614615070040000b640306103500400b07941c0c500102d1202138600d4507081c2c020000c05220000c2c454210300300030303441581110b21030a0105280c58000002135035a91320100e201040140000d0803801c014194514150611004081e50710a1400650003540c0c2c0140e1044180000d0038080d000540300b690030f03680e0580c81d083c18a114619502c0f12a909807000304600200c50004042140241d00740b401e1002d940103d11447d00c0348400c0d81100c003004141c4006401880c480c6041014100e40000d0092941606944108002d0307100d64818040c511041102504a84400e00f4090400c1c00c0080c07203c010280b00800f880a42000c5d1a00740d072142d0807110464103d0241d207165072002c031200401d03030158240c03c40020008203450308011101c0155100e425510703441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 862502571 1250 862501321 862501349
    0x10051303030b0d1e060f09120201150b07060b011b03080a14070203091e0d240c0203041e120b04150b030c220c050a0216141309020a 58
    0x300341d4140500302d8070400841d072040f036145181d00c2d0b000307030082041214210701d8000c0c0c1c50041007119682040d00483d02d50f440411409801b420009140c51201c2110030040d480d00d032446000340b1144680400313499401c0842824000c1c5665140014051242c20505002c81c80c000380d4114198085c203440b20610958991005043c03c1d400c1c1015580e11440c90308003071551008100b5040c1c5c1c0082642e642e0201200c607840c00078a0447c00e83c216088020744560080d50380d40100f030a100d206c02c2c8000c90080d000e1840c041004800034290111103040f469240107070410070007005524126490a01000c0400005522440d6902c80c4c1401d038803c90302c8100d50341d032005000c110600541c0420b41d24280f41d6460103200c0b100034400081e4580f01c00c2d0f5071192041114240c01c083e07001816101c1d034103a040d015800c0054100300280a4010b410804140f40107104014200904038101e9540c9002c40d5034011100c24440409070030000d41c0e0120b644a02e03415555042004c0240c1d40d6003c682000b131600c80901c0742 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 862503821 1250 862502571 862502573
    0xd0b0916050409030c03210204080109031701062c0603040c05040b190b070c1e03021f02120a0513090b150f04121e200d2102100513 58
    0x600381694403491040340f90480510109400034802501c259041c50704a0844100c1c800b52500481c100c0f01c0200c0151002c1404510b0a4056101007800707402606ea1440c030041110700020184024010500018900505081900c031180510700715042200014001c203200d50004c41c0e5241c20845d801d40d150400d024040006042901c5144c503807800c15190282d8900c413885003a0303c113000c940b0449800040004118050280c201400b002502c2c2d840c21641485420418085000000b408141c0c441d2181004056a80241082d103462401c0b880d0042c01c5c0c501d03118500c00c00c254200d4290582401400c2001025000c020b0300c0e0900901200400083c00c16244014090703400740841800480c032100300700c0c001d5241c00600c251003c0b1200c0945946d410035007850f10312020011803170404940083d01d05008104054500d1b000c84182d89009441e41c0c143c110020030105a0b65004054001010300000c8006030809500710742c030300503490040380c1404010345044c1c42200c0044409208030301e040d00440c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 862505071 1250 862503821 862503853
    0x213020a2633010e0402042d0b0c0607030504030e060309010606080c13030b07170103141c0e0d0206041d18030909190b060f07030f030c1b020d0b09 65
    0x2c480d0499241120840702c042d01a02c4040190707420925041c000000300c00240e039611901250040c108130011024001640310807484240c12415551704425800040403894000550540d020258130301e00508803602d6540c1c1c20f80c02031030040c005404106091410803140c4e214400214040c0000d07100004040703260000040401c80c0c06001610028010000c050000604850744400d598008400d40b400c1c1d203460303e0039075031503585450001020000c60000000e0111844003102c2c0c100c551003d88034003401c0101d03012202c00c00c204117580424600485690795007080d0240042e400d20280040745419200d954200007072008003036018086800c40108a05d005503090755185102858008500f4142076000003018541e0044c1014440c80b10806550030351011a00001c03850f080c00762529581d44a9580c002d140c540c03040f40290040f4400010080c540d1f8800c0c4200c1250794190307a42c000058a2032408102d10131070300310050303900400100290002c100b400040300d018a080c240200b1141011103128 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 862506321 1250 862505071 862505101
    0xb04090b150f030304180e060103030f030c080106120c02010b1c1a0402092e03030c030201050f10120206070c090e1005010339090506011107030213020a26 68
    0x120340240d950b0051000c0c241c5002013501c0580303460600b882c800b40d03a940c030280010114146000ca15110b400000002e05030041060801c030310803650148408100703d00705840e818400c1c4a00000101a141c11070129002c552044401001e036100102e604000b550000d00300d801400841036459025030707040001c004920014600391102401c4500040c5041c0d00011801a0010b0003903140c8a0f510b4111448030701000c8422480014101310b13040c2d07068407810010400301c070710242200950300e007102241c60100f01d24030795131003010100d041c03444090601d84826841009510226001502403242d54002424840810050b004044000078100c038a2400982b514075948250500d6628203401400402c41c200021890340c0d1450254003c80a25100404800c941c201b214801d10380c1150004070f08014107421880c09120242c1e20700103241d544c03039040d83e2200318a01c0300035402101000c989018113102c0e0050301c0c1c0c8001d241040d441c807145141000410b5600040e010b4905141001080141d5140d4800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 862507571 1250 862506321 862506361
    0xa20062805011d040c030b09070303030501230f0312040b0a03060510020d03150b0a020c01080604141b1e074808100515030f060403120b04090b 63
    0x91025514200900c50039100240620003d001600001020301091000034070003190b20190f6013283e031520302501d82c1c68802071b000c1203000904050000606080c103403144100c002d01c0342c08030011560858200060740e18082d60940e014000d00780504c0b62004801c0280c002480103521190341c90b04508801012150250810341c8508406030080358071076400207109882d108141400208100070404900c18808941d101101824001030800700b07032680070464512181c42a203a00482d034031600200015594048851480e03403140c0d01c0044c108903280041694004148601d044c9000c00d422448642d6400702c00360801c2c82e200000b851303c100140090b05c0c461410b5692482400840740c0101c00080404c00e42501240080c40c1c410110101d58145014006205031070071a03002030b100a00407809490202c5400d07000300349004d080700583c00c0c0030400b103850b2052400580090364456505071140340c41c075072100c40c110743daa616248403520740780b14140c1d1303050180e4101c41152508481450644c441c00003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 862508821 1250 862507571 862507651
    0x20a020405060103181727031e0a060218041103041209151d0406091d01090b0c0a0e03030a05070b0901060302010233180f060105060a2006 61
    0x8095200c4e80c08031084c051000360311061624503108008010304090050030142001004c0020a42010520785980030300341e840180c00b914524081124507040304a04d089c4a0010340d00080030410000d0100d0f03000b405c5007203200d1501c25001d5a400c010804a6410b402034403600d110000510090012005607174100007103a2401c4001c00e03060541d404441100c0f03441c694148841c0d2005028402e032980900000c13080c01500070810300d90b681d0480c0029045080340800c1d27040301284850a40203040c020701c43d55a1700260368120036141c455905650360310080c0540200181e10f005800303a5642800140100c0711943c0e40c0365201e00035420841802c28000d0f15406250b89041d40800c0180d0b008607850310854452001550a075840c0b811039050b0686c1c0c513100d58100c0400ca010000c100320581c0032070041f00004000c6070403020620260710381d980c80c20300510354000c106001d045c05441c071545040700c0d03182c45c02c100cac401c030000d03052000303460702c0c0d0305940c941d0002c459a041c0c0c151040c8041d40000b081d035081700b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 862510071 1250 862508821 862508831
    0xc06020709110d020901032d27120908060c04140f01120b06070611031807030b011412031201030516030c23120d080609071b1e03020a020405060103 65
    0x29040003101e214812080303c2041e000b0540d0840c0740e00030b0340041c4a11070090000740f00f03924250480780da030311000444c0400795850300c040946140110044400c814510040721245c00c94207448020581041c0341441c010083c06600c04505140d06024040c000c04444060645507130030410012115005401814002c0f00c5050442483c0c0e030380510003500040c100740c000100f141c280b001191941c89088000b84c00c09041803001e00442c0030340e60040d0f201d0900e590fa0000c00340c0000700184c0c3c441015200140019100780c00500c0781007210300300d81400e6500140000e48021044e100103045802c048c620f401900038480042060010501103044003c0940c00340740c44407411a611300ca1505030600503504a1926880348100c00058040103210b00d54004166040502260b46c00c1980c1c2c0f88a44458000a8607000100d9842d0901820b0503004031f00700c3e00e4140415800c01420b080c49010304500b510980d04105491100300048805082141d0199000c4c0c0b2134030303103a0300510050303600c00741c40581018606 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 862511321 1250 862510071 862510091
    0x30d0b1809100c03020409021809010e060d2d05060708010603150618032a0b0406201c09081509060612011401181d2808070c06020709 59
    0x46541d42d0402d00300a0300280e5a01010003c50003401550013618203188001119060000c01103180314078224111142ca031141c0e01e8180c84201e440003a100c0d40e07040f100d801b0600002540f04036000c14400c445003200604903242c01519010102c1c18042515103400031024085400c1d4443c1c8881c4c0501030909091159403244854100c4180c424440c02007001004245031100103204a01c2000564200b03281861019107503012080103c1c1180d201d130490a40c903800000c20030b19010a580407112913446040e840640804030406003088241500124003d80401d00b6200040b034000424070b45841c4d449078050b5040c180c586103031000d1041e40100070f9866008010124034000b83c02548220706488048511070005862030241040d02d000c0601042d80b100040b80405000f01c1040707800c1c0f65a074040c070640307000d80720715840c01c423034854a08015008480300c201000080300d2a4029014085a150b40c0c0258546135400300390022181100c4000648900308081c56040044001601c18140c00300821910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 862512571 1250 862511321 862511323
    0xd0f0509130b3f03120142050a050d0501230409021e150324010c0203060609090a060e010f0c08090606090403110d020c090106020d050306090a0b03030d0b1809 70
    0x940315005070240e1112210705583c82c24000c1d1100381001000d55041d0b5619441020a1000d99100840c072001c41e030840c4400140e541d1103070380c0d40310110b160f03403520080e0300d0710b4129070a6105d0140501442400c010307100304900644986802801d4455008004602200380c111100c0810b296480c41070341400000c40240c1e17940480c40c0c1c03100008070301c02c00c80045058040b40d42d098a44851020b900008000c02007070881d81d0300d26840b405000744c0361200b171390100c5005450b80507a0301d00c06505944100005056414212104c50700b040c0303034008a4100e01c609546641c00e65551080c80352440e5120418042480344601400c3c08801e0309040902040c533101520300c2c0c1c0e0741001001907100e560450045010b06000c1c0070f0a0748401c00e84000d5480c0030207283c20107507407104090f807107900604400340002102480803c20420700807140e0b6410346981c48020400c20300b140007410707400390300b50b9508241c03500b5501003005060f9107600407408a00100038408200108080005200180503084101302040c20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 862513821 1250 862512571 862512649
    0x110604050a0b0c010e0303010608040221030d09080c0a0c1707081002030402010516080a09060e0a0911160311160308090d050f100603060f09050d0f0509130b 69
    0x801010910f88400718450218090310b491140b03e085400000001305509500020706803060b8001d4800c020f0001a0700002406054400d071042c903070b0380050013403000c0c01070980c00c61039409000d00011410321150760a5030b400c242482204451540f01c01d00208040303101c81d2425483d80070554003820005141011042d101c00501c80c00d45102c84d800000101117a010300d041e54041c0e45107650f1302e42d0341020f500c2d0060040d8401c8130380c2c20100e00000000140140315565084400001401408441c0d140549280c003034015484080c8604900384008140382c0000018030340c4c014001c1e511070b50002d00c50035026003040b250b50200b05400180711400d101086603603045520801003591803019141c4207040c22424192000289460341c0509254a4512106504110107480c02140100518504803002c4003c4901c2400001d04903041442d01c1030300d5074041d0442c070410070b03600d003411460000c1220000c0d02d50041c2c0e14842580c241d40c1d07207501ea801c0c01d100140b594810121036401d900c0c1d4081e0360320081c100d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 862515071 1250 862513821 862513829
    0x6090c050702060a1e050322120c05010f05090705180402150306030115091e060302030a02150f0f0a090506070b06040c0912080403021203030c040b090d1e110604050a 73
    0x7031400200c1c04c12051160060040300b0085000802c03510341190001011a401903a00240c200d0300800b8908017508418108405568099600c1c3d090003a00102070350321141800701610317103540c0c40000c0210005a8051580304041a41c00f030600d05007031038104803c100c02da00b006030030a08050f04200041c0c880395200e0440401c4030700032689a07581d684c006805030102d0840186034840e500d100140d010750302c2e0803140c0511008482e84416544038100c5200311407507844040d5240d0300c8141c800000d820003040d440041e4054440342e80c90403030261504005544402c01d8440600d40000782d01541d213500c00c480d82c02800c0111046441c040d501e0702c40300242e00000d08554412503541c410340d68414010910100148641c1c4070200c000380c101e00f010402c50b0414401130b40142e04680e5003203101400442103038441e0300c101c0c00841c00e09040c0598040c842d0451a60740360451840707a40a070200740c0d10188890350030b0b40300c20003041801c1a80742101031100b1810f0914040c17101403005010550310740400d10203407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 862516321 1250 862515071 862515079
    0x308010e040f0f03030c0806180a0b03150106020a02030d030c02030306041104150507140a030f030e0109170d0605010806060f1e12090f06040b01210206041806090c050702 75
    0x140c940b8142000d1101862100600d01d00072001140100b582680164044190300e40300e56110b0780d0303100c081c00500380da802d50040e1043c040e440000d500300325651100b4001c1d08043c0480303031044480708111030104001c1c0c2207100542d210200724000c51a081298409804241c80e061000307641072180650389010143c00c1e40c0c8200e4540141306900070358842a50005c00f041109030761042460040a000c6601000d000c1e1066040303404020546040010205d8005905940340c2d9910044501e0407001010700008284807035494142c0c100205500c9901d80c0c6010010784102a84d50080e080d0010403940203a200324140203200301001a5540d952050b1a00c041100c2c9900759542c160b105048489084c0c0d480d10b031030007200456024121501048101d00c5205604100d5095841548ca081d42c1c440313080340c0081044c0031600062104a001c0c1a110b90a09030900070f850711420294000307604e40d049038200028102111004c03006403076040c05804000e00154000b00311414100000405e18405c0703800107802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 862517571 1250 862516321 862516349
    0x14060108160e040f0501090602130f09020301050307060507051f0c03050f07020709022d0901120536011103070e090f041e0c12151401060e0301020705010204080c100507030801 77
    0x85c048290407110080e0b0b4002021503071841134031a40f40c0f04a26030702170b9621800c080ca101003090700f0240700312410703200d00034014000b0301e10304035007180e15038070071181120030b03018801401c4d680040900010758003007240900410340f107c5040c001000c9800c000d141000e04400c0300306109444c0c0c0c01141d488252441c03008007580d0b800c40071079650b203000c0e10304a580c0c2c0243c00c450801403c2c22036901c040c1890300300903a2101d09444003542e800041d00c0d0141e401c4104400b001d00203200380c880c4011b0020b450212450042560400d4508050854590540041203510000100300703079030340d00952104000104840114580c1400801e03003240c454011720003401004090140c00d90f4022a442c50b01c401c640c40003500141a433981c1c88040320010030141243c0081c8007401c03104100c800390040c42d0150828407104921a880e01e0340c11100c02861085071605554204201404124280010006045540014003a003008042444920070034030501c1c908202d018882007000a41c0b0580f06411501281c180c446 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 862518821 1250 862517571 862517573
    0x306090e0a0c06120605030a0b0618100b090117070e1017060418021009030c050d050a1b0b04030503130506090904120e100807230d0f0914060108160e040f 68
    0x20405c60b000360380d01d80b01e091b090104210b06503181c0da01c80c80d0300751031039103800c2071030050605242c1302654103840a10f201c0c0740c2800401e000c0e001502207410140740404041d540c07141d030280d080030b0564400e4001030707013808181c005040c0701400707004002d524540300503d130034800d030700302458280541440d01c903036211040600565000da1944205c1e43d0000c00c031a00385c40d81301d4405402422188400c4503516591030300001d403441d04803459031596411001911032500f156840025440c001031224013003506c200d00206402d41c0c1d04000e080078500c240021952500c929481c080b603c50240d010790310501003040341c50fa01e0784030324581e10742003135106a40d03842c0d07c061807105948502503514880d4010500e40c14006560798003280041c090720385ea8071044890880c3e03c03030000b915401500303d1010518100520400b14003650300110090400c07940c0011461095600c05190444071070f1412040d900580c014030010070140f000030300c001b00e0603080b085020724286032221118001030003d000c103a04a00e140d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 862520071 1250 862518821 862518857
    0x303090604090b03010906111801080c03010506030907091104030302060a2c01020906070b070e0a03120f020106030c1203080109060e0f04081902010e07050103111b070906060306090e0a0c06 83
    0x4a06d49600c40303014003031076580c0091100c0d2600589031a41507034401d000301ca092035001d000c546004a50400710302d89183e00385030601045510161024500784203800b40050010154420080407030009001301350f80c1c07403842c1002403800b8000381403021304520744420a07481e034424030344c200300308860501070911092600d07540500902504030126000b400001c3d0b4801042521101c191061036941c0b44c184e03034036464400b403201c0c1c0000360000505050507100701c440f00500031143c0c1d81a44d1442d00c0081074240e2a5a11101043c06660040319045c02010f00d6004140c0c1002c442405002c1a61041000501d0485030000001001c3c003112820400d05000c40d060000d1501200c100904060354441280580355000f4003d082610080d055030180c04001714070743d8440d001c1d42c040c2560035442c05040c0465840c035600001c03469003010007140f090b13010008007104a0b015030001070042d45c900090040c82c1c50f03056001d558400c076031401d15401807500304001440c514210025100c2600d0f144001088107903140e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 862521321 1250 862520071 862520081
    0x1802010311070f06090b0114090705182d2b0618050c01080105010c020603061005040302030735150c0f04230303130b0304081908150303090604090b0301 67
    0x40e1000c0c0780c3d00511414806190825032030944152003102d0b040c0e0340c403901140080125002c869100f00a803010070012442a4094130719240588014070072034450600140009648202c032084685001800e440203d4603615a105500d50564101c1c03000070036141503e1a5010745407038940c141c0c0c0014840300502600341d02901c0703c80413003600310008900310b00b0b00c240c0d501c800c90480c50014462a0001c42c00d035201d0300e907540410b039025124a00b180c5601003001110710360940407008210050100001503501003103040010f0000b01d4403058070006c455003121010740500c5018a00401c221082c0c001d2240000751070700144100104804243c4810b05154000d11480700005000324001c02c02080c15080c010306403d082c108681d00c0000b00380501d003403545034040e522041c3d04e1400201810045410304500440c1d01078410361500c0d103411180014007450303448880110b0000f5200380f00b00304c030540c100c04064015200403401182400203100008501d84101c0c0281412070fa118089010f8680782500300b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 862522571 1250 862521321 862521323
    0x3081c020a031409010605010c1e051c0f090303080f070c39151b02030a0b011e0b0f13090504080901090e040302060402060a051b06011503180201031107 67
    0x25592041c411000501510011000c03800324941080480c40d143c2e01440380b0381c11940f043e19081070b03550503500c441c102041c40030112540042003541040024405021038040360000000c03d800d98441083c0051444c101a0b40e00e0f400d10199100c103001090704100c5c5540d0140c0c40c222042011303a941031b03048030b241a5040000744110380e00c0d00f4190080c005003103002c102200000107400c007095606010002000548940000040b40031a500a42403182850641c1c034051446054584a290303401700b4030b80600c3c4002078510240e0381005100034505403081a030510450402c90500070f05165a60620344140503103480001400507840e4019028050300c10000d051500041100c1d00e051b08114130254031000003103001500f8000302007444544030404074066a016802040f85070b1b07840d428424503130b0000d54600d060040a00540e001c120444110380c480c0020783d0080c2015524010000382202660301000c0189801c140743d19424412144101c0c8901e602440e020481c04007000c0c0c03040d40b234421084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 862523821 1250 862522571 862522627
    0x618010b0d030302041e030c0e07180305030301030201080a02190315080a05010b0918030306010e130f0903020d09050306060f0a170a0c05010804111e0334030c0308 72
    0x40e0418960958054400c603040d03009420070607040640c2c80b0300d01072543d0000170a21030070283c09020008402c9c0d00d40b0390000c80d90411101d056051900304034074000c164002c43d00c1d40c3c4000014402c6503031200b101a0040c5000c10290708080300c03080b4068082807500d49030801c2546d590b0030442140d0307411040000078203d800541d59400a5070420358064545130392100e004515100101d042d683e40122403143d51142d14018504580b81c00c1c004449008032203555036401000c0c0c0c9001c07600290b01e44902c241c4501e84140025111800d854060704040d039034444801405035080d400c01181d20003161240e405401190301090408448000a200f5829608200d90159482610f000d07004000120107910714015094510004d945800464030280c0858008000705a6040b0303441150400701c961071034098040340800100c20718400441d1921090710300b1070600c0d003d420b03020803490040a03081e89400d001c584034003080c9401d5454115075140c051100508603100026074081016410341d03003a42015402e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 862525071 1250 862523821 862523839
    0x30f13020a0b0f030108011416030b060d0f09230a0f021c1202100203071d01140d1401091103061504120b06101e0f021002070b1b0406020618010b 64
    0x2a0f01415134000740107001c841d40ca070a20b080c0c031084500c140c9a21070f01c80d820f007d20680180c007404a003d000d2881c030068010800340040c2074100b0050080311804501036500140d1000141003000280384a82c1139010281400d0504400b0303a4804500004015040551240415600d00c0400c2500c6050100009a0318a1a00840800031000e01c90040307030059070300b2a0303200c0f400002008100d20003070350000042880400400901c140700c0d004100c420764141410035500f4400c042032500c0e0340c405178101c200a43d640d0303d09800070035080a01c1e400b4110f00d49041103060084400ca1205200140000b1304c25011420301c0300310380621100300c40c0500b102c0c404032584041c00e45131201088000703662080c41242034034050710090b88640d50903007000903210715031038101c1d40582c130503030300c00004012110442c0103071242003120003820300007410300b03034410b26500c035440c6000d5120b0f20700f03844041c00402c4481000c020401100d41e000030100d03004404c0f03110940e44148090010350051126000702a00300d070201c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 862526321 1250 862525071 862525087
    0xc08040326210402060d14090d110a1e0609050a15050601022e060806040203150103080906030a0e1c11071206020c010b0306010b0414010302030f13020a0b 68
    0x490700725096001c00c1c015218440214006400e8035005241d004400c0703804145000c0000c06079a4001500240040c000b64601351804103440d050743c0100d80f0204120340100207100d071098040141c041071a40a19100000c405942c42082d15119401d002400c50b03280004200130894080038040d1075035034008000c02c0403d03501c0c98041d440c2d6200c40000da5211801c3c00068031020000c1c083c0c54403c500581c0a0700080380c52004208210200d010300010054003103503c600ba88125116034000743c520080201040d00d800e02c10186458020030000a1040c025001000081d400380150703410b9420440e09944c0743c0d515007102c440202034201c421307002c502c90902a0700c000c00c2440b07079046c41c0f0789542d60307050303a030302c201e034105541d9480d2a20a0f855404040411134002c2101580a020b81000721400810200d0a07000064605082070f08924407801000a08101600d464403100940800a080c20750131481c3c92a5640114030000f0110070241181d441d0701070865a440c240075010303181081c0400e07207940c45 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 862527571 1250 862526321 862526333
    0x20120d0902010315080c12030f040f080601050a0e0106110c0a1805091f0926030702062412100c050c0c0319022e0c030807140d0207030c080403 63
    0x1141040c2e010a18102038600c0000003210759005580c908001803001c04c0c9241c080c00344050108546465600080c01742e80805254540204000e02c40911500000c82c14940518105001a031155200d9480d0000c02c02c100000061580e0440d5040e060080c040e4007006105802e01b448000d205071301c03c003a00c10110f0701c02030301100c00c09200300c42034040100b41d480d01c0003103642d4581c00b0003400f8002080c070900c48605000b50402c54101e40b20b1075151008029044000c8058611030307041041600022007000500c030360401840c0da1041d0601c03200000d5100e03600b5094008003400c4142c0b4025034a01119034081d403010000ca540a001c1210108415252200c000b0305a0700540c80c00c229900560401284528001444100855600040c210740000c59800c001903201002c0c00f8402c07046028003001c0d8100300d05031003c00002401c1d00e6134140808180b800404400e00103080c60280105c640020b441c20b01a00c069038444040d509005940300c0381410241e5010040400003070410000003004810880d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 862528821 1250 862527571 862527581
    0x100905040501030c090e150114010c020a0e0f070507020d03120231060c110402030907080703050309040f15090515062d030c0304060f0209100e030f030403020120120d 73
    0x3000c0d910801c01e407240d80ba03509071685c50320a24000c060518000500000319440010050b003401414000c1340000e0390390114244406c25400425000040c81c00c2003541d500004101e98049080c0c51d04928088071503001803010025010080c2c104003032900000d4020501c0d5044603080710b0840c6080320035100c07800c60008045803400d0302e50301032500c05400242940c096002d00c090568440c924440416100081c4402034200038085000307071281c0d450003d9a80003c1c80a00d014602980c05580d43d81550018001030b00d640c00100441d00d450142c40701d00c00c10b422061030041d6059814007040c0354031a580d414546040c10400141d0100000514005511080c43d0010603510781600641ea1a030b40c110710705074a40421211080071140c00c000017400a0f00561180c01c484042d0100181459400c6c17010400041280c91150042440c031003000d03086107410010034290f131540000851800d419a40020b0218641c80701d801180d50065010400b100ca040c8940040a5003005810b900d900d2140c2021780502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 862530071 1250 862528821 862528829
    0x12d1e050a0518070f0909020301090b0a0b0a0b210604020d140a0c030e0a0f061503060212010819021306080a0c03170316050a140309030405090f0402030606100905040501030c 77
    0x4107403a1400720f007900e010801800315140703408a21503075460402414054000e00004980c595a1030072842c0000302c0740c1110034080c2d9000342d40043d100045605014100d101500800760317024081c02070929680d01031060400e9810b440620b5081c9403692b802140c0640100c01131009820300342007059031584c400040c00c83c0b0540c1008811f20220707202d000c080e001c0f01e040020301c0710940c01c00c070f6502000c40c00249081a600e8401d0030006812110202c2003400300d4415001240c05940000303a103000c824961441d140905201d001a05a012440ea00003060b2a140140240203800761138030000301001035071044005001502c141e4441d11240d1409030f6804171540421114007041c0202da04500011400b52072146107040c001b120b00f200b9015043d5940d40003c40800100484445006075600780880914094071040000b1903c9505080030060142070082480c1c24604180c3c0c10000540e03400940315400079800d480c4e6030903200b00b501048899080301e4004a410908010002042181c468485002c803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 862531321 1250 862530071 862530091
    0x130321021e0c0904141006061d1e030307120804020306090105040b070804150603030e10033b16030b18120f07140708012d1e050a05 58
    0xa4925188640920700c0720090140ca41c408034840d034190a0080760360f90040c0c01414000300001c0d004101c585046c01c02401d1105141c1c03601c0b0100509134000c1d41075801001c040d203120440c08080f501058084010a5071583d002c070304070b80004139a49080c02201c03481500000b40c0030103500880005081b83c001641c04a020703103d1900058143c0106126440c000d40e4401080790980d02c4000d000c641403200580165030120310450400a900b1342c9100f100015842a01c03001101c0c4440e078104410644141d8252040c141081c407081500e012800f200d00000301460f5401103e0781050080180c0801e035034440200350705c44d8200c1900740d060b03e0280901202e11440341d0320760594070500c0c1e80782c2c07460440307240b00c01550242c050390b10704818030005800b61801d42001103040051540b00c0300500c0f55202c0c108202a00700010900640401707018402c4582081650242c10041241c03c040c901d2420603000000c256841e5040e0503510020300c1c0180002d4102c41080c0b003181400c555900040906880c105e482c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 862532571 1250 862531321 862531333
    0x110d060e041b03030e090408210a2004050d06020c0d030906050106050a050d090203280506060d120c080409060308090a05030d051b0307020306160e010c020f0613032102 74
    0x850581042c0b00c40540b80e0540d1003e03400b80c140380600c043c0220281044500004c24021a60012190800f255034411004002d4806044c103c03103003c00c44040d180c01d040c9684030701000c491018550340446045900a45003581c1c40e05c102d00b4800000c1c010034103122028003c0034090200c0980c1a0001d10269014050802c41660790310000d0b9401e10a44850340e011540a11081c0034440060307008184490019040d221400d0405c80807001c803000d1030f180390340011024920182809006c02c80d840d4802d0058a0140450302107446099031403140c41844420000b00d104180c0030016003806450040c9841c03007080c80340580782d1901c403410b508074100440c00741041100000d61407400050403441020103803030301490000d05002401c030a800460640320107200c02c000800040c0c038200041840380c2a80500e00e44180c003a020018410812882c5150410200b4001c0d08050f07916442c0c07116501004031745169031414480161100011aa88054541d040e0380500e02d2511004154140390441103900390b0b24 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 862533821 1250 862532571 862532603
    0xc0807020c06041815090e030a1e0c08030a0b0307060e090a050402090c07020420040806010605340c03030f02071d161407231b0103110d060e04 63
    0x750314003c5100d4128498040e0b001340c6881c043c1036005c050f004406a0300817034070070340304c0b41c800c400ea0340c9441c1444419800066500803059000b030b0122000c031a5806150381c07980c0c000c4030085c100b4901401c09441e04a001011418580b8540d02c801d90094000c0c0a44850300da55000140c00140204401c0303010305003090000b201c401082c0b1980b803083d603004115007038035120043c0b0182a50840401203812503901c028810580e0060303000d002c610b541011601e075849050102c0241050410780c000303014400f060040404c00324049104007600c0b1307805030f80c0e17038a442d00c7d014418905000340303100070300740c6501d41d0804400c0c1a44001c60740d01c40703002a001c0b11200d075580e106001141031500d1181640549000c082000007143c005a00b10040641c54100b8903408683e0641d100d0340c0c0444411512a003603014511480c0300b0340c0880305801814240905202e120403e0140c1c2c074a07800c04e000741d04040e65080c080001c0030800040d20050020924104509611664200900c2000341c0d41a20700240f12a8411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 862535071 1250 862533821 862533829
    0x3020a0e13080a021203041518030c02011805100804060510441011030402090f0402010203130602070f05060a050d090206090d0f0201140c0a110409060c0807020c 71
    0x2034000c200c0615841c20440a40d1034044094101d0b030001c60031800760108081189030043c015502560041c00c0c01290400c4528000c01200c0140340d000d4880c0d80090062404aa00803007450072554081c02c01641550b0880e000001c0b00c9200e410003940081042c031502526075001700d03468441c40c880c041c1000180c031135401107404c482c0d0910420b401c000184a0b4261521080c0b40c0b141e070344408400b5103040100d50100074000d1505050041c031616400104068060f080c90700402020142e00450540b1b1800c06802040000e500100b040026085803c08078045910030001c981c02c030000743c030040c0a45500d54ac8000d494582ca48150030000198a5000c01c680c54188125030f04c09003191902d0307142000307820300070000d0306c804001664003040900c03805015407124001d2003202c0388200003e506009840c4005010000c08548242c1541c5050080941070800002c040205a42000c4a14034090310040010050140100c00600309030a0802c5c4d1140c2c140c02088080c01440b0503000c0ea44040c140701e040c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 862536321 1250 862535071 862535099
    0xc2102041d010c1e180e0115030f0b1e010908030d02041706060d150207051c0219080306040e0f1b1005070c060807030b1e040b04060b120720060103020a 67
    0x50003070f030341001012400b00340640d080e00c0c94401170801800c0010340c0c410b10900742032826400b0840c607900c446203040c08203615104000103105a290704024403200540400c1d0240300520014071021400148698180e0007102c0281c01080c01c141101d40c0c994111b4040f002a420511501491a0400c2d0f18188030304800720b19a4840c44c0c001c2c01e0340701c04405070b8031041c0940000e69a4004004c1d070800044010130014001200074001c40c5407801d0b2078180390100207142043d9421440181225078403424005601181280d40100d011580401d9074091103c3d0f850030402c81301e10306005841801c044919120b0a4070700c002d401300c0200e0300e11101441c00b800980b12440343d4100241882d200003018488940500c2e0b00f1900300180b40740004041032914049030f03889120f420480307150305054150368818030341802000318480080c1c40a12240e0b24000104403580a01d042c181902031250300001c0c4403d00c80c0d0300703800c110075681c0341c403171086016904400e4907810280004e070b001d524802d50110390038106040f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 862537571 1250 862536321 862536347
    0x14040b06030903090d0f08040b27010e04021c060306090b010e0c250501020a08010e0a09050a060c05160809090c03091507090810051e040c2102041d010c 67
    0x145240c98500f4080041c5d280010310f00311600b00155110b400807035a054081c0014101e1503c015545a03160701080f1642903904e000d040e00c2c7c005030301c501e0181f40d900c1400c41443e88001d07900585c40d020601c1c130b2814420005400a03541619260b000024444960002c16400f40515004d00d1982d0b00e5825029010f00111001c007a10002004100c1621008108021164280c0110007410b1400f5548490030b99004130794000000b81c0040041c807034910700c501305540000715010200496551661540d449036076032940034004507600c0030007031360081c0254221000b6a00c02d6a000300e61559500d4031000d00d0304000c0d605401003140030002801c40c0c0c0c0c00d9040724012880080141200c05460168001058009000e0030400c940003c002840400402000d2400c2c2c40420303020401340307048424002034144200325115580884804e010100305550a0b040aa49169070601c6034285001d00950200b0b0040c0e500940140c41e18003003951003401045407a402c000031200030700501451000445403a451040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 862538821 1250 862537571 862537573
    0x904050105240901050906070b0a0c0e030703080c0c0303040e01090f180b04060f0e010e06090d0f0f05190c140c130f06090c02030403020a09050c0a030905150114040b060309 76
    0x251000b003114198002d4501c0d000c2c149030841ca001881000320b48181c00045048843c400004103010400066005e117240942e4586090030040304c100c00001ea40d009070b844050550240010541d8030308406101031440300c0310190480399079607591a00b20107824424800d9000321480c02c03803181d5070300000b402100b140500079200c0703481e20251a1a0700380d0711070004d0011251960b50b40f101c14080e1005000d03111108200030b00000b510b400183c081400c01c0d000400c509090780140103076081c0250485403100301a1218988413200f5000018141c910340700d117402ca040c61b82030201d0b200201580c41036000c10301d18840c09801003048130350342c0300e0366881c00b4038600d4942c003055815070134085041c80d501501714101004000700b8066915440701c0b080f68030300e03800c4000581001a0500030b50405900070381c01050059020403691500e03022113034460140300c026000301901c414034003041c00020003009184410702c40916046582d6410481c6811026a400c5402907050000c0d511503450482c090300c0c42401c03840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 862540071 1250 862538821 862538869
    0x2060a0c092d0f080f030c060f10080109110406140d170702090f01090506060403051f11030925120611120a0f14010302030a0f05010b040c02030904050105 68
    0x141c01100100360041100d0000c840c40800c000c1118030110741c038008050700443c0c034902c01d041c50320a5080659000e80360005900403c2003c241e45800115240e00640c0182043c4190321500219100c0e090184e10902041d82406501824441012421950520304507401c01001c3e030b503001251000b40900d80c82d40d500500f079800100c0424403d050585c10214603443c11032504e8481c0c0c1c00500c600005503010805260311400510401501c2c1c4a00c0350400c80440f10113003031520f599545c035038518580170a0300d540f170880244540c0e040056008020350145403180b9039140c0c40c02c0c22a840c2d80344541d032414003c601200c1c0a10000c000f0307031a50070080d101b1724100101c44860989425014040c2e00a2000349d80070100800700b0341e0111101c41c640120301c201404100940c40441020940d40e088844002d5440e0040040005035000640600c1c040d511104103084100e243c2030460040c030540b204281c00605000c680d100055000c0020a040c0408039070411403640c072b51040c4013240743c05d528000302c1d001f500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 862541321 1250 862540071 862540079
    0x5010906020a1b1d011a030c0301230424050a15141201060206010609050f01120b040f060b09090a020306060301050d060e01060308091c030e010c0c0515030702060a0c09 74
    0xb1611040c41c01425003c2c0b82c119960758940e8460148100c660a003a001c0c4480060041200c6944078400404900f9496419428500da4608040c4010700c02c1d103044110401d034008584048140206601000070000c00840501100250103180300d13803030746441000740b08408500307450150045400d4451704800b01403076105080c0242c40b042e5038003000f000d8105083c0400d001d4041c03d0f5031075a010f081c1650140415525202010b003120481d6000b20307118400c1074802200f01e9a006c500c1a403940115400810000c1000000c02d004082d10360320f0704509400d101c00450b8203d110001050502d80c181d4401c1e15999512400004030300043e1480750b8094010001001107140c03088000002ca80100400180185035251044c211001d0381d004036581308000c00da03130070315180038840c2c0c600f00580301040c10010714071a6070083c400c40b0031240b03007418040c96100180034040882d01800213808040e14034108041c201b260f01031241c00495040d401480740000040e518403071030003866a1a2015126201d5013428 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 862542571 1250 862541321 862541333
    0x6020d0c0216090b0a0b0408150702010e1207060209180915061f090b04120c05062b0b090f220b0415020d0216050c06040f090c200d02010605010906020a 67
    0x15030b0000640c03005403441c01146c40c80749100140014045440180b40c0543c0c00d440704c81c025a4024849030959150a458140055010804400c89050b903d001076aa200c940791000c02405181c0310b46400c041c0d00f110110410039840d9007580204e282000300c4038001050844c0d94642101215490b402920010f000da00301d146810044088260030b0a0111381d0b141c4518401806822a03440001c0c0080070350502400d0140744514a4043d00c01500c0007840d00c1414800c02e0309203440c0e1000741e0010502e08808054604445c1e100703419400c4001c002e9100d9081c20054111207040c00d40e0340c0c031200b1500401c0502d4401d4544802071000e070740054131041c1c554560300c1d1509030100c0c002d10783d40c080d03800704000c01044119100402d0b40c1010030140030780588590402901d0100312280c400d0154000f040107202100c41c03c1441e400f10b4907804008540c0940500007100c1103008803504041c070048412a0044507003000c035900c289103405078001c22643d59600c00440c0d0056141c0b1902c0e02681140042c1000316070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 862543821 1250 862542571 862542581
    0xc10141803091c0b07020d080705120f0406240311040501030c18320108031e09040b0301050112060507090e0606130e090f12030c0a08040302010b0d06020d0c021609 72
    0x300c0090705100520340ca8841131200c4c102c0b62000184c04c0404c05801480e000003200d5040501c40c50720b0703403c5c4981a13058415260018101c149222480400101004010b4015011010618048401314601c0030070003101c1507139600045440c0400d205d80301041d41040d10406040726000052601900e280242803004041c08896810b0b0032a111030304151006080c0d0b030711040030581c0100c0c00e041061820300321400740a041c1c0000750139030020010a02160f4004030300c0050190364a100c0e031fa41d13080b482e00042c0140325030b0a01980650074440002400400c030940d01500600592080c8001d0313880d00e034104c41c0c0c40f280b0301460203c0c1119002048142c149040645400da40c2e122010b001c4a8842014020b0288222603802c141e900002c102c1004003024000c6690346c14824038400d00750305007002d10b074503240980c050000810006200103414103100350400c0b40903440243c041855400f060034100701a42c80228412282403d11040d5043d003880040d5008290300c2c100c81c81d01d00a81000001400b070300c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 862545071 1250 862543821 862543849
    0x7080705040f120b1008070b0a020f0d0e120c01091a070606090203062815021f02070c1401120c030609110306031216170c1014180309 59
    0x200c800e00c00842e8000300c0010100141c2040400481c42c4002d51906504c4100e004103d010384c2200400200308441c0005000c205172540032640343c0c2c403811b5a2008a01d03009112401748440c2c81010303031503c000760f08118007440503401034840b00d07204084181c55950310030030414030b580021841d101c100700c80389448032140349943c03031000860b141010035250001075619942015081d2540002800850f00e0110604030b00c500c0c4502c03c1e1000c90305900d00440c0006400e120305100125248841c03100140300740503a0b42c0e0740014400240000c02d0403000b101c001d4104039001c48500600c004086004c3d0420b0a0b80c1c1100f0005175200503100c030503114041c000e440202d01c610149174440602045004480c020304c1c03003142c040c240c415100e1906204140c5400d1504520108442040001c41c1c0801d5410461440854110401c210300c00b0402d0348000385481203c04111403401040c101c030b0307120042d5401035080285030601b0550961640001003841c014011015100c591080140138110f0402c410b4110040d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 862546321 1250 862545071 862545077
    0x11706240904150e010c0801053f120a02150c0a0e0a1d19050906070509010c29010e01080a170d0e07150815210d1d030d08070807 57
    0x294804800c402e0644e9045041900c0700e9440350300304c02040c0da00c514041e0050074111910a03c01425036444c21050302103604251460380711024098013107840d64040380303003c0e0852046071500650359071844800e4000380b4426006001d00c880710300d4142881c1d60814002c81420900c030f071825840c1c1234203650780901c0c3d00c483d541100001d40000b5806c03c4d440d00142c404408202a40103a15281e11031003080540d88072031403842c510705400e000c444403001070030a90105081c02c10030380d0f51295000589205000c0040117010440c1c0d965804021503100b03001101c29080110150000e0741c80b4403051800381000d0040c054241d111608120100710061045600070001c0c0110901e03240013407030f045090f01c1c01504010415800369208000428070b803461044020314030f00d0082110304000c2070058441616880140c0716100c109140382c00c07407032090b800c012090303042812102c8031440420080e0240714100916181d022000710f4000f0035080100f1403c01204030380e501c01e0751903030382c0391000e031640e00c4050040810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 862547571 1250 862546321 862546343
    0x40303150906050a0801020403050a030c0507080703150c090b0306060a090f080307021003050f06040207331d0618030c010207052802030a030e1206011706240904 71
    0x1218040010340054401010080b41c40c1d414142401640c41440d8480c3d1903d0f031042104001044011460400d01581454904811500c40c100303d0714003980c40c0c21108203401110000002c00c901103c4400044a6101041c080850694015240c0240600c10703072210364000c01c0040c2e1a403400100501c0360f211113090040c2401d465940b07403060003d0641203042164800138242040d40350a17400016813940c20320f020701c01031415004407114640007030721950003160040f8422040042d009081030031f0110414030000c0207551130061581c00c40e08035494403101840c1410303000350f0346040e09890815030a000000c0a00342c840c0c81032800b81030103070445101140010312a9030981c050a0000b403840c140204004c00d501000d0420128904004500744903034600003284600050f240421081d08054160808840038048440800c800d00c842c1a1f041c0310034002c1d100045040400460640c00035040700044901c15607078102c403069a1052003803141c0d0711400f2651401c4207440c004104c81d500c14031810440f21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 862548821 1250 862547571 862547591
    0x50f01021f0e070f17030a0e060d060b07060510080109031407020d1b0e06040b0f040b0a090e010207140111120603030f0409050610031107080306060c0718110a080f040303 75
    0x3043c100d0b580c01030a8840011041003084210081110385044000d41c003551605a0910000d080c641880200c1400b695000c9401440415030f036006d10000e1542d0b80c6c0b069a50700117403805034002c101c101d03107110184886a00c0402c0f02d1905104005141e85e050721045a5856507000c44403054010201c100e0307100809090580004810520710742140101d0300c80042564208283d0361250a00105040d01840c41d09110840603900c4209282d041312056800041d552078804c04101e540005411408105041aa503170321103e40c1540108440d138081e09200d00c521030820452402e80b00c00810341e0010744414010302c0613a45070344065980101c03005088901e0001150100459508190301c51480c40350340318104403a41c20f001c641068161210b04d4100926140d440854030240224500500b0300c42c2e01100090b0b4a032114011104c070b20b5007200440e21196074516000705100b03820302020b6009402c28a04255122800d01664444810707030300c58150301d42d0b600007443c0b10608000c0c400d40406461b042495 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 862550071 1250 862548821 862548823
    0x609020a050d061e05010f020c1027030b0c1b0618010b030607021e031c051603270203010b0415080d020a1a0702030c0d02100501050f01021f0e 63
    0x16146165071981510744007041010801c8a0b4903600050490900f1031110a00c500b2408207001034440908210410641201007240b401d00322400c96138010171100718000000d40c04c064242200b002150b800102e400f03000341011010a064031000305440c00039008035001c03a400c06d01800b0306c01c00e600702c03a1640b803a41c2103003036240941c01e98903034056480150030340144010a0060790030340882940105036070b00704901d0003552008090410f0040301c845126a404840703003030081391440f001c4112070b6404007120600300001048255040800401c2120310300600078064000c03020a071200300765007003031882150310b40c3c0f10000c84400c08a078155a0386901400340e0741e0314820a00ca00c003600842080040c00c09140ca460405112000010344d07000d044403100050204500401e103400054000149850344c02e41a480c40c055801d007000240070781c0440c8000640e002900d480580d1251400b8411640d031102400f65580d6610110341c01604941c040c9410709d800c43c55010564154000c0005400364005009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 862551321 1250 862550071 862550077
    0xc0c03060906060504022712030408010516020f030a0804021507050a03020d0219110d0f110a0b0406020c09190c020f0c04061d0a090b16200304090f060902 68
    0x803254981d0758003442052003283c3c81110050101590704501e480003443c101104105a80700c0e08280441140e108041601e401380011142e0b003078482181d484d20740350bc1c1e185001e000e04540d14080d0b0701303403640d90b09200c0d480002c101c1500200c0e10051440d0440441045400c4d010040040c3d800004a040901030880760500034181c403401907019040182252400a0810042098900440d8011007401c0c040800d180270300c030f1115600005900c1410314503004a6040c202c0b1840103402e80c0c603013910b200c2c00d00040500345c0d40c0086040b514032480d00d4035000117440a0140c0e0094400591201c040d50303a03203090640300300b600316400460810000508080620903101c51664080045e00180c0c11462909410046180c030110f04840510155060404080640700b261130030000c25044a00070a03504441070340407200305504043c10450b02d10302450000351211043c08650b0014208694001003a52041c0840400603035820142d868580361203041d03405000001d0480501c0d50740c918000a403d40c081c03000f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 862552571 1250 862551321 862551323
    0x33603030309020307080601060e09040f14030c010b030a210908100225080702220c0906022103060d060609051f0b0c03070b0915010605040f090b060412030c0c03 71
    0x7011a80e080e0910601d4100300c4594000c404580c0714000500903a50082003006440c030b41501e010300345076a00e0410b2450500000005000e1003a061620030b21001c0120080801c03042000007840716103651014556152042d44011788a1501403007086101840c040140d407007886145409883c0c5030319031403038030b04204002d102007401d103a00003030203610221250518080680b030594901c80c6c1340d00a4441504520888078000e01c941d00007212440c9280d80208140c07888541d401d010004030300c8856019049451900611002d88a00d4010782058000e07648090440300882c06540e0031a100c1e10f041c0080020a4202150130940710030300458080380e9486100d2095040c2900c454040e4035040c1c00300c0030103919400500400004100403039400741d00000b21660250301c060900d442e5507441031071600f00800d01c0342e0046504152400045d400d603011001d4400c1d52034045030f5100c850343c0c9914050031143d00143c1e9681184c8140801c20561468001c0702000034001d04026203003014696903000c0c64003081c8c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 862553821 1250 862552571 862552577
    0x101a03161d0909060a060b090607030302070c0f08070e060907120b0d050f0c0405070c0b01050907090e1003050c0301020406201204180605040e19171602040b01020a03360303 76
    0x100024162107000d00d100604070240c12920303201c036003404549c3e107204a510103000c0c10f40000c3c42d1000c0040c900607007402000300c010260b0015848842c126142d0081e40703c4c01203040310301c2e8081280c61a141307040500401954035100340803a001e1000d0f402510902100c81d6008030300b4500400811014030940c0408a806406007580750400e004100c21141d01520030310030400960551030014940301c1d000c07810740344115000389490380c0d840b004458103410307070b0448004e00f800481030280813030762030040000390703441503044d685002805405d05080340140d2184074002060000024a90101648842c540700f5514054030000400d130300034868103a205a01260783ca48405480b440d0287d81b6104180142400715405e214103040041034039030300e26940c0c241d10704003088000c1030f100b00844041122201200d0f4010242c407188180c607004c01819061000303034059810110b00c910191320115607111703803aa140e15025151020181d803d000500500365110525038484101040e42c24429100001180700b07075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 862555071 1250 862553821 862553833
    0x11030a0806101b03050904060302040603030c050c060c07050f0f09180708121801020f010c030b130506300627071a070812101a03161d0909 61
    0x3824442c1d1407a4441c000410000c0d00282804031888010350191029090f01d0215103d8035804005001072180741d1000b58040d2400c0c1000007015004001940d40a0244040e1030210809509104c1e8a210344500c1c3d2048e03810265043c0300324501620b6800200001402c40380d08203410f4008107004603000c1d9903109a100c00729803180c0b04007100b0810310018118a0303001c3d0000c09800c0607581020f02501b012104800017085030b0200c6640b0030050341c001c0c24560802400300f0603c40d50080c0080485c9080c05000c3c948080e031307070044410755006080c0102030103000f0b0b0041d5807803c00c1c1d440729400790a0400c950740581c00c00c002207420003081070354010102d002035442100c0003920000888845000d020300130760051402081502068800b40a00044a800b002c3e070f0340d181031501c4c0c00503101c1c0b01c1c1c80041c00080d00007480441c12151100710160307106403101911900c81402c8101c807a02040b15081c590801e440041d000c450710440342d040c0e1411070a20341d8030f142651000050306040048507602c0e0240c0c0a2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 862556321 1250 862555071 862555081
    0x50f0c01110304080405121209041e09060e0c01090e070e19060f1e080103021504170319090e07030b060c0604050a11040b0307030227040c06030c090e04060c11030a08 73
    0x41400013000380d07900040c8581c0c0c0b411180c0230143c0c00f074075501c03d2165a54246403400700d0000813100e00303000e50710f08080140400f075241080042070303541c501084602c100d40c1801d0302d80d400380008000b40d902c00b07440080e00c2c1e503070b42800700c0b841240305c1001504001c030541d81043c0400f403040301d900502080d41700c0510f2040c02103c0180004c071001200340e070300c01e1226a0081d6007a009403910341982c1e01030303c451000500c030101508042c40b85600107800071000a2140c28803100c0407014120504402e102e48590b00307031401c0c2c122071030300403170095180b0302c40324001244017203000343d104c0303116204050001810b22040d03069150620204541c01c0e0341c550408905176040007509681500d0703d2000f244c00b00001c40115003c2a07480d504c60200900641440c1994144030480700c4204422007203020038014245424549031040304003030f1207010046400c114098070514001d1000700309851007122070401d00da071180c44901c042e0146240c40d41c203014070030138915461798052004101800380c80e196610309081c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 862557571 1250 862556321 862556329
    0x80301060305360f0304090510052d011e03020304150e0703061503050109050703050f0127110406090b030f12070f032625050f0c01110304080405 64
    0x1005150202c11003920645800300402c9198450315009540c560380712845600d41d0340fa1801c44803504150061001040c0021515003d4011500c01c2e0f01200b5166103003640d8005010290626055a19a450003c0c80b0746101801ca00b0100b0a420414500040e01502c1c0d050f01024603401c9104d0030001a80000c100300034002c482a0345010501541402c00c1f524a441007401c1d02e034510f1380401031150741c45540328007003c000c0450510107150840020469854940380160b9a001a0b10040b2840c1c05144a4111a4101803294003100d42000100742c491148000500200d68800c4500711601d6200048106042d03c0318425000038041c0301000064140050341094503108051000f1411035000800d41010002800e080e101125400401c101c0d0701e0142e85005d17141c028810021a004290076540840d107000c8074250305015064440443c03607410503c0085000104000c4410000314608100036240b010740c070720044c2031443ca000300001e0780b44180d240504e1141e0058606551106000c28140014a8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 862558821 1250 862557571 862557581
    0x10815040c091e140127090605030607110d123e03010f060315091b03180c062001020c0109060606180e0402011e020105010303030c0c1a1b070803010603 67
    0x8140c02101090070f260a000688180d04050003034104203a894a01b4425106c281422807181c04480d0401000d54031001004000d1a1510a0f83c1c8a03109040200350858051880c201c21020b2540281c20000100d500c15200005010f001d000511b5584000408015460b050944d16400414410210300c20070a203440d500d800c80e80904081c890100010852000d00581036003c644182c10082001000070389840d070440480c1e4449000c15003800d60305521800802d019aa600301d054404009000c1e42020307084200301c0c0204000c250400070743d030512640e8001c01d0074114860020b800b0308091000070315030303900f03a07000044001181c0c0e44604500081144a0040c00c000d0009841c000d10150519031400c09200716034071500d080856040302080030359204405220b082002110316140003000000d0082c0244800d21017038000a150400c440e82d903d21424480b21843e8004d6085410010824001c1c010054040d0004049020722502014110000000380c81c044e4001c5880039220761500754064203881c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 862560071 1250 862558821 862558859
    0x9110118060f3e1515031501090203010f0911070308090309150403020916080712090209070503040b060303091305100f0618050102030f0a08130615140915010815040c09 74
    0x41c110001131440244001d80309a80155a100c9200c0074100c6400480c4c1021000700214000203800310000c502125150000c50403104010340d03e01d0b1442d900c13080f0b0300c00c0391038001c241406580704000040200703114813074507600311101e041940d21f0250004002061110616550405407501003401c106505e40346241e664410303014102000b0012840000401d071650041c588030900c060500c0b130402c0d020180c2c1c00b00075501d40c0540107030743d40d007062000589542c0045030304642181c61040041d8890030007000f03407000d0b5240a440c1407031103c03c00004401030000200344501c410012130740003540b00d1100c0902c0006000076111000801480d1405580b1914035401090540d801000010b032241c003400c2c222116401d0618004a03d41c0341c08410194050f807070000034000038140076198600039026400501151500240e240f8a40b060708180704211300308951007140c504001c03401b03500d607500444805034003a008005107502c4100000c0010212044008140d0000f5010401404450748010a080b050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 862561321 1250 862560071 862560073
    0x50307290405180a060305030f03010521030a0e060f030a15080601030201020304050111010e0105071809090f351b0f0a110f04060909110118060f3e 65
    0x401c1c1080b010500310424125050500002a80000c20191003580b108024591100c00e40303030381e00316001032100c042d002805038910803003258030a0340a4103019008a00c1015000c1d02031801e103410702400742c40b04d0b032031802c1c3e00303411080822119400418440003580f083e00f40c1180050442004c11444480c10780d00e03000481c41d80e1001c401400541c7c0c0000c03e079000c99000340b0713100b4000410341c0c03400c0d400350400e26403500300c031340c24902407110903074014551a820b80b200348000f9692680c1c1c1c1030700c0741c2a80c45200e00600411100c0d40d0f8100429000341e400071800761400c0d038011800680d800175a411a02031200c08001703400104204243c1007400b6403151504148030000d081030030392941d0843c0c654100c2c180041054a0004c00700600d5240d04868a0301c02700010400c008042da5849403002405010101f00c03040ca0303403004050800d42c0948150740c510411500500c1c001c0b0b0601100f507130f40042c0320600c6024081c5003022220301e6a0254200380071602d10128092402c04000f00281c52140d445050600c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 862562571 1250 862561321 862561327
    0x2103010602100f02070b07020a02040f110405060c03131d070906080a0e120a020703120f120e0a02040912031422150504081803010b060403080a0905030729 68
    0x3420381c002202d18903004010303400210035481458a800a2040c03c030014102103440b0104404140c022410070030b014001c1c1e070107005440c0c00d49000405c50b84012099101c41c07406100c140701e54108a4054160204a40d0840e40b0700300c0750346002c000c0182070760b000da0440c030010366a50f030a0905086400c1c1d001036580c1000d070042ca04055010b050b60200802c0900d8096840c0040070003504104480829545e205003c2c035030341c0300e0041000307454010600064a034401025440c0e680244581e21070341403402e5982e503040e440414440500064072140c0341c445004d1064103109005661030303115100e4a5403140464104500021601400f07030303210880d4070032540d10802c0c10010002c0c10031042c003c02481c81800720740100d00b18a410302c800404107080d020304600d08002c000400802100400d40c6124402007040c8402c243c0042609a5044181c0a40c01071030034007041001500080107000707102418103103d0042d903105c0e40464500900b0360f22040d10480801070700c4881c0d15803445691032104400244621b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 862563821 1250 862562571 862562579
    0x12090f0f0303130f020d0c060c0308090609150a0b0405071d0307050105090d08040e0f0402210703080901020109050d02010506012d300506011b05060c032205210301 72
    0xc0680781880c002c4d02410304154050115542c41814041c00e940c4820650003a179115580200f543c03c0c000780450100e04030310082851078100007000c520444100d401070807101c00c08405851869009000c050100391070309a1800d0711f565070f02405205001558403881c0c0000f20b180c3d100d0366012076610441c0a82c120070014880b599004049668040003541e5004201c4441e240c904050303c171b01d9001d00c0c0c515090106021142d0380b084c094038003c60084850161241500c0282000c0c1a510322201d00756600c00c5408100050070000a0007030f2640500000400900701c2e1545410700c10720074203e5006035503510800c0170b02e6030404085680c02c80000c0c2c121400d602c507495050404440381a04200340003c0052106e412400001e883d000c0021249141245141d0801c500d40031300802c1e01c846001c241405003071156141c002100d6005260044003c0c802a16209211042980050102205000d0958000008a800348000b4003142d2140004002c180701006801d001d03a8400c0580032041202040104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 862565071 1250 862563821 862563841
    0xf070b0d05072d0c06090807020301060f080c040c0306051c060e030a050f070c0515030106030f090305070f050f0723040b0a090c05040504050a0203090d09121712090f0f0303 76
    0x10310f2512904107032192081c4403a05543d42c908078900245824200b145101c10804004080c241144c404e030000c1c844580c8488125806ca98280503400c941d0b4031100e01c580d8246415040740403413170150b041c002545074450303001c11100313500a50b40c03c0508041c80c083d402001224801c1c81c03120f4603840301842c2001c0000b40001d00a1003a0701c88089006030100b030010034449003111b040c1c010074000f000d1402d2001c1128208066410912a12000ca440c00d204003160300003074010702c10990361603070310b092521205075074180101c0300101c800d803200c0c0301b255a00c0b61903541c1080070901a01800a0305085590f01d01100e1959041c80c0d040e15008030704015a4a03541e03240c0b40079240568481400c041380e00c44040100300c80764000c0d41e00c92503206007010240007175420f05500840c0140e4074001a55a14805006d003590640682d201d079005210780d400f07066012400380c030752101040f01d038500754a140c0702402d01601c000d14420385001c9400d80040300c904001301c4082145501042403d03020f5821032a0200300c070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 862566321 1250 862565071 862565117
    0x8060a0b0412081308100507080606070b04050106051309020a08031e0309010905100e0d23090d080403053409020304021f051b0f0d0e01020f070b0d0507 67
    0x301c2c224592559074108200502580c0316194040c0000c44070035525400300340c0d545801d452002103240b8100200700724600c9941118403491000e40402e01c1d00500b03980b5803a0341c0400510513110703550b8800001c141e075070b0b90b0003802d1803490100700041070000603401002089a03040c1d01c2501c46074030400489405688050311100c64603484040030703890b0307600d010505005d01a103080040980c000c80428024045507584405a521385480c04c0700c040301c12a1905840724405054075004004440c5070219642c8414401131801c010b02a1004215504070364442d8000e0b089904222180d810200c581c044822013451f42c6494209020f0320781090489010f5103a6500350740e0700807520700b59000030008065482d0740c400c02c42c0643c0c001d1407d00e055102e104000380f140d001090000049010400d20903192107000404590041c40a00074114513400d01e00251485142c81400e030707040d40540c041e0b1402014040c080c148c001d0016007800343e50f500c550700c4e0000403200001c050200b48041e41c214005200d080b1110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 862567571 1250 862566321 862566329
    0xd060f0b120c040e0f070305071d071403070203040506071401200d0c05090621101a091503010e0103210206180f2e020a050a030b040902061908060a0b04 67
    0x10340d504030144e0050501e881d110300304500784500e0500008210000034600111090410030354146440c6503c408210081a00c5ca6400a241d1a070301404a042540043d60400b00c0f6004484c589a60b40b0301094980d00803030b1068403456900340d1240b199107020f00481f207800340f110041c0340b844801d403d49411680a900c00c11300707041e9602c44c0007c448501400071030340300340001815a0307221081720f80103480100520091a030000790800200d148045145400801d50707221002060002c07036080b82440060b0440b000c450b500c051a1000040d4010810000394041c0041c2c80c000000ca41c110b05008440030601450a03200000c8002c962038070642c0801e5050f045881054003a0301e21120448182c0b070b00348006400a41c5004240d105030000795400303190304060700601c91380044581822006012802140502c501041341040741e141401c1c4250311514030010020000121001070b034011400d0303a0408900c40d40034442c0600340a6040b5000141c040c0d10060803140c0320402030a1142c0380c0a180220302c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 862568821 1250 862567571 862567579
    0xc08100603032106090e010221100e150a030f05010c0503160318051c02160b0a0f02070e0415151a0d020c010510030b070f022a0d060f0b120c 62
    0x1500b0a6000340d542c008000402e0b41c5c40742404003540400100c1d000307600c4600d03074829208a0711458010b15070183e440a2050442440e403401462524114900c0c410009010380015040300d02c10900319980c880e2500061400340320040301d04003d030300e0503508481c080790710324003845401c5c010000c90610002002d1034010261030702060101101b84160001720b000c0200a1140c02a1700c40340004002040304c2e018103040caa400ca50980c0860f5480a41041c80380c0500c4050710350400c40d42080b103000d690055031112182c811644640d65400c000c0500340802d5600320344c41001461108000e0000d030044400f40340c0042c201e20034203858898034a54902d0a0b0b1042e82c80220045040d04004401c2d50598080703181c4080280803501d0400c00c1131070740c2172860104a40403520940031483c3c86214440f00c01005d00303590000c10300790740c0388410641440000100c0080562140c8420b0351151074030100c00c801548101400f240500a1024650550b03000d140c1ca113015182140140382d502000040e403000d0150151 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 862570071 1250 862568821 862568867
    0x114060c010209130c09090e0606012105070e10031e15030b090703021009060804260d0c020c030c0a090207080f03040f050c040903020307061d01090c0810060303 71
    0x1203903280640107402449038840e40200c1da1a05606054202203c05005a03552052a50b21030401e44200c0d10300c2d8a5800c9180c3c440c1d030001e403441d4050344400030754103a00314800d00da00a030120f402c000c0d604112501400202d044150350114204a0041603142c505414144294030328908038440100012800b01a0540c170303030131030216481d0100e04640c003550304040c46003a00c1c0360420445541d4201440201c0c040c0903110406c1041a03c80d9849000f0307104940d4451909450b65255030018014003038441403c240c48420328401c194101004289800300100c0100d002080c4040190801080b140c089000740c010581c3e054007640c44403403400546504050050300c40c001c500700114540168000606102000014001032101ca000c10040703c034801c1003100d070248a40d2040c4000d03101c2e03070040100503030703c18030000c0d00203900ca0f0010340700035000a0702040c5522272503030401d0039601420426a84c0e4114a0014040840c0a100340c284c113181107003091041c5813441d50000c0489040e68070740c03d0504030f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 862571321 1250 862570071 862570087
    0x40e25050a0b030f1b0a051207030603080706090302100203070e031e030a080c070b09150105041a010c15180c0812220503010504060b0319020f060d0b030604030f090e011406 76
    0x1d44100d4080b17a41949180380c40d43c2d5040c50242a03a800003690943d00c410410004801d903200f40a071030140ca5000c1001420900c1e240e8071003028040c4448200e0641c0078103149071512804910240d841074045a4440540304c0240c012b26050074044440319602c0c3c060a5402d00c1ca54800100710b44943c0d0300d03490404455525034121802601602000500411000041c400902d200040301c10256200078a80d28459a852007040100c07107500d100b900604000d00149940b543c010060a84420302802c4c0d1070402240305200034044aa04841d146003001d00304030b5140512200341d003403d020b08a80300c002c040c1e50840000108860060341c080c690744c0190f0f24200411240d10f00040401404041d000b8001424103240c0900903000c26482c1a01901c204101c000c40c20040300c6015500307a40281c490300b03003480c0942c144440340d4080101c01003510784070305504005440400c5030510840c003d550b1011203c2d241c2200410714107c40c0c0c07104541035008801484000044d4452200c26441203030700030355903580c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 862572571 1250 862571321 862571341
    0xf130309030b0901020a090906150f0c0b01081c0e15130e0108030d0e0303060907110a050717060601090b0904050a06050402070f03031b0c02040b040e25050a0b030f 72
    0x45500001d00710382c101c009100c00e4035415005403c8141050f01c42e15802d9481c1c070241022a0154480c080e015060f24102c07041d0340c0c1c0204482c0090021900d0452192052078580071100302080c0e200902039400401c81e48002c9650306519004100c1501c1c0400320002d410000500c0e03040c0031205101001c00006041d80407107031400e100f100070b2158035403141780d07581d407120010b40703075000350208900c1d6a003400c0d120b0400d5400403003180c0c811480140903100ba900e81c00c104888807204059148000d11880e2202400f1a10420040e40104201c1038000d034480c1e20f000089041410251046052229450040c000e4060500540d90401c4003540c00080950f40d0001360390107001e682e4001900144001005014494130b07101c5d40070880c0c080d843c14004941000d42e03045052848441d0840050210f404100061074260448103184800400200c2c03010880c01e0141d05080c003070000f021843c0010303c2c0301303180b004141c00351100801080b260040f91600c0e100c0e00441c01e2200400103900b950b080d07400038483c40c0e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 862573821 1250 862572571 862572587
    0x3051c110a1211040e160e103515060412050714040501080616020307021816090609090e03040504020a120b0604030b040b060307170304080c0405060d0f0510050c0913050f1303 77
    0x10b0000d00c15014041c9800024109e03094103030321980c451200301c2800315044811354070700405a0f1040d22004140d5075204094158403078040140e90b001c0300400c00020a0f07881e64014000d03007402040500a0140f40c44400012180d6109400380218103200041024100100f902070340400b81100b1640c4021106c0012030542c4901200254071a52424540f8880000700581904c00d4100d40c1c031901c491886000c1c1520465168030500c400195038050603c242401e54000340311001e0038108603810b05484a00090030717604012324901c0000c400c100042000495405007a0004205139040c600d0241180c440310044400180081c1090780c115011520b20f032002c0005170010410300081c01400b0202e800050380b03a41c814803c03403400d8416000605030501d481d02c191401504020410358011419680b00e910140389104196101d0194542802c2c25101c0390096911928448540a90b40e85240040244906801c1c00046090746401e0030040c0092400c0d0959400014075109580c80c4800d034a42100d81c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 862575071 1250 862573821 862573847
    0x30408130513020a0e09061f030f1803120216030e120105010b1809090d08100b031302040c020604031d061c2703051c110a1211040e16 59
    0x80c070711442d16404000320f503014101d03415261340c6420f0040c1800c0d041025250702034801a6012908001a880401c50355000898041e200d0602248003007448000030115020301522034909058000000c0400d40c0c410303446422040f604004604000d440c006030001c900800c1c0d4000e09200ca400100d6016a0752140680e03000c00b101c4000f0f1016617102c0e1b009901c0b507003003d426103921805481c40c1040900d0003c03012441812a80018100e80c42c0c241400c9034400006041051280c494160100300507480c40001c52150b4092881c00342504144e2040c4070407a80070040383c50131900702e10305200010740d10a140303540441c02c05c910141c49150000014156100e15010101c3c2050f0044501038407074103903080000301c011801408405261094403a07042446c03001b900800181d0b04105406041c00e040d03400d0315607190140b00010f500c04200305070040c66488158900041140e04800d1102e401241c0110b03c1110940c3c607400f800c0ca4582809400190400380c9101d10070000d4000b42c0e002680301d0b1000070130751 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 862576321 1250 862575071 862575079
    0x6010e0c0310050d2d0308060603060406030b090c01021002190e0312070f020901060302042d0e0c0c0f010c05040501030e0307021f08060d0305250209091501120203030304081305 78
    0x89906283c8800c1e180c00034060125446486205e138421000003444061119805071500300155035030383c04200741d0790b200422456105556130b0000c4041040d0002251295522100030306003100e2020000e450f00d504608054021801001014581000c41c0c004401218150410a00070449100080e08059a250292400b660041075440500c000700c01160200c500036140e490b0a640c03206002c42c02d0b07100702c0c00380341e00d803030444618454562040c00416032040319105802c028192a100d512071045001c2e0780000c543c1d074010551100ea00c005000b900301261144008100c0d800e035050300640300340298410079041c107a035913155000400c0140211b400c1c2d103500400705451070340120300300341400074552400d1000508140000c1c0e00e6041402000c1e0343c0940580f903180c01c0824800160320f00c0c1041d214209a402e165019040c01031701d600e40307140c0c043c406090281410035080300341150100742c160f00c0a010304a443d0032800c05a1404400c60350030540000d04a690341d00d0054401c0e0716003445030f00241d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 862577571 1250 862576321 862576339
    0x6090109090c0c1e0b01030b1906060807030b0306040c05010c11040609020a021618022b0203072a032a03020a020906120d030b1801091d06010e0c031005 67
    0xd107a10414810316644a01401300c0c59001005010000c3c00101c3c0d1300903c020b24030401880070506203100240c0c0950054400700c074283d134410005003516083c0d481000440c0200e0140440e0039054041c46024210a4004003124034141d200c1c0804c2003491302c00c46061040044000c010b000d44110001241074016000340246952013051100070360009a14400500420030004403c66035401201c0c11078810b0202c00c4e907072009088030000294412907120102c1d01210710043c1103030400803045000002249030058480c509403002800141e031418a04407550810030114082e44000346007404030a03050b00d410a40e529900f1019181d82003984110340542c89002c800004140e0300240c4011200d10036560b50303e258542c03800b4001140780d10349481440f90016101d000e03419210b64400158183c005150901c0f40600c4500082200d4080c1c000030841c13611046e20302c0074456801c5210070241c0e41d11008010035890003003220f640140280a4a03e1a00000041641543c40148a002030400141240f071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 862578821 1250 862577571 862577591
    0x20a060e06010e07050a091401030906140103051b012001110d06091a03030d0b011404090608010b030c0102070e1320040c030c0c02060904090f080307020105060d030e0609010909 78
    0x141d1941d007445000c9a44002c2c00008110341d04c101c0545802d8070542d12580071260502000c504003444440b2010b04140d0340d2208000400c0c514080c00000c58038000d000300c44c0b5410f504240e07050801d46045981c0070300b00000e0304900d59a00441510004c9090030345290f607403482c83d010b54090803003411103082100000c14070b9503841d4035079805001103a40d601d104119050404000016a021a0200c075074180c006000c400318281460308200d403041d0052400c00500150050310810303903081900070015190307445d4414045c0100900c926641d04000300c0051800080c1540000d596510601812a03009100004504800c02c130013841183c59902420b480034429600d4550f44a042801780003c1c4250704100312220020301078401c1c07001c1100c2e0f42c0e42d8105607600c150203100013540080b054540182c1c2d20203c2d5408580c2490a0001252160320314598a06280134001c1c05e503030002d4540c9106400d01c04c02440020782001d0351600480003924155201d040110050ba803c00103580719072480c60070404401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 862580071 1250 862578821 862578823
    0x1020408030d052517010815010608040611030106090f0509131e15141f271a090708010503030409091b090606120e07090e0a12050405040e0c0306040201050a020a060e 73
    0x1043e1a40640105d00c0c10381e995002e0343e13541c2c02c1241982d0000d00140c000504c4203612880e52030358130130301944c1c010408207603400365204542d0099201b40700050030840240022120301100314020f16080b603080e0298108001200c11a02803104024207500025040c55803104551500140300d40e00200d810f403451444203021009019800801000e1071003c60003c4e03400c4c42d9000c0c12001240c1440c00d291191814a6080d24500c400540c030104403403107148100c10418414050380e0840302d003205054181d494101e06101702c0c03410141080c814000c1310300c0140040c1d00c0002c2a24100c44001202050387c00b01428201c2422140d0000c0203565509403c0202d20b6050a4020700102d626aa0360070440714003a10019085501001d40080743d500442e900308a4246160402c10b81145600305507000b1036020354030380d9070721520407442102003000401c00700700c2d51030b091144490511100002d0b00d6401030b82c10001e511071000901c0281880004210a41e00c00e20800518140b668410f10811000413030710030003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 862581321 1250 862580071 862580087
    0x31f0b1c05061c0201080601020f0303010308070507062a03050d021201080c0301380a030606090c050a1e110f0c040f0902150f070c0902030a0e01020408030d0525 71
    0x580d4045081c040482d80a082144040000c05070140000c03245810a500464a058018083c0350441c41120550004040240002c5000b036208050301965203226290541c104583e561101d070a021078400c02c3d01310801842404031409241107400c443c1c0c1c0c55030b850291514003503500d600c51400e10203d56498401c030300800040c16184510106c2d49055002802c0500342d445022400b20301e21036101150240e841e0190550304800a4820302102e822558408103041031555442595150b03210901040750000038800c580c013000c44e07490701501d00408050040c045007088820072441c09000100c000700e944c461995205012803035401e4036160007540d00104e036903105085105101d6841d085101c6020300040c441c00c8030043e070140602603441241070050045802051448110b500b04100700380018054524200103481c00d0701d00140c42f8240014050111007003101056030030303881080144104800041900e020244285c804202696100740c010714007c01480c10034a0140312070020103280703400641d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 862582571 1250 862581321 862581367
    0x80a3c08120a060506090f030703020415090b06161b0f091a120705130f0504062c071203020c0301020a050a180509131406070f0f0311031f0b 62
    0x1000c0d08540b0350840c1401116210302c1042e0b4410401c00c1a0b0380c450400300c1e00c1c018500d0000b825202c101e0317600d0b00400c081c2c481c081c0c080c11540703036020428010808184103445100d0f00c1a1041c43c20103d500001d55806494110088c7c41040c00784140200c14001c0a44c00001d040b548421031480ca6840b000c120107040700541c0c5040200b0450003160450400b8a03e034164889000014a80c50349850305000b900600d00c400c03040d413240c40d04003c1c00100c400340501c43c000c91040c1000200c642800400d00000c0094200c81b00817036a00e290b11a626500008500c0140c81d40400718038103d0680b49410b80c90070745111300d859019400441c1400502da00b260240044103000c1d15602900c800ca21040c01c0010307480d00455601c8001a404150702c404080341c01100207100b0390001012184051007180b400d00f0440f040c00014180102c86201190f01c95031041104040d41814491600b0310046154140401081010407618400004440c0c03090712012400805000c600b01d42d54603140d500701c00e0300320f01e0402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 862583821 1250 862582571 862582597
    0x1b15020d020a0c0e06030a0b040f0209070f0e010807050d060e0604150b07080f1204050705010f180b03060103090b011e0e060d170405060a0513080a3c08 67
    0x10305958018000316012102c250f0080522291034248421000c402a0180840d6050b2164186020000710860b4140380181d00a90140a1000d07261041144101c0c004102800300118034003420102c0381c002c0410078101d042420a80901d07034604200300c505010310380c40d40a100d401c06000203900c0340d0b01080c05029800503038080c0016480301d00b001d0080d448900c43c410400c00100a61030201e0241c001030285134012245c681e240502840042c0d140c548152000e498981203a00104159a005101042c49640b18202404100402c420008024911780700700e1402010002c0001e00e6a8031940c0006400c1303500002e04101035031210880d910f1003040ca50000c40c500110303c400308482210b5840140310300401400c0a94801d80340da6910b0315040b4624000c44001030501c0f021409580b00405418142100d079609500d4841c40c5841100300341950340480d060b40c0008804a01048120158000e0541480381d03d07d07502d5080041100c01d5049003400f8150320200c4480c407000c201d800d800400001e90019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 862585071 1250 862583821 862583833
    0x30209070507020105120601020a0204240906080304060e031006120c081c030207060e1015120b040b19060e0f1e13020d1e1203090f08071b1502 63
    0x2100341d445201d00400a80414014420800d1021007079248991011042c8151003002e802c1d80e000c20151a601005105018001a81449000c00c100149401024070318824403113186404d00c80c944030710890064204114008180c0c503159101000b8440340e00d41c018a04101442c1c0d0b80e01d40c413104150b901030072100ca55400c1c80000d00e0020014107058403120000d40da04807002803040540080d40042e000300c0c0c01c00d841e800d00d0251030006000305041500502000305903010810116010700c071741c682106030000d082c0d1007910003040a024680340e015034425000c0c1560740740d58140b01d02000d2000603103e02d0901780000442c0101178000f410b03024030009011901991111190321284140340c200d5005461440000541800b0981d03554181c02030001d000c018406801d81caa807151b2000d000500d03881000300c001110100051048000b0003403040780380c10491000c02e0364605052070360200b0007910015001c80c0b5001442080720390082c0080001c2c1070040c10a544100002c25000c0514010300075000721 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 862586321 1250 862585071 862585081
    0xc0f2108040c05010804050a0501141b0403051507051c06060e01021506060a0903060f0203160801030c0509341b02030a080325210c08150f19030209 65
    0x2901114000e951002c0c02100080c10007004640d411002402601d1502c44d4442120100ea030070f00c2801110503800411107041d01d040380303441488001e01201024000c00800040002c07401c041840c022076180044500015112408102d48a0042000c7c10000c0902c00b88110303e10304056015000719180750301d4010036403c01c0801680c440903014040c05070038040400080139468000004c0c490a115030038880100c2d07480782c542c80c0480f00041054241280e0010512a04005048e00b000c441c4c503980ca00a81e46606550ba900281c00580c45054010b5541901080440703803400ca64501c05000d40110000e20003161500e0b54410400c501450003040440c450500d90300701032002049856000ba0042200300451742d82c54485500c01015442e0025804c214804150301c1404e041030900c1e035607962200d00c000d100100000710300400440041e8039280074544c0c100c1c190007500c8540d20107040c16a803030486c04500042030181d1200c0440c80c4d80001e44030492940b5180d076082d2070b025a4000e44015115560b8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 862587571 1250 862586321 862586327
    0x3150f1f240309110d15020a021501051f0305090703080a030c270506070501020d14011d011a0c010f051008011b0512091216120207060914010c0f21 65
    0x240f40003400c840340941201d01d01d07007020900c1c820040d1040000e0340103211b40072003041c1243c005004800c0160000074800e04000099081036024143c1111180021604241442e219260501d0b0080600d0b03100c40024010741c8040c8075400040d90441180340c0d071241d480340010000d00c807514a801c0810701c000b4014846c01d031001c2000c01c801c2e40342e000c5109040d00300810440142c00403402110259000c100c160203e4a00c1d0041c1c52802003001100c1446505244900150300008000900924015030040010222200c0800c030b40e840c1031a40c9598552503900703283d024181078501021000d00300382c10b104480c0c1c03006d2050800c83e042e00c40204440101d1100094521054039220b40c0011014030003110381139040381032190000d2402c411104060312501c49054503800508120740e80014100c2a10140006400c1c40718140382144080d0070403070308041c0081c1c04010300c0d0140d0703813049200c2021840141d00030100310400b00d8110007480c8600310329241c010718903070450150001c1584070a868008040c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 862588821 1250 862587571 862587581
    0x12010b010207090902120f061815040b0a02120705090102010c03020702211905010c08060d03020706050d14090f0c150d0c0519020705010e03150f1f2403 67
    0x190581c040d14800e450090f107807000d400c20f0038060381d0089070f810a000111804003c000c214190243c080d02c80e071b00d00700c01c0fa07400c0c00001e401100001c0e00b180c0840e06490901b500c1c0c1a50059018564a04c203441e00d0191800a00450080306c0b4074038192020300041c02d812002170310800500340e00034410310014070b50440036070080707007402500a20000300c5503590072524030a288145002004507201000303286250300042c4480031054601c0e9540d1400604841c1e400b0403019400581500c81d24076213010740d82c000355034000c80e200d5182040004550200041c0c180e0b040440541180048420103080c1414141d4940308140042c540c1d0303120354500d1041900300b8a0340e22146500c88039072641800e81513200c400140800c1d00204003003000400c41120425408031480c104030780941d00900000342404000351188042610040c80f170350100300c9000803410703040989036203c68080b424103426215032498015481141d1002081c1e000c0c4130344046100d00c1d00b0707100c0c400d02c48000b41d400740c0b9502001109908a030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 862589928 1107 862588821 862588841
    0x70c0f060b0f060414040504060609110904061a18010c06060b03060901170c041a10020d090f051804020f0405100807050415060c0305040911091201 65
    0x7402d203203507055110001929000d1516003003203500c01c4498415400c0920458131040044d040003030982000008192030394051042800c00050b0703140c141c1021300d449020314601354000895000415a0344a0a40540c020920b080c0e0601000b00300c031211141b219061115010140000440e2841000006e0003141050782c1c480c00c1034002c01a83d0745041e8461310702d014071490382c0049000081800704400404540009500d42400340c00f11803401c9401080741d00008144511401d03c3d00800d62080c000082d550b246415501e074060304800c0300e624001c0c1c039005903540e101d00c3d052403d44400e0395005400105290f80880011002070183ca0003200c0002e14080500b004211083d800c00002c0087e1408a138240240c41c0c010088590850903841071500b044000d00c0c0d40802e05d0f000b0303001c450241a1380b84013401201c03200750070760310903501066450b80900c10101c210400a6010711500c1003003 = true := by decide +kernel

theorem cover : BRFrame.Cov 862410071 862589928 := by
  have h0 := BRFrame.cov_init 862410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 862410071 ≤ n) (h2 : n < 862589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
