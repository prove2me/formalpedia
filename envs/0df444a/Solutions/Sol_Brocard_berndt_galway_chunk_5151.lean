-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:55:13.007425+00:00
-- url     : https://prove2.me/submissions/cd070a1f-0146-429c-bd03-15ffb91a20b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 926258992 ≤ n < 926438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 926260242 1250 926258992 926259041
    0xf030408010e0705040b011b0609150c030b0301110d110c06010605120105030d08160c08031501080114030312100815070e01031b0c030512011217130612020904 70
    0x3e000b40c1d4010074003605c0520111a240001070569040e03401e400ca0300d140c008180030188281500000b40c8141c21401c0000e00d69181503461000d003000b0f07101d01010a00308001c0c250541030510881c510070310000e10041c100b407071751030031342c8e001d08914080242c03251030920109240420520001e4020b14064a0302c1e507883c000b8151540c9a100142e2000b442608119200d81303480f90484150790303100d45c010201c00c2c0d08103904a4143e82c00c0c100707107802501d44c480c08030802c080c00c56a0354286010344801d0f00d0700c40d40c40e07907901500c01184490030106500f503002030283e07201da00c5940755895080080c010000d010a900c1e4855245003c1030071104011f202108014469500e800240705c2001d03050a00c0c080c88100c000c01e8401081c241c11644900c1001911182e0105251040c41940c00307602c9211014400d9595031000862001680c00c000c1e40d008400700014001c85907800c00301c56485090f000200142e502d410381c20340e4030300c1c81805040c40f015004c00010141d0758030761041159062400c10f0031210b0350305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 926261492 1250 926260242 926260271
    0x1503020310020307050a141e0d060e160f02120715060e150f01030605090c0307030e03180405071103030906010e010f0311040c0309020a0803030a0b0f10110f03040801 73
    0x1c0340c10031010651041040c802002c0d031100c21074030001140e08241d43c0e2486d0200d840500da1040c8048820481d0b00b01001c460072040300c0009047c58483e0b074009100040d1203411340500c515040da8601e0b008032030380d2600220113004008140380190980142d40021444003034101559000d06811510765100200c030000c030300168402c031005081958002046890a41c8010546032010301645202d0b518243d000600344e84203410203006011b0180564101e0305044103240c1c00c40d0400e9903840e0200341885026420700c1c40020580d803503003050b201c490310181c030003000b4480103060280c020010000760796001a00c1c640d0400045000745081c100803c52507140c82503c0c043c1d00010303000005601c0f80740c402000880e0640905081108045800241650490406134002d192401000303422a44484d40001c031520080701035881120140b81c2070ac8900f10f8081000485598004000d034007010007030752012050b102e00c03401c03024080c14100300d901048401c240b0a2071604503901c92403c0340c0d1660702d070070400e26 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 926262742 1250 926261492 926261503
    0x1508070315050717360a0b0c0a0912030207030f12030c02062e12030503010801050609011d061305152103030f190c090608060306101406070615030203 66
    0x5034a41411400e1450441c031003201805060f100d022003c0b05c4442c540038804003602d011400c10728a24102c02e2444480060321303280e082409991607426040051a000310110031501c10070060fa071030903555400d1860f5580000514802941188250070000c03001901c0782409040c4c1c81d026802880348204180d800905076040090418215084003060241c00f01c91a02080a074040d01c02c075641030890a00390702c0d01c2c0c0c041c07503038050071083c00141014018541c110300294180c0d403440c030003400640c1d51402844411031080c0324801c5034400701e41005d0414509295425048440200841d42d48090002180300707031181900d20300c01400049540203c00d01d4416100b680400c0c0111030400c9100706602210f4480c0030007005c00c035512800b0340010300c02e050102192a02c030f8184400801c01040c162a006280d0380c070a0089001003440781e4007142540c43c1c00a6070701d102d090030304e401140756400d1407103000c0d01a40207038000d0342100041c480000060428044c2c0306440c9601c0039052580d900c1c41c0100761500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 926263992 1250 926262742 926262751
    0x80f0d05040c14030d0e0f010e18040b0a05090c100521011d15090601090e16200a1509021c02041b0905061c1d070b0f040306150807031505 61
    0xc2e03000480c5c07004001d400285465444c00100c42c545821500100143d603550000c3c0500c86d401200701044c400c00081603035071180210b00540c20450190740d803400c5d98084400a890207112640010300000c42c51820700f002d238046030024078116060400c100e00050701004801c202030703581f1900ea00107107c182c03000c100013031803061000c00e0b01d03032103007010903590111704121091031b800780c0b481000041c00c69000f40c01e000003c005003941001d55141c502c0c519500f2130346404000e00090300d003101210000c13070b00c00012034620303001b08090301148100356105d8031480c4034144051000c589400b5500b0241c1c3d1200000112050805c1c0d184680d41c8207131040004651160010303e8500c0034010781c0d440d0042d4030459030f4050724000d942ea50350321810082e450782d408020700304400000741040218800c250b0346a002c1035040d9540800c035035a1a494182880c100e0251100502404100744010004075090b6000303409030344d420007240c03c69035850700111810f0501c207420903107141d10780806100c01c0441612070740303030700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 926265242 1250 926263992 926263999
    0x406021b011b110a0305030103020f040209090f1b030c03070305070e03070f05090c13030b041a04061505060a0e04050c250c140108071d1c0c0e13080f0d05040c14 71
    0x3070340c1346590040d0442c0010b01000e4000e60b0b100c0c45128040d1116411144410401045501d00b8601503414040d03020701158035009480074000040002c544400c1940d0052000c00c00d800d0a40e40e07001d01c21070003807000400c00c1c0300f00303c550143c25503a52000c0c0010400350902c642501c2c0464205018407032000805400f500e85180300700f119044401c80e002c0c034a400e89a200c0c40d10b615903100c80c10803104113180c601446101d440d40178284010001e0a0742300d120000b010006180c1040d64035020050103019074004440030900c0003c15103890b02d8030750310040d80240c40042036030501183c0c0b00030410a5000041241d0380b003190f4204c0109001e002c0012000801d0f101007107219903e0382000080822402500400902039002c40c118140d032028040d9012524001e02903a401005d1189400f060103022007095030070003031003000403805103110040d103032103008001c052000c40303800f070340e01c00d24903030701c02d8502012002d000d01214030104214080d09000b10b0113000648145403d000d9110380700d4040e070100e14030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 926266492 1250 926265242 926265253
    0x10b0f06040605030403030213090605030c0102160621050c0309060a020901050403020402032502100b06071707050a052b0206040507050609030712060e1608060406021b011b11 77
    0x1055480404540540c0d5051a000c1d8503510703031b4a420b030080d020351403103213100c5040f1410104003400d50f07500440c100c5108404441c41b807610032005a84078005801007415a00344001e080c030086020b80c8480302c0e03440c5840d0750041c8542a4080100c12103005941c14209240c0000034080d40c900100040c03038019080310f20462a0010120010300244154400240035a4010002910201e141c1000341e0030408000204d100320300c0c007060003d40f124000460340c401c443c40c0081a00f00c43c00c0880c00d50b20440d902c200242098614100031801c40c3c1c020f104220384030700c00c032502600000c0c42800880010403860100480801d207100c401c0444100344000c3c4400c42d8400000c220204000240c0c0204850058403081c0d40c0e0040b143c0800e0407c82280c000004004940040c1c074200041ca6001c1150603840c882650b92490709608402140f0440380705400a031341c40040441c020540030390040c07a004903008a00315841c9141c14496017921500300c42c0c812034405036044401d82136004080180030244240c003400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 926267742 1250 926266492 926266519
    0x4050108010e01321c020a090212040f170a0f0905040e03032404150f050d05030301061b0c0b07050607020309031218032d0a0807030804050a080417010b 67
    0x10710010000140180c650002c0c01d032502c15809030081c000a0383c00905038059602840c0e002114150707a6080807070047c010144005003044030340c4251210220038804250039919207840b10080496602c030165901030394200140351170316107000101410710094689030101c0c0a0050007402d51083c44c2e210902490174444045140800070003103c1d885607000d18800301c088508015400c048030b13007a55140d0020728051401c0502400e00d040b00084502e40c6420b50400c6032248207200c064800c0c00380040c05da61090006012841c012819002c1000981990841840d03485d2500e2001800d1684914400d14000402c64180030040c000654840010f0004510303003444203000c0703541e803c0c40c0068203000c07500101d0140c40c55015aa00e0780c800303102c02800c40e03116178400801d01e80604980301d100300b0000c06804e24520120004105d900b51a40c204070818202000b41d1000e40305000c004104440134052a4008800a5001c030043c0c4040c0140c43c4402d440b00e405412001d08540740030a206204582684807407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 926268992 1250 926267742 926267759
    0xd0203011d0a0b1e160c0506100f09230403050c06040b0a1d07120501090501050f180a0f08030637060309020d0f21120623040c17090304050108010e01 66
    0x650401090340d048481707210582400c8614090a21004056000d40010b0008503010310343c0610544095070780d032809461f40c0c0d05180c0d08407031502d00f4940552085200b0b03404c1780b015010125900600a00b081485c20701c0000502d030074072200302d0b402c4803440344d2003003845002d44a034440d48010510080c03844000b00c1a080c82e143d030745c42c40c920a4022001d6003645034010804203420010140d54420004d100d50304040303600210740e84003150741040c006000c4030300140481001032184041c80e0861400110a0380b6610b4804003940014003240d00610100c826416800303070341c1e44c100b004c05040344d83c1c0701c00302c05802e00700300f00c0000c19400f0108160a0014a40c0966189107190100b82c0e40544515600c03c21490300e0b0014100c1d41c6000800084224070b0000c03110b4009001000c0e03118002800c0003801d80350380c1c10810345280130120b40d041048410704100c06080c683c0c002c40e0072040c0f82c103142c80c4009010485110103c000c440b0071209810200d801c12003940c010300b400703000d0180840c0806442d070404141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 926270242 1250 926268992 926269051
    0x1b05100519020319020a030f0203100602065a041403180607050c030d0f1205070c0204090c080a03030f060b161b030c03080309120301050f0d0203011d0a0b 68
    0x940c4c4201c0d800120720449502942c02068403840b1070742c0c199204d140107100b4a00a084910034078002d40910030009044120a8803445078407030022900030341d41051100304400c0c1d0445642100d40000100d05004280c0d40703106100300811103813400e03003a12031038240b504040b0314a045102e039841e0744c014002040300226061a100d10050705a80103034450100307080c024640a0720046541c1c160064000034001540d101150704002e1000383c580c480707403280b1840600c0840320126900c000080c0c00078007080061410381c011300705580c0039096243c4055190402c490800c10740130070490101e6942c0c010122003000500a0034001c160801e405800d0840d81480b0f841c220303040e044001c0c1503104600d00c40088642c400d07006005550004c8601c0a0f00d5243e00e13068000b64030a540f148507500c641000c4003444102e4170101d81c16151b020380300700c040c101c0035410712002a0104d41c040341d01d035480b110500b100030f80d12000c1400d2942404004c00300d0140c02d0a24941c00000030b020007542c1401a141c1e1541c0d141075045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 926271492 1250 926270242 926270281
    0xa030b03010b1518091305060f06010c0b0a11030a09060f09080306010c0f05031615050403120e07150c02010f020102040e04021219031101060e0f01061b051005190203 73
    0x28807035655550b2109440204240d41d81283c0c4005c0390418040300300414002000400d104004882c91512280100c60a0441c00c4070307100c3c006072114000000041070f01c1d05083c1c000d032000c1c4c000f140d08100e40e002803c184e002210b041d0b000650300c288038000d02169000300020305c08149000c10440c00309031504503861000500c201e0601145000140c10000401c80c0a00d8058001c0c040e0394891015501d0320040d051010300130385500124444522030710160b4030540c1d01459054448610303070b281141c00240900302255030040039009401d40010307401031200100d070030041c241c0d40782801803a9620024291130b840303030112421688144410300c0400d0f24400200e4011b6011a840075406036940c181511700b5245010000d002c03445c0801c07403020583c000180340b0405014400030700440b900c408100e040050103d80700000009868010060035024290b03110f0300101c002d1000412400c0754450074600001003940d815119581d00401a900441402294036210380c0d100951035810292250221941c0006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 926272742 1250 926271492 926271529
    0x608070e04050a1b061e080601080c0c07080a0203060717010515040302040f090507050409051002070c05061b1e0d0f022e11070507090c0e060c030a030b03010b 70
    0xe011600340700c8104020040241d021560745291210101c0060961407148510804105001b1140780c0202e140780b000360702c0f200e2980e41c006503540c0b208011114100e015142c0101100300b0402c50984003420300501d006480e00b04014281800e142c414907142c080001c080788100680e84040d502c1d030007142c1c080203044400445107040b5181425040b42200d20460780020b600030314201c0d07240c4030414950003040c05940140c0a4607940c0d5130b10801c0c0000d440140c000282660804d41b021040c646195000d8820301d402110002a0582c40d04040b5550b40d00000282c0c80c4c61b44880d180712009a0104059680030a0007418100c03800605424140c5c0d4042040490090052041c01094014402c1120001c2000c00030740501c002100c40e004c9410129501c400800c0c03407414003261264042c1d203801140d01c65944440244100c91612900c00010407070503903007000f0003140410000c5c40395a11000fa061000d100c00203180e80e005840c2018040752811200c5d28040d90501010b590183d0340c0040700304c1a5a00315 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 926273992 1250 926272742 926272769
    0x81905040609140613080604200609040207050102090a1d28020c010e010f090201080c133c1403060c1902011d03040305060c070b06060a180303031b03060807 69
    0x30002030960142e045d03540b034175031502a000035141e000021105d01076405181e07007034404100c840301400c904002200c11604800e0803c40503100d8181a030080c540903000740001410310260400050740085541d0240c5090202d03400307580201c0c40c07500d40035900079180c0c45041c2c000c140002c400201e0002a26004084585d01042e080c041100a42180760b4000010000b00403003291900307903400621200009a0000d404d00c0001824a10060111412004280240021140762842d40c00089000000d080308000c0b00d40001d14a03c105e000000032080c1c00b00f040031862900300220110b0740071aa40e256071103603200301d0030710044e00e006008880d8804290329003400340380c014a40c280e0140c42110b80b030002081e4074040c2e42d441900044003505c103991040302920400d403140381c4101464001c00301c3c00b0709819107042c042002c80c6003100050440040364100900020340950500540000e00c1d4800d4000c69111400300e01e00d2540356020980340c410b681010000d4038144040240d42e041cbc5400346900c4c0ca12803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 926275242 1250 926273992 926274029
    0x60a02070219080609101103061215010e0402040e060618070c05060f01151409130f020c060702061303020312090a0b07090f0603020c0604020f04060b07081905040609 73
    0xc1c8038a241c40a10388009800510303a0303e0300f440f551440c003100c100300a4059040094042040745c080d00d191022000740c0b15046072990720820002101482c0500c2d00d501c500382d83d26112032042601c1a008203001c14042c0c000d031a2900602c41030352108100010f480d00040f040248a6846840d00100c0d0321101840840c0c1da0703543c180c107031200001e00b0806030a510400302008508848890304a0603117100856020b000d0300c0b1711800b81c0d42c8810984c40129185005d004000480c213100350707004c050075600302c004a07118080d9018201240c0c41040080040d4004404021803280c0400c1019001104508060610030380381c1c400a441b07008641210128403804004550400020841280f141d50044030307524072410546000b4000d0001440780d00c45162540303a00041c0310340070740b00340c6d0600110100504016500d540c01c0002034140250302507070195941d1804181c41d946170014110f00c3d03100d0b000842c0e44000019101030f81a10b03481a200030448104070a000003a4400b803a48211030407000f0604100c1403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 926276492 1250 926275242 926275249
    0xc08010b03120a050d0b121e0f010b010504120c0b030405031201050a0b0921011d06060108070f23040f031e020a030f050309060703091e0b0a12060e01080115080a05060a020702 77
    0x1400b071447e00c0241f050a49018050048450300902c54203804211041c0301d203401011350a9440e203544090100c0d0b0f0a101c208403075804640c02140d12440b640e8444003c94854800d00e02c5034006503400c0d10340d9800451310403a003ca0650100d40034140c1210300c60089854070b11641110b115002c0c80c1ca0045003084400c00c1007c0c0d50038199808015030200901c10010340e50350041d491100314402c004180b1807400860519406652803a000c1e11441d541c10340c200548006c10303150030840d0b00380030a40140564010205484c0003014001422620001800e031600c0d509012000206003034664142c1c01481040400595420b5408004c50f039100758130180c00400380c1041425402401401d0790000c400251540815030f110f80c844041d42c59000554800700d582c04105a0720210b035010b2100100e000700300b011426400781ea041c0c0e0b1180b01150007c41d40c2d6888950301e0480150030791217804160744807001c4005045032002c0da5400f4000c107400603c1905401d84034180c1d29036019000840c0c065000640030103649 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 926277742 1250 926276492 926276509
    0x503190203011118031006181802031507020d18030308040f0602030109050402010306140d170c0f150601051201091a040513021c0b0c090a030c08010b03120a050d0b 72
    0x300f198051500d500d501e81c0c4002010905000091007802440c4c04001017000622034402500c002044100260821103c907600904490000710320700c4641071407890050b84c007000205a514001c030004081401d0008001e490315254440756814000307125080030004480201c44801c0300c0c1c15141c10141a100c50034000340071820f0000107043e2a000100100ba0040607410841c041d074400ea90801400340e440b00c0844040000c00205944078001144080228042c4003080d100b551001c6085850036070070f82c500c60303d024102d0001c6100c54110700f40300c140c40303140d61002c65400f4100b0b0034030340c3c81c00340c0848614100e00301c1400384101c6e4994070400e090040103040c1da59401c0440146c410484c0d818046406194521044000c91080a000c021403104144450465110036441501030140d41c90346c441e0241541c004110181d0408500280040443c0e0745800d44030092070f210000040000000051600380000514100c542c60400c200044400703900404032003903d54400070024281c1404400141c00d00d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 926278992 1250 926277742 926277761
    0xb0306060315060c031c09151a12010e120304020901060f0e0a06110706051c050603010f151508010612090606030210052109150703060312080718050319020301 70
    0xc3c80124465444080c0080108404075010841002201c20111070105903000d0500041084d500c20740c0b000c041c004a41c20894080526611509e20b100e281c0020a01c5504162611750300340c0c0d140c401c00003900d44140700448640ca000340c81d0304c0c81e41c074050300070a2b8a0303e8184a05070401c601011081e003818411141081010380082004018a50b02c000082a050102c2c503060014014850b0000c0d03210700410448841035105500041800001e040c12001040000c140715095500e0b5983d044541c03031948500c42c1042c07800c2e40c0c951130560401109001c808903003d09a030030700040304010300030a0313040004161000b0980e200411454090300d4200c0141c20568402900080e03101c441032621500803020f0f02410081c0b1410041085103040d48032501d040603a0610f0960304403c83c580b0701c10308000c02080d423000707013802c005c0b81d00c994903640d908090761824008000100b58405010515601c040e1182290020b201d0035100c040c142400661070f1104411484030000c007243d100f10440d117003034001c800b01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 926280242 1250 926278992 926278999
    0xf030a0b031e0d030603150b030a15140705072d0209100512150c032205010204031101020109170a02071a0414092e030b07030c030606090b0306060315 66
    0x111080c00b40022210040400e5940e03507030107400c1c0340802080c424469102126000f045001624207000000c00c002e00c2c4400303040b41c060141403c4000403600145000906031480500060a2461001042c130326210280891080050420000011030100c000d100c400204044004403042000c003d407141c80450303494001e400144410030400350302c0d00c80000d942202e0007581c610700d04c440300014050b110342d030081d5205108181100400c0441800038061548151a11894100080c600000c000070b6540c214040f50980e400103000d00802800c10161044404280024072104c01d860303445484840d000b01f14030121010105200d40b6640c801c0000b00020201c1002141d5000d086501c1c415040c1e000b0b004a440c1e000b803e5a42200c03074180341200038071403842d035000034068007250075110442d0702c1849c41402441881000c04004502d401d2002800785085480010300c01419030303c09030644040f0350022050101480d07040008920900449178030040441d078240d625918540c040424200c240c508640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 926281492 1250 926280242 926280253
    0x1718010c0e090105010203120115050403050a08040620030d20070f121112070609080406122d0b2b0302060c0a09050f030109150f05060306010501050f030a0b03 70
    0x80d01074004082900c86202540e030380040341e8860300103990301c0c40317030032141d490080650004011800300740954003051085490100d243c2645c98880501d4040d540205641e941e100013010005550032401c2d260301440c501c0009150100400b007981c0d26409143c50340781d01c007510380c0458403000104c3d010b1801c542120b00000c0f510b91440e0300340f410b9040e00220088840b50050300741e001015001703440d40b0400b03d5014005005003494021040328640204a003141c0661301c40010000140494018101800e070580d9500f404071000f0b107450060750b240160540300d41400141c83c14450740440261201110315100200d808005800401d2841c1c10b51704030500d03004039806901d160f528819150515040c040c0c1c0c00c03155641ca17642a045600c7c40303580381403070210340c880c0b40802007410a20202101040f004000044801898070f40b041140216403120440550320581da0300342203468071800d074006200360024030b160360500c00083c1062042c1400d04c68442c1002c0001680243c2c5608400304101014080c1e49 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 926282742 1250 926281492 926281511
    0x51b120310170105060306040f050f03340c05040b1903050606031204080d110109051f0f05010506090108100807080c0a05010201050f0612010e0f1c05030403171801 72
    0xc020000da400b5810b20050301c604103100000b0140909401001c0c021b000d4a1592100e0392418500281c1503000c888502a0b100700101031103090001d0004000744112802118640111081c00c0c01c1101081c0700e4884110200e20000c540c2e03507016030041d5602a03800107280c3d0b2801001403021181d0421088410507800303800300410034003140c03180c025402601151044800700c64903142c0e81c000c80c010300d40036910a045290340140720742c0d100280d82c9000400040c404640362582d9040c41003840100c80b1254800465104808040c8103280b80349410001c200219410130001032003522640711881d04000341c22010406001280c540300b001031035800c0442d280d0503030341d0801648500d40d0200392481042980350005044d401802880d22881c403040c0652200d07034640c0d04105000b9120070200c031040d9a25050b003410034104005419009030600d004107003500d0809100c3c003001c0400801041003003014000c0c400004e0f0440c69030f25031884802d06101b01d9643d00c0c0010355034071421070300b104c07595800d114901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 926283992 1250 926282742 926282761
    0xb09030a0c0902251101080612030705011b140d020a0e030a030206040b0618061e0411040e0108010b060a0f050f031f0e011d04050c060307120b04090201051b1203 71
    0x1e10300030a0403c1410320020180c4221002c0f02109130014150011503010016150312400c94250321078001000403412402100c241d915641200c0d500322800c0e0343d10100250000ca00a52406450b01c4078070701400d01442403485000c1c68001c1c1141481c8603500846d040800e203014101400c400c41000c0c1c200c0320105180d040c000d40c0c0300b4040d14156407403002500464a039041100c490043c00301c28080070100d68440005201b10080c9003007055010705119090b59583e0350b142d000c0c5444004100440540340c90034486140050781044c0d00c201e405a140c00502029a10741e4000d48100452a04100d8004407040e030041c1d8140c480c3c160310343c4403c10000300308101381c01400000c40300c0d100a01c5214090f40e0700c401c0500d900401c2800b502d400300c161241c0043c5180340e1083c14940c001d200340c09550354030000d40c004c110f00d80c000350382d4000070034020700480840702210b10a001074508204c0b0306016843c01d0b600041e11a101d031400e42100103005202032404030350100000c600306500d089020ba968606070515 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 926285242 1250 926283992 926283997
    0x7200a0b0c0a081f12020f21010506060c0619060e01090603050f010b130f021201120209150f0d06020c060106050a0909020f12250305040218100b09030a0c0902 70
    0x207007003c00d1458021803500318800000c580c5642500c40d19803081800d15529005011810108981c041c001c0c80c0d220289803107140c0310510702240340004400c0c03c400185400d00b51003004102500030103040c4540040c4c8000020840d406c02e60b9541803400f100c144e00e0300d607006058103402c499070b070b6240d00c0000140749140b6400303601264000d000340c481f03400c44640030900703035883d408c0c045512002c041402d08030501254008400303a5241307000140741036009410000c0302c003000d9001c211140041001101581400890140e00041c4240316070042c08040c00090404140076030428052000c0340150810403145a040f1441d0180b41c4007200c01d19030392014002c00507400030090741c2c0080e80341000002d540201d40203449801d8003141038242807802c405140c1c000d6440080056600e0041c0c20343c2202c0d0424007418262442030160380101e40ca1510303005221280f0314440d40810100078a60402c00c2d080450003d90b804e83d90306041c21503860b04d25800081c90081d0307015005e02100e82c0c41000003510095a0f00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 926286492 1250 926285242 926285257
    0x607050304030c03120f230c060c03010501200303040f1e050c1e09060f0a030f0803040203070f0608060409050c0a0617090a020d080a0507080d020306090f07200a0b0c 73
    0x500201030641004803102101d802a6a02056450001c513911181c61407d564a02400e4600385003031283c0100d056250410030355903400c2c0c8980002c01030006582c850380c0550400300359402c9080046001c0c0300d0342d94030312000304050951540348092800f00140c0344d0400403c28004618502031092509003561a807000d001c685200d8000801240c00890005d601101c020f4002400c1001650b10482400303059046100c3c01c960000142401200040402022030803850260f22015200d203413030b04c140343ca80074241e0060004407448560404c2131960000f4100d034011815200850183c0c01445c1280c581090185205e500c0b8440300408180aa4801620300d0b160081c02c0106800b03481d000360b2140c555541e018003a401800a20544010408000040032080c0f80780c0b50145c9040e0b860f4540855030340244110010894001007803040600e40622000e401c0300781c002c2c1c60300b00f60034050030140000d8044810010220103081c00d02048540c1846008441600a44000d02919002c07080080035801a031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 926287742 1250 926286492 926286503
    0x705060a050709060c0308090307050d050a12090c14030c040e01020c012703050a091203120507020d08150f060f070c270e010f0c031b0c05060403030b0607050304030c03 74
    0x8001582c0e18031806a00003160a01e443e0011068000d4130f00b181d9207000248070460510041241a00140041142803500700c60b50351810f0f00e4480407080280701c0342c039061000490328141914600130078402d2012404a0f0100303101c01c41c44030307000404039041150414030350b43d00503c0c0c1032011119480640085c540159004020000b00210103086c0c1c03250301d6071042d401040955002e401001078011001052210030700d04080d9075144c0e5a0240c9140d55400703201c200d002a034455600300c0583d84502800750042d01c20f001806074a40c0c542c40003007180c0c50080494140d00120707508107105442e84800c0c0403040c80081d000c01e685040c44140700070f480d40101c0d001c0321300264500000441003000c9030340e900325820203a541410030700901d5460000d0a914801881c1e20f558950f65030130001120701c5040707005420ba840c040707040c0c100c0020340108541b2800da04805e00140542d0a0001800412100e03403107985824006003922048020950f580102c0d50001c100b844001004024850300304102c4040b2403252 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 926288992 1250 926287742 926287751
    0x610180308031914010b070f05010c02030406090b090d02011d0301050f010e0702120d0b120d030c080106021f0509120309070e070f05120405160b0c06070903051506150705060a 77
    0x1e40c040c00495244100e03811143d0002401070291201441c0206040d501510030035920452075111182122f410741c6900025a2000a0800400b900907690700014000030024134140440f620100b000803034007040c02410000303140c10000c0c0d10980b910044400d110050002c00082ca401604101814401e00400a9001c50700001035005403002030050360000c2031105450500769074101040c090000c2222445e80203034280c28024654200300310b01d003140c19541d54040b034a802d200340040c08004042e0041421034004136100d820143c00c80040319008002d0140010780756960410060800214164030700a107c800002d10219250005a030000d40d08402c400103400d45900c82e09903411110011140080b0f54280520041c2c4540c2d00f1480d40c0c07140c081c00559102410b401ca00c01440d41d010b400c2010244804121542c00b188104a5240d2140032400d05849540c15916115651801c08420b0707584d002c0c203080002d40036181d414010340c1d4401c0244c0607940b600300d00c2c42c00c0c5031500740403130b0800106841e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 926290242 1250 926288992 926289031
    0x70c0803046216211b18020d05060a0b040308071e230303010f0e09330f04030c12090302040f050106030b0a240c120903030206130803061018030803 65
    0x2040502c4c0d401d01d0407144410945101036480e0002410700c895558224050b402002a00404c02554007a5402004800582d01e6140c210158211800503107410f000361a0050305028202e1010122400c2c0c0303402c01201d584501304d504d00040d0104090310714400b214042c850000801860905880c02a003100e4034886201c1c03041d540c0696640401d10525941e2001d45008105008882c51455005490380007075942e141c0c11128440c01c0d451200e07103141d18401414040e4603100c0f00304e004c1250403011403842055a41002d44004190858840c00505580c3c2140000124240942d0341c420045901400a01c050070350a001a00180030901c40c0c0d03404a800c00c110401c192802c1c4000303009403a01901064071a140c0304000e0380c020340d5000728480c00d20580111090200310b09000413074805245540e000300c15815490b000341004009401098054004140c01c170009442c013056a44c082010746407945091103c0408031201d10402c9100b40203c184060b004c01800a0031008504c42c1c421045442c120010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 926291492 1250 926290242 926290259
    0x608040b071e1d031e010b011b030807201005060627040b060d150608040302030717120711010507020a0b1308070c0803046216 56
    0x745107010b403564455050080409500929814862102104400500180401c042881c0001c00b0041c1900b42d0112402412010424054481007000c20311f01810350402d01450408255074200300102481503000000f5151446039200507000301c800030000300c000e150580030503203681090300341100301400c00001400358109002202c4480b4192030504040303551040307103208074092104840c0d601c15118800d0f44160f54814015000c0c1d15000c0e01c0002d0700700c10744090402080c00703540c0500184a44ca404000200390040240c4151035000300100c2c2100c1c5940d500980548a6100800e007008900c000f400a560380c8a82c02200781000c850082200f5280e01e8004c0e03958094601e40100080d00c014004bc10401e041e08018100e14450910b5a04050040d504c0014131903641d0030002036030384040b40070010210155100107881d135242c400b0f07441c1c01c3c4064803100144089407000194290213901a007045401805d030000c819040c032039900c001ea1058a100544840411a07495850907511380c002c5402d51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 926292742 1250 926291492 926291507
    0x100f0b06031e0a060b1e090a091508010b1e010327110604180e070504110703090f0b040302060c0f030309010c02060a05010e0115170106080a0f11091309020a0608040b07 74
    0x1088170004e2801c00e108a040b0380c59601002c80c030314041d80c405104203800c9031244d50b42107000e00548040441c254004048401d40c03075407203520021003a8103092181002d62601d100d040c480b61880c2c0b0924020401c1180180e000e03144818440504003002000141c44144e4440c081481ba0310503c0100a040891400c001d818010380c06043d4010b4600c1803c0081014103900401d01100f049065a400d143d4a100040072245450381c8a041124001401030800d0707404403c0310b010740000b441068000d0b08000d01711182d80124003000340200c3e000110350001d03200410511250170355009c00c5982d2841c011184078042d0150300e076140003502c03501001c50030162003401202e040e20084580444940e06e442d12245804410030045414801641e507134190303840704006154041c00e140e0301c841d42d25042140c603541c212003d401c600000a4504105100e00f10940342c2115201131341228110828a42110500028500c184009500c0031030540006201500031007414403c6021340d1031b0030481c3c4c2c1d03007020070780310749 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 926293992 1250 926292742 926292749
    0xc0c040c050906091503090304061206080309060d020d090c051815041e0501030308010608070201020703140a14040905061206090604020607080c19200102100f0b06031e0a06 76
    0x107201440300305041e0a1041c0580140c0100602c034030141050404030031619881a0f600782c440303030400503082c80202d030000e042942c3c0d080a010b0810000c2d01d4008c0040e160f000b110004e40c407415001680202511068050351004406000c0802c81d20000385803580c1562800c0c4203160088920f41d03008100c054600a40f148074100201c0d080d900d00d80d400c0c2c10000202550b00c004103040300001c01091040301c00341320303d0380a140300341c88417022941400c0c00900b04440040844045a0040082c1e00009910400300d4000000c520202c61b1140400396050711604a40300d20b03041108404180020b13028220f401080c001c4a00341c4281ca4404e0345441929207801007107806642980c0480081801401c1641c001c120503800780920505001c0103500503400c003502d091380d0800d810440141c0400380018a28400170000304018100003038080c000000c1e40707484400580410306035075064402c07141c5400740c201c000d291078010000c41e40c915199440301c403921900a60b9010000441c400990600494032400055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 926295242 1250 926293992 926293997
    0xb04090b0c0304060908070609021c031d0301020c010f060306050f06210312010e0712020a09050607020a031a010e01080d0c0204150806090309011101020306010e01110a02150c0c040c 80
    0x26030703550311508086910141003200e40e1680d8082180100390018040c0c0078440c452100030540160074010022180321051034600024030b0113480d0b8000a03005841fa11000159204d0320b001070180c02c00090080c000c4d890540c0780c650030070003480400d400750792265058a103d80b4003008141c40f404220b40740e030b00086980300c1e0040340203079444040c0001c0640502900d045201183d15102e4508030f115800d600c20b0348800c0882002c801130221441d00400c2690041514100c11410803046440040a4015a104190054500188586c259220b524240300a0740e04843c1c5005252858a0320300d203110303024410b1749088100c100000c2020000410841d00f07078809542e0351041d02c102030302004000d00c0400710207003000c00041c0d00001c1800060204502c100110700145403a418a04000751852031080308007149a441042003180c02c0c0e0308a070407440181d0302841c02e0321021100c1000145002c200c1000a584004003600702c0c445a00303288010040c42c1c42c60400d61b65968a40e0b41803006454080c91898003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 926296492 1250 926295242 926295263
    0x1602010e1c0c0606090920030606010503070e0d0c080606090c040303081512060c04080f28022b0c090e06010302011d0d080901020601170d0521090c040b0409 69
    0x542c03060501201150240c2d9001526a64802e80c40b0116085480101e6088850741d40341f6094040d40041c16801450030303809003519181020008007140701c010300038400c5c0401003440c0c10141e1a5410b40a0540da03018148011164441801e1a0380b02d00c2111101e214044500c002011802d048003036030101d0343c0c15110030340c003615060710300203145025030b01c420342003020b0504a9028120402060f4002d111f85502e2903611401c0140183c1410075403800381007140c1c429212031080d100030701d9120844401403103100c031a1007514400203031078915015071004055800300e5101d60303100e9003602e024082c9100341500e403441541d54403141c0603201c1c400900320580c1c0000e001000594002c9101a4203158107283c55110b4a5220300002e0b01803103600c20607548c20a0200705054107503010410745024200c076104d203c0c24940135040031650382c0e002d45022410080e02051014050100c0c1901c4e2604407012100d681d503620f04061002d17580e91a4a008900c41d6003410139104250409100c2e00c00d603960806503690 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 926297742 1250 926296492 926296543
    0x50606100203041809150506040c1701141207060f08280e070f0e04020a090203100303050a0203040f080d27060e0d05071e0621050a141602010e 63
    0x58084054000c0e00c0388503a21810703c5c00c002140011500300c4811940383c001681e0030007009020485101c404420144100360b800d82e4080da05202103141110182c0b143c40e14503001000c041581d9402039403542c0c82a00c0380c24004140305421013841400034065644080c0d040da0350030300600c408108003500d80e880381c2110b045840408030a4200000104c030320801caa00003a915408041410540d5005640e140c1000041c8401c5291461041000701049072041d415400c2503035001c0200c141901c001014020006410100e107402442500c0041000d01e00041c42c3c11340c1c0e58010361311040d9400c40c0d03000140084403101903005022240d01c001401028440f10a01d0608070b05491a094954807d58400070300c138001d03800140c08110400180c960260140c84111400300790201001c0250031130780070b2000e80103001d003120925030509003807030302541c40109060b103c4842d0380d8000d1003025008002e08101c86c0421050940440e6000c0030044d0a60007009400348200c940b50f116000300c8020780841d8038a5030341d80c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 926298992 1250 926297742 926297759
    0x1217070503041103150a140108010c0e09100e07120516021b040204180204031403070b060d020d02040c050c0f01060b07030503330103050c13150504091805060610020304 74
    0x11a010f0015048a080035003004030701c86000f90803501140718171f49a040e0005044600d141280c0107140900003800001d512078070142021481081d114054020040090030714000b000c4864020000c1d1b0160198906180c0402492003455040c0c3e20121402c00c0c0c0402d461621a05490403800a190301400c0f00c04a880c1c0049034039000c1403015603020b5020301c00030840e05441440304000d80d0a80c03400507039540c0381d03241c010f088804410b000092508107000c0070002c6503600c10081d6010008846180211650f40b00180700c016264402035081842d0002c3c1d894080d421500514032850380340d0480d071854100c010000c0c2a640d15000d07078a6456000d025400019001d0005103401c07801c146451038440350300d00084520080b074103100f084d8049602a40da091541c01d0300c16541c10020307550155240c100e030f40c152264003050504c80c000c00c9100030044035170880e1040c07003034030042c10f420740301400500c43c0000e0703e0140d003c081c42c05031020302034600030032a640f400b481e404641e82c0c0d00d900a1070070b107494042ca9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 926300242 1250 926298992 926299013
    0x5070c0b0a030207080c0601061803080d05041a130606080705030c120a020915090f06010806130e19050c0f0d03110703021513050103060810020315090103121707050304 74
    0x1601e042c5034090007403200040c03081010700034400303408000300450340c5007a40c001d0880d205881d410320301c3e101154052012683c1103040340c04010144001040c0340c1c6036444d042c011827620000300c180f20071034032003440400708a000e0150102809200140400c5443e2041652240701038803070641e0603448010740d40900d0400c00710111100c00d0303a03000c4c0c80400000d07801150a05008031000000c1a41514249206252520519800442110700244907180420004c0c04188001e00035904c1652031840c0e0030f038400d006400c814049000401960120111042407103204854400112014011812007542e9401c00614003554000014030b504510200c40e00d06803203448107000e100c8880c0c0118000800540c407400110762070340070607000c0c003652154a40702101a0078400d4000741e0402d41803070320401c0320300e500290f1100540d03141e10005030b994450158040a400c10380e5206a01301901d480000b0502800c07010030300380b2815a480d11010404144070580c41010201c0b819801301c0c00500104000c038100c40310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 926301492 1250 926300242 926300257
    0x807060c110d1211030918090717011a03030901020c060c030f0a0e120105040302060105060a0e100c0c0609060519020a0f0c0501020d180e060d060c02010f0c05070c0b 73
    0xc01d5456002903402180d210255042c0c10744100588502824580703600030800c1c18001d00880285041c00d40f000d000a03880c200f541441910045e06c0c1000c20303044c81c0d06001e44e00040c001d040349104141d042c80f105078003802c038062486400704c2c04100d01d03e10504011040300e9258805078013428200702c02e101008a103400200321040203100c24002000381d0781c03d0b0002808120801e0711290130031941c0208001c1c0b44003400901c0d915507410107043c000043c0d000540c003810f4031012120b40d5180c4481e41001c950b602c2421081c164402341e20f080540032541c00054040c3da1600540001980c0c41c0c80700000d070f03a031030424032900f00019010403070300b0540b804601d25240680300d544140d038009007494907245000c281032038054a145500107030403c4290303010484501c100e039280c14450744c0100034207400f0200030602d12441c41d0302103c0800054142e5a80a420028958401c000b00004800702d8802030007018105408410303a85007040700c16240b402078095440b0b2543c044d640d0000701e81401c1d121103044e0000d40e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 926302742 1250 926301492 926301503
    0x80c040213090e0106030b060f0108041101030902090115140f0409090606120b06030705100c023f16180915090f0b0c070b16020c04020409050a050a060807060c 70
    0x21030b0a851500529100c04819000441c401d400c0d03040c06500d4001c0541201d22400340020310015598018403020341c820340110000c0102e4050b000140c02508211000a511950144c00460150145441c5281162007552040f00b9110281000011480b401c180e000d0719a4060004108040d600d0f040400d00780d220305800324080e0356550f006c07048245000406c1380c0744c0360744200f04a00c07414100b049c900149030460b201d920b038149450000d0310402c28800003a014a0f940411160f168501e902c5444205641c10240b12061075600b249080c4d013441300001103203a00403201210104407004a01b001600d90b030a000200e1080e44800500062090b40b00c1158540004130015004924911981c031301d09004802286a040091400c0030700008001c215580e00481401964042000b01c02440da0001c1c3e802c030b00303140c900001502039142078000340641d5803042c0002808105002d46800c20340c0223282104041c00540c5601e0100c0c800e455030345c080c00f01980c0c0100b100f0810940710f510000c82c0c003401034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 926303992 1250 926302742 926302777
    0x3051207151a010f030225020402090a061d0a0e060d0302070e16080609040f150e100902190812160c09020a0f05041214010e0d020c0a080601080c0402 66
    0xa041900949030b580c010141e02801c1ca9000c2d0310030303580040d40001c0d001c00d107107001c510700706183c9a8504681c40c0d080d440e41401c1c06015000c0115219981200e014690040246840301e1307849000402001440e9030461030f0261f01d1201314401c1c03c0008207102641d40c454902489503032000709100c808003203550180c00710710a282000a4114030b004045028610505a418082d07001c110098118100940003c1c043c8203007108200203d84400021550307a44e2201101c41082100150640a040400014901c50042a143d1240381c1004d034400c1410030310030f851120490580110581422041b4850079200d900600042c4507000c04100003440034441e085924400e0b12040d4899140d0315071360b83c002c105810750001b0108000c5400c211541480c508602d40345140c9400c1040c000702540001400810780d61304203041c10b1911800f9049030420080b040100d03500c20020020083d43c0e103c6129004c2c0c020f01c0026004105100081403150594a03918003c2250000080034003000b54000c10f5682c031404c116 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 926305242 1250 926303992 926304023
    0x6030203130f0803270715120606170c03160503130f050d081012020f0406090525020a02011b0201090e0103030302120a0b09040204050408040503030714060a0603051207 74
    0x1c1550210b01c690040258a0302c900e4012441c4902c81c010181e4aa02c803160210b00a03100000040c0410503140341342c55491002c050f640d41130303a0300721070200510402030802c0d5020810641c01368800e10000e0b04a050071101b03848e1449052145d20003940e1546515182101905005020710002c503000b208448400c3c980070300907112860500310b142021542c6400c849000402250f0050b0038540110003201c002d1000c0d445c14102c00891509844024068424060818199a81c0e40e0041c8009d0800300414011403910710380e0070561255400600c00700c0c1042803045101c81d0720000704415460307411303100c40003000d40707118009050240ca150101e04002c007540020900ba042426024000c510030f440241c0ca03441a1543c0f200c60100050081d001c051810300b01c1d12050351340785c0e0722642041e01581d00045030385840c14608074521490300165014400000c05200b003080a40001603001403450950326684c441d1400102603844d103100103405035000c024110b0030f6001c114001d081d00c6100b441a10505880c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 926306492 1250 926305242 926305253
    0x120c090d06050a24060c060b060406021e06070909050907031a0f06010503100603050a0e0313090f02030103173601020d08091009050a05030409021b070303090603020313 74
    0x680908841e29516a824002c042d10240100048404401d14a2a2502d00c2d1184408030640320320501e01081680401102441000d43c40185180b002400b040d54490311a400030b983e07200d0903001e1b13005075091250080d20a10001c1000c3d030203008030769a0701c2011450a41850003400016140000354081c03000000700082410308480c000842c06a6103c5071445d00345400340840d900200490305102c4104100100c000102c00404140d035803d003400107860321110441c0d002800d1441c2a1101d904c4000b90b001c070324802c1c010f0302000300c071075242e070520200b130020b5600e0040e4003081c40020164842e900c3c0840007040c0c034001030010100802c080c41e0b000c56121808008040c2c1a40f004542d030000070324000c2295070306015032542d4600500384001c842c1072105030140c1d1758072040d01000e80c01c2d6031640320b032081100600410031141d070808100c0c1d842d01d842d0040e902c000e500404482414441e0003125606883c404240344044940646420f0307640d61030081d0950103544018040c511150030070346098005038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 926307742 1250 926306492 926306509
    0x1b152c0f04060e100e090a0206030a1b02060a060f18050c07081801260708092109040b010f0203070b1503190b0604090f02060a03020c1926120c09 64
    0xc07030103410b4043ea08000c41105903000c143e403c109440c6440d00104410810001031405405505403000b86d925550251034100a085c68828002c4258841140c015610740c0010a20b02a2500b08020098260344581e29081d849003446400c1a9554140f0441500340f855407209074840307182030300c00f4500041d56403000c0890740903100d4075411200703c0d504086c00b542d1140418483c40410100520110880790311100c0001008260108004141d400206001e1041c892000300041404001c0d6003289898a0390344150404076441d40101c0c540981d03104030b503102e0000e000d40b502c0e05802552510410f0f032545045118020405440e00f54017880022a507241007100c11421040b605d10396240e80d8440c5403c811004000d00104c2c403503070420380100d0100d094030541e80c5102d42e0441d03e595a9205980c0d00350064024200c01038a18040c0180c500900310302c1c001e813100301e940708104407080e0658942d1524103d136401c00300b800083c94280002808100e030341c2802c9400c1443d078a000740c1003805000004404a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 926308992 1250 926307742 926307749
    0x110408030408010b090c07021005091002071a0a080708070e0a17011508120c100603140d0512070e04060b0a03020403020a05040605060a05161b152c0f0406 68
    0xaa2000908002400e420320410903d13050843da40e1501e0700740440140302c0c6002e0b82501a1207181e4980c480e0104ca40a40100d400c2d944015003c2600e51252040213900d420305442003400d04d4003840c01b4190114425801c8403d9054161a00f614940b9040d0040703a020300300400c0c0c40c2c00c2c0301c407810049441c1c1d9548a103280c0101911002c2640c4c041280940360309480d1118005d00b01c8107140207003444020400f01d0f22600c003040090916484050004150345040e00281c0142e03222442e01c1004001d0207083c1600480e49812001120b9129118400448135441201200b2000190f41c1c0003050500340314864004034900000c2c000304031113032210a1108507602c01907042d80803c3e0f001808100b10704120321b06000170302c01150100480d83c54640412614400c4c4c0300701d203082080003e0b00a423110b240c0800c8400c903507089500380803031420802000a4406940c0224500081103080012800d07105020400710807006086075001800d18020040d105039010703618075030028880e000c6025544580c403846004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 926310242 1250 926308992 926309009
    0x6010b030106030f050c04060c03021504050601030308070e061603121508011a030307061503050d03140c0a020a0803060a08060a05010f080303130b0408121305070f050109030210031104 81
    0x12940b41080c00380481d00c112412003942030034082048624100f19061f102140c500303080407400001c503850228200604011680800c00c800310900c0140100054581d0507680b00b42c0310f005050315020429208003006910942c3c0c840c0d400c011814000f40508681c00495201e0f00b0040300f00001801d181c02510356003101203442211034041001055400d010b1241c0584480101544c0c14101d000402d071607203d0400d000d408161103201707480c46c0b04400c0f00094011600001a6140e0b81184c020040241c8034092101a80d030848201203480030149408076194240160010541d5130440d50310705880d600003d00e88e0b68001c522850005a070b80e818040544a91142840040e07198103007019080a20b00030b4000b021164014002c01650905ca000352100b4543c014184502d0707552540307040c17600e611501c41810102801030050100d90701c131003014542418030030b800303485102c0d4589072a40c5083c555071240c0c0b400103000750313000c0002d03041160061481c0402840c020400210020029405d984264003d092 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 926311492 1250 926310242 926310247
    0x3020a0204060b070b180c061b070e090606090402030c21071203090e10050409030804060e010219181d040b0a0b01080a0c02330105030601150507060e06010b 69
    0x441c6818440e410240c10a0641c883c14107915480f1a0401d440c001e2003408511304086454041c001c04000074070038001c00814a0746d4a21061541d100e500150510401f824820200e0228004042c40a0036128141c248028616552034408120030444083d2090b80c0601890381415211b17220030108444c440d0034840303e4a44a070b0076804245c0b1708442c690007030318500b80d0180404002540045c0c7c0c18201d8800c0558054107480d48010200758a825a00031030b800782c5001c00c258101600070302e606200340e001c0d20003003105851100f125401d078031800880d403070b40131030405000c11020f010301d046c0c0b004c504070500700e40400350316130922030b1500601d69445142200c0340c1082004002d001c03060242c3c0468580000c3c00713440070200003e04100006419001c21580310381d00d1540c031034400c000b00901801c40316030720b200b000c4500401d085180c0c0c44100310090915003030300210701d505000507064100d03400c0402805089407040c404854940240328100e03400c640703600700b1402140041007280d000c0c0c000000410b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 926312742 1250 926311492 926311513
    0x604290901150915050d0f0b030105090c010f1808010f0b091e0103021216090b010f02010b03061b16120f0c0201020d080711010204090204050f1801090216020306040302 74
    0x321081059119101280c0c0402c50750480a41c03045414003201e00c01c0028030210b00c50072209544a028000c185141d140c68007094111250340f81c0c00c501c030b44d030a007075000b00702c2616099402e5171100544196540420054110700c44000e100b05003000e01d00291220764040b190300c03500d82d0b90940f0840c4420303c0c2011340350580d16811349407400809401c00e00103000c054620140122120880c0d034144806441440e4000c088061428280000744402981c8880c601047e91105d0800008000c092000ca0010f000c001c1101d81003401442074031714298005006002958644802a0080d00341280341c410b0a0000d2141c041280c0c00f480b4069856031040b60441d10f018520307000144641004402c403810000401c1045000d80d0700840c244803071312420701d0610580d59a1800a80d49000032442d9803207158400900000c100c40d031a0701070400d4843c1142e070180c3d02d0304864100f12407116901e0003802c9442c5503c004000480d00f96009200d0043d103960120f4910500350006424004212410760158100c22482e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 926313992 1250 926312742 926312749
    0x70305150a05010b0315150d020a09151718030c030703081902030105100e041503031101050c042d05060301030303090b0c18210a08040f05010c1505060429 68
    0x11809400c4501444c1c0c11403502400841000c44482a80ca026820b030181d12038025880000b210b0708001540d10540d980c08595500621100040c8605041d0300800c20300405824480c0c0200b41460440504150054907508044011100c40c0c01c01801c0c2444108803071032001d172007803000d407805902070b856820f800d24201c5078205200402c2142c10a0300c034410001848580c0e92000800c00c2d50041d864030700d044c1e4040c1c0300803030010300819140101410401da4000101035000b51324500c03d0005100038011a1a0701c04002c40c00d0047c0e01a40c0c0481c0031210090f901e140840e0064036240500b085608480e07643c540c0894415031081c2c00580c002a205c130381080c244404200703195084004403910758506106040b4524900b1181e50320030b03104403a02c03290310380c402000346017180c18645064140c490b4107200f45001c9115a000d845070b030300024603034840021298040c03e0244481600580a00b003020110b402120041000a15840e0f2066446030184800760442c40c0e40c4010070000504454292000c0080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 926315242 1250 926313992 926314001
    0x180b071709010b09040602030601030b09090309040b040507020c01050d090b0106030506030114010f21021201050601020f0a03091a0d0f1d0309060f0a1103070c0f0602030a170603070305150a 83
    0x720202c0e0304120f00f8102c152070b4080c001d45c0c002c0c3c0211005860f0740701e00740101e028199410303840e03034404610003c0c000e0041e0048001d00c04d403c000c450801010205109100c00e403941120410301681107a082c9081700d5000d00020304c5c81407036000300050514445e41d102400c09070280c21420020759030b401003103000c3c1030901c140c011700c1d4118152100d103507240032140242e41c0e0b800d000791100d440c012165403e048400c400040380347d23940203114611140b030310070005000f0401211080d00500c500f00550ba00d420011804d007421036090b40c1c418078420300b000300c00074012180c81e503030b00d001400801003461080300c0e6108001075034400c20400f00f8608442d6000d9007011030b00e401d43c15004e800812200c2e100755110000c0300c040844505005071504440002950411100000f505290200089101c100301607540541c0940303d10241c1c0403040f549800003241c0d00e0144520f00c1000c01c03240401c800001e000142c1c49503201c00b00404591882d81c60341c1c0c88034100480c004002030b80710440c5043c440c005281e4001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 926316492 1250 926315242 926315251
    0x11404020909210f13030f1b032619020a0c080304260109022716020d0305151201060e130807060504260315030f030706180b0717 57
    0x74500c4481d600f030f1103032412802c100074001c20240040e0b0038400c180c03d6015503c034500030300446428240c0e203003800d206810103688100c03140e04030348500350804808440003d0940f41c100c1c1066082d101c040009003011150f40705620f06441d014000b88660000508456280300000e44c0608510b082e1032408024100c40f42d003010103150001d02c0148121090303002e035284201443e41114a443c408104100c1c01407071f611401a402c40100641d4503130200d81390007180c0c0a4155081c10136100c0c0d035007810111500c544401d0381c0005030030040c04010002c0c4280c1001c0e400861480000405020700400500c00d28803610a180207651650030410106443e0403209a00c8943c3c0c0000003408211641d80c820340b031281100c000d225603075035404101403000f42d0540900346444c0c40e1b18252a48052500040789030811030300c00d500700c80c3c03c1c0001c5142d030501040c207060b0340170001c000310b00b0500566501c0028007800394242111114400c20640030400c0340404a00a0049880d200e9100c400036240c041035035401803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 926317742 1250 926316492 926316511
    0x307080c07060c41130b220f050f0d05010f0612060510121b1203050d0b0301060e010504110f030c0c1e28150b0102150c070308060d050114040209 64
    0x4d0f0703800078014242c518000c010843e21441682ca04070755145455541040e00400c0746d9032800300d420848111144800d0320032100c40d104c01c201180d0784e108110f460641314091a03400c82801c00c0101003900b410403031215194402d0300045640070742645502c089801d1039010420784405c240d0343d1014802c10344500c0c5d030130505c211102c030080c0d4206881c1202d10074550304014a03d1682c4000d04007004a920310903400b51880d020038000b054800c3c10000d002c0d81204405100c3c051510b9a00d890501d0144298800c48036103904c5004640c1c42c1c401084000c03c002d4030500014101082046480111400298815003c000049444e4180c42021903d0140c0c50001852854014118502464000110510741e09241c03a540c400c1125000b8042030003409441000348010425441c242014056801819a00d81c0070303402c0700d9803252130101342c90154105682c0c0348003c0404000f02c0f00480d12660016a1108000d80640c605403169a6154210360b4903901c2d01050307030403507028801103240040c01302d41c2004881307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 926318992 1250 926317742 926317817
    0x605130911121504111002011a1c020d06050417040b0702060306040e1c0f020c010e0f0a050603090303190b0603061e0d05010e0d05040305030307080c07060c 69
    0x10760350125089020040144980e08800d49900b220b2000c003d8041c040d00d941c403d4607a141040c0c40c140d01315036206404548101c01c0043c40998a40c4140f0448079a4034100320710002c00c0e4890814020120b403071111450607203440440e001f0168584910814842c0d108240000d000c0c50301d070411011002e070f41c03800300301d803040d04003c200802e070581c8055602141e012581c00d41c0d29101e032400100101003124036504580070301491a0f501c202540b248502350030841d1038520152420f0b140c1280c071181d8280065011802d0f10751902000c0c200600c0c44e08000501400018001c3e40790070006034181c1041742e04080c1c50f40700008100b031255450912507044d601c00d031018082c50a0640004503103010060007039018221052300f054048040200c80c81c5200809400c01c00f840d030b064100b0341d02802c40c5181c0022144540f00340031045a10400840301102d070444091820740c0c8a4100490311400c01500b401c64400050060501140781417242e4080c030800c940b654285d64404490440070100c0c40b4050101c3d00c50103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 926320242 1250 926318992 926319011
    0x40e1902180f04060b0402070c0603090b07021617010b060f040303090501020606090f19050712061e0308030901060b040b030402040b15030a0207030c050708010c02210f1615060513 79
    0x74490f03420591101c03002c00d00e10003a0005c1170080c001c4440151120300c06600004809402d54000c00285001d1341841403d5a03039580f0680c3c0c1e0790a0f01a8200100051120802c288a5040c800c0a01060400c00110b5020503140001c2d080e5045940d142c1180c1c3c000003001c104141d0082240c03001080c00380050402d52800c0c10008510081c01407160448036a414002844c0c00818440311805d00081c1c0000c200c2810410002080180b4400040003054540f84020a2942080e1002d1002d50b541c91280c00d2401d00710fa46461907a00054244186036494640104aa1118201130806008151101902d900e8240100415038801111690003100c07642d4450706604048001c40b50f109404e407002580c1d03101c4501d800c4441c040711f03107000b030041e0044400200e8003180c1174207c4040000250b0854201103010a080c0410f21800c04006000380d508010140c2461407101c0a0a480710504454411265041d1103402201d0400d001e150000c41c0e03242e809100c00c1c9854142e000d040c4007034180401c1003000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 926321492 1250 926320242 926320261
    0x60906070302070501090501141605030c03131e30090506131a1b0607080402010c14100b030609010603020604090504080c1e010f1b0e040e190218 64
    0x180503280c0300416400003a1501444025000700c80159400002004884481d05407907030742200664281e84801c555000d50407030340e842141903c1c060440600840c0c40c6031500003401c408404860320444203040320200764804040d2011008540c0da0080c03105564400a05803256108095a40400007802c268a03c01c9a481d600400f0a41564000d41c1c1842e0307610841c2004030076840380d550004415899082070390500002d0781004e020144265044c003600702844070509511130f0011252034000039518000034000d0342c030940b908a03000e80034640b00d03400c50001001031800d10f1650151003000d540c4400c502c1c000d6003010418079030700c5202000200b2046045900007400c074403031841841072498031a4045030500107400700b10f5400c030591030b0403150105030400011384055400f540d44030440d480c0c4140014420124001c110b00076007580e94013032180b000c0c5080ad94050180507912070b0896602c10308081d035400b080000b088900170000304101c0b10003403407040200012046400000482c4003006100100c50b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 926322742 1250 926321492 926321503
    0x30201020903190302031b0102040521060603010b091b0f0708121f032a06020a0c06180b1803010f2007030921080f2502031b01050c01110310080609 65
    0x51560300a20031f03c2e00c8034000742c00b80c040c030340016a100100c10741d0f500085100c0c0842005d0101d980040e1440342c3d954a04141c201c5410842c00c6820415000c001007280705623200c0c03070010070707041029141044507540b4620402d400940048880380000208680045883da82041e407001e1000410001c044007864403203054102840300511605400101d0702c2d4444136000030001949540705100065a600c410007036803100400004e84411030701d0f890100b4268810407804000b42036240300c10382c00a141c0000d500580e40464040e44681c2003180031546995002c0c051044802e5000402050700c0030504000d803401d0b42c140d0409103202c10f0403c01800065080150f000440d04110720151000041e009200103401d00c0800090144100180b07100086014801034040001210840e02440402241030850848a800c002e50306520040c0c1000e000c00c4002d01039124084185401070405000000c0c060039030300500300c080c103070501c040200070601042c00d0041d0020b0000400400090a10303161b22900d40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 926323992 1250 926322742 926322757
    0x4030807140f1e0106120c230d02100215150f030118030309031103340b0f060126011e03111521040c0906080606120c030a03020102090319030203 64
    0x10310040f1107409510340c00e51100c0010100b280c40d241c481800c624125501c20400c0c000e07100701d0340f03d038100c054030310595034198501c4180241140100d010320340c003001080a0280ea04104510441e49861708510710085228010052080186106c80c200001c0080c02d151018900340260b1403ca0395500c020200407001001135058100020070100a08044414001d810301c2e80c2103500c4006811441410340c265034071156188080004e1807482000d0100380c3d50165004003509910204000c507020800f00c584880c2c002c00c050401d28000000160803402184000f444401d142e802880104651050320b5560786080020b240300d06801800e55540b00c42c1d240c02125440d0190402c103c0007424010300804440d130107058159074445c50001030100d801c40d16000c0b28215480485a5000620800325000d0103049c0d0300d0030310103050301e965004144400701c1160740f00c502c483d01ca40415000251020f000b150115800f90340003607601c1c48241e003407500e01544090794413040807882d0400c1000c02c1e80802640c0700b030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 926325242 1250 926323992 926324023
    0x3111306121433040305072003520803030a05060906030a0818040504050a0210050a020d030e0102040506270a030b070f03201209150103080c011104030807140f 70
    0xc51322581021110f5025114004011481c403403000482380c80355001c4400005070490803202229880964071103030032400604403044080401e0342d0381e9031020340b41c280d240c14084500c5a00c0040c10000050259109a41c03112020780c1002084c00401c0c00d15005a5600c80c9042c1d803e5038050900d1030200c4d54071402004050000e002c042002d0308003450f0445c290245240041c028405070a0508200e602e480c12840102c0c410910892402c040c81e0050051b51071401054025210510030f144064010741103030065602155420040410150b6540d0060308961500710f240c2d0b241c9200501800300340050845d9001e12810f950b0f081000002c81c5c2e04185980030469241040d1207485601055029006d550714502c01c1d518032081c0340f120380500e4801303802881c0d042c2c0d4490f00340e44c50750b2902a4903028405005440070301030000520124490310300400c1c00c00072200000a8480f0740c842c9480b5142c106400031a038034a4005008420b0103036101141032101002c01c0906103030620703e80260761b80c02d050201c2210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 926326492 1250 926325242 926325343
    0x90e1e0c0919090b011401080405060703150504090c0602070b0405030c060a1b030206070f09051804171201050f060c28050109051510031113061214 65
    0x602811030b1001c88541d900c000140b2050240345443e48910000b4000d24a035030a40c09807039000d56210b4950140070f246c014000d09441e45030000100d01800101e2140894407032500310008150701c5a220b00200c0ca8007800802c0c840a04060000b403c0080c2988004480d003070070f00083c00035640200384561081c170100c1e14a80c1e5102d10740c000f41d5252588003401020fa60309400007800703054022031028440d00c40d41d65800c490014524055911070a00e000e066001640c1c0580055502d41c100c99107134009002d50030284084001404074001c581c0060b00c2d4120b10694500100b01e0781c01d003005d0b08002c40004480a604100181e0b1101c0d50303c0e0400840e180c03c0ca404c0e1003104007100b48820610315070340e41003002485500d4190503c0b030b907101001300c508801d03034003200001f8080d0030703520b0102c1007900c0c2d100451070b20100480c01005000c04040356480c00740c50352403c1c0000c0711000140f20780d0300d0030322514500e0b2004100180a600700014201031401010b5011860300d4216484007400b44bc000c5050803c48 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 926327742 1250 926326492 926326501
    0x8040818040f020c01060e070521071103030106030c020c0108190917131d160f0302040e090a0501060816060c0f0611120a02090618030a020a090e1e0c09 67
    0x1c015141e58030241c0011031000482403001d11041d00032400b610300080d090034642d1120042107504d0710a10101d042d0384520b140000d07011700000b49115401ca51145815401c0940b11a00b540c111313402a0b129034082030740c0303250030390446405000d69040f403202400e200c01a440e21110905010901508420586a030341007001d0410015990307008404401403c076545482005903080c2c83c61305640500b00d002c0341c1c0d0307448201104031100f42140c803801d0051a41d80b0f080f40001d41c01c1e20104e44202c0d000080c50340903c00801d0f505c8a078590580b01c5d244000c01403520840d581005421128a600441364a41003c8880b21028140d4603000003119800c5c40c01c04a00120fa00f07052211000d1103600404190034583e40d102d05690800117044414000c52116200352207594013070301240314402c0342da604080c040c024042c00030018410303504820300141c02e442c0c0c407200e282d00081e071850040e000000d07199600c580c02002408200590a2003866104410b654111020841030340c0701c50792031005120381291070004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 926328992 1250 926327742 926327749
    0x10e01090e0c0a0e0303130e07030209090408310b131703070c120209072a150c0306050a05122506080606070b01030219031e0606050108040818 63
    0x1026080030340031041c1050038081545603c25081d01e40018840b85410446181c0407003258000b0340d01c14101c0c031603d0701d05804060030a0f0300805260526909104a1002c0d44410a55502c6240f191004035500c07420460f2000b0410502c4110408080c44030252030f201051401d4114140c0b007100100315182e026000310290740c2d01d1035030070114000460a60421a40800002500e0b00600c10b0385117007040b94440050315500306800b40082d40c4160544089180540904491018050311004800e80b202820004200700d200c0028212401c800ea10f070000e1406446200e400d030f0040c480e24052108526140004040032100d0150600c9202c1c2c11405500d05a020000b03000c40c40410310000d06095041400d41d808541180302d42341c003059401000560030300e0020226a1801c1d0703c078075001d400340d013180c0174406100402400301d100c2c1c000c4c03c0d60102c0451942a000c1200e10924104411100741030b00c0d04c003058944992110341800b85460074400056880e0782660000840042e030303001015a9100003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 926330242 1250 926328992 926329007
    0x10031107021f09060f050a030b1f0804020112020a140c160e0f151e150f0306030c0904032106050603010b0309070b030c0d1a0918060108060c0702010e01 67
    0x30b50105041407007050000761540303800800c0200351140328000381d83c1c5505507605515902c440001507010000c003c00f86000e9030110203214400392a01e148600e4554110460304ca04000290114050508010440d0b85c03101140814900300c46095007410403c4070b028000d404003032508a003010011615138040c810030843c0302100101c80020402c0941d80f180c140c5a020740a070f8121614402c0b640000d0201c80c41d00d003e07034008103000b900300c84405a40b00c031110141c5a8450341d2961084443c070442d201103a000004d08480f40304007101070358030304000b0200f500c0c2881030b0f514180220110307020000405c0c0c000101040080d0078401d90341d80c040c01c8451b65001010b80b90810382d07112101000100310050b0101c060b51003a003840040320ba01c2d5440d1025041d09020071600b003204000100102d02c48403086810a07004040364846008641d8100000500302d40b41c01c8a13814040c41c607441c001a00e01340100201030041188002904981c01c00215441561040d400041e0602800c6a030003801070748540350 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 926331492 1250 926330242 926330257
    0x70b13050d050403050d0504120b070c05011a0a1a0313060207080a0c03020d1812210c12031505040507021516030e0609060406051f0b040e010b09100311 67
    0x40d103540403003494025150f900980401e860340d210340a078409255000c1d004550565100361041c0200c0416035540d0314980c80f0040598041003540c0c3c0a040000301c4c00d004c0d2400c86101808940b401441220501c1181720302c6a01200c0e02002940d03e191040308500122a00042181c1901c4402c0300e0604080c000781c81504002405a0400136105040c594041450041544640c0c2541c03011040b1a80898951501d413210045440d05000204030044405018050701480323000201d00e1481502e8842a43c0401d07104c1c006c0216034402ea44404104203c050800e1803600b40c24200192884c0b0b15400d1010030f514000e0f45e024680d1103021845240c000c106d1034015451000c0070007010f1505038207a001504203050520b0101c0c0c24941080000100412582c3c03150100c84001c04240c2e9542c6c4882c0302800c00600040c840d105902411231020103449120400307001c400803196610f07441d00c03d05501c52001640302136080300b07061192007941e035074004598032030314007500e0b022a42405400c40d003d800c1c071070501c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 926332742 1250 926331492 926331503
    0xf1c1a0d170a110f0c1512150f0d080714120f090d060531030e0603100f080a0b100302030309090c0f21061807032c1501050a050303070b13 61
    0xa441101c0b00070001030b0b00082e96403d541c43d81106d002840942c4203402442801e02c88900311000252500180307903000c41c030511009000b02c400680314400f042d81b2400c4d1040c29507042200061400030b11206080441450070740740001c0108500c61800012580500c001c0590390303000000b4182e41c1607503813101c100b8070581c12040412450410b099070084481495080629103241d074070320042540481481203104e0340d00354985141142c503a00811405900041ca00071350311003440c0010603c4e16040c51318101410146009190540c0c1d141040e840c51070006101e0034811180e01c20910050724088243c0c0c0302c0d281c1c1034602c4601900c500d007c1c00d81a000b0842800300303803031012a600710300f0092050b0700d603803000400180010719110207007445044c05c0070000c42d1300360040c804086081c05102e907000c03044400d9008a0007510f42440100407003e908c40200c80e500c190b03c0b501c5912042c00303019800c40c1c014102119500b45007803401d0003298503402280380150280c8030540006a50454080c1c100d40c0055000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 926333992 1250 926332742 926332753
    0x60f0703090b0c090f10090e040501020412050303040b01081f090c1e18060326121302010e010c02010909110c0a05030703080f040c03080f1c1a0d170a11 67
    0x822940769001513005600c2402105005041410100e42514001c00c83e40d454807901350030100ca05007801c40c06001100c080d9420400000c5640b044080402e00d60300c12000340d962402c0c282040c100404060708045075681045101c8107119400304600d29030a645c0c25408540c2220300d040c101c24100050340440e80c8108801480718410601a020707100352234501d080c0c0c04a0244000e8414202e0fa2540002824003042c40643ca10035001c0444400c01e41108240c190300e0400303c1040f685400d1816218840f02c0e60070030214204560f00804603030441705003031800000302046a00001d0a070880c611480d03003500c2c0e407011140d41d42810103080b04d1100307000070102c0d15080c40074500607030380354001941036000840242c00b1800c0b0303456180b40c1070700849e0002d920f1910541152100d1200d980040f1100c01118410012184d1980d404481c0c1c1e1501040301e0340000f0058514441c1e10f1102e00c5813002141b02c0c6803440810300c009800b80c00c080c0e107860165800650ad07021100d00c2a181070150710305095441c8602c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 926335242 1250 926333992 926334001
    0x90903030907081225060c05030a0e2a041d03280504030b0703061205011b030903081302060906040306050106091202030a1b05060d0605030f030309060f0703090b 71
    0x440c00750510720300300c400140c1c1e111111a1a10504144a840d0a400f00140895140c203803403c21641000040f150062401d5507554004881c09481040089840881007003405003151145881e01c0b040403025244225105e0081c100804581010007100c420014500086440c0d603400b1941e5900c81804c180158007421903400e6032500103200401305450b1200160340000c0404030240d0040617141c48460806040d50b40c0d0001064004115000701aa1000001407901e2034208890100340213400000d0584000340d9001040f405680f00e450506040002100000781d0024205a10a046d9095600d04024510008449200d440e04039540814042404400e000f0709900c103034120b500680703030552400d6452408818400b80d51001940c580c111264000c007040304128500c1c030f1380103800401c904842d00c1d17000080c03654004a02040c4d081c2e682d14424405801d00304103000c49406034000039419031500c109065074a01d00200104e150031000b001044003e8040e81002c01c030680d0003003d2440c1e5141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 926336492 1250 926335242 926335261
    0x31205090303180c060f130f0602100e011806020c07060305100e040f0b040308091506420703020c1206060d06090206042312190c050303070606030b0108031602040c02030909 76
    0x100f000c5081f20759a0000008080c680d10081d402110383c0c41e00500020020b00020703c00410ba86c032680c030111754030350309a40d00c144a102000d18085104403030050b110207002c1500d5150001c03540003c41410b00c0d210511085100701d00000080318800800f2110907951441c2070700c04580c0c00d810050440c00701d00c00340000c242d0442e4442e40311303d00680488204180d801c81215484070296445034000044281400654940e6481c407000c2210902d40140f0410315940035081d004802d070755005c08600003060030020507074107000303603045000d04a940c00090504014420b88824010300080d00c03d051009108042000ca6084214000c4d0000e08242d1100e40e186c801d0b00754407031007005102045800d05510040d81c0782c02c840481050480100a210b880d0742d203801115110000741098030f1190003404d002a180d90100001c2000d18490079011802c58694030b0007805c8402c1c1a0040502908240000e241034031311681d084038210b0301101c010452a0458105034250311a440c043c0390041100c80c208000c22a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 926337742 1250 926336492 926336497
    0x19050304050f0307020d020d060b18010f050f100819020409140a050910050711100606020606030d0206070513090e070e060409170306120303010e04031205090303180c060f 75
    0x14080c5050301e5002c094505180c1c1c9a21810b00c0081d80b040c420b10301040581032070001300c181e0601ca0240002c031042200e0000380640d40c245c03100079a5402d2040140b2805005401e250000c1005550404c903020306280020200700e40302c0000000c010200340010408030b0020407025031030f80090811550745032109404409800c0210703100c0c050300240804100b000c8101d00c19640b144228030007504448032440001c1014040162184080105249a00c5035010060105003041c10002d0b20019646243c00c00c043c0c2050340082507a8403a80240c102000100e80120301c031a8802e10515040340d907080c0101518050500035046400c1e264581425a0240440013903d03c2c00d64201003241c0c0c40c02c0c1d42d40d50410058400071800208200c0a1040401030105004050340e04504002c261000c0010003140c07551658000741e118171514003100c000d00051680003180e00c1d4401d4403a1304140440c0c648041804c0e075030300c00031740001c60a502200f0301c20030440c014000100030440081905645440d03040048a0b1078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 926338992 1250 926337742 926337751
    0x408070303060506040b16030210140a11040f1a0f0a02010c021513060b0f06271f26160e2b0f1a0a0f05060f060a020102190503 56
    0x2d00e0075001159500c1c156098400715684100309a24001208480c160032205a8908800794400d4415603035440d0800d0040b26090000501c0d068018940740404006650405101600312101000180b01c048503680ea40820346141c01e03a0b41c80c0044032440c811925109442d1042c20301d40010541e001215810b40241c1d815400c075a007101c01c100c00c0c403000d00c1000c20003a00d01c0400b044150300341e4800500941c220114000d0000c0c814898510f400c0d010a100e90303c0107003a0704007454040e40013a000703c866685207071000f40070307102801d0500c0c01040076003101000784401c40911000c502c00408005015900528100091311030403a80d0410140c003107480c0801c1e0b48114003107660703c51441d40c0303801c001105200115240083e00c8ec10046004103481510f07141c40150340484c4403020343c1010503011407200d4070300b6002115041c0c1034540800d16030126060b1400c2441024200740c1444003da566003000c8200d80400c80700716507200340b01e03801640240705804140840e281c5502c88045030980040180d44503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 926340242 1250 926338992 926338997
    0x25030c0e0109150e0307170f060f0f010302010309080724060803070f032001110304020f01020a032a153207080a061d07090819060c03021204080703 65
    0xd84284001941d03040c119008648110780b0150035075042510803600c80c0c0100c0005419540255112464285180c0c01c007246030801d83d011201c2030f00411401c005c1141c2c880880c20301d503042d50070040000c0841850600c03001c0d04041c2c1b41c445080501103501e08036209035030f00c03049500700b2038542c5618030703521000d50225407201c5140000c0024181008001c603801c0310303445154007680e11446d940c165642c3c600c81303201d080000089a0600021002441403003180031002c0c26560300c034038051040000c130b900d050b4241c90464018503681400243c001e00c2100e002180b031100e4440040d540c20520000840e02c03540586542403802d9503c100c950b0a2303011a54200d0156a0072001c00e2030480c0d0031318000785502e42c1e2126140d5030400034403c68031a0084980007800400003285060b40c2e8800b41c1441104108004841940b00091055443e0000d520a004121181c042e0a61010f00390007030036407400182001c0d006d103840300038050300c1611a9049966441c3c0000090446080a040c51142d941042c0d904801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 926341492 1250 926340242 926340257
    0x30f09120305010501020703170d0b1503010504110403050a0b090c10170115082404060306051e070c02091e0f070807050f0a110709021803011b020c060325030c 70
    0x4c03554800714514060f260010749440000e200300000302d01640c800c2c8240d001080d6510100d0743e40341e0316000900c158803480c80341c05072254100002c01c01100c42c0c1d5510201000c1c003c2004200241000c00c0b0382010641144807444240d42d044052030034540d1f0300c1c500a0740402c0d504125490550041c9200070948440c2415100b544e880e0034016550040400d1104045025800012003040002d840c01484071040360000d078003002c800e03005c1000c0d9903c42e001100c455403114100410503c0020040485a030403048518040c10000005410314456840290144110754001400541400c2c040c40303c5c20b680d0050300300f031840c140c10722011444040d1440b40c0001c405401060030780c0e100304140c40748044080b44032860b0245005090764503804031405801e04d40181c5400280100e514400360100c65482c21010f00100c0000c403c0608560000c00402c4247c2600309100c40700710343c0042e18200050040d208a666505e039140e80380c4c1c50180c0c80f952001c3c800c20741c0c5404100203070300d9001120602c89035201c100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 926342742 1250 926341492 926341499
    0xb0c21120f0403051b0c0303030f01330c02060417010204081501061d0103091202060601032a03020702180a0f050a0e0a12170103110f01081306020901030f0912030501 73
    0x3a40020180d03000fa00058040c8030a00e902a101c800703c1540c3c2d0000790440f18a80c4d030345008281960004c56604081048441c0104000540030f4071071400c5400402c0c40d10040e441c2d41d80c010b40c2c00d5071403c00042c104542440c0d01d07070864603150100c0b000b8295a03110716200d400341d804064080c1d4454003810100f0f0003000d29a079080740c440070a16058494035110743e81d0303040a41ca07000b001000d480401504140c0c540c84001c001c11041010302d160600c4a81c06000145040d9001509445c030310080514030400c90f00115014401d0740d0349a280050017450027603954141800000e034160a40200000ca10925009015040480b548844210710343c140e402d1003640d0368450b6250480701000c10001194002e0f045840000e41e242503400c140c0441401c145e0340312484100e025200c1c4009030822100c0180198101d901c6241c40809102181800d10f060ae210b40307824441d4005d140c2c15914018040b540115404425a0081d00501c04003020194104603046241c141400700316507611485002c03038034000011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 926343992 1250 926342742 926342761
    0x180b1c02120603240106030513060507031a1206160e031501091803020a0b101208040e0117190c1503090213330e101805100b0c2112 58
    0x1940300c0c010f900038071030981c41c206c4183c024003002000761400012401e1b802000a00c80d01c162800b900b041e903000a00713081490042d507910700e990b2820501c0f42c0980407880244000004d0000d5104100c030b8024689201c24032010340300c0f01c0003800044d6240c001d2521191640728801441c6040790a604410b01001d10032a0510001300c200043c0a4011b800586c0e554000c60544480140c0141807041c042c010581d40f6855001503034948001125405000501044810f501e84003082c00350890020780001098002922036580000c0402d00f10000e6602c0045028890301c005110700a244510b4429800068050010002c01d10302030b00300e218024240840040b5005489030506a082030101d00c15804000b00d103004038558450525400d10008800214041040e9050309002e450b07001d0250090a0911503c0000f520119400d030800c83e10781010040c82d1035180d00480101e500c000b0340346694203074400e0243d007003a90b149201038031654031001a0001000321401014079440078100c1104544850405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 926345242 1250 926343992 926344033
    0xb07020c06070c030605130615051f0906210c0302030108010c0e03070b0d0e0109081b01140402060708090d110a0503070f050f0120100c180b1c02120603 67
    0x60000f5140d0f074414400503405910964100ca1011007000c0c0980841d51a13100f590b45d191401102107140700403c11541c1401203000e40c00744080c80999040c44100c3c10024070000141c400d000800490b100250546641800c01284502620b18203110015030490b015000c8e40c401e1003080c0c002e61800e425001028410400e4035072410009001d0001c0c075207000131f03c1c41c0541141d0a010895580c40d82c80800f4840248120080c9a03c1030f40907030b8568400d4640c0010700e40394210440c2060b4104480d49101d90740d00024036501139030444000e500c0314000d00300041c0c140282039040da000340c00c5660030028072581c081140c105d0041161001a5103441d00c00741600c841c031038490f6152040b003c1500348118907140f07040306000101890a4801041c10407020b0441c6500b011242e10f440d0040c0f40384060744911401410180002401c00208601c02c07000100340b03a0042e4812030001c810041112800410458046120094000e0702552aa54446c1e40b460706208199941c40c403c1c455983c01a0044245000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 926346492 1250 926345242 926345257
    0x201020304050c130b0a030b0f010f0303050304030c0c030b04230f100e0a240b060a050306040b21071e05060d05091002040b09011403101703070209040b07020c06 71
    0x14180e42c80542003405504101c600d185120180c559104400c170703484100b4024002d5000d45400c40903814151300031148290180c1246040440001003170003c203410404481d00254940307841c440d1060241002141010580c2004201011941c184014027200440001c0c404400761072500100300d01e1031030180d440d4010320380820190415001640c00004940c00b01a02040481c2500c042c0001ca0380c60f21130300c00070300d0b10700801c84403440c0c010000c60255100f00400450155090b40ca000701298010304607000040529100c1c50f00e902210119448018200c081201041031300300c00c05508103c10781d1101441d0065082e1410401d0401100c203490b5810842119800f0f030400e8a80000d001400000c0d2000821a40451058045504000000e84002e200406107400c215403203803140703000101003a0844a001c0110074040c001c0c4400b0340b400c91000300480d4401c400403901621a22011810b40c05480c0c1c000e54888580c404200c01e0040c8051611310a134525820350361994600e40812600d4000e140d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 926347742 1250 926346492 926346503
    0x110102120a090e09030d0c0906110a03080609090a0b0a1e050402062713060e33010917030c0d05120f130507032f0303091011030307021c0201020304 65
    0x84040090f2418820030325000400d04042e64981086241c410041c3c401e201610381c00241c40c00802c001f1958040310000c410210303a00600300f0301e020360b1070040481034050300e101d1183c84c0740720100d00b00306d5080051140300b9a0111807d18a032501144a0780200391001d881a00300403e2030580300280c42c0c520409218a034001c0100e820003c0000d011a100c8070001d408941c0b1400070744140d20705a8806402210900ea04040459000e0801c3c8511013040c50141c0070076034105c0d560509070744240440501032400700500c0c03990038204207194012201c90308168800c160b1120708040c00c1074a65004001005100800d404842a007996001300b00d80768030a82c510081c2c5120f4181c046958032066190480e0440c0c0c040d44010700c400d815884550802d041503100310369401d007203a0b001c0800400394951542030a45141142104030701500400d0301c0c1d20034600c40350f105010803107400019074003640780b0720340d445410011a42c591030310b4980070307540380d0780c01c40c09610100d0038115640c6028414000c0324880c55028 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 926348992 1250 926347742 926347757
    0x309040f1b030e030c2506080f060f0f09040b0610110d0c0c0e0a050907051e300607080f0c07120905100504140414010b13030609110102120a 62
    0x181e000300c005208009414000c0c4c007040024101e003a0301084192054034460a062449200c0400180e400c218543d028030b0500c03100108201e140705903240c00551107081954859102c120600c0082c0400c00500e000b00da21540e242c052100b03118140081612840c410f41d0b005603048403124013a94600030901d0102d030146d21082400011900c20b04100b030700c40344524245005640c6404000c02941e0007256111802991201009440001004800d0081c10141c40d004aa01c91480940c209079018030243c074000d500100d03c09402c1e6030031070398408403021254a61004a280b0803c020386400007604c02d00005038402001c42d042c1d403141c91004d400307100030001c4140341000580ea212514503406900034280410060002001d031102410306403030540302d580d4107a0f100c0c2001c8158a0205c1c265409034000e44c580108441c1b80810313080080d06440310002c441d41c440034082d240c503200381d4103608014070443c2400d080c403003044424049621a00e0b02602070307440c00320554242016500503040b00500180c0c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 926350242 1250 926348992 926349041
    0x3030301120c030f060507030b0f0102030d05250c03020111040e060f04110c0d0809060906460c08190e0f061f06031e0e0f0f0309040f 59
    0x76600c44091910521000ca9500d60341d80f0780d950301030300000c02074a4982c0c4034400c0001e85a41489600c41410080b14146001060180002d6076405110356148000d503a0b140130070903031341e00c40007454402110240d0300e07009004032000061040307208410860166081040700001c4202940684007620207034030840030190b40300c80411407092148040c440d04036644229245441c0c0408005224400750a0700601e03464150b058000c04062000b4100003d40d042034080c0100d800000c112140c1082203000c402800d406086032190f40c0300440008410910080240e19281d18010842c070486a0122682001a501c8002003950341c1202140c00d40c81820303201002c144008c03400c0e44140a0101018101c984a40302d00b02410702d09101036540303092084070050700200d85c441c080b4410001e40f401b031a0600c900c800740c20400c5112100d8146500b0602c5c0c030340c0c000e040416020407110606c040c22034119010398100340f2a440d01e0350721480c07410307029504048104801d45914060282c4945012412990815a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 926351492 1250 926350242 926350259
    0x1060b031b0c06040c1406180405280501060806040c2102040b04090b0901120f230a03030e010b06090d0803060a12030908060a0605180702100c031d070503030301 71
    0x101120101c10303580c24019400300200c00c018603486a485024181c24040c100003407100c80440000369680715203010070151310202c101c940ca801c00c01d02c0942d4040b030540c640e15002241002e100001924000d0b082d10f50102d40280d40e0082030407030b40f250301e4800c90364541500348000d0790780300c02d1100c010404421000c210204e44001511495054400043c141a242d0810300c02c15030003684100e005d0380d00e44907424558074251320118014039140843d0070141241d07580d207040002c000710300517066100c1e01c0709468050410702140b4a0b03a103a0501600d40184040c50050000c100301c40b41680d0640c41c0035035080032810100d0072206445002400303482001c0490381c42081c0c43c7d00c000e007100c2c1c20586a04000900c1210030600154061003034803010304180c248203030103107800c1c3d00a03d169241410328400f040b09032074441c12201110a2007038049400d81d1221801e80c034000403014184011860310b0141c5001c181c1c16072102001e00c0c010090f42d003076640e030360070255607806860140c4ca5041c0c00400c010050701c0e2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 926352742 1250 926351492 926351521
    0x306060d03090801020d1b0801180b0411070f061d0334080c06070e0a0e061908011a0603100608040609080310030201080a110d09110a0609031401060b03 67
    0xd101e868240b0b2000c2e00c44141d42d0a907003086a240545548548029607249045955801021818076105110758901094400500316040e40e41254665480012032940c8450b0440110501c00c84041907450101b850001460380403442c09803045460095140344400202c0f000544440c80c1d2001136050602c0781861000741c4003e09a0322205a40d0091480c0e4810540c024540c90135000b0300d61030f921000c00d540000d08141000304003004000c025591041207648000481042c1c8203602103c041030703521400441d4051504882c00005072940701400540800b0541284080b81030b4003482104031030910f030501c8035501084d06e011101980400b014040c16100e00c0701664818010b500104030b400c46034803250b1a03940103858203010f5140b00c180a006558106640b55000780c211002000003600010250b101e030701035140e41340c012644800c260001d010300c00540b80320002d8001c0c00f46035150b99449020b00403030b100f07110440d000e01091820055400d07040c4144801c0740c0b907000000e03155664580c00350309040e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 926353992 1250 926352742 926352769
    0xa200601080d0521040f0c090b01090b030619032103090203281b170a0f020103020d3e030106020703030f12050702010e070504092a170604031d030606 66
    0x41c1e004d5131140c16014410400034000da0048000c0c010002050130003030380000d035680060342141e042c9098803002d6680040c0140071510600d600e030b5140d883e603000080e641c04a00c28102240105842d01000380401000402104041c007040340d00080660f460607000d440304414040e5160300840300c012500508008840310003000b1400c94043c0303203659982d00002848403a88801c0110b008101030001421521000640d00961001040101d1255690364a0701e660400c0c001c0c10503801003030701d0704d81805a400c240d40d4450f8401130a0540048005110992042d082014036008102c0764800025031044040300c2c10794205502410b6081d0031506c0030350f0000c40c040c8900c0c080103441002e45004070a20f1090302c1c0645226400030809101384554507150011540003039100d02d00d80301003030b40041d01610310800a00c0006000008100200c10381e07040481166000e10702201d038180e07843d511707064080340007441144aa22140014100d288070421601c3d074a1000e150150b00c0798000c00c000c4d03d04100d07450300d413 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 926355242 1250 926353992 926354017
    0x9130309031e03021629040504060801050609100b030106050f070b01091b02030a020d030506040e0303100e091c0e0307051c0c170303040f0c05060a200601080d05 71
    0x2992940c440b009030010410365080d0000610801003003590501c055035001e0003012a00c0503141c01d0098903030700d0380c801106200b0081c1d070050700c2c1112220b4280a98008160080080281640e00d120441c003070002180c00714810655a40060340c031655411100381501c4a60140506603030801d0300c26522907001507180710388240c0512030000003582c82c2800c00c0c044d06440340040390303824546050341d074690b110001c9101550828409021041c0c1e00107110302c81f4034140e00c0c0100305516200040b400918214188282e180000420841c0f050756290454048500002c1d55a096569000301c2a8403100c011070040001c500c42c0c582040ca192040b0b46480c1220b40c01801d89072000d076901c0014507a007000007484000d0142180e144000d100a26002000500c101d03034290300c5003029000340b10345130321004000414054800404e8030a1108a414140180201802e92562040c0c500000f410f160038002c40400e020020b5464030000d00c601090300c5048480354401481c4220000f00107450580124111820 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 926356492 1250 926355242 926355257
    0x203091210051302040b0d0206030a0c0509030a080901140a141b151501020a0c210c0f15030903090501030506060913091a0403080c030c0f0c0c040f0b091303 69
    0x5580d1942d10640c0d0262262091082c00f01e00f25205000a503585103ea1901ca800109146400360719000b040381d521003400a8002400013981c0e03425502c9020380002c03c5d8040c4541c0e400c076010013024000402c4000700c262669414400c03407250707208503441b030504000e00144061000381d60051134800a010780149409240981030850044545070862040382081c03480c03404030501c8244400344c41010801035082c03026040207000b9440c0d090341e4400d213110f07044080340c0412000461403195600e020704583c2c0300da20610f840d41d40d40d11402c1c404519008901540580a0803031007401c2c064401c410070a42d15844420800385080015002840c00800d2560404c0f401c010014080c0d5030440c46200e00072061000042c0d0b0f0f03410741070003070030000d04080741210705011100303010119404c04940c03079018045c1900c0316604e9a034204100c17424043c0f50345442d602c5c00d0104032605860b1b400320b000750307491606860401c50308610780842c2c02600da003031038440d82001524011582102c1250391780c114043c040d0a2040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 926357742 1250 926356492 926356513
    0x30108191a07271a070507030206030405010b0d14070b070b0a1505030a06060f08030c211912140105010509010c17030c07110906062508130608090d02030912 69
    0x1111060032054020450b400640280841035070354501070044c0f03804510b4582041503a03035405070b549045002c068030030341c40840010308000c8250030940c0b200401400615030f89500f45011401c08112101c0c4020070300489201003907200425043d030b5a8941c0024038681152100030414000306024603044010709081131002c40c075500e00700a500c84540c41510001080740c501203844c0c055407a65080001690810080c50040d1040002c1d6011034031404802c50801e02000e4070134400b0f6105040d0350740922402c01b52107a007910f8101136031a0180c000710400f071000b618170b8003040c20f02100c24000c0c90b020480c24418034401323500c40d416007100b4500c1940014801f1085c810042d105400c2115070010030100020312004212622007001c401007815a030780000d034205180051031902039901e01c00d082280540b005401d121602040e410216005546140d0700c404100a13411081040d0041d41c022400c88004106d120000003100510703142903a02030740c148001d01d810022290807542c03003c04588503004698 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 926358992 1250 926357742 926357777
    0x15020613150c17100602070803160b0a0b03070311100206100b0f0d0612030f080702070306020c010b100f020d1806210204060518101d0409050f03030108191a07 70
    0xe42c051184c40c107150950700d2030800000d00c0d09160350811034803074000b4880500074051643c0941800b81d804541d50f4580d07910801d00f20020441c1407000756042c826803400005100c0300c000b815141c1181520149400d0850003820307640d409040d2a41c0d92201040c500800c100f01c0044041e102080d010301d5038074504403801145101307407800743c1c000401c09102030360500b04141e0082071990544c41d690038419624030f00507802a44034001e030b00c000740c511500001c0310003140c03100b0760204040e410010001c03101091034030f0300103040e407280040c4003015205588101d40403a000c0c00b03051007080e500030207003071000e41403400071502c46c600400e07050100815284141941c0d9820f0020b40301409075a650303a600c40a0102c480312048040300d001c2c5015014020724580110b900c04003410940c22203811865200421401240003060752500103409800307070002400507604048001d604031400401200d1060705030034002282d180c41c1c0c130001440c81040c0500e6112040c1050074135a80944642004070660103d141c68 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 926360242 1250 926358992 926359037
    0x2130b09190806070e031b0409080405090412120207020901180605030601241b030f050c030a0815060a080f150907080f0907050f0f0307090615020613150c 68
    0x6010380b9004442000b0113030380e015420030504071045008001c0c1014601004220042e0415101c2c00759441d42030315020f100c1d461045078001c107409841d541d41413515040950140b0042c080303080c001250b071030511a20304020300030340c0c060907001061102203900e85816903079018800c43c0f01d180307840c1e103035100000d699a05200650082451441855041031340034543c1115041c0c404080c0b05201d00b4014440d43d1040480b000658198941403c030300000408501ba1842e0240050100c4103120003d010154140c2c4042c07414042c40304070240c191003564180c10810035015042d07108001420b00310000d20a05500400e06030000640312009000c0c501007800703e003031f44404651040110346c0200074400100001d5001d298800b078020b001d000c1c1242032400107045850044042407242d0014208282c0d0740d80c0620141009019415082100a99524021204007110104070026014800014582e80c06000700c1c1c0300543d030310422034141c48800d140c0c3ca000604c242c100348010000d60342c90015044184e03402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 926361492 1250 926360242 926360249
    0x10605130f0905070f24090506130b0414030f0c062704020d09051603020a12111c021201020a080f04080d0c0e03240703051b12061302130b0919 63
    0x20f8110350181007201c1b03445002201151600e00144540084c0e490f039a002d1300c40401e6503021580642e071a80d01c4510212444801e070040d10883d030000600082d04441c48400703030002d03c01035017036840b000351301c000c240d0b166440300c1c40ba07039080003081011a2000140e18403c0c10a07070100400380300840030b0003010400b280c02420150b6601c50f03030340c007040b018000c0030800030500035070600c2a0b04c012415039020480b083c0c000d00c074041c0762501040345207041281c1740f031103840c0405001c0c0850340408020340031088003800004080e4002d50b0b1400340818044c0d010700858505607a15103609800341c4464852081d080720040098540107028051810210464083d4142201c055618610540409010582028080814042082e01c0035411120011081d4040c80d1f0081c0d10381030000d229514008403002038542900704045e4500006003201441d52135240b028020074060714100002040e4aa00398200e20964120800c0012680010002c1c1680c1c600242986900540768203100440e03c60250b403203061540 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 926362742 1250 926361492 926361509
    0x11404090c0e0f030606010e0f030307140c01180b0f0a0306121b06021b040c0207080703050d0e04112d0706020705011a01050307030b0d0f03050c070602010605130f090507 75
    0x2d10b2801286807500b6000b000000c100d005c0c00b414100000041c0c0040c4510391058010400721030381048c50786e001e00584441c2508003824826221070642e0503038841c0d2094a0341800b10710851440c0c03c04429840d488426202d5102c0918a05804410455a40c0d00b003140c0000070151140070100b0708200803250203c006125584012036140300c0c1301807980e9441d460b0041411503220880c030030b800640d01424010303400d0381a40d00040f54031003d001241001c0140d0448905440342c5c0c84000204000007a80003802c40c0c1990f0360b680502c501000304015144401400d140610083c4024070030144a5450078461884004540c042588030010341500e540104905942190b404070b0814180710b0280540b45214070300510b4086d9440c500c0300003074aa400081c0041080607984c3c0c41600705516010080340c40150020045a002c440c50b2400400c01d41c8011017034241c078090f448001a11600500440084d150010000640280c448180000a154002c6100714050701d84503800040781050003200060a8160b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 926363992 1250 926362742 926362757
    0x23070c1509090c0c23030307020f010f110a030509010e0f030403110a03022d191d0903030a02130b0a0305010e150d0605041a071e0804050309011404090c 67
    0x30a4050001600c40e40818492802c00281040c0c0c664448007100ea100c0c2d00c01d00c8412071440c0c0050101d03401e20360036503944076448000180207905400050340d480c40d26196000b4050105516040070540c0d6440a2044030b080c01071084806c0359000b504090341c03090324440005100b00040d2a401d140c00400c0c5880e29041d04000b5003401400300181075000101d106a800002891031030f07020941d10034070071101c1101d0105c2e008c517450210885109586c40081c000700358603500c009001c4043e5441b05248928181b85000c421442512081042024418128000a14110750721002c0800c06507014070131000c0700350402ca0010802d42c0301d50000d0038240d40907990020301503041c825401c000e404c000d0303d541004e44aa910b4110070355607001d0341d1000a03500c90004a81600c3e140f5050500140100759400310b850180200004207601c02d1030403801001040380300503041e010300c0c0700361008601510040c0050300208540d25145d40140489028050b083e2480303407074660740344039000c219000a03c000000910b01f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 926365242 1250 926363992 926364029
    0xe01050106080730021606020d1e0e1b03010b030601030510050c07051b0d021201050403081305030304020415050303031503011d0606010c0c08192123070c 68
    0xa40d11850300d0644000442c13540d003800a000034a030690b403221304610785d0005000503115060b03174625207203191701107815074541582e0300c2d42202522080c0c00080011170480540007020901c4c0c000c9030103440401004e40f103605031212507202c40701829103500e0342643d250140c1e03000a440c00c102d11070080d40154080c1c000740401d5090b080c10b0302c7c0c0103448800841810b00103c40820b6011a100355070081400c5465404420140410407101510b1000380d407207a10742d030503442240c81c1034221302d114034800d41d982d815542d20655a10420703000c400c80078019610502c0081c00608056014840d6624020121580c5654400000e40b550b802146c0d0865085d2141503000c6c0242000d0045401501030540356652100ca41600301d50386a6009042c00d0400080c0c0f100034007801a20302c0d48002400615054484440010000300104851040d04941c03130b10300c4001c85400301d00c095400c03141004482c2d56140207240b442c258408080c11a00088852070780400a4800141c80c10b20b050008100d07503020012021039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 926366492 1250 926365242 926365247
    0x6121a06040b100525080d060f1406090303070f032d050a08060d02030d0c050709051302121606111c0e060f0708040605220e0114040e010501060807 65
    0x601800c51409141040211410341d0b40d0203245070300c40221480e125403520034001e070400c80d0780c041105100010b00d41c04502000d10120b0340040c046240c1012040c403005a03150100d1800d080141704145041504c0c082c541b0705032400d2002051a500300408507424035606850360480d06c181610110f01182c25000c91100c4130003e04100c0e04040400315460b0025100444054804e00c5400d10340010401d1807000180c10340e58466000c02c2207500a0102c917420180c04d240548490382c43c82c01503480344242c81000a02124038060700d032281c541c180d4002000049617082c409506d4000780d403200c1a000340020786032103204400205004240ba65600c882d040101201c1300d00344501d025401030460316028060004580001480b10210f4043d100c8654079421960b0868081c012803400425005001400058942d44980500600580d4031102c184002c690107080b0488001403060312040c11502c401005041e401c480d4051305203001920225040060150090843e42c0980081000c83c05a4040c00007859 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 926367742 1250 926366492 926366543
    0x1005070c0b040501120c02011e0614040509070603111e040e09010e0d0806061209030306040605120d03091a0405010603061d0a080306030703050d1d01080610030b040612 74
    0x41070103400741c509401c01c00002c2007201c2c900b440c1c0c91030702d4072983c0d50b58505100f540820385103400d50342c1c010110006070301e500340640460701c50a082803400d56903002a81c50b2038491603004240000051880c04c1c64408146c02410200611340480082031141c14810006408a041c0800720394001503650303818510145140c1501801d80040d0b60724000303c1092a5a00003000039070b080325400e00c20f0150380e824000541070320a11800309c05100341c600c1440f00c0d0320070010145000b11422501440411345940034040c50040007070ac00351aa40c008400008194040d5025080c402e000b000708003510142d90014241c5a0401c0d10221520380d5610402c00910203507104080d083d07061050380e813100c041c15507260383d601c011101024051481c0040072603101c1d6000c12000c2c004560040548183c0040f604000d0300140020420b540c0501c0e80d802c0000d907030340c030802015100700d1004141808482c00c05a0440040800012154116988900214029040c034807600190781c880c044148000100190701100e55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 926368992 1250 926367742 926367749
    0x270d02070906030803191b030506030705010c030512060d06090503030a0510151d04052502010603230c040e030703031109010c0803070e04090c1d060306070315051005070c 75
    0x42c5803a4040c00000c40010072280c02130751035040da6042841c0450518001d0600203420000c3d040c00d4070441114a4054205a00c604402c900382c4600c0c503035803c01900e0b040000400140010344c20001307030481c08400744415801c000041d101344c80020040c3c5e034100481d00c1d0070307001381c3d1903074004010020402c140b400380950007071040c541e20300700310310b001640f205501011075014207001c540c00412440e00913802d482c00036131200500500c09070414a031003078841000b81c030b808078034a00210003941c00e450050041c0011640d0010120b050190740c041c50764018401308291600302c2c0180030105140341c1d61800380900c0180550b01a694074440e40c41d000c1d00b1079407000000016a0414010344030781d40e8109418410554000c85280e40d40c0d510224200e40d40801c462605520524201440c0240901c1e00034080a0381c900d10980400710030709482080180d1400c44025516910150024601a01c0798220305400c0001c9109458110307164000581842802890100000d901040910074480c4116120006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 926370242 1250 926368992 926369009
    0x80411030a03020d0509010224010f1a180111010e03250c03080703110105041104050c090a0302191802090415030302212a01051005010215270d0207 65
    0x2858182d8020391100310002d13038401805404695140c00364000d0100401c5504030301d40640f40f0b0202c880c2059100f10081c01141d03455410b8003c0860348503015800801c00402c003082c200d00b00f034404032841e100c01692001c142d0401c074030f002c4411154142401078980011644014540f1091089141107910900f410074071a2464102e080700e01040154041100307898101e10425511601c604043d035208404c02e0104800c0d600c0c1078204010700a4810742c484500504a5003880715403200700511615005e0920303115400044080204010310303044028841c4e4602d032031540b95030103540c0c82d1041e20b042ca805940e081a2600060712011614041c402d440150038800400300b4841e04586009517141c924441500c0d5000e605041586240311040036181e10004d00c1e096010440798850718400025003200e440261982410045944030b031001044c00705980042c0d00815100c4484880e8040c0c0200c040c0c580070041c44000c1c10144c45041555000564151000c000e0255610941000f0b2401c681c952182c4507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 926371492 1250 926370242 926370253
    0x70822231c0f0923031605030624010e0f0612040b100303020d0c06150605130906080a0b0a020409140405060702030438030a0605090906090d0c030e0306040308041103 73
    0x2542e40c01425900580703071070942a045032000182189459148081120f5051040800030040000101001c005540e8264103642040c0c0341e1500003a203010766a0f90302041d00f1100c04020840d54070035400313440c843d0390050000c040320141e10003044940d84803d03200301d900c8241e44100320501904142e51900400040813103191285942c07402500da0b9a08600b210401170715406182c10b00c281900244070004900c0725503400320f03540d084003074002da219007a840d0032440c030040c0000300241d45103c0c40041b076058002030009203985580b11804040d0051140d84442e07402c2c040440d00e61001e100742144204200310414080c00d1074241030345002c0f401071010f000c65008000a000001c840440e40c0c0301d070a20a070402c401c080c004901c5000b42610380c51025041030001c030402c00c0e800c00c0ca800503800c0380d00030b035140441c07a00e40c90051526503034101d5074411140e00190841b4003052003900c0c00c5041c540280750045a1403603060000342091030580d4107400040c404020700040c02943c2d20445500c11003180100b8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 926372742 1250 926371492 926371517
    0x90209151014040902040b030a0507020a0309060e0a1211030f07080d08070507050d02030d0609020403020f124603020a03120605030102040305010f05070822231c 71
    0x108807120303074a00d4500700590703201d16a210301e0524050b14040c008420341507458540b50102d01c10a0780013240d82161960810001c910b03a5070021910803003490705550340c2d84842c0d080401c142c4180040004460b0840103070386002901c0303c1e00c0380010100705d214002d40c1140d002114105854445084100c2d0f40031781046800300302141c000601c9c0780f0108031a080c0203c2c241d8418500307a9050094034800383c2a4050940c65200142d404002044003001d0400200034141d220305244049000c1c84c0002900512145090483d910300700c202c03e500c60311190200d03100309941e04400c2c506015003600c043d1176422400c0002012111540c00e140074518000110603c40c0003a44000b03548d01000800542404100002030700300320000c0d007160000d884081d000303641d1a81d030b9180c52802005a6881580050319000c08541d40600c00d4182d0b9024803e0030000c0d0120030815482c5002c10024400b003201c56001c425042c1c0310f0044462030b90400d11203404094884548241c450840c2500711160900400000300b4081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 926373992 1250 926372742 926372749
    0x310020c123c0d050610050a050301090203060301021303080406091719021c210513032a03060203090c0f060d09052e060b070809010309022209020915 66
    0x11588201c46031104011060b60030060010040c514903100c0c4500001600001c1d442d0590070190050030700740d540311490300f00060129414050381600c1d2001603010401000b039462140c02850700000c00500061401c03402d041e003025071008562046032030b000085030800c0442c0e008440c02004010b2202c1c66052601c00401c1c2d15103c42a03030004541700c07440d503848441903448203442c0154010a0040720110f019180c02d00940c19200c100d0114545002c00c00d001410a1060f41135440055072f030390303241040070b0031640d480c100540f5031b4110f45106011005540300800011400348015070141100694078200041c0e00e6040c00000345606010b1480701d070501d6000c1e2034413011960b8050280300000b90021852600509120301102c04013a03001d00b00545c1e109004007071040100c00b41e040c00b8100b20250740c50250044900a034036024154841c18401c0f6416075000303070400300d030951009040d03c0340d43c030b507400b05250101210244581b0856880c60218110b042620580e500400e0012070408403c04d982c000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 926375242 1250 926373992 926374027
    0xe360d1404050904150f0b1c020108070c0326040302010b0a140607050709141017030a1d03060a0e1002070b150307030b041b0501051201030308060a050310020c12 71
    0x2c050090003110700240500a50302121428800380032001c1c0002c080b000340d007102800400c1240e920500503400d030a40015100b00711a6803565060b1034010055483c088140c9248056240903002d0091300329004181c440e04000364055400c2c00c48a02c10242072600b0003e00311a010015140120741c041401d0000300540e010b146010781c011140944d58094a01e82507040c4551a40318401840c101420000039908403500035100b0207104182804155643d040914490811080d0000030f4004001040b101c0e8440e0b0300010880f00d00c401ca5407103815030100420b1804004581d4805500d940300c181c4006508207004005c407940c01004c00798100781c603a4072000724048020b0321001100010044082c400c0d207003401544000c41e049002401185020300f048130001d00080a0303807a240f2101c035008221903009034292070b401c1d448030b01c17000d10f541c2c2581d40c1500c0f03c40024151991081310a40c0c00a00c90b6420080740c42d09541e03010002d40c5450b80340074035515050750007000c1038145200380407850201c101c2155 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 926376492 1250 926375242 926375249
    0x615160c0602210a1b05070317040320060403021c0611090604170a150e0d09080a02040504020a151101053103140309060f010902030705040e360d1404 66
    0x10140d0360742c12070480035105111010403005e80c260000724858144170f40401c2a1003268000c03101043c040707424840d024401c4c4103901005294001e0341d1400302c00904560785201100d40f002e00010718140e16a00015914030941c8104c080418140c011042000a240940d0700e0241c1070140e0542054500304c0015198040c034021900d9400302443c45120420041203098040e64100340c0040501000c59007a1014011001c0800194400e0f80d600b5680b0034411000c66003280d00000150404000710b908201c0030b410040c0059a1100c900040070501859040c0b46c501d220841b80c66032515580801400780c00e641d0001c0c003003000409443c2c1c1d14946001c607503d0790035010122400a008000092a00390b0340c08508040c50b1410130f002104101104000244003030181030b0f185034070b008681c1c1e2303245042c092780720803511000010018442040b044103c0440903801400f6841c1c5a4901c19051000c203450140d00b40c6500300510a010b11088006000c2c400128082514030b400301403140110320401e094402d510 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 926377742 1250 926376492 926376553
    0xa0209040606170f010b01020304050901030f0606050307080c0a0801050f040b09161404051003150b030c060706050402011e021c0e030a050601050102010f090f020103050615160c0602 80
    0x400103420800c0560000c4040c114002002c0c030030945007549180d8544118124902c69842c00310090110360001055030b08a60000f0510851a8299a00d005114142500849886440c0c04010403541c2c2d061080c0809800c04e40002d120740401d81007007060320841c541c01204664901030602c04240d0342d1221469209400440300602ca440e441105481d120f001c030a1030b082d07503c0c61f510100b4580130451810210340c1c01118140301c6511501084140390583e0320004080100d410351114809500e42c010b25112a40201551042a52400420303c2a444003c0440e41681c0c2c9500300030466811104031080c1040c0005100d4101042d00d00280d075460243e007001512450400c44000d070039200c3c100c0c031070140c0700180540c2c03c02d42e610314180381c0e610001c0c0a054059400e016640b10700d203038144070b80d180c01d5400280191000301950015001000c01400e107c0d0400018400c1000045580c8020280d0055410b1300044840050503d207012001903082602150000020b513010300005000342c0e014480c0d4403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 926378992 1250 926377742 926377759
    0x180e0103021e130608150703020328090804090203060406081209060d09050f0709050703090314030903040506130306142a041805011503021204060f090f12030b0109080a02 75
    0x74003d1103860764a840150908a002ca00e4000c00f043c078040d8941043c40d10101e98070b8425007903043c0e02046440b445d40441c6040f40b4811508d6100c2d04c1101c0d4a805640059040c45a841d841030540c041c1e0408100513400105018150400748280c0e4000e004000207400c1006498800054030f20032003c81c10b1052402280b81408007034654002d558442d4400100d48110b140b0620b140d4644020707216566090f0314100000c0c070854024080c0c41c01030755041e41d0340c40203004826488512500050700542c40c0384000d00000c1501d481d560000d00b00140403962420143d860340c513100082e038000d00350544140c0e0000301403201d80c05000300000c150220008c40042000072080d041402070007a0391041e0758102c64010325407080f0740306034810340c140c80d803a06038079154010100040d8181d1241051802096281c100040c0203d0503a0340025003043c0001004a0590740d5a2159450180034010031b4407440d60b4100e02c40c1d9003e4052095158200b000e00301214480d01d0001c070103840e22510000640030b01c418 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 926380242 1250 926378992 926379049
    0x8040603090524070e091302012a080418060b090f040906110a090b0412120203130b1207080907053006011503060f09020702030a0b07180e010302 64
    0x41c0001c46070003400f031201d0341c00001d080d82c0f1622201002d58100c2d022840b00040c40c03c2c40d05000400300e03c20140b034031109122107511341c011140c0d007512600102c000f4880c14801d2004c030ba84e5502d2120614010080786445030b08060464921955069050310441d16000d0700700014803264050305c0030b5000c11686036030484071070404203010309810400101500d01c0c004400040c1c0d40c000000d0014180c1c1c076038954400c0d03502d0344012a41c5214602903400c0d40f81804d105100002e90782d001428450419105032802c01c20300002c07507d00010031384c0102c011502f01041200209014880e01a0700414600d0003291905044a18a46480460098030301582c2c7c403485613a0010002040072503c5245502c04070192000840350300c2e1103603000e008151401a01403045094140310340109801d99081080c11200707185000580002903100210890f0103000358958400070038054503030f46110346d0450311416844198a018546044078503005809001014401032003d43c80d1f9039481c6034003119020501146d82d02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 926381492 1250 926380242 926380253
    0x111005190c110a0813060504050d0b07111603060b060a0c06020a020c1c14030c061515070303050907050102030711091015030204030308070516030c03201e01090804060309 75
    0x14101c2c401440d02c0341c02c00d00c0040041000007030507101c5144980c0e0660685030071049803144900d20455034003141c0e2006010104505640c455041401402e0000c501100b50203894141400c0d00351130181c1d0555080d0030014070a150144000041048074440d24040390490058407040807140080e0600350f01094210718075008010b2040d000000912219100d0b101011000011503103d038101c80003611808002c103280740c00426220441c0e01c5001810540e80c07121007050205084a05160b80000e21030440502d0103140e00081c26024041d903004110307480c0c80e0030f40516000d242e9000c2030444d802040600302103183da021020448400302c40080709612104000004420745400140170840e0f003107401506960940d0090084038400d8450316250381d2044010750b240d0181480440000702801c440308002072264444040d00d6201c0e04000721040c141c190750701d40009a055080055901c4803003c42e040e080c1c0c103500000d9250f04038000b071040c000f640e034480790140150320506081c5600c0d03200d24000c024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 926382742 1250 926381492 926381507
    0x109291303180308091e18090a02130906050609070c150f020f0703020c06090f04091a070c02010905120316050f0604060203010905162319111005190c 66
    0x8411002c0c0100c00c036220304005030503a2040f071a49200d814401d0142c00800a136134201d400c2148018131100309003541005c00e44d400c4000034148281170080100204c0180c0d0b605520442c0456078002c0082c09503003610b414000c45a018201a21800c40002004039159100300078544c660380c02400000c41c1c91048410401600c41e40b03244000640c000310f02000704140350000351a0300b074065800c031000300c100340c01405402e11501180c5c42e00018004040070700707420300d60010140c0c03a1094000e220040512a000d0000d41000d6a0480014500040070300543d03a00009480150108440e01d100c45610f0f0901d03a680c82c850034114100310180a00000140701c2d00303000301e04c549054503040e100301d8505480e0900095109000b10450355180c0400326040d09441c4048801002c62901d0350030170b003c2426000404020301060f2845c40e41c204020146050141c0e0120300302e0140c454541000302c09028000380d003801c1c1c0a0035064005440e08003080340869162100e80b809039035240b40028080c690080448480c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 926383992 1250 926382742 926382767
    0x712020a2103180b1b09010e1210060f050102101e0504023f0102070f02010305130c090504050d020a050601050f011e020a051b1302030c13080109291303 67
    0x10701c0500301a03c203004103407103080d02c00c0500c540440f00e100e040c107140f0403c6000c1c000b50180091402504180b0f1418032041c04044906200e0440b11207a0b15142e2003001d544103900202074214400d1410002c5503010082190318140700081402031844900e68040740e4082c65802c400e0303803a02d65000c0380664441c0707040c180003195000421661040710350400c141c247c4207050b100c20030412140035895000c0062003034610070703903010740e2511a10025400440c0070b068041c0070441c1e0300d034840c102407001442c10108000201144d05002c1058501414944d003001c1c1032030018410f6400c002c80701c0c4000f40c804180c2a06480c000c580c03540108040b5001214030311514480d0007101d0340380515080342c050300003400e0f50b03501384100110341000e10300c0310304020319184903141f281d00f04c00310004000c50242145c000d190320503159104142010100d50100d4a1000c403584940d10a0355680c1e04203040c0f1112201464010719110114646140182182c0c0024400101440c41d80110b40802c43c1c10540b0030381595070314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 926385242 1250 926383992 926384021
    0x1211130204051f09060c0807110f0409062405030607050a030f0c02011e021c0221070917011503030309060b030717060a0e0309120102040504110712020a2103 69
    0x98041000b0f403030f10149510301914041006200005046441040c40403038041c2d1040034035085c003455684640c102c901500c60190b105851040d04512911244140031140307008541c0890800300b2040c03a01041203021032903080f49180410103000980300000d14a0b0400b14503d82903507640d0502d0b80c110000e0003010214a4501d0a0444546806030305400caa0036903124400d20310940d04c4940b980c80124459407900d865005c42034100a0442007481d8040c01c0c185844410741c00550107081c0d003040200501b202c8590119005040621911400c54043d00b6607202c408001c00c407405800030300c403018100b58032009042540758003c4030100b1203150003442c0100800340031103520701d460301d030322041c82d50782807a00340b400d40315007400034554440c18002c1c0300080840c10f02130b600d030404c044107004200c0308030700d82c0350102e41d000c10001031261a00e104c0c55a034030060249441d280e9610b07142482c210880c208c2d0b61800c640c480388100003c5002c4c00005000d4540c0020007040201403204250b004d04202695407a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 926386492 1250 926385242 926385259
    0x1091a07090302060d062106290f0117070908061803040521070312020c0414041b030b090d031b0e012001141e0c070b0408220609121113020405 63
    0x401a2a410443d03a1a4231511050040e9611540e4591040c1300018480034242404c141c0400103041c2846c0f61401c0504c10b00d4984c42c507500c241c0400d40c4500c4140d4a200000350381702420001d41c8005e02c507482e00280d884041c4142c04070080710345a0b072800340340501072041506100d1211205448211001140c01368016194039650340d0910540346684c58001d14058005c03c0c56100c22454035101d4403d0001401c1d00c140210f4445440c0c40851100d000c07018064007002c80c0d0040080307048410003a00ca070081328024a0080b044484c0242030703d00c0020749500150307820859444032900f102410340344072400c6ca000009460f109202502e22000181c0e90290365180030402842c607000080c140e40700b0300300341186079a86001c0481002d917a0b481110b5090f0004014860140000d0901c0d03131664005000300c01440c00d00450048023403101031840840b0510344186401044015040016040103103044841d050304c1c1e20b10380c0c840c1540443c204118500c1203605405500303d8425a6050300c02509002d400c594 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 926387742 1250 926386492 926386529
    0x503060402161b0b160f0807020a080706300f020f0d02070c1707140315011404050f1302010c06200318070b0f0a2001091a07090302060d06 61
    0x1c42c004140f150382000b4600031074000c01d2030310651080f02ca05502055003403c130140355890320180564448000c42d12142c04000440150303841c10b0b282d01c09840342a0182c801103250140145c0403a00c200030f441080f200354106181240014555500803403070300000400d072025140c580344000d1040d407002000104000c1620385940c01d440d80a1300f0000e100320090304140b171b1681d840000445100103450020385c000d800030b10081c5180d8145245075240601147c003c01441d05510301510300c2600401d40003050781e26240301d28682401000c0d0043d0403200b0520140c101421840c1d21000b41000113818007180740072180803c20168882540b031001ca2104580000f40e5800e420103a5209649680c8100c1c0c100340d10248291000c5448401c480f10072003d50315002c240c1050b10415081140c10b1000c0c000f1304100025036440c90000c1c0b9102481e0340b0300008200105260402c0790003079240c03ca5080304030004c00c08c042c0079000051a001d072901107501d84e0b140c8030740308100f0380a420305800c000344500a039820721 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 926388992 1250 926387742 926387753
    0x1e060d0b04140717013303020d031e050c0c0117150d060507080108070e0c0a0309020607020307150210060510030e0f07120c080604020d060b0a030f080304020a0b0712050306040216 79
    0x92466401c1c1c07980860b07001d00544403200e02e280240305440803c0c0c88006c0101f0061a10000c4105014800d05082048498044c07081d40701550185141c80424800034680050483c288800e034104003013401c24030702c0c038401c1d4400d00c0d1a414004045902c0d0410900703049813550f5521001d541403da10240a20203454400001816084284a140c505128140c804603401164070368841c8100100c1c1c1007141002d022803002c601800e1151010782e003080e0200021000b6803400d00000b0054010806c0c4c2ca81001d8410100900d8803100c00c18008042d80780c1701080c4000d56520904100199042c0b41c0030500701c0c0c1c959090341c20001210b070700c40c03414403500c0400586d13070951b48852000b1a00440540d500b29558802e0a602c4041c1110001d62140c400803c00e000220154404046daa102400d407242c3c250300e03030340e07041d00381c20604d5402d8a0000c404020402180391014500c2d0142082403482ca04040603a52039100180d20103001d84180840440052003036190342c3e040d106400f0000a0b014031810950821 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 926390242 1250 926388992 926389001
    0x26060402011b0c031b0509010e0708070e03060f240315040309050306070e0102121206130f060b070b07170a1a0607060e0d020105101710051e060d0b0414071701 70
    0x220140001040005207500c2c4c100741f95412a0310071f440d414010b640e40c0204441c0d4003c02002c0300180b024040040c5850703101000002d2040f003052070b03a8101d1b42401e0301c512510b02144a00c030b00c00594414000345c841d80300403d40720300701c50925000c1c410544441c0b5003034421107240c1d040180c040c0f003901c08125403142e214240c1c0300d40d004282c007a01c10380501c0300e54002d41da00c90082c40500d104d1000000c540030b030520301802c40c140a205500007503181100d550a80a0300ca907a40040f2107000045035800074442e040a119402110038100250340c48249c5180498181340104101c620700d603200103a0713018600b81030080b08a904003d146654603852841c140004101a064082d0507210f000c82d401110780c014410b07d409012042c0c059400c4d64501010252201c07081010306526010300d025901242c07459014250148400c1c0381d04403188081100c050030023481c01802684152000c8a9080c08280d82c84140c50b0000c0c0c1003205802100008d83d00ea5241510325406070811502d8a5505030144406602 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 926391492 1250 926390242 926390273
    0x60909161209021f030e060c0d11031302150c010c08040b060a05011b080d0606110609030a05090f0303071a01090b030304050a1e0f060926060402011b0c03 68
    0x115400c00406001c00c01003140c019900094002c407654000a020030040504807030941c070103180c041150744102e4151800e003482692504200f00000c2000003118080e03001d59843d240c01204000d0071481d00c0404180707980381a44000c0c0c0544100741607a03070501c900c2e00840f2500b40e0844001c2c071019001a00040c0700010454042da040c00140c4042010342ca0410446022500140c0d1500300410361480d40b10303038800f03005000312009482004000ba41c82e4050003880018011600d0341201030a8410001d070400600810901c0a904104159440329400c0402c7c0c804c5108107944c2031342c4810789003001c40e203903101d2404058a0141d004900020325070016a19170306840902070700784031910302c4209150381c034010707401181e603ca4241c8200f400044034514403100c48101039450302549950712070840040214a800401c0042c002e03080a1114420f00d182c420402a032210340e20416014030120240c030356101030802070402c80c520026000118102c2c0903894015000003a0400d901d5032031078501c1e0314148100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 926392742 1250 926391492 926391497
    0x1208030c0c0304121a240609060c190201080106050a050708070c08060f01030c0f05063a0e01150311040506061e13060e01021908040b0307030e0f0c0d0b040206090916 73
    0x17000400983d8940e411016203030703c201c5240d00090701e0b0000c0014540000d07140030f811500500c10003040c580d003081342034440c0701c025410b1908c0c400c03580001818141c05130000c200b405010000e181080d5404011188a1500000000d0300c81a541c03528031040007540d0f1000320684039460601200c07031b44620f0b80b0360403280309450f000d4205644038a09402e0b1082e034032600e5800b50701403090440c024542c001184040c011010301d0010a80741508280c030a10036141c030814081c0ea10b1000a240040901c034121702000840f2400e41200c0c5141c0d02d119038084248406c034015500c0d0804120551590419244105261419441c40303042155103240705400c844020010006045000030350103001c1c503150220110184e02070050345140b40e01d00c03118550720701c0c012580c4010070000014040450703c003450040d00565004a01ca080c401c0300d441c5080483c40d0402c043d5008410880a180d55032206c0c1da5000d580030b100000f55513110300004246001e8143c00a4010b00c1d60001c20001c0c0c0100c042008513580c058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 926393992 1250 926392742 926392793
    0x906050703050a0e1603060513080313030207050f1c14011a0306151f050405030109060606030e060106211b0807090b030903310f0f1208030c0c030412 66
    0x9041d020380d0340c15441401720311001320b12014008204190025a03005c85848096517900f900d641c1c41c19403039030046908048642e0f2084240003015410f000d14401044100da680f00d42503110030008105030300710380c04000541d0700e0440182c00c0000c03103a1000140740404000304000101d00e08003502084406011604c2801510000ac1c544d8580203807800f002640030341841c0c481d1425420842e000b041c05012041400030910001070f090b035090182d0101d0a02c940400b060b05860090003070151070341c40d0b229501a82066005107d010303840200581c0140c050000030130f200014010801c000e0040301d0b004e84080c0c1c8030b200044141500880380c5801034800d0b075a051001541e541500d621404280c030a81156081080035500f601130320a0491806403002c0300b00c0140d4004640d181c45d061180354048030136148070080402038180c0071200a001000034203405007084d900c6a58100311844000c256103815140825000c240032410420703180036100070104012024084e0510049094015607055819800d6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 926395242 1250 926393992 926394011
    0x30e2e02010228020319030204051804021003050a060b03090706080c03040c03030f12020313140d0e150919090f06150f1101060b180603070815040906050703050a 71
    0x14801c803030f400c00841005070034180c00d07080014100280c1401601c2148418099504129607107030b075100c00c42075691801640e80d843c000902211070310440c0c6494a11410f9810040540c4032501100c41051107883c0c00145565004410802042103070403900722403001004114850b280041c0107800d40b020b80d100c1042e00d9a4929000050380b104580003044822408810800a401117080b003d240603a0304003400c401040d2a5850301f00d0300100d40b00781a40c0c0811030602c05000d000642100005e01900140144114202c8003800d01e950381d011250040010140d8034030342000c501c05842c10064010b11405190191160b0315848115a00030340009501c0d00c90341d05000d001a01ca40713030460303064807414030741113428820030340362440185903440034891110650151280c003031140b4070107000452840f989603130390880030360402040c8006080c0200380810500030021b8000b1411036000750358122900d03040c50f120001c01c016102003940100030604101c2444030068040d003001d440b54205503c00c0044e03001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 926396492 1250 926395242 926395247
    0x21f11011a0312030a06050607150506040614131808120115081f05120d080105120a0f080708160b13150b0d02030f01061a04050303040909030e2e 64
    0x729440d01d5060748400503100b0208402d10107107038007441c00c140002d081c45d0348a0110b111a8003c41c0121811195442982c128148034864141c0124003a01d042010604000110343c0d00c648024180d4031030490051120300b4501d140d0441d01c0d648040307101980342e21710b00f450701c0d41c82500400040034480030044004203500d684002001031080c05640c4040468551002d9051a5582c4502d098110042110085003e03225948104010309128006103c10b60402d80001c000107410381104d84584807100000c01da520001548dc203003660401d00456000c2035918021380c49100b101c13002000310300081010a20304c0340c000811080c883c0100c028890507a104480b030908200940b02c001c3c44000c010003014600c2e0340c1980035500021002d0059000300119800013840c1455000040240d1781d1030300d100b80000b48a22810302c0d080740c1c03580f5000d410142840d0000340c40c0e006038054120300741c0c0e4884210041c03502c20342d0703007044100300a464143c201e00003050404640494440c0280c94040c50706c400d441551 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 926397742 1250 926396492 926396531
    0xd0804020105120901140c041e080a0b060105071b0e06030a020d0605060303131403120a050a081e09010b0405090c0a0b0c010e10020d110c06060904021f1101 69
    0x580c16510145407491415150440340c0015104541940d640c102c0c5110f0507010005050040d481820166102e502d032108000e490754141a003105051341800301003200c00030024002d580305500c50b41c40c810390703610840100c809020f0044040d0143d003840c0d409001d5040d1401c2c160f801d03502e070180b1103a4107560b020245a03403250301e808000d400900218031400810078581c40640c00410081c141c2c0d01c0d001c40e220203544406255000103164500724500140300d468100320043d9510344400f0854105489841c01803d0b17405041170700304c24440d070b40c80015a0b080c520780403500904800912076509044c003241c542d00070241031846c03902032440c1c0800320b880c007500000c4ea100e045d94004c0410b01c0c90b40c108000d460407900018062500d030764880016040703401040c02051207501404c8001038907421500301800c15034030704401d6402c000700100841210402c1c04101c0643c0300805880c008502d482d0b074804034010202c0c9980c0324214030400510800c0c0c0a51004142d80501c0040c4028480004e0321404090720b070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 926398992 1250 926397742 926397751
    0x30f0405121c060501140d0c030605060a02010b031c020703030e0310020a080a06210201050f1308210406080105010c0f0b101e1d040305070611071a100b0903070302100e030d08 77
    0x6e050520856415030f40da0b411401d024070052901141c41a0782d0804105a03801c00d400b14800350351a04410000ca080401003102c041d041c058680c5100440c070a006902c80106000c0501006200250300010323440800070400d036008015421075981d202d10070024400138064582065150a1000010303000c030303010708060951002c00c04030700b1100307045500561362540103181508040e0018031190b441845141e0402c001001c0b034002402034481040028a0403500f0756010103100c0e4424001800b2207903015240d18107541003030806080031107080c00e104010900d00d580080c5902007a13010030000007042c2502d0001c9411244422600c200e000c00096050426401800c81018010039055010710700c550240350814001e00f05280323081425101c034401d541c50b451450313240b40c600251643c10440141c100850b11655483e41302c440d030400016a0344244000e228134054020085404502c960742400b4020003954018241141301d640740c03101500c0802240307031040c4a8081c10031403d5200b801b41d20307034a128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 926400242 1250 926398992 926399027
    0x1e07030b0102032704090b0610020303040c050d0f0203010507021f0b0d06111b24161412090d03060f06020606150702061c060503010908030f0405121c060501 69
    0x10203c14030642184c00013103240102100e1042e40c4101c81d69141c5100b03003407510340921496100c0b40b034084240701d13015125021340070840d0f00410400000c00c0c1c2600c40d20080d00c1c8201c4204081076190309040140185220000e50315501c4c02043c02105c4c0d4002880c0943e2881d04504400d0404041c0c20510845208482c55504031001d1001307000001c500794060304420071542c00c01420720380340344039011002a030380285000e43d510145500d850507015840c2500c42001d048a084a140343c4101b541c0d500c407003814825010300010f106180351060704141514450030203041c0400c882e24000d400180d403080004100303004245080c10110b05031a0100a030001d844560f0000c2c0542d17103072a418824905d29010090382040000c0c04001c006070b0b1214000e000e0010080c0182c41c4035100c4000c0301c0100e40c1141d1009201c3da01d4681c0400c000f0382d503078080d268400403e590422184c1e541c0e0400504050408ac0701201d0102c00140c0d8201c045024960300b5040610200304010306034481005480080041303d50001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 926401492 1250 926400242 926400247
    0x9070f09050903041211041a100c080d02070c0e06030a080f0a020a06050106050a0915200709060609030b010b0a092106050109022107140307030b091e07030b010203 72
    0x24002900000d400598607400c80f4680741d45c552079000c1e03e05034503104481d4555182561641072400e4060b000c4c03a034081e040444900000c42e800608091050240c002c24400962908001d00c01002c0075500c10b02c05200082d0b41d5025649040a490b01060248140544100300032645c0c0342800903104074202d5110510f10b240c203947e44100e100a030440c0414204500c10400c0000000e8628040e40d80240800d0715000d80303408001c0c901509002c119008181114880740c6491080e0794021a0710f14106441d81ca20394102e82d540010902b410225003100c502c035420500002969030b80034502004076030184000d03080070798a40010314028443c000390280052031440c4d081c411180c02c0c06a2010810144650b140e0310900380e510ba8050b02c10980c00002255030100390213419552105022801c200ca895800c4c24038645540c014007000040341d0411000e51002c000210784901981c008105950b000300184103600c2c082c501180d11b001c011402c014465000d102290145000380140703202820141c01450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 926402742 1250 926401492 926401499
    0x110d02070c081903111218240406051b06040c06020d030b0906010e032401080c0102030316140c0109150b031605010815040e01090203120703080406020a091d0f09070f 73
    0x280c0900c5c00a003a00c10f0b034042c3e1201540c034407100364000d04a807101c1c000c4d400c50b080201401c015000d0006484519050609a0110000514401150103445450a040c0c1e1030701c0f2181c10b01000304501e00312648081c81120305020501010318a254201c80030f503801c4918142d02410101d050b507601569040d002907203000171504941c000c1340700c490100703805421074a05d2a0702000050b54078164040011488240c0001840200020320040d10004028001503146060001000316080c00660102040208007000990020000c00489000040310b0009001907015400c0003100580c045110712200340c03600c58125980d0401068451048442e0581001d51524000056411440c000d03c00000d60b400c8082e6032480d80e5980c810b16800161403000043c01d0340051050503c0d260036400780044440080c00900c2c0042c1c2c4c062405c03584250300c8840561204100340080c0c43c40c040c1074010400c80c102040c030155085d002c403d407140c410300d014000844240c9a505405440e0b007541e001c0e481c503c025094091 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 926403992 1250 926402742 926402747
    0x71e0605040b190e1c05060901060602070909082205010e0d2105090d03090504230a020706020909040f0204061403030a0c020a030503030f24011b06110d02070c081903 73
    0x120152800c60801c0d842013040f000026103101c440140c4004101810590041401001c010322540000260007c010440c10b1010107565880300d8840c0410f00f5803150407035410804210f054580d16803d05100031055800040003002c0061640149070000e4440d081c040305034a010b4600081d001d40241803804000d50385103400c0728410591170b510f01402800c0104c022151a1081642c0e6800d000340c1d81c141d2403e040000308004d80c1d07000340400700c6d01c0301e1314040c190840d510300001640041e82d481005030390f2002e43c50000c01034050303011031030f91000281c810030007840b003c0c0d410f55440354422a030800c4240d8032004000101d100707444d10715815600500c00c0c040b2580c080c0c00b42c242220b00060000041c10307500d40c0c80c60b00d558422100e15208070103441c1884646c120180000301c164100601c084806001840000c001c0304081501c4544900c444202c801417201662001e4424009280100d07036078500d00d00804060340c02044100d460314110003001501e00c001185041c8402040042032003400e05a4404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 926405242 1250 926403992 926404027
    0xc23030102041a070f0c0f080105060d0b0721060b03010501030f0507020706030e1c030b0108070c080703050d020d0c0302250b060906060c01140109110a080a0203090f071e0605040b 79
    0x11100310030082a104041340c01d440c8144000c0241641d47c180e190b0601c6130079400d5034006080c450042c96100007240004020002040e80010070b0300c3c01ca08a04442c00d0480e280128000d03041440515040340842c00c0c0910400841c142c1d82e00780c13028883d60b034042e04850101e803802c030303801c10041e00b11075400d000c000d10a401614045611008941e49520700440611320042601ca00b0300110780d0300c5940c11450b58101c8101a803005007810300c501616441e8030340749224417480200604115000840300300c00c040550581c1da0b00040c0b080c00704100e0032815000b80080d44032040a4420854400d54500030f20717004108200c64560100c4128002c0e142d580c280040c00902601143c1e2080c07052250803400079003403140c58034400400c41680e9055161840c50b40480b900c8030b1040140b9401002090f040540010540d0b4200f60b19140c01a541e0741c07000b80d02403c2c031032180c08200311405a0400042c0c0d182101828517508101700143c0c817031103a510031060b120751103280320b072184140c02400001015000780382c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 926406492 1250 926405242 926405257
    0xa08180f2d0115031a041e08041e031b0614090406030519060f0b010f0c05120a030204091d0a080c01020d0516091401020a0204180c23030102041a 64
    0x6111107903031004840c00c0d500116041501196900c2c3c04006014103125001d007002d08031044e640440c1899201d180340700d6100240c20b068005100702c050208140c1808990051002001c2040152561941c90309003072500c0c801581c02c40c5254000400c4030a95400150849145444140707290455034800000d6400041400ba44141c5d00c01d000004107106101c0715003184801c0d03d2480e040745152410004450404541180c000d150840d0030f8103c1e42c118a104840300c001e81001c444011107803400c14504450500e519030501001700d0700d4072420350950082c1050719043c280c00e001074242da00c0d00440c0042d080b88042e40b250311540501000c500c4910007004e140e10080005464007144200c00303000d680c401e0341c035420984c0c2034004808481d64002300c2ca0001d440c800802403070000c98440000e540b0010148068891f55949041d4840c0d000500840015540e00c0752a110085031b5404190400d2608605040440d080182e1043c50328941031007110196000a9000e2101c0300300c02003018840e401544 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 926407742 1250 926406492 926406553
    0xf1e0f03100203010b04060210060f0302014a120a0807060b060a0f1205060901230405090706020f060420031e16170307030c170a08180f 60
    0x105035546141e0755000540c003801000c00f5aa40d513a2400c20002e01e070004010000d004249050300c00d0202d511a020610308680e02440d01106a60300110b9540c052100a00840c044071440500c500460f000d10095a2040141c2400c1c5480600d207103040c070952a088400310801d41d00800d51030300002e488040a40611030140c40c000402c85100000305805d6404254540045013500b480d110103c2d5010180440d51007072007905110034207101c0c022841644041c0100c80980040c40300d9502e1104101401000e4100020400d00607400c0c16080d19890300c101e4011100140500030075540880c00001d41c107030180354800c0384c80705002e003004910051400c510b0001940b5000f41150000c03a0300c2030b80c001d004d00e501e02c01d010702034498506003514032170106540009901e41c4a040e1a0480345000b2050b10b52441d0141440f90400c0c081e45000c80b14144036040c0007001c0c90703011600b141416031100030700d07200703113905440b41d0800c3c002a8190390340c0d10030280600a85c0c0d4804800940d18500c1511220b0030302103800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 926408992 1250 926407742 926407753
    0xa09020a170c040e0c180114090d0b04210e0d11030f0706020d02070303120b150706091101140a0f2c13110304060b0d020603010905060f1e0f03 63
    0x40d0030040c0100400e40c2c40300b84020002c0b805000c200c3e04034504d5908060401c00e154601003d100e4501051440c043c4d1480c1848250700c4404555140079003101c0d0302940041c81c25217004458501840d45403800c0c0c1d400c0e00c281c647c507a0191001c160913020003203030b0011922740c42c4070a0001000c00c822050030503070440c1c2c0701262075003540c81c80d1002c0085030704002148000c1e00050b0308012000b81307010010140f00742103600181e002c00120f034005d14410006c0b220880c01103000f41006001c121060840e4011541c0c0301c03800101c9000b40422544400f61840c03044040c030091102d03e400440b55017059050840603104208101c05015014140d1103045a20b1410315524403250180400c045041e80302e24801c200300100b01542c0306240003001291140310f640b50401c94800f144030008040e000040c0010043c82e6690703007001ea10f5079000311703040c0070583c010003981c1c5c0c943e151022600984800d48502d40a0456210001d60620f001385805101800020526250780c9081c0108030a0100c000945505030264 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 926410242 1250 926408992 926409017
    0x13090c091805060619170c090403020f100204050a120f05030c010605010201060e09030301061112361c0206070c2904140906060d06091a06090a09020a 66
    0x19405400c0704030071104645001c1c100075041040c1400c00082040348950800b00280080d00c1c8448105016180c1c084138142440b114013800c0d6181a003080c000b80d512940102c10482010390008240c2e802c10310b09002d540c148191074203100c040c0d00440c01083d502104841092200d18101d5448a80341c9000d000039040b000d455840b00350460384500f4a142c15651101024820703541c0900500004200c014107014562400008a588900060040740208941d003000c40b8030209081150304414000c0d90002507840c49520284200f11070350120000c020208440c071007400740c85800c0000b08050014140c03076520190007456020705143c821040780c0c0700740184040030100c0c0c0c070414484003414007915041c05076071955140c908400d0420309070030003e810802c402d01c00c031280b01c07030120b9078401d081c0c8042d1150b0301d810780060014001d0f85400c04400d468840000340401158010181c1f0b40c0b51040c060321081c0e4040244180ca20441f1803080c0c004081c0d002c20010302d94940c0c010702050445d4904040089c0d41e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 926411492 1250 926410242 926410259
    0xf0c0306041518030e0f01140a08091e060106110f0a24050a0e0f1b1507060f0c03060603020703091e0312020a0b1302031509100609050a0c02060613090c 67
    0x143d0550076000a403455603900014144900c0600441c20242004550400420508401c0744200004d20007000398190109a0f0780c1010003801c080182907085200c40c03d41c0d52080a03988401c01d210f99400181c0c0001440703003014003c5003110030540e90001074001e140342a1200102000315489541c110841c074144444592030b50f200c2c090090303510481c0881c00280c00d03113543e498080c0a09440d0310076084070305500c40144456410f07170030201c0182c4403c2201c00404c45141500d00802d6005880305040001d041203988030355100442c0a562a05c00b0000e582c0c1b12002101240101c40c0001c0100303508071014054078101c02c6002d60408959076602500f19129a280341d680c08104c4054401369100002110810009440c40c65225910381c41300f88405015070002560f6665038841c49014150b2000821015402070005803003c0700100303020b000c8956071300560001440212850350b11685011300040081e4400f15195003d2030005061724949419010f1400040400d0035040b1100840464000781125 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 926412742 1250 926411492 926411531
    0x12120f0114040e030c0f01020706060b0a120f1d0d090f060f08060a050a150e0402070c09051302030d0c031112030712060e040303060611010e030307120603061d0f0c03060415 76
    0x21b4490016841d1107240c0351450070349600d0b0300031110b0700d2406d1040800456208406420140d0f541754046118030ba0b1201c2c6500030100c18142d02c170242d031020b420490b0340d9800107070f02000d400d0b0342d81da4500803952440d428807140200c0c091070300002c1c400441d01e01034912400040d90031500050801c02038556490005444010f16488500740055148441c1d00d40360700307d03013200c108510642e070540c50f200550b540e410380d20f01c85003d20120b0a40d1000070401400c000e09030700540a60140031620760401c0c107070000e851401c4440d01100050b0301d4a440030045070000c07450000d0301e501d070380d01e09046494801c0c041e1203423810500748407281a900c010000e031410540f1207190086002c5d07100040c46a0030325000074a410380511401800c2e038180520042c40d28000401c5a0348105286403900b14800700317243c1c081c050b0040d984040c1030076081842c960100c011008460b0a425001d500310741e81507201c0d00d10103032108a50504142c3c5034000340300090216071940d615484140b0b0a4400084a40e41000c0148008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 926413992 1250 926412742 926412763
    0x31c110408060106110102090607030c050a2a0914011203050d2c0f060109050c16060e0d0807081302011e0c050106120203060a15050312120f0114040e030c 68
    0x242c0c0000b00400031a07800220350300341c960780d0300001e5240039004404549a803083c0400101046198207500c1c05102c020700021581a51026041400e6000314000131128901c030030813445250070140340002d40c84018450381e0380b0f4181c01c1d02c000c01960703c0e04c880c6d0f03072401c02881810350600000300608a0088107a200701d4040d103505000318401d40c00d050036440e010002da8004039030140e21410003542d0503540010a80d044076849600890301d03a4901c90010300070b01900c2215107111040030341100800046403c18100c546018040f038500c0c0000e40c5089922440560b100c3d00450010401b140941560100d450505070060402404c860219000d0401180380410761100041d03555a40c5c4041010a01680d0300411101d6183e000c0b500541e000a40c641d00c0c06006100180d07a100c030b40100801201d12560028480181606d000d0f00310248212034551002000c03011810f17030a4001482d41d1380303503079105050390042d880c2200044121001e0200600500403036200a02c8284402a0303c0c540411485001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 926415242 1250 926413992 926414009
    0xf09050a180c1e0c110906062b0623090105090f0604231009060f0b0705010902100216081906050601090503011b18140d21080405060609010305031c1104 67
    0x2152543d081404584c090b00c17860900c208844014024595500c0c0160313100c80b90f2003120103804003058400142c890b0138031210700d00381e503007040300001704500d00d6400d440c61501401415140f86040604100900d803003400b51503882801c0c10045130800012054160344454007500010b0f045403480002c9a50220004426a4001c0724000304031f50921040c4510008128400040c4846c5080641892604a0f40d000343c840007140400c440c1c041c410b0035040740074402d0700030b01401c21051181d58000d446d50920302c80b0300701c2c50b40e10f00400030354401c00050880300204007003e0701c1120065541d039100030b030201500c003504200320100d01240c40e80d000c0c4101407140d0102a600c600303121105034082c107044914080030455180b18842049900a00b04030060f8440c001c59103e41c1c1d602c0d81d890120813106a860441e45400307100220488180c1d00405218012401041124416511003003080000c01007408010038540003808060100503a50103096900c000d5071801050b01101140d0b1200b05400c0750740b11282 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 926416492 1250 926415242 926415257
    0x60e0c0c1207240219020f030405100516080c061006020c01030b0d0c0b0a12290a0b0f091309030c060522080a0809070303050406140d0207030f09050a180c1e 69
    0xc2c043e202a0380381c00905c91034006060f841c017031135140c240c40740164407070385014010100b50900304521170012110b0918045d50403444004450030030b0640c0d60401d01d507070300c0386100c0c01010880c10f4605105020031a226a4000c044040c640c500440260600c0e43c402030704a224401c0b0301000030080c418000160213602011510380c1d0903090010607400c1100108080f80349410112420120b161040c10a03200030800401601e0144101050700e5030059400703e04800b00210315801203a41000040011400c00c854201d42c0300d90724400082101c00d0500000d011030440c040540000351950001e80d40700000b03182c000f542800964015040181030071003295025000201603d030903030003505c010740064441c4000c061060550b5000742c007a00ca54000d00c418031070300d00c11203d41c07151500f084803103102d5095415901c0340030038070740540329681604d01103021036155072022401e8104590380004843c1500414191120480c01d248000c3c90406c02d00f1007001500b00c207140c001c20745038510158190040e0344104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 926417742 1250 926416492 926416507
    0x6090b07020d0302040302130c05070c03111305090303150103020405120601170a0f140106051806011227080f04062015150a0513060e0c0c12072402 65
    0x2800c02d1103440e182401d2510520051025840700a4460400e068816000400c0311301c6080540d2140640c01c8000c1465052242c040308010064004e03040c0c000d4141d0b05107100604c045804001c0d1042198030751540d5106000040c1420074803410b4600090046c14010f02e09a02c60002c102e2920042044040e07540c4448010862042c18620003000c40100c0360240c100c140d000d603601d214a0003004005000b0100180a4042511003988041d004040003007803012001080c06040c40084030072036485001c0b070341541e5825820314030b900420982c07065408035000160a10038181180c280c0903902914101d01c1880640300c2c108881d0018800740ca040d854990f00354102200280d000e03c980b45a140301c58028110f20280076032000f040a4101c02004140c1a00302c1c42100401e18114141d80030303d52014904c055141400d400354400800d03100c602d0304000540d694100e40d0a09031080e081c0ea004264003002e100c1c0c140b48003100141080c680710300c0e42c008071119a4201050164105075503040b90304e0740011000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 926418992 1250 926417742 926417747
    0x190e0d0c0803090a170a12030f140105031005010f0501050a0c0c08010e250611010902030601170f060f0f040317041a06090615090d081803070b0f040612060306090b07 73
    0x10002020b061850000110003105c140d91101c42c4440001c00b60402a5442c019240c0250440b50001045520401100119a100c140707807040c28410b03030303000340680c0ca2404c005025901400c0e041c0d8805101c102c100c640361000440d40d507484904564101304660b20307058000350508400b000108400e00000c80c0c00c9991b03008003030500180030301030300d10103849070b405007210b00d80114008111070540c01e18107051600c0700441ba02500c3c0c030f40c00080d4107000e41c9001007030a0b0005000b0a0103406110304079031000e41c1036600c2c20390341d29003954800b103964108400250200ea42c2c072811036000f88245042281808045442444c591058400326151034140304500d0148118404550380800200c80c14900f0382001c00215030514810154101c01c1c0c070000680c4c10403a250380700f4243c40300d42e020342101d541d80031001c441d4030301010031100c09100340500c0c0c0300000e44c50081d805480401c80140011450302d450004260755444d003542c5840845602d8034030002c085072045c0701d003a00d03441c002c2052110603d00700d41c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 926420242 1250 926418992 926419009
    0x60606020705030f0c210105040303050f131e0204021b0604050610181a1c020f0303074205040c0b0a1403150a03080a02010c05190e0d0c080309 63
    0x18000e0b480b1308200d0f14245000284407860560903101070000c130309128050311a106110298090039030070312041c841055496800740748240101d2403403001640303401404660b90036a401c00039102c258104400300c500c1040a0036460b800e440100010b26000403110f0010b110000c06030314180540041c020001400b02c02e101e090780c002e0803190138066050800c0389800303a044c200721143c0c0c28141d550418081480c0210100c0311a280010410480ca4407809411003840100d581c040307000f2a40d0400540726401d0020a403507096a0018800d150100b00c001d00d0048044202c0890b080c1001040c600024800920030781010611100700108561400341000b1155481c0e9902050758600100899008180c4c072030b10200300380c981c20007030a96039200c1144241c000c2c000070044a5020242020000c1041106001030210600580003800001410300003911940980480b002004200003042e20b007180c400c01a40c00d10700002000010050300342d44501e640d00300c058204d4030342c03030340300003501500c610303100c640c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 926421492 1250 926420242 926420249
    0x80d02010603031e140f181008071206090f0b01110604021f02100c020a05070b1204060c1205040303230405210d020703090603060605120c0307030212040606060207 72
    0x2407000a00d1036800420200120303c200d01c80d05000e00d10645a64400c60030701074800c05400d4025290605120080f0360350b0b00216290b01d600021800c85001401c20000400e0362496545440b04640ea484000380d0b1103081103100c00c3c042995400005c141c00006105050080301d583c0c10008000310420005410700c19910f08400796036100e0000c00005070b80d50104490b45124140410510b0000c4220507480c02c810003100340d0401c1c2c104079001c0e240650014036081c80340e00071003c6a0700e10795a15240c0d42c91f0f1203034450f40c5425009800000703000c2a12500104082d2030141741002c1c00340d9200c0f010400315034060300c08a00094907440e95642c00104142002c040b00e646460745000307810590745031070f43d580c890116a6542d0b402180703000c5c450300c0d910302a1610300181c0e42c0309540d908007514000f0103002d010300407100400c0c984103001c80c12501c50801c1d00d91340c0303580c283c070001c0c6a1036a1010110b143c1008143e4410150204081c40c50b603205084081c0c003d038400d00d0003080860030514040d007009035682 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 926422742 1250 926421492 926421497
    0x2a1b030d060803090111062703120c0304021f0e150c0a0308060f010e1804020d1a0a05070c030509040f021e1c151517070e09060609010e06031807030309080d 69
    0x8043c03150040722823002c0b120340c00300c0058144208403416001402c50065100031081c3c600c00704104242c180c06c20004511445c0b00720b074460000c80c0400c4549115058000014000078251103d008070b0b41403210741d102610320396403c01c6060101c005000340c9402000002180000d60a0f818010141810b42c6600ca820809003402e40c0980805000700e03c038100f840b82084161014040440e080d5192102c000c56a1508508032510004525100302c00040c4251640905030f0f02c2d001c00280e2152041c149490003581c1643e40c589481c4440701000043e0400350415441c0e15400c003c414203a14820a4040c3c03034030301c030305c40303c6485260541c241600d40b900b9036004841a81424095420982e0b8000c2c084103503144580740541074110403174202c0305045075501074442d00a440c414016085c1d040442d484840304200c5061109070f4a1300140200c0d802414485030104548200b070b42c1d22840c1900285901c070080300e5941607240090000ca52074107060740d1044d004980108000d0044140c240074041d901c64090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 926423992 1250 926422742 926422753
    0x30f070b0a030b0d020306070c1415010308031b03010603061a0405010c1403121509060f10030216020607030309150615050307050c0d082a1b030d060803090111 70
    0xe40505001c0c440c800401040603500d00311150103543e0700070780380c3d0415000381c100c4400f0f03d403800c4003401c0e07052741c8030b000e135115121032030254a10180002e00511605401c01050281d9103140e4400c43d5035040504a1040c0180c8054203404420b0120302643c002d05281d980800e0603450082041d03004030304e0303000001c120b0604000504c0142d8001006240301c0d6030004030090b00320b0002803060b0541c000d900c4442d41081240042c007a443d048101c1f50307100c918003110107031002d40390710041100100c5d80c0d02031140c1040182654016480c040e41c00340c04410701041c44074501007126400a046644040400c402203655400701038244100c0040d0001d41e07150300b92041014a0511a80000c5040d00358a420100070000000505580c41442a9001040c2c00d070100c403450781c2c00040241c0344440490703a5501c2d81002d0900c50350420044e5403803150a40710300290501e01481001d00580049020000e6091440100a45003d4091920411000b0300c0c0c1c1c44003543d1100500c0c00014401d2030540c0182e42140e005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 926425242 1250 926423992 926423999
    0x90a0b0c071e0e190b0d1a10030c080d080c0f071104020f030a06090f090201050904090201110706171302030d08040303060504024b0a0329030f07 64
    0x1e0168107544181103a40b01800307460070140140c1c10380740c100c050090710304404d00c00301c4803103140c02038003100500100b4040400c0a40038885d0314501c80402503d4144c8032040821003241011902d0740140c0c1e40440c1c0c2c0c00380f646988503a80752410550040d076041e48070b05520100e1035480242c490300480041e01c031343d140481507801000b072401001c2e8040c100a0303d2408150f540d41e15a41120f40e08000300031072a0301c0703180c203000080082c08180b182c952800c0c00c1612034402c0c1c86072845005009075050f190f0504088500003440001c0500079022814400d241c104851903080c00c000890040603a50f0f00d0b056a400b00c0003c030150888040d1440000600c02c403080b00050303802149580a4080d1443e1144840e512030500301c0c082d220a07404203402500c0002d100448890000d20440010403410903950500c13094003100c20043d88202c095900034035548010f4508030040c0703000f010341c10350b10328020880c820b00540b01400604a50620349600710701007201a043d0806200344042404810040c24000380f6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 926426492 1250 926425242 926425267
    0x203010b0d03020a200a08010b1002241b0c070f08030a0903060c021f0204050315060d231009050d0f1b02030304090204060e130b03030403080703020120090a0b 70
    0x381540000e0030015002010300c4041601482400317078100043c1780031682951180b94a00900c081c0340000e020300f0012038104132040c000100101140f00d600f40e80702a481000c81002c1e4041400b9060f10403000c1c0308201c003c0c452205102031b090204d03002d00980300280c42c00001d10380b90111640000900d0700b09008950b400303901724462004903600b100c008614250340440803070400514001d074903861414100c03179061100440d4046c0040e15001c1c1c003211290784030100a400c1d0b49500f250b50542c44040c0030b06450006000d940400b184e1706101e001d04503140359075000a03061005903004108015910140d103018404100450032a021540c10090304203c2180c0004001c1c7c5082c881a13040460317681418411900e08000715030080c20280b8046448070740754030b0f00038503000c03060120038070540301e003800035441101d184a01110032200500651500b0315556510b40f10b60401d12040e41595602d4400900510103ca807070340c0e8211201030340c2c5942e401202c0c02c1000050607a049540e0103a0240648140c082c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 926427742 1250 926426492 926426503
    0xa060302090a0b04090c080f0c010504080706140708070b04060b0d0c0911040824060a080705010c0c05040213091a01080c0903210711100f08090f030a0203070203010b0d0302 76
    0x445041c00303e050503002c0c001c1006404980d0000b01440c00700f001c0000d148001180300c03000e08081806443c0311083e900700461780c0d40200e000b43e03030554001000421001d07009a140800854542c1c400750704080c501c0d1985030303013a00b110606980b41d135107140c200804c0110310320954424840c00c5400154561080d111400100418018212150341e12002d181c00701411905440041c08003030300304d0f8000c0740c103420018143c1780144501c490400c1c45002003070b607034a402c0d280031040c0c03060039004001c91450823004550b0041c0701202900c0b1b200705060041101c3e101c900041c10f100c6404020442c0c1c41d494031760f20004a5070561011740783c0f014039144813080707a079002c628240c004100c0301c10552941115000241040240005c5182d0031f016240c00c1800180d1101c00f07811424000d9503c200d05443d03507810301408507144545180000c2900e006007107100e000f985c280e0381000700c010840342c1c2da082003258545558000056000544d0000c0380142c1103107000d008190b840700003510850032110751903602071341d0349 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 926428992 1250 926427742 926427751
    0x4060f0e131104020706201204110f04060618060822150e0607111c080a0b220e0a05030906160204051e1609060e0105040803030a02120a06030209 64
    0x160041c1503601440701d2501c0301c0c0c44401004200710750310100c0740741070f41c0280b80403004c03025081031802d440b845030000e01099542c1c0d001c20701c0d42c0406641d51a42c88101c006403c030309050f4050340500481d50561510701c200c0d805021161650451004100204015403181d42c1c071090400959130200046052601d10010550040401c0444d04418900c0c042c240c0c000c801c020700c014a0b02d861801604401d00150260094130f458540b000740e43d0440320165241c1f417031510301c003442031070500b4010a241c1c0b0906966511000c82e0b0b400183c0c0d0002103000600b02101c510010094654494110007100c01c18450f80140d030035100010b0000e0080e41d920740d03403240905500d032445041d0101c0c0b10010003000800e0401d0007a4018810020351420001814819040214070380034901814000740d202c044a812005070000c040d00c904541c186007400480c2d0b429640e180c01410094207100019000d1803c20165004000b40c100c0581c880c03204c0c50f50000340706130040400450368205481080075854071048103801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 926430242 1250 926428992 926429011
    0x191502090a12050319080c0306012d030506151201030852020102120a02030d020f0301140306010e0103060908040314060a06090c02121305060307050904060f0e 70
    0x94a4698001034079010103644140d5031a840141c00500b004004002400d102d400d1040809480000b600300315642d0400304c90001840c030341040416200d60060304014450014452580e11400128034070590540c20191440e002c80c0c1c640081c08102e190540c5250b2030300703081502d80d43c10440006024190000188805428100700240c00071401200703200e44e5044441941d40784104c640d00040700d1a110442d040400003090841c2d05800c850401046003290300ba805070b008008100314980c40040d6a0300169000007588000c100c08824205180050400085821034060301c03585800003001044d411070780844e11a800540060044600d000b00701c80c19241c21506c00511154940b4210681d4072950308003502c40c0300922a024080303600020054440c0c0c40000052001c00d41c0e4203038a10aa440030810707000560010b44100391080d2945018161091355000402a866030301c1c0c0c0441c031964030580b0a80c00180d00024103a106c0c1c103040c00f40700020095021a005070754509820091b88142c0589040302 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 926431492 1250 926430242 926430247
    0x140106091b0504180905120304020103061a0a140c0a050a0c0e010b03010e061503010e0a0b1f320c1c090b070302100c05040e060901080a02360108191502 67
    0x480131141d901c0003060543c00821140c00b1100f124824809410844040f800a400c2100100e10b1516410148001164446a031400e02ca00d0701800d5900003110510010130030010700c81020041d0040000032a0940107030041c04503181c0300c0c204074464000d0350f005000642c450340010821070119000702c0741100c42c030b01c000c00026240c21001402042100c010058054070100021440e02500441d640c001c5c101840104907600364402480f506d981c426140d611029100704002c0b101da4010010490301d42c50140b040f00b100300b6400101660701e10704000b143c0c200c003004070f16542400d2080040951406404134080405440c0010081640c202800344200000303000ca01d0004143c002c00c0741c05030340541210b003400920712485000b80290064491010b1040c400804101241010700605060f0f5a1041c043d00003010290240041d01c410a90746555009100c80621403003030503868070001c081c40100d0800125450710841d185809810110710b801078045207141000508044050034144030380460158 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 926432742 1250 926431492 926431529
    0x100e1b0304140c0d0c0623160201030603020d03050903060a0203010e041112060109020a0f031b03020c1e030d061d18010f020f04030201111501050402090607140106091b0504 76
    0x40c104031010300f0f22500404d03c00c45100802c9010750840c0e085e0344550365440700340c0040401c07008013010002c02d5101c00c2c400401051a10078044843c950f585401810301085050b501da012a00b0100082000e4002a0021036078140c2031405120144d04601c00e03110550843d410036062900c01807020b0b10080c0001c00b401c1c40c403003080c2c4450140040910901064504543c2e454070610040c0d80300f00301080000b07400c0c4487c480301c00d0080c400d0413141c02c1c04a560015440c41200141c0003580016210007039031007080b09207102c40a402c6070f00200503802e50003640d151801d0200c00e00560b00c682c6c0001400d22501f0740042100c040007403802d5400404085001d4005041e1030505005000c094038418815000140e042d250300790180080c002c4a1003aa2100480d015050300d00d516120031000c000340002005004100e00c1ca09500a05410280180300510b070801030790703030003031900c0c01814042460794603074000b080b402d00940308441d421030206060b16080c09020400414910460140200c540d400c43c1001c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 926433992 1250 926432742 926432783
    0x14011503230901051008030f090405040519032706050a081f03050f100e3406030b090606040501022d03040e04110d1703040201020c09100e1b0304 64
    0x203801076041000c24110b0814207001e901030507088030388075085c1d03004010000b10524004115200c089115a6041c201219401004080c1a021f030060b100707845512020224080c4803224580c03032900c242c4494100380c0005107050186511030300006107240e011101000304640001c1241c589001c4c5180c8003006584807145122011803000c00c1e80071152032000084108807001420740f01c1442d1a074121814080d000700784105031401010f40308400e421815000307050703d071884841c0346811407806c5040207a0500f030a1410b03180c0541e511200c0025222030b02d910301420702445c0710b0380000c02614503038941404e24001070342d110b010314654020700034229800111480c019081c510b4610089003502d03a03840c1d481aa06445200030754060350b1407600d1100d504401c2ca801114281e6a42d4069000a82c132007111020740269000180240e05600030350065029645d2401a0944511350042c21242080d040c01ca6424145000602c131001049075403c000c4c00c2c07104420240c070b40c800d034060b40a10301904c0c0c42d04407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 926435242 1250 926433992 926434031
    0xc0518010c141e06090102131703040305010216110a03050613080f04030602090918120703050c06010602010e0d050f1b0a0602030411040b010c02010f030c0216080f0114011503 77
    0x2e60325001c0c0f0406622405040781c4920070003112181210465211902518202d1080304e80e0318040314034150007004559880340d04141000034560660f030415079a5243c8600766449041d29468490301404064108050321030030280880040d545180c0c0f8a045541c1c2d00d07900d400180000c0410001e01c02e5440410400b01c00322990410080e000d0341d115030b60303882d00c027020790000311115100d0603948000580015141c5450801295034800401d011021a00e442855501201080d020010100000641d0040070402940200100c0c0e000044000203a00c516060020088950081143c2000b91036607a0f200001564800c001d0784909142940a4040591070a0340d400d0700103100c54004000c02c400d2051900d00c9401070030f0160341c00d11500c00388200450f001909400c0007404210800034259a0398407960100d0680320841c0100c3c2c100d102c40121607140004140e00c03242c6250b01007041554841400e001e101040001252011802c5d41011001440413010890303240800da41c91448900c43c520b410503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 926436492 1250 926435242 926435273
    0x603090308010902361c0803041502041d0703150503030414010905100809150c220803070c080d0302090102030a1404260d050913091a010b0d0c0518010c 67
    0x1642c0844002c00c0f8031600900b81c000100c1e620804511511140f020381c1b501015900383d5000010034a1542d0340e40c0e440000305101c07402008070a90034000031031510701948403c5c2c40040c40d0302caa0340040c68450001400e0f150b40c100314801c400c4020350108241d44000041d1070640b140041d103c0902184080100d03215000c40c2d0000ba448130320001c1101039540c00034039541c016200e080030f036043d2080d0407607402040101640d809040c07070010000c03510119240e2014a0220700b032412000210b6944600c050b03e5508a0302040e640042c1c4030a040080460810142c0036100c0582415424004800c0c0040e442e0700658900c0400d008400c1d01100d541ca0290f01154090903094423508941404a2221b416810510401c041603104512814041c1b902074401c0e40c1c82a00c0041071014136240d9034000102512540000f110071f0000303076554004002c00c01807001d010b845990f9850b525034050380e10711025100c2e409070035000d101c1c041110008403294080034030300610302801c4c007030001340b1540b5000031004440007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 926437742 1250 926436492 926436547
    0x102070b1b120c011107170706140c0d05011a1c060b070303061502071a0c030c060f09061305030301030b15040c0203040618050d0210171f0603090308010902 69
    0x180d90415892403040a000852030703e100030401c03045240c2580140d4401d1200282c1601103e5114046a540c040010310486216050202d8081000159546041c100740c0744104000000704a81009010600c10079005050030107200603101e00b20360f11150b4900c6525041c40301d1b04e075503034080f160f419803076006000100b00b2108455a90140e60030000c0040c8000d0140d1444003200c0c000007800d07603100080500aa9291900c0450110740c00d4800240359440381c40646258002400704607049142848024801c40007410216241e241c1500c5071030408000802c040600b090703e22003840800c1c400000d49064075072000e1071840640f40d5903800c0c100c080034820103030f601c5030819014003074117580403000c0c1c13049070020f4031141007003200504542040442c500a080c0c2080700301c4050009440c1c801c0807526000d140d03080c04c0d00052013800d8000c401880c1290016218240e2404001044484c0349401000b8040340c5000c0240b08510b5800905603401886941c0f0816000703c2e1840c280c203001c0900006589100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 926438848 1106 926437742 926437753
    0x4271b0f0f030b06030109060e090d0c030e12031c0b0a0b250f121409060706050411060409060e0106050909070f030f050f06030c0402090102070b1b 65
    0x1e458010152a2214420580c44150045001e0480307404081216802e000b80541400b40c00f9000d403040e9440f0702e400310180c65004541000041e81880c0001310320307a543d00022030303604041d02828100d000000f0741024682408010350764800c5602424050040180c00f00100c60010f88036245450340108401c00180c08482d0041c00303000901680d4007001c0c0190784450444284207142240c0d1203a405005207070141c0c0010000f850001074a40c1c0a281020001c0440c07000d0140100c01005a030300c4002240402103081020070801d20050141a00c1d903587c3c00e02d00000c2c10652040552032a042000030800c2c500c580c0071601c01910103488851707180c580c404d081341d0500404017048101a52800e07001c10442180c000c13140a151030050b00d520b282040002c06080c03c1c0f501e0344451003903104010391462642c020802c035003140c0701c0b504541d0f25440001e1924a10312a0200300c40603a00a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 926258992 926438848 := by
  have h0 := BRFrame.cov_init 926258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 926258992 ≤ n) (h2 : n < 926438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
