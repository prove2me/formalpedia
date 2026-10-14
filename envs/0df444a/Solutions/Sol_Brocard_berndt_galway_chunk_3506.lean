-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3506
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:51:09.050314+00:00
-- url     : https://prove2.me/submissions/a95725a5-125d-49cc-85b1-832940428949

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 630395683 ≤ n < 630575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 630396933 1250 630395683 630395729
    0x3020c09100e0a1b050703090306020705010507080c0703020a020d0201021c0302031b160303200a121d2a041506090b0a0801030b15030d1e110604060510 67
    0x840c06030200d031104690200308001d000380150740501104d040c0210345445224800c0d00c8aa006240031018003400601c00000304140b0710142014034020000441d4902d844040140805001004214449000c0c0206400300368005141c102c4143d040d03c41400c041010300060349070010a1b010324003168000700c012009180c2c1030b0051405050309100da0f54014800c00071504042c0070740440d0344100403d941240780880d1094100b0007110030b0309040e6400589c100a600d044990103440440c01003540c0c0780684001110600c20141062611102050100c6000c0c45080c3c0380d90203034070401c400051510f40205110050386d215039420000400421602090080c107040580e0640b05241c0810354078074000a21040c00403c50340b90000d00d50780d04440740c1c21507031a10364032000604201c8010401c40107454140e10100b141e03064031070041e15201401c3e07013015191502c01002011400400960f601c007104034490008440750416444000800da43d0340d000c000c0901980c20ba4031904c1030080d49900303c45811 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 630398183 1250 630396933 630396961
    0x70b030a29030c0a0b030a020f12090d0815090a0b0a05040606180605040605030c180a140907020c010c030806040b09130b01090203010f031b0512011d010b1c03020c09 73
    0x10054040e1007941c010f0070b08000d02e00c40d141c46032440441c010000110220b01a0380104800d20a40c0302117030404034032031a01003400340120b921078959130190207102d010580104e04254069001e10401e00c141822a0202d45541000741103290760688805010941d40c0e110f50140010300805042005001e0380c650004065041007151050700c040c0100c2c000ca00c1500c02c50403202920000d8035828619202d06602c5400b0360300050016403207815040c1c1101d40c560f2059489401485001c200c004a41011810000401d038040c09290035035103d014188660798100c121048029010b0400c140680d03250800b107030203000c44148103a80810307060100000381d500c5a6542003801e02490000b215a84c036103803070320101e12003805014400401104c0400001d04650202c0103c04042c452420001d9510808198070180c0c85009400d00d94403458a4074400d561292800100440c1c00000d018501c0f018020600792440915058840d86201c8e00000900d4001c000d120811040a41032210610b40045440e50304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 630399433 1250 630398183 630398261
    0x1202010c050318090a02180d0309030c0905070e0427060e10051006080609010e0c13030c0501110a0809060903031605031305010c03090605090d020a080307030818070b030a 75
    0x4c1d20702840420500152031081c1d5102c3d210204800c00070034841c1d400c210410216280031001c0002d05400840011542d1110f0b000421070800041614106680c001d0450b00001c820310f8007442c6400011003511015101c507042010000c1a0071a00d6165805c112014090380c0602506c039104010740300c40c15000c1d0b94000d5202e605100c8041e24030984038002201d407140d00b520b103240d0240c4444018000b19605102e500c4c0c0165140080b0307442c0201c05038441018130f400c0e40c4141c41603074100327000f0400d40d6000052812110f17080d402508803031a15942c0c1403110b028480f62180117040c04142411180c0f010403c94074407104a442d1000708172544c1c680b00c0d541e036200c1e104403218810315603400a4254000c441300c2d14040e505851710007032103040c0b1004407120340020000340e9001c20500042c0300035854a07001c80f0f020b461a8005107aa850b011300b8081c0800f03501907c0c51010100484140303040c0c0d80041408010385102c0c2d0704c615900d49031102d5210150000701c88210310b01240c100003200c1d800c001d912030115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 630400683 1250 630399433 630399439
    0x60203040b1e01030506010501140d0c0903060e0c0618010302040e15040f110715060512010f0b0a15030c020a0b0c130501050315120a050a03050c060c0906041202010c050318 76
    0x1414a0b0a2544211410a100040c1241d00c200300500081d8000c4061028400d90001001c0c00d210a101c480003d56643c0c0d03038140045882c0141c14401c2c454035006200e06000e89500400d4105103400100d20103104000e05511035462890648900d81c0c441d40469005000b01000009035081003c03d0840082d00410000d100d1480c103c1258070601003030107050f89401500035480d09142c130984071045010481c0100302809503885c040450b207a41c889000101c9640d04100001d0384810f80200d4500300c0d886188424414411000c0c1000342a2040d0881c8c0c0d1810103500d070118203e030089105a10345502461f0082018044004016130120b0507005000c20000781030a40701030f40e40e01d00043d90707180300584800039400d102400445650406582e51032940b4030307002c1103806100c01a1075090410040300d4003100015000103002400c0c0741c080014a403c0340d040c16010340f8008803080003510741c0c880e85c45642a8a480000302205580c0120100350945410102356651400c45598440c040070140d401548 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 630401933 1250 630400683 630400711
    0xf0c02030f062d0f060108060409020a0b070b1003020f012a290402011b0f050d0203041a0c0703030807050702100503011a03090c0f1f0c02010f020d08160507060203040b 74
    0x2031040e8280ea0640e000703601421500c0e1302ea0312184011544800b0003440260032a841e050b4480c016100d40b2004002010749400058840403d483c0c030a100c200f010b0030031801d47d0b6071600140b000d6a40d9201041e00a5800d08000041400780a281847e54885104441c41e4140c0391707644000380540b072082841a40c42c80e00041c420241040004ca000000a41e00a4001228818000c0e500d000f000090450305000301031890f500e140d2a52010724101c1030540150041e0008602081503144094000d40400000e051107424803004010b05507032403e680c4030160400111002040b402802081152280b0350050000c8034a070018100203090b980c000c0c411a070b40940c1c0c810030030001c0725101c81a0fa0091100c40017815582264000700503803036011441e06c80c3d2200700006005040c0032840c50003490700c00561034a9034542a540000b500c16903d0400303240644d008003010b03851540d07020b411141e00114003545c1859204000718215214050b2030401481c1c18400801d0005001e02d0840347c40c0311310000382402c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 630403183 1250 630401933 630402001
    0xf0b040b0316110f0d0f1107090e1504061a0105070519020d1b06020709060f17010b0603090610060e010c02100e061b07121502032809060c02010c0f0c02030f06 70
    0x848101003407c070300086400044040c0328038200780e0003498488a018049444011004801d000340100581c2d0807214140d80d22080f00c180224080038503805482400e1450030807034561100b586404003045c0341d02107800100c1d000b03001c66680b080c48900c1e081c1c1050744409064184e41d482079900110b8000c0310058030134102e0004840c0694050001500d03443c80e0888011032401841110013803903940b4441483d500c4110b80f4100751182c2c005584a03059200042c03800341001d28000c3c802141c00e812070703010012844c1001d400359800c80c242c0d0117181c0c0d05417840c0c00e00b048955411104078607001400c0b03a04c940002210740c1e2040028040058100002082d50b41c0c85540f034a001000d1540d00c0b070020700348000a611a160702c811507002e1076200581c0c401040390380c154a810001070513074450f001c8821541c3ea180710018840c3c58403a88002401c20f00080018130f18100c2d0141c1501809046541040142c21004003103441c10700078100800003103803c94903141090341d100070301c0c0d0440c0c1c0840a076100100d0b14035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 630404433 1250 630403183 630403187
    0x901050f0108071a0c0d1d06030f0f1b16061116120e0402072a0e0604200c0d1205040804210506100f0b040b0316110f0d0f 54
    0x1030303040301c8000c0300400426140090040302480c01500c221050740f800e01002d503440c80c00348030b1440c0c500215038507030300d4581451100360400d007000c540740d0b40940414810410700c10500c8016035005207030b030308020403160303689401640d24480d00b0305250502c10b40894907000307046201c0d146085c1c880c407402040c420a00081c1c401e010384e001c2c00c050070503126041c0e03420002144034640c00388103c028a1410400f00d40d02c010108080c2d074001002141c041e01c8030f1240c503030516811f00c44100f580200540c102c00c03072031a020071207080c01c1018090a1050b5560000c441d501480c98030f042c456440c82542d80c5440d40c06031039885441e510f0701041c220110718245440c0c85892028410980f00b00e60211100741800c2c1041087d08001d01b001205020812440700360b07501080c03040040522904002038400010703401c0c0a040030068105510000610100340f00038031008100701c0503030740e100d002d01d9101070440e0880701003100c1521040d4043c1801e030090300e4000781560b0006c900781c49180100c1c3c80301d00d841038102c0c100f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 630405683 1250 630404433 630404461
    0x5100615020312040303230103030f11030702011d1c061406010c030504031b031a060f030f1902041104090b040b010e0315070519050409110a050301030f0c030b07020303090105 77
    0x50f55228030407090002d400130b406a03014100c6041904117100c0521020071055401220030f0308187c0c0429000c000035000c0980c010006c9401c05100b0014508002c201d9001030800c0c240701c0100c000100000864100b2038482d03010514000207141550301c500a1740b401d194000b0b0513440b0111459400050001c1c0b80c0d540105244000c0aa240d512903245c0740c603544402d000603041420818240c00c0b0240008089030001180d01803a5010080b41a5241000300c10401c40d034200028641c000e4001c0c61051002c5407010030300d00ca0110b070b41c2445a403991194030014008090307050360100104008103001c0b40441545c1d0102c0c00c1070109079010452480c20300019260511198141540340d40880c40c4d00c2d03901c0c2c54901e01e282d00b06406080450600341e41031550030342c0d240300ca00c03100006103010504118120b0b0a02406224102d2003904500c1c0c11660b14009010f4441400060010840d0500f44010004c07400541c100075500003076124030a060a020007901c940c070980b51202c0540c200000b1501d0400320b0300b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 630406933 1250 630405683 630405697
    0xc051204121205040b07150b0306011a1e0403050604030207090b0604030201050a030e0601060e01200705060c0c06160623010501030905211b030307080a0b0d051006150203 75
    0xd0418640c52060342c0c1c01c0c080029410810301042020b110024040c549a006810700d5407107604480c8034204201240c0d4122103200080d14030aa03c82d13001005419240c6c0740011000003d4900242d4808041080780580303514400d000500200c001000007d00c10041801401a40320342d00307807418241e66240c550142e900720300c00c859000108110800040d8000c41c0103080c00c8081d41400300c0c11241100f060360030100245e102e0004a0200d09201142d50382c002d407800c91001c5e8110918140449443c0047d9a0750090301030b403401004006100190f0840c10084030b40302c0c1138000e00c00f42ea50303210401d0495461140d000120390190a204558900d0041c400c0b0303c00c0c1e5503107040b171407003000da180400440103807002d03410980e2203000e004408014040c5640c5a008800300329000746a40c4c49000040c8000031000d856150842d030000c0c01480004c0d5840020740d900078160f40c0700800c4040e03124001652043d41c1c1c0300300400f00e1240121000c000000303a0440300480e5010360301000c010005a5003a0384a00c6645 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 630408183 1250 630406933 630406949
    0x161e03020a0e04020d170a0905030313120201170702030a12020c0d0f0903060e280f24051005013905010902060a02100b120c040518010c0c051204 64
    0x10710107208001c80004041e501a000404c24040c601142e15800d60510f14021a202c2c80000000c40314800e54200ca105402490300750021840d1803c00064403c4200d80c0b80a03c104490f61b420007001503a10403000840c0c040c407a051010345906045401940d17941c0300c18141e10103d00c8100701d8641608e0144241e40010400402034503070503120000485044400e41c510200b8010148000700125600c0d20401581a01040c0100005030300001000d44451844846024408002441c0d0300014081c000001d4100e0b17104184000e680c2119280c620500c80113217850120500e4141003001c08180030b000d84040351020f881c0c083c80c400d00740781020048061321030f00d10181c00b10001d84402c0d203583c510380003030590301030741c00080c0440240d0b0006140368007402c65600141d00000c40214401c0c003512510035500401ca4105000006d0701385402e40b0313a40d090690b148540c0d903440000e03001b400342443c1610742d5070700c1900030000c800003600094040c103a0614160b54505c2000c00181c9160b4880c011134003500c20b29 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 630409433 1250 630408183 630408199
    0x11091603050a0e010204030506041e050a0803041a1312080c0901140405120706030b270613150303020f06070219030903170304060f090809041508161e0302 68
    0x4000140e018000c040c00200000390f4640300342220503000e1001d4800346200d080540120b06007802c0c807180c0381b5203800b0f6a6030103450280302c1b480040c4000622410cc0e960156445c0d0f200e43d1a030821046030b10000282c00800e002c074101300308410380002c0c0c1d0050901d10820500c003001c0f002c2002140e10400c21070307960307003050300400900d102980640c010f030340d040d2008100603241540307071404151103101c18100b0030b580b5809a4400e00855401d4010354800500a4580740d500d07124854403084440f48074940e05110f1061030740492401c0d15407125940c400c180c0c40703805200903010380c0083c07100031815202c10380041c0078440e103e542c00d120200307a1301d00403078544d0700601d1500066065811041ea00c488100d0074440d00b200300000090300b100002d0030080d420341d4140c0d00e80c5061b08054094400751780d07405980da0b1414145100260000c404e0343d04421003a64002044e5021802c03074581c90100d0f800c1004540b09680020180303500c1c0080b42000d9410004001c0c07180c080d00c400c041d04c604243c1c00002c3d0b2014003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 630410683 1250 630409433 630409471
    0x906261f0c1d030607030e120f040f080102180f1207030c0501030f150608070216091505030c0a17070305010515030c010c1104021809070207030c060e0a030b0a0e0303131109 76
    0x1090300007d2103aa4000140c980111421000308102da014042502800c8400b1a080188040421943d4001d0501500030b5242898000e604c10380203456020481c499a034861044505803542000c04080c01030080480f0344881d100c0c1082c448807043d034030541d400281080120501c0035041d0140d0100c401c01c2d040c9501c0c80505103403082c0c0340040700a0080007140302e680d40c082d0b904085000c5810046c83d0001c030024840111507105274001d10b046e00040d0103540521400f050a4640c030680d0710454800c10b80215007031000504280c04c150081d4030185c5190301386018809500c2080704244269101141214030901d500300065070348803070340c280184c51904680902051810250001d1000c2909064023502075060f1400044809100340c85034801a031010101b801044880c840800141131107050a6001c0703905140040d140c0c150501004043c40503110100701410b0654025072600e41490040c0e0780c981c588090201c152905a200c29640c801c440498071000b0304000342d0b5a405256088410b50840007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 630411933 1250 630410683 630410687
    0xa0908071208070f0305210603122503440105180601051e07030f02071a130b07031722110d0510060f0906261f0c1d030607 54
    0x4004c81c0140c003840000c00000440044600031550307020000001603000d42004410706141100c000040c080c0c2c440b081104408408490390808440e00aa40c682d4440f030101c0e1404a400304001d508110003402c2e544100395096010740c0280120896594802c81511440c0030907055140c802c1c416141c1004460b0144203404101c4071000340e114006042013880c1c43c104103508481980c05142c1e0410307100300429040d04040e44407802501d5113803e8402404400c1c1852400c2c2031181003d2200103804000213403850103440c904501000529036210020b4070744d801402e01410000b20940110444040358001800035002100f0071404d0118226290820402e15510300f61042d8150f141e441d80480210400c1c8002081005280c113852449500072980a14040ea00c0d50b500496400c8115241d0400c0380600904243c6a25058a950711006048010302010705941c00c02c070700d00c0f0a4611504034101d5001411400d60001890a0601e60f515000740c040c044001480c1c076066980258144c1108000c00c5100c0c4c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 630413183 1250 630411933 630411953
    0x40303140a051201030f05010f0605100f1e020a02030d0801080d050f12190f1404020d081b01021315140c01060902070501060e060d080409020a0c080a090807120807 72
    0xd070850410a01d000495600049048400d0b0b2003102d0249000045204000742801803504806100030144581820280060a80c0150b0300c0c3c048100b055400303070f502d103843c41840684410160030380355212520003607000940744e008094083c2d000384210401200e9803032241d981c7c07604a505e0900600350384102c006046034550300035182488615400c0c401021080400a4414040c64520394801c0029050a80c0041960045968001442d191211720a01c0820382d021080d4040c0d81140c0460203100b440c6002240c03400b80900709101c1080c0d600210030090310560003031002c01303290b02c110174080da5584e00703103c0d00302d06c018030210002e04c1345001100d00e032400d00043e22100b0795180010800c0ba807204003910490b0404d807020750790b0341c0d1201c5080160003000206150448405e86000300e49190544032814144242d1041c40e028990001d244103210307114002d14591036a108255543e144d421200040824106029506640c0030f8034500081a0303800d0b010f0000040c1c0e020b6078a5040c00c200c1c3c0c440039113603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 630414433 1250 630413183 630413197
    0x307120b0111030c010f18030917010212090d18230103020405030a03030b2b1e0f050a050705031603080d02040f032906010c0b04020f090a02091504030314 68
    0x20101070b450a008200042c0701500b40c1c0c0360300000002d4144540a10402a602850300036006601c00014600c0030279803150b000400c0d1480e844440c0e403412910101c2034020b1017042070040241c170041040c03040b144c102003081043c8100f1031b036402032040b5070301c0c0040071030804030704c264806510708071200e012602800c024080c0812050500608050365040840d0074051250406c034000f9540d881100c140b03140c42601c55030822148559210008a0a030b050f0100007140c1201800f507596010802ca003456410304a40500350380521078580c0e0404e00d1420341c0c2c0d58546400c044446014545002c9858140020060b907006100d40c4c007150140c2c519102c0903140d90040ea4440501c580800011070401c05485071880210310903038102d803c401084030801018207001450385140340f5500c0c00e112160380e00081c0030388290380061a0b060951500d1000501c460205001c50b60081c0f0940304000c2445251713809040104802e80d1500b0035078800380140316083c80341b03000c018007140004403001224624000070b0a50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 630415683 1250 630414433 630414437
    0x6010201060306150f0b0711060f040306020f0a08092d070b07080901110114010902030a200c010b01050418020310030f0f03170f07030e030f04030506010e0108030307120b01 76
    0x1e540d449854010030740d280490007500245070354400f000312480c0101c40c5801000303400e4440703003841b10340d42c0e986290200d405060f42c03045a01045079030200780740f8011900296840001159500d40e0170100e00c8445d0080f000130303804512030100040020714042401c11014002603440c00c81c0810150b4004520f10b4590020303034a51140748000700301f60404100401c0b250340102507080e00c0c0c0308003000042420155002c580c084d6418011452442c9568401050545507415009030b22550344520010007441e00400c032510820300f030002c48112020320801018082d0001000b44090000040103503189d1181c1d00c00c000f090002c0c01003400c06000b04ad4007540d00700c4a030b2000103103195034907101d00514080010003601c019100030443c60415412649803082e909071012080310515140b210030078420389c024103200034035446040e05060b0820900480d000c00c48031280140e00c55840342481e9660380400d005064210000000205201200000742c1384074983d0303982d501200c01d2103002d07440040d03c5040711040c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 630416933 1250 630415683 630415691
    0xa06080709080105090703051c020d031109061602130212040f03090506040612061703090f0a170a060506010c020a2c010303031505060a02150c04080f0703030f090e0f06010201 77
    0x1480303040c207000380d5001700542d5006020303ca0440c1025030400310310408040c0a01000401d850200f03800ac03c40d80c23a101914100010018480010820b0703034400c10644640c0301c20002000c0c4004410103c01c2c00d60301b4001e60760f000c580004082030f00101d104141040b000b03200300c600040c00040988052001c00f51082c5801d4a00a81e00c10100d0802e0300b0580002003c6108141c0f200b00001e02c0d48aa44014000049002101101041e40303035241e100c1c2c0117000b4001c1c0304600c180402519017050040040903402101e40c02283d591083c96105c82c40214101c400e5421300e004240250320a000d2151510b0300144240e50030303440c00740e000b188103c901c4500e072031f004c003401944c0007032800d00c0d040306000794000d03100842d0420310b480403100724111540050344500380600c40c00500325400100300520a030f0b019010351141c3c0321b0402c02d90080c0910381c0018954899400c40b84007145000c120031007160b1083e2a07140c0f8083c5804016654407420380205070b10340d801140011088960b800c911a081241800005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 630418183 1250 630416933 630416939
    0x4020d02040513061b0504050409031e020a03020c0a060917010605040914061b0d0b150d0902180c07030e011e0e1804051005041e06050a06090b0a06080709 68
    0x41e040c0c400454210f59081d580e440558107110190060b024201101c002101038603078280000f40c403078010740c01043e00441d03a6030300810815002d44208441e03009100940e982007403800a000b95910381c100c104400500038141c11503191304040c0c0588059401e1a02c0d814685402c0c00d800a030255402c1d000148503648401c0005100e803510700c11501424007540f491f0300c081c1e0441035401d03e002c101400b00c03500d06040d62425028514810f042da1040b14110741c0110b00e5901d410000b82c006080b18800006020f00050000900030035517000d0310034244299944007040202c0c84640c0e0002c032040317400c03481605003003003403e00081c45400e0070001a4030504001441d01003488c90004410b44000940c3d010807000700341d000041c030708050050441c800409050304a4505585d62585880020445441040c1c442d0f0109007000400403d5106039002072050f12001d15072410803001606040e01c418200314902503000c2044425401115989000a405035030100d03d05542118080d1009040b0820046801004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 630419433 1250 630418183 630418189
    0x307090e19030504050a050913081b0312100b0a0e06090103060b071101030e010e153c01090603021e0a0815060f0d24060e18010606020c010203070b04020d02 69
    0x1601c00a0b009548890722941448148514032003140c2240344580c0029040000701c3c00310210309401c85922081b42074648010201e40c6000c0d07441c2c46031030700e081e010220f1402d0000c210007110601c0740b9031008140f00304590300c6501c0c0089225000c001030004d0703005180844d0740c0c10050000c00301808103140024120f513840f003e181c460303046000110345039140c2800d00700f02c0e9030b8540a01012001000001c010b0019040c840075551801650a044106a040c00007408242d90038140042c0c004082030380c008031000c5000040c0c0300ca22400c40c2441c00707060b003070002c51800403d210310805c3e2903002d842c5170103004080537400704056154100340d80c424001c4c1c01c080707210a0700b803005010f41c02c45580d5141d107a0074040100040d1401070182180035002c4080f190f00424000f07880310241c001200301a0344a900d0300e051180c050012a000b00f41c0c4d00039a601400010284103015501c40031507840204115604e844c012600e41c8000b6a0960059105000ca140428001154660450b10007010300d0140345050f404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 630420683 1250 630419433 630419473
    0x402210705041d0d0228021212070c060203070c170109060606170f1003030c140a0308011509080705062109010606110102030601020706080411120c031b0307090e 71
    0x5101c0454918090401460804c101c4900e000c802c5002500380320035040c4448152503100d0030300a0ba42804403040341c0a41d142d44044440c010446025a1102d5000050400f1a580720708002c454100e542440019803c0c80071055901d00c55200c100c0c07220313841c0750000c0170001ca5132540b4000030319581c503500500001d4680c03223036800604e00c580b2104100401d10040d080c03011402400b40841044840030010304507581280c0c0b0058030b03454184407043d60180c0c18900441008645400a140302d0b44020300103168215030494100c0b0000c03051050080202130b0100c03000c100500c600049544424428040c40c944040507102804840b015441880008081d01d5007511003900c40040a9548000c1440f010307602a0450285004c004001d42c0744d8103100780001c0d43d914640c442c0d202000441c83c04a020841c04030340228822030700a10316400d0b000606550781c3c84440241c2854843c0c0300e081c148103108801c14010315042100200078113011440d0200020241602e20786404003401440800003540c0d60b0111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 630421933 1250 630420683 630420701
    0x3070303020d1b02130504031404121e020d110d0510020c06070c08070b07030f0203070f080603010e06040209041b09090203070608010803070f02030f03040e060a0608040221070504 79
    0x100814046000050140240b011901928a81c82000f5820300150312601c180c1c00b201d0324410400140c0356540e007400c881c000701000000c02d40c52400580000c4081e03404414100350360007001d0000891080f513002802c2060700503030094200403020001000300b0b5080b400403516800240100b0300483d4150340b0366013400074428003503c80c1c9902181040075070303e041114662101f0241029000d0541d240ca0342e006a005013003000b000300c03034810000b540e2107129401c4200b441031340b0f10003507440342001403002d0810440001e40c0e0001815402c00160303146014002c3c21010004800540309035100d030b40a00859140060055408921041061192150904440f030041456210008450802e80304050400100340d104604100c0c0780b900510241d04080101d6000303550100724415014450700c0031909015540f82221010301001c100020140d40e50070806104d20030441c1c0848405894000a50300301c10283d40103508001c1c40131010100b40c80d244100748422501e0007c50342e801d0b075250300040c1a503d600d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 630423183 1250 630421933 630421937
    0x305040f0602070602060c03100f0314250b070503090d030207030b240d03120204060203250503031f0509011706181b04020f040308070203070909020f0607060b03070303 74
    0x2808000c403001401192019048a1000c0c112141c50408020354070140078000c40c4034940000081076040850990b207500508120031a0b1342d035035550b800e101c4a0000c0d0700b80500314a0203000156460550b82c500407040c480d6094182f184141d04042103101282c02038001160107220420252140b81d64040c4204545882503008000241c2940352820b064800580784254400c07600c0d010f000b601d50700c0002c0142c02502503c40040b070700558241110080b00d05e030110880039100041c040f44043c2d0100003042c5000048000c500c60320300084c03001c11070b28041400900203070002c1c8081420b11119020024002d8030700750903501482c0c1c8650006041c1542a40b00e043c0a40301c60445600034007003030003242c1d84241d51602d0445080c5c44d4514107178039110300c00d2080941c10084008400c40b56100d906492022107140c841545468881c40c0c1031100c2e900428081e446031042d540009402d5001340988161a40c2c0078000c010008801801c1c400c641e04035400881e4040c0c0c8031140894191001c000e00401540a9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 630424433 1250 630423183 630423187
    0x9410318150d060f060e030304060305150910170a080d0b010504171b0102150117010906020c0105040203150c1204021c0308060108100f0b0c071502100f09030c11030111070305 77
    0x203a00603103110645d001a06110000000d509940c0d004815101190340e24100030a2990719100e10b084182d00390604592311203800001c0c031440c2c62040072200c0a884803511803200e0b1481d41c403a510703501c010108000b08980020440c11001d00c199800800c071122060400c2d500780358403280c500498148002130001c442c2d2016001240003050190340d2040781c0c3d028006403008205c40c104801a02c0d005011b2000c0c09528049103040e140000d501c121400c90300003100710345171051841501d0203080d00b5541a8403920900000000400042040358040d80c40c1050345441c25041c01740040718070b00020800d0307a00c0003000350340c00d04680307401010350b5100340300380d40f0b034510f030300e4094009000c080307000d8010607820740c04440034000ca15080694505864180c0d03140c035120ba4001980e1494101c0680001c3c44034158034032590740554000403003121607a03d004080c004c2d104105001000c030b54250030090001030000c50300801059030b000140c0304501004e0000710705400c0040701c1c054182d001c03c030110005200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 630425683 1250 630424433 630424439
    0x19350a0906031a300c0f01050a0f0c110a12060f020301050d1520040e01060206130f030c0b1008011a061c09410318150d06 54
    0x4031050356006004a418204102d04000590010032404014414042c0420421a0054804108180082c11061001401c600c100382000c80d8803220921780aa02030603c8200c1e00a0300e42c011010354401c0c404036914444181031414046a65050080b010341c1e9582a14400e003070a40c944007264409050011040f0800000700c0c078003a001c90300b05c1d84c40d04803250b00c140014030550b50343d41d00b08989141c0003d0705841212454240070001c1c410300c0d000d028814950701030750230030301c2c5032001420480e0840305901300c891381d8541003aa1240d030304031401815010100001b80005018859144285003740351607140307202103903a88820036205a42079005010602800c110740740e024014002c41c4c3d454000303000350004400010503024064002d44202d11080c40170080f02d030300f5481c0d10008040e0b800262102032207054103400c1203071044044147d49046d0f141c00c002000741021403980c81c503551100c8003d40c540816540d8103200b00030118040e80e803240c0c0341c0b201141c030408020040c00821040c0480003800b145 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 630426933 1250 630425683 630425687
    0xb04080910090305030d09081201091d030a020706052a0106050321040603200703030209131812020f1605010908070b0909070e0d030f03060819350a 65
    0x40d0000e801c010850448401d20000e0000300956403151054000410042031a107002e60242c01801303111341300711020200004014101d600281c0480c440607094417030203051007031110744900c6280148000b40c0d0100b84200300c218803440090407149204060198100c6a4000d030350350440315103081c240f03181e454581c04e005501d02409811050301e880110b10101401030f40c0e2100c05405039128a005141c2c3d907102094124001c1c1c110722840120a280150f980c0c40145400350003500403001c444e0041e000000000d408400c548a05c2c6070030500c2d203c038802040740503908c4201344107440c0c9003a4114015180307650340100b401c004021940c035446c900715082c03d0810f030004210f050315500c15080741d8810f03401086092001000c8419150040c0c50018140c1e8900c402902d1003100040869000b00308480081d0501da441a40303c003d42e45a03036001d12210307544400641e42d0380b0001810691220f140c0c030714080080d0300440d000150b113403074001800c0014003882d41c5d111211142410161000300001d810341c00f9903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 630428183 1250 630426933 630426949
    0x908030a0b0f12100903031103040309030b060d05152505030108101104290304080c0d050a12020903120c070303021603030e19030c080d080919120c0b040809 69
    0xc681501caa641040740b50030f00d0340c1c2d61900d021400d0240303903803120080c051602c6608405a48e01402c80302582d2030806250003000d00c1110321060b50015281808102185040310506240c10340020003040b15040081c0c40e26140800034000605481001c45408000d081d01442d08420842e1a21016125854407050303d0800160b1080802c0e02071410320040030801d81c10041d0740170b030780c500c5885804500092007901800150420710302000200403082008000d020307001000291000001d44558843c130140c142c07200c0c0181460301e00407a19024051190070b025030302a11032014000c003191109012010000602c0d44200007081903504895410300501d5010081e04e0441e0007601d1802c102035145450041103943c0d04d4a8951292000c51428512404c0c481c00040c05580c0181429095980c0c0700310140d540e914624014002c22080030000ea04014049031354031204580b14112000600c09955621840c02c020000400b44007003002d980c4086001d444009214038410307510316554904000c10000c0751 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 630429433 1250 630428183 630428209
    0x305060301020c07032915011205010f05060c070e0c0304020922170c10020a0314010348060e270604020403060e16120c060e01030908030a0b 62
    0x6070780100003910809100146a00840b40c1001103600350701030000a107070321582c2201c0c3c01c0040c007600800340301c0300194101c008030100409032510807201210640740030946009100d2440d0007118590108201c0c24081b00030101c0c0c0c808403054405803625000d01d1461032034241c0e0111031160012081108504144071182e4000900340f6804148101c4600d00400701a207201d40240608991407015155411002c04c3e00c01c440c81c44070658501c0c0d51020003210003500680c004500083c10706e80c5c83c0f44003090281b900d905030790f00f0a83e01540c20b020100c50756400c1c403010100124003c0040d0a0305c6d8444080c1e943d100c174103924000c280308194941140181500c1d20b01d048184116181c06030794004a4075031040b051109400c15208159607206000500203000d81d50014012604120004688a8000c1080404030b40030416290110317456425160f01001180030040c107546d400c0b18240b14440c040c40d9041100c01c130502d804500c6080c15a50724036541c02c141c0c0c2c56400346446004440d42c1e480c18240d40805 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 630430683 1250 630429433 630429439
    0x6150305010b070c121a090c13140615040e0703090c14030309090601090b070b010807060f051b1f020706050f0601170405120703020d1e270e0a020a030506 68
    0xd00c2e003c0d45508001031014468900d00c0c2e849a60703003000300700340c0350a01d101c000981e2080c0c40703051130b01c1943c2507192071304050081c0c0b2499030440d41180d03068680c480c111036007185452848042d51020184041103200c1000c00b0210319080c000054001c0c103a051003441032125990100d10483e0500c0e02c80403d0110390064900903458030301d00d101684000003034a1058000302c0310024245c90300360051f162244039801107800740c40000f828000f4005442c02d52412505480e003201c0006075508021210028101ca803000006e0301082030036120980880c0494001485a0a0352075149407203040c003158120041015401503004160300c814084148105a4004a484e24244140c9010320000b40080803070000100c0c40d4403120040740c10301404015400140031000c107080d55030b280b50700b00a07560f000507820407400102d402407038000c2c0c030781703660401c010b03006c0203844540e0349241203141021545040400c91001212444000071820194484d43e40118071624005944000815004007039403802003020380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 630431933 1250 630430683 630430687
    0x40b0a05070c05150f0d0609020a02031c0506090106080405010e03030406090228050d0302010e0d09030c0f0b07110f0a14031501050306060114070c1511370606150305010b 75
    0x40309240400440e54680805d012140d680d602c201000c5004101c1038000040d0b0f81d2010900c46407598000004017010b5254601258a2000d26030110043d01d500701d801c1a005400000104540784c011260281c0280c45500085450501c00303d010f03103940c10483d015a5a41d8450001000b5401c200d4800c1c154000c1800602d1200c403020b0702444000501ca05c1003d0041040207034140078140300b1740c0b118405180c490705075141d048401c000100b800c01140015182c03070038440c2001440c9120700c003041c0101c1c0e511840041c107003940c52701e4065042c15158141d60700505140348120b41507442081c144040c069540e40e40751507044030002d040c90152a0001300060150420043c413050380c0018a65a02500c00d2034100d6056085540098071400b80a20040126194110101d660400400405030040807071b075170f02d06180c0c1c00c01c0d0580c0e40c494040d00e81280d08040d000440080c1012441180c0c218900c0e400300e10308200c0317603039a12400c4459551080d00050314030400702a03015818000c0034014694892102c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 630433183 1250 630431933 630431959
    0x140724140f04080c0a020607060f0c05070b0a0903030b1801080d03200f040509010e01060201050a0c0804140c0303070c0f050409050d1d040f1b02070f0608040602040b0a05070c05 78
    0x84103070003014002516016000c119020407072010080103003d80c1c0c1c003a1040d500e80f2140c4c41e1005c05403003030034403581c48242414840980140b054080c0da4510380c2000c0072003101d0316002d008000501100b9000d80c201921110509490f07180d0144001d600701c1d0b035111502ea258500009141440346400c8003100b0941072002000f0034007401c50b00ca03400942d00d20540c640d07605840f001390805104562015410006c54000020030001c0401054104c07442e6800070711a550b02ca0480804481080403124041811040800e01091149010000106c0f16100700c034454490400020f103541c0000904481c10030790843c05010006400407108001c00c010340d0103100180c402d9442507126180280c144080050822105d4602d108900e00303041ca912000d0003c00c0019901c24030400074103a01d440500c0f25a600b00c5c1c00808403807002840d03004980610040b0342505041a0b0103c807444400340058030200e40030300011451414100c018410008641c81d03096844106190001d00c0748d071154482032141c0c2c80441d00b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 630434433 1250 630433183 630433201
    0x302060a141e0a06081c140304030c0615050306151504060f081f060f0e010c0b15010507080d0902130e0606040e03120403030204140901050a0614072414 67
    0x5941e90a80c80308216615a440f403207030b40c1c001c2940364801c83c2c4030706c00c42c070854001a9500039040c40100d880d0359065140c0801000400e41448141e070001c0001c6c014492400c0801e0203035000c00b071a4800002c5e180d41280e940c20000f45000c0056594100603103680c0d0f0b5202c00f51818201c0d80b040c3c2c2c8030202980d402c2500c0c0c40707409880c2110081e03001e024404100c00165414054503460b030040c414100c00b20501c1511680d004101d0106081884080b5010403500001c03903004442002c030080e4880060602c560701c10299458440031103101c18180103091028400159111020705224a04150002010f500314010010103030740c0150900b028034940000c00001d0080400c0322948003805680200d0b4052220243c80e203180700310303925001200c0c0f085051008240d03041c0c00900072112422000701c0514048000c00070766400030702c9400e611100700e0740700b00041400740c1c0618000007204a0020b0402c0a03d0b02c4101c00c40d0980031a510100340c125181c0040802e02d03208807214046800b54004c446d140107d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 630435683 1250 630434433 630434461
    0x1403010e031207021207031e1d010509040f050c070201020607050a08220f03030b040b04020c07090b150409200a1b0516062d2001180302060a14 63
    0x2c603007480036500c0006503180b802042914408801c400c811592a18513090040401d91110071283c4011000e40c9042002c41c400d1801c1c41c00001d940c801076040212010040d01c45520048010760450f8442c410710700040c5007803051901c184481e001c03035a510300c000e10009050620007403940083c40001d01c411810240d010900c0e50780003641c4c0c89642070404100030a168030012035000240610020b0144108055164001c5840d500045e1014099000584104420ba0152035004c18981d03211800800c100d170096004014105000b03043d07a6002a0310b08110350060340260028031001e621032449011004c2600c211034100141418070505002c0c0404008210090300881d602019020380030400c1408014800b05c081405604000074031035980d030801508405200982d42d00f240321209602214220340310105100ba0001d50780c9020000b5810150b62040d2021324901c1c0d925035070b4078541004003001c080c5089542c1e010f90000c128502d8844411000e80b2280305441400d110b28134144030044040741c403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 630436933 1250 630435683 630435697
    0x6060d08040e0402040f020a02010209030106080c030a1b0b0c06040b010518060607031404140f030102072303070b043002060a0b010315320604050103110702031002041403010e03 78
    0x7204900c183c54a00004c0c004c1c01042100c141018030000c2c0d800b40080d0154024611648145c00038821142d45801841e202c01c01009500c2c1c00d0307003003c0c010100086801d91207452086680c0b001ea82500e80350300202585422002c005500344c0d006000303000c24803140e2070000e0300400c1d0480d4a00200d80707030b00814055809000e0145802508081101c5c002c040c080c410140c0c804030030f68030054840e542c03602600031450129000b20b008032851001041c03203003010700840304278907000f071500c1d2004c00f40403006100d046801d95086519000c140800400542d600b403003940642c0c00f4041e9008141b0b01e02440b4291509052440300d195a0201402405690003041c15907000020b40000207903400c0743c3d001030300a0b101d90501109159043c40003c0742c010540c5485140302d100b07200e0700d03400400103403002090b03c10130f03c0e041d55400072060004000661207504080d5140d114680d2407802c04640d640400d1414034064814400a81c002c034042c0403202440c0840900c0303840031002840000001040181c40c1d114101c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 630438183 1250 630436933 630436949
    0x160f14040f1404120306050316060f0221030a051608010e070c020d0602031f03050c090406020f0a0e13020405180a1407030506190b09090423070806060d0804 69
    0x1050304084035140d80c0010300c1e034050b103202e8203054645458541c08208103c0b10b99400300f803400e9400f1070241070020341c0712202a244074004496908120702540c4801148443e0411441000c1e507000c001080d0801e8068940320b002069512400c0250b0920300b0750300010000d001c1e41c6003001498484d103074004100340c111001684074868686515070112040400644040c2d0450000666078040000b43c5c0e0040d8030584c00f040b6040c4031a00c040c0450420b40c4024440036005901082903010b50b46020424540c100f841400010b1402c043c4002440c4150880c03480e400209600141c56005400d101142d02c00702e200d01101146403e04007000502c0246644000340400001c0030000745003104a07500001c8202d43c441080d4040c0c0ca0400002000f818049030f00da4000d01080c00a0052101d200081b9001c0d80e126184184c10100f040041c00b8503000010410b4480032520046201c80e000c00100c550440c0380f651026015081c2003840281c648800078015500400c034010300480030420180903202501c1030300c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 630439433 1250 630438183 630438191
    0xa030c0207080111130f031a07020a0f060c080601092303030403170d0e150703091a071106150102070513110409090b0a0e1209040e060702160f1404 65
    0xa42800c0345841c0d00d9070002007142d86000b030b40d0030030550300388040c2415240500502d4000d98903161050f40036206440f00400c1001800d00100d0003009031449164000c200d481118010891612912400801c800040c0c821a980d00d00110304958410001903000da030030b003001249079151009026090b01d03140c602c1c0485040594400d500d5540510484004507040081c407035113404075a04d401401d5001e001c01c04010361822603010020301c40071420340100036080c0948405903072400c4055020782865503084403c2806050840180c0302a15101400b030003181c5e0322501e004941c091024176104001d00b0030190030400f041c104090fa0307030000c3c01606580c0181c03004404129903240c0c0310040c210100f50b07010800e5000c40d000c41d005006174402c00025002e10003080c2c25032960f040f584204c3e104045800791a400c082840e242c08100c210083c03d191001a00003d0740341c001c90380e10350401c45e058800c1401a08080c03030a40c2e0a0800784845c0016044036102d68001d540783c8207207000d100c4051040540120b4a0f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 630440683 1250 630439433 630439451
    0x1409061302012a021302040806070309050d080a020d090c0801110c0d0e150a1e050705060121050105090615100503010603050a021612110c0607060506041811011d01050a03 75
    0x26011030b1a0300fa540a03040c00b2003a00c4010340c0c000130350000e01400b01244554400103d2691080c01003903001074000014145001c54031404440f203a2000380344030200340c0c00304030036841c0c850b0303d11502c0780c1d070350158411419590400c3d058a00b03440c0c0080307410150290a01c483e070300078070010603661480c24283c10302996080944010a013a10041110615518800b00b0060307001e981022030303089403071315168103060905010241958039028080000c1c0c00c0c0e43c080c80c01070105030442300f0100c8890040984a4030719401ca99500c60940740200da9102c50390f0440c00500110b038000b450003150280c41141e03d8100c01d461104020028001481480c04240d2a1004a4000c2e580b941c110341000e09202d403500f10f014a642003040d42110100b039040d002625091a41d510003d012031880c18180008001600e01555500d402c0d002c0c000180c15140d105540e1058190681d1a03010420881441211115030b0b104290b40090140b4a892100c00f9010344560f640a50f542e91200840744100098200007480c210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 630441933 1250 630440683 630440747
    0x8090f040b1003090b0105011d010c030e0d051e0105010614090613080d08010602030f0a030902030c0d0b041a06010c021c1209081b31140906130201 65
    0x10040d00c1403600b040c0b560b410030b504194190400b801d124099031080905036601c100444c1c81504c40c134801020001c000780850190f62080c0c518080f098001e1400c1d420303040c011f10004032090381c5400c017101c080c0d1102080c0f0600c4115a484414203296010080199601d80900942070040c0d0310185a0050300010b490704842d0350304c13410741303d000252400c1c0da170083da107510260340e4818048507040081790b6410000582c50303100100701c81d07554188000d26401c00300d460340c040d03018019040049905004041c15200d00da12401501d0306040e008040304030071420203050241d00640c400d0b90200c00c1c1c01000703003044002e0340c1040d03140620550640d10384c0b036211300c0303a111095042c031201d100400c80c80c18412220071299102c0003c130155916017041c0c4100d14003542400786c0380d00001c60501d03009807001010711180c1040b1881c10401e01a1114007440d03804224441001315001e004144070001911402e002c13035810f00f00200303603014030f0001840c0d40328102130300064941e503d003101d0000140c110211004800b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 630443183 1250 630441933 630441941
    0x30c1302040909061a0307061e021002360307060809030d09050c011803021f0908060403030207030807020d080c090d0b0a06050102151b09060c0a21030908090f04 71
    0x14940c0c0c01000003090f145010406480c0729450140200c03003080f01e0301135a15021440604880300750301c4002c0491007505454641d5000c160700d240c1075001d50140510713480354a000800c10114034a0005070070342100c0e410420305403000b145100549011309613401c11034070001018000d0314401d08001c0c4460381c50394506ca00d10b11462020003801410181400100003002030310900903142601c4010041c050103ca140f00c611040c880a03602c20000d541103c1e00c0c02c058864840a9511440d04080650b00c40304514034200d000e80301180000d41c00207910b014598030215803a00004c80d440904480304d09050300802c00100030305203500a0500044604031640c80e00541d802650748890440214a0700020358001031041340300d0380717000d801076495030014110318101c3c45200e003420b495000300751030000307083e483e8030382001004c00e0300301c0d004000601001804100701c0c5034591050880900c00707121241d20708045d0514402600c103050a104106001515031301c00e949240030301352200034154018200080240c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 630444433 1250 630443183 630443189
    0x7140a08010e0c0901090e030f0f040f060c052b0f050d0f0f06060215070c110904120207080303010b070602070c050603190606080c030f040309030818030c0a05030c130204 75
    0x650301c0e04010820b41200420b030060300720000c0b140c100c0e007680d90302980c00a840d50343e9110030143c0c20030016800c16060040c06041d11008900607941055243c003940c10850310b06400540c0803555201801d02003040401c40c013450040290403030381651004100100c0003243c0131000005200a92400002c071070f100da415198003901d005024840007168003c0540100b00d460254169a410000e01089060001821020405aa10420310260384a210444240c20b40c4c40701210501c1038032412501031340e5100203040c000c1d400785070314070700c203110840002c0d02d0490158480740403504240f004100c152110b0084d150300135000f0b8000750b55a2403619042041211507000f85034000000300601080f40d00240c0304100b9031202080c10080c103500c2b040c0964141e5000c94054110450030800100d424500c48401500107110342012040b164032a503030b02d1000d4000c1d4291402d8071281c2c91101540c1c0c0303020000c885030741c03200382c541500460178800801e807030b5640c0f0031401d07000b904041d000d0750822426038102c03002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 630445683 1250 630444433 630444449
    0x5070315031203200c0f010506030304050d051204182a0c050f0109050c011b0f150207050f030c16030803070e0a09060b03070f1706010e0f040f2c07140a 67
    0x4d0b110b09003081c00142d0094249400380e0f10900d03810440412051107103a004040c01402107040034079203420400d115820203000c032094090400b006a459000c0c0000e071000d01025040410041c040301c0c001012101c4441c9000c7c440d01291488010700f88030304c082448142030301c0c501038280b0801404d005240200380544010150b1030414003006001d408100b007201e10800341d0703076030105640e52402d041d443c60003180f000c2c2210321a02c610300c0c00200219152050b8840880c1c01509020a580b101810551001e40c80b0300c0da070300000382140013500e0501580c260110005031071082c20b4155100d401403800300408030b07002d201030500711401c60b0352120881c00080c915082c00b8000181c9501010806400a40d0f801d401704a0700041328000314011100f0b052901d00d0024150300e07598131540111441c1500140b1581c118020103840e40d04c2d5100ea00071074503036450b02c100125074600410500e640c4181c0c0c0c040c0b042c0542040b1680741c484108003040b41c10880e8400c2c1802e8040c2e50070030001031048140b80d440525 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 630446933 1250 630445683 630445721
    0x1b140c01022505060c03010b0307050a0c020d0c090e030414040b01030e0715090b032514180909030f1605030d02190e0307150c08071a090105070315031203 68
    0x30000110321180c11282d48280107560180e12881c4807180746010a0080c1c00050340c2c14030000300a03620405c0a03003403210781ca262031184881c01c1d401150414a641c0c2040c0c40958004200b4050310100d8010310083d1911400150304e440c0c6004140c540c100459910a44a1038076241d500516a12a82007404c7d000280002d03640d0031907580d18280c4c10268900180341c0880c40c030402c009542d58070b0341e00740c901c50311007019030070700320482001c1e1350b841401c4485040e41400070341d142c4624000c90b450040c000c4d40d43c001e811440390f40e45c44000c00040d208020941100c9a20802218400e011140103964400590b00c2031002da503c15440c22504500962000306a0175201003401540e9480b941c0b24110b00c904d850320354150410315481403640b00c026501500b80c40c0d0040003000e00e41c04d0320900e00a003125018074511414060250740c0c01c980d0441108502201070b10030014801005405e03c107064000c070607402c08000b1401501c4640c2032a8945202c0504050920500411524083e402c802070040d20385607601 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 630448183 1250 630446933 630446977
    0x71410020307120c090f03031206090e0109050f06060a0e10180504020f100207140d05010207080415111b01120606110705040203040804120c0b0c0606041b140c0102 72
    0x2412207200b414050030030f90400c803400809501a0407038400341d43d094400c4e061124207688081c0c0d82c8201c2d490344c1c90007169942c00002050700991064102050070070001141099290501c280b904001c11041c8519030040414081c1d181d59010514007105c10303240c0003410541d6107202100d103c49195000c0c000240107070651440142c1c5035031107107120324401c4031140c0004100390284946010981d07144005a80507002c2400072074502074640100301c40c001c242102c101c074540d641900b641c0042320308403210362010900b8050140b5105001041d078a0524040d02c80c0140407000d56641c3c0c0190720307241200d0103c03040b806d41c0e692103004040c03121440304800340140d80d5140c0d00100594800700a480003801094004149841e0a0088030300480d0003140f82400d182c01c1c40306464205048090031600580800700000d03c45801e4005881d00d480c400019007807603d090802d100030784510413000c0c660403001290f5a007003950420348503002c2c0341051003055110900409401e009200b0030100d03a2011480d48112 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 630449433 1250 630448183 630448187
    0xe0a0e01090b1302030f06280f060906050a0c0602130b03130b090f060a1814010c180b0d05040323090f040522150c0e1014071410020307 60
    0x1401030302c007060310410201d0314a448900c0072070105a4040c102c21440784c012071542c0c07628000d2044002c07003401c003007100c41c10003403107806c85181c403a070001c00d440c140410200034290b000200000100b11a0400070b260050940c4014150b014540000b0708107607001c50003000f503001e0312031094054400041850307503c1c03e104000817640c0c24107080843d100050003001480030000810303006440b90703c3d88010308035038907102150009440d03100c0c60b0800e0000400f4101c030100b911103000d0b4100c0c6c1d801500010300107480c86002404020310030b8078080040d9901303a040041c14039030700c110b9100102ca080c1c00140da4603186800c4a80081d10749036181c0c0400194262090800c03084002c24000c50116103266100c1c42000601082d64000c5801c007116112041c10044c3c2001414503004400d0701c107000350b800c2522035000b10f07001c0f85c0c800c00c4a680002c0000ca01e0141a0810788440303c800c03445800c004021120362030210440c0d00c80e01c03034028141c00780a025004420310421459410035038141040d0f4880c0750001c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 630450683 1250 630449433 630449441
    0xa1a09011202040f0b0609040e0f0d0c0506010e0610030506010c02060c0312150a03170c160e06010201381302091302030f04020603040219030c06090e160e0a0e0109 72
    0x1ea104030700d010340650f41e5104c0e034820030a007510058030441c18000660200b0000384091858951580580541a8094141448001c0100860f51548444188241421403424005800c138225400004080c0542691558800e0301c02d02410b2401107016076480c0012255100d149000039049000420a8040c013140840600403108651100c3c03000d80d5030360f01c00c5071403141415201a42100c50f00e1070500105014071404542c15404105d041d181c85c407068240781c030300888200e140180b4040b07a10306100e040e003903000301034004400340300a004c4681e00c980400c50001c2070011002d00301c01255155001e0a031f54540030303040302e4802080040c0070000d1038002006544009806842804101074a4445030707000d00c00d40e8003680b10742940b4400c599903603091200310760028005aa010001c0301c2095841d40d51411100c0203140308039005401d146c600038010300342d42015040304010140d010704114a444c5480c10000302104140741c480420b40007600031800303030107094224a210244440000c15a1010f0f030300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 630451933 1250 630450683 630450719
    0x80d050f1603260a14100603050c0f03042001030c08150111011a03070609060e090a060e04210507020306040b070309080a09050312030f060d061b0c120c020303030a1a0901 75
    0x80600c600010170407845201007084030141135807000e01c1014445c0782c1c0300ba8056603101d8000002a86820341040305100c0316001214200c1d6540b8032a2075110710070780c03048140a4044001c6c2414032031400810809441c1c900002c2080c80f02c0b03800b02c098280c0f2a2703c6612540c3c0403c010400070001da0025040c0e58251440d0307c403803070f4060700c6455400a0001d00c5215a2821a60707941c2d502400081403070200188210040c0c4000346641e104c120100b00c43d0f00356081304e40201d100e800401070411104420355014628401c103003042c020240800e00240c0c81c042851030788240c0c01180003e541d518480d00384d00400d0041c81c05007400340d0100c1d83d1500c190b000018003080d0345084044841d580404c416001151200b140c10f4001c8040c60b602280c0c084c2008580c00c2c036642d200c1d0b00c01061909180b00c2680317a1030000c0c105034000904c1c44c69a2020310048003078004009070b061800301c54010700f0f90042641c9100190580d03500907075442d01c64035007a8440c00e0050140304010100382265030740e08500064400e8201d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 630453183 1250 630451933 630451951
    0x22502040507051303080a09030804060e040f02090d0809030a1a010f0504111b070b13030b0606031312030902040903050c1c090512011e0501080d050f160326 69
    0x10002c01d45107406502039800d03481c507200d402a40581141e49000d256000b5220380c5060202c0444084002a911400b80c40903042d6641c960302c07a0924481008192214404100e900900c10462010561200303104441800c0d00640741c030b903a82420780e0200385006052400074180305003581c0f007a40440f00c0000081d0499403010244a406a00d0342e04000c1224400d15480e48006400c100c0e0804c0c0d000400d22541c4100403a0040c0c0310415541d141c03034100e80d4002c208502d40b0900c914418010820040011500408203076039881c154600700c1e009603a0380f0800074019090310000941c2604a9109400c6846003a90140050203114000d00d17010748190050041d56401e0b01031268071003211110400e00d1250400d09031f65a0740d0700b45c600000e02000d03164500f8070030a2035480300c00e14441100c01d680100200031203c9400903003985095045814900f00003820406c0050400100007200b01280a0311480416001508a1003406190070f40c4c9150348510380d01d48452005500010071901005060322455a80e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 630454433 1250 630453183 630453191
    0x5090609012001020a1e050d05220501020405030d020c0303220f0b030f06102304081b150f03190615020d12060803121506070818010309150e0102250204 67
    0x107402c4a90000c9007020801b000603000d2000740c48490003500003136044220740e64540e69000c501d28080010030301903581510103a40016007001241000c2020a507149014400340041041e1080020f03101c3c03064110a2080c214800402d250200802d01004001c0c115414800966030b52499180030b2030f0030880b5032412018980002036040d0801444081d58010541d6444031000c006c081c81040440c0803504a052001e010b11001c15400d000b00070b00f5100d941d0046100300003220290400c0440c0c00301080d41c0b44448010301c4402c50600d91500ad4039001459070800900340da4452070050300600a17984010b42e518030740040d059200ea004540308030f03a0340641ea1400101a02201c1c00016901c062194034401c0d4020441c40306c00508072030b86d0310b0f00503641c2d012070340c0e10b800b074040020320030780102d181540c0318080003074044c0e03050148810710901480282018000c10050392107003440c0d0840c42a201080c26140c410b10144c00d0420340c1251400c40c03c1c50700d0348000041c4c00b1032441c107412070b06500700c0c000c07454 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 630455683 1250 630454433 630454457
    0x5071b05010515060415301a0a0b030109091a040807060605040204181d010c05030f24130b06160209060a080d0c0c03050304060525020105090609012001020a 69
    0x113082103900340c41e2140300c004c8804025560880340b0400200d000e207a5010542c0884c14500c044100650552003106000300d541d448015045941c17404ea420450721502c440b00040001007184000ea904541e20035100052070a490304003240681000d0038041c41c2d014100c4108000c0020800c060076949006035020401ca0380c642060108a2040d40108035460988a404001034040c81d0017014140451030881070396400081c07501d5094490120034900070480201c00c02544a0410320301e1070b40000b1030b103088807500d8006c00d5004049110010020f02031948041411045096a00800b45030b201c007506040d0ba0325600030400c41d0500310140200e1065400c2c40c0402c140f440d0a040b2042a14242c0010302000382e01c40209894030300c038401c4110b801e0004030400102003181400948004c01c1c440e242d4540e540b12800c0004559071807a0090b0301c82c142c4508000015036400801d0316450a025210039a495009100603500781e038560010900e205406024104140390640203416001d0035030300c032100c07d204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 630456933 1250 630455683 630455689
    0x60d0203091e03160609050f01020a0807082716060f11011a21070b031008192307090e1204320d0c0609050a0605070605071b05010515 59
    0x1100b030155010794018001c494032200c0c041d0414010360b01c00d0000095414480d038440381018082d520900199602084c0c3d16070090700516015800f11003480c04884603d08036414070300b01a074034205624004c0a80c044211480002c002c0b08484411624040480b160758140c01003610200070642000035550700e001004644c014044c02c240070b085c0d035a0144403941c07980180300700413050156130700317811041e4030600300049400e0012170041c1c034616a26640e60300d040408044203075030781c0c0c0c0003145aa001e0076828006407241e031041d400080c0e01440d245a4000320480584440113040c40c404100d0080140c00140c00d43c07282d00512003031f00f41d4805e42d04030980700b001485090140d4800d501c003903031111449081c92075003940809400c0141d4400c0480035075040011a0b6a20f50300c103070441340d07212054024041d07660810303c050014541110f180103e42e00304580204540034445008092544440c04111003a0051904210079000703408021140100d03414200e010f0602518460301e00412801049145d01f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 630458183 1250 630456933 630456973
    0x60909020a051b0a140a02041503021c020126190b210a0c0608090c03030a0f050d060e130c12021e0120010f06050d0c030f050c060d020309 61
    0x803000381c0301d0a0801c82c240c03e203820041c400204062260080a4420002520440b001c1c1050894100100560003c1d48107110132211a0407000039501110358013000142c5e80da000c01c2d951714942da03551455010345d80c80140d0311001c0304c82c40c0e1020880303011482c40c051460144c98521407a803c1e569401180348104e04030044a4032940380a4014842a046800503052092980000720084046441034003068490b10b4403a2034035001880080d0030201070003004407041040c5a1a840103d001d5031a000c00010084c0c50000118184401d000f00417940100c0e24000f944540c00508103400030305045d14005015401074000800c0840d02c0040141c00400d80540301c1000c0a41942e01814408043d0240c6004a600c0368803444254104060400e48403481e015a180b00d0a000384001c001103244506544114107407070305900301c0c6024410030583c29002c98900340640301181c1c0c1040405200c0041e5082c1181045000c00350f06030010000100c0580900b200d60081d48242d901d581550004458541c0c1c00300b00c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 630459433 1250 630458183 630458197
    0x9010c021201020702010e1c030c0503040807140102010b03010c091e122901030f0803150a0b1803150c03090a0503070506040c15020a0809041514030d05070c090504140a0c06090902 79
    0x3015a0212100001e02582ba183c91a500500c01c0b0b9080c2556044800c1c030300a01500040a50b1030300c07103500000c55030240120b01d40200304800a0041181c15840184002c2c103500c607041c4e80d1980b614003175101108201200000c0c140c0340c00c21001d0081c107800d112042100b00b001c0ca040b441d06070303240040c0c0f117800c0c1000107060b01e03130141030b60400701e405803103a080320340001d06455106511000d41d034003d90b0320171031903c0080511400650b120784540924a07002000b40036014080c1d04203000c440b000c03e2854400c994071400d800081912034550003403461070036030f8240d001481c501c40090000144040000d1492103148921003481800380c84031088003001c00008050809039028002d143c00044001d0007401306514083d0002450500c12070a0000291480d40017500320004080b84180c1410140003121000b02c46080040c07410100d40c0d04e54410400a00c500c504803a41c45022500304042001e08020700d0407001c040303480b1010340d0f06082600c1e0b0301c240300f0580404d0000c4000035100005000350f80d04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 630460683 1250 630459433 630459469
    0x3200a0f0c090903020c0306010605040b070f081e1801050a1205090c06130e06030a030210110f04030b0717100905060a0b0f0a02070816090209010c021201020702010e 73
    0x221801540c4050191400040c21101909141c8000c90082c269100d088001c5001e58002c2500c90103030401e25081c0101078004d402000b0381003000f032054101c1641128080d952016540200c041070b4205a81c843c02816502a80d8080c000c024102e0394031808040c01c2c4110b90f98128a00400c3d040340103640500c80d07a0309000101c0c0704000f40010007070180e0b115550040c40ca5003600c00e041e921200142c3c1c190320840c00500e21071180b0000340400c1c5004c185a5501c20410b50051441072200c0d200070350780306410f10307802019644540211524008482c10355204222404c140d544580d2a8500140c292030102d5a4000081600340b04505e01081481c01901480107c21641072090410780d41d1805008024003085c0c1003580043d000607000401da008185100040d2181a166921451b00030b042403456403021005034013900080202403a031880302422240d240350016611100c05c001a103a0b0486030768080d6120710f03490900c60b0100c0041d00241460762003660b5402000c40075004204003407240d0603d50304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 630461933 1250 630460683 630460693
    0x1090c09210204090b0711010608060f010506210c0a0e01181a0f3906010e09010f0603052d060f04031803050106060e030307050c010f0c0206160320 65
    0x2181524001c0500c14107400a400402c40c1c1c002d68031110410750003581c1c240d000500000080401c0305c4288036401c0a42b6411001d84000d0034210050145241e0601032113108210000721800d841401d10054032168550038005166407a04015207411070304612000d138045641101d59036415031003442d0310402280c40c09001c6080d036081469521034621800c141062a240c108030100101c10900c003e003e10020031284080505401c045002d08000c9219198035100c4081c00c50b071014a80c00304070503040d00d40d4030f0b8503444241d0b03881c1c0310703076000d007181e4000a520300386807640200602a0108a0510038030200c00c10f15158000d0405402c02412003a4841e0044d80042000c1007160010041182c0c011f1b009103004803a41c030503000c450481c100350358801c8440340c1d550b40d010450503400c25140070551008401840c02d02240b41c548a4503a20420340e068108484281d051031124003035240d00d8240c94015000c540c030380c500c20591040342c00e0380d42d034107034080f4440e000001e2b200b0724100b01c428211640000580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 630463183 1250 630461933 630461969
    0x4090c1b11010c0219050a0e041203050402040b0d120207060f02030f03090307021206010e060612130c0902071a090f030d0c030603062a020c0f06032d01090c09 70
    0x3900d607220904400d030400500322115409603030740e119864407981c240048100c0d141d217040c041003410302555001c1d16503940ca0408100100740b80c0064412a2401410003080c1d0b81c1e103910019004040b12040c0030341c0700c050400d181d81403201c1001100e0304a8065000ca405250302c0304400e48004e6131040e105c0780140c2c010071242c0a1000741101654000040f04100e904001e403d0740000e10a0070060807034503640e40980010400d004c0d01c2d4001c01c0c1c101c1e0007928024900031a40084240c1d0343c0009016251014004a10404100803181c0c24001840014070854030340c2c255140c0031515500b08014580e1a4601c8804030706c1000011071015030a180b00401945450540018003026040000c3c0c4082810340c0d030303100000800c40c0c0e0b00426070700810382042c503400500d82070080101c8a8101d022141154840c0c01d0ba080e19403030760786c8450f82500d01220210b03181d59034103450b0b05071494050a00c4a00408000d41d0021902440d603070181a00d641c41000d02042546850450711901c0c6071203582407106240d8011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 630464433 1250 630463183 630463193
    0x30e090108030a14040b0a0203070b0604060f050405060d0203100603170f0318031603120c1e030b0607020303070b100e07021902040906111305060309030703180f0b04090c1b 76
    0x400e1013080c10b110b440707081030f65601c1594443c3e0400c40d442c03805a0070004000e0100080f641001e544840e00300c85c108001800c02c1010700c0c18980d5070007102e0049a8030000301c0c41580e18900704241403a8020100d0341401014064040035050b03a120889103001c240890340111440b0380700744da480080360343c03c140c11940d910100d6100884515801c4640e0f01041181094401848040c01e529600a807502460410943c9205003205e40c1030610314104615407003450031980507000d583d200485149000329540280200041c0c02d4480d5120003507041c4400140c03541044801c0300038074411803e01105c1d40f03084d59201103501504074100c8440005801c1a130401603209892119800d559001402c00210010b5982c1d81c041183d44045103108085008074035009582c0010703012101030103050b107203e0304506000c00e119a60780a6400000c0074021000094050b28101c0e00c3d10760300920b2511104010030340d480082480e507178850300030b41d071143d400d190010113020700071804080b51103210421191015803035240d0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 630465683 1250 630464433 630464447
    0x90402152b06141c02041e050a0e0609030c0606210102070506060a050a08120f0705030313051902090f180d02030d060909031b050705060f0304030e090108030a 70
    0x2808215075851110310411030307103129580390052000e0200181440c2440b0f00e240c211a1882900c501c12020019100490030381140f06512980c0e050320085028100b0001aa81245008803109195440d10040050710007a54100b845021203030420350340c00d81c070f0301c4074469100e06c220701e6019550b51242c408200380703040441d6040d008d941e48503d0100010840d0100d5401c2e0380c0214001d4440742d0280d0300b0300481d86403100c0b4010040c5002c4400d802018900500c844e1100f550b2000640d0b40480030404091801c1d120048038000b0740d1101c16641d8903d40180c0b1030040d01029001a106403155a001e5541c08010515030b82000342c009004025569070041c0b20400c0d220010540105440c10301c2080051000c100114081c5c481c03a03030040d5803a0f00c10a846442203070b28541c485103a1900301420100030903002150820040540045c240c411702e50340c20300610303000c00c962140b60402d10018a01e1605440f420185009503c25514034903144400f00c00c01c4a0804280200170958100f0000d6240041c000e0507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 630466933 1250 630465683 630465697
    0x50601260c0409020318060c3408040608010801110306061801030e0706020a0b0a1104050910050d0303022203031409030a1a0106121514030a06050106031a09040215 72
    0x4100e151540f074188401c1a42c00541e0400100c503000b40c1800e0b001001480980c1d401548403c10a00300795500d50102d02454040400955602243c070b03003000c0c10010352413601012504110450741d190382c0c419009180c41000d20804086500c0c01d0345210f0300d0711840040700d015407801407006081030054000c00d01481c054144880c117155072880d05032540750041c40b00c0340007010f16070060120240c1c00d04004159840051078850b6040c64458825010154003040c1c03000d40304140d50421781603848960a02d01c0300390305c0d0402903101c0e040255100400d0340c990010500c1c60051003c00c200c0780c2e01e0001034010054140070080109000140d030b0211703c42d01c4000741041000050440d81400c1d0140c64402c1c0d10300d0701410340d20604641100500501d41c111110340d03000c4e6404101000900b0582e012440400c0040c001c0304404e141000c21000700344d9040207054040e580200b01045079580d61100a00145482d000141103028a4201c901451410b50b02e52481942c010f410315059130f0500851071502e80c040c1b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 630468183 1250 630466933 630466951
    0x80706021207171c063f08070606090507030b10020601031203020d0f0f0b010206090c310e120a0206010308090a08030a0206040c150509120f0307060b0405060126 71
    0x8058180304510b28a5000e41003a0703100e800040741c60804211a6107100d141003100100d94514402172612492a810310000da03031011b00030403200c41d41d413414815910481c0300142c4043d08088001c19084160340c4500d010703104a4504004199146080c860326441d05003103480035030840401040841c5000c3c5006860010340d00e4018504405540884100c44a6150800840c3da480d15841103000d02e620402d803501d4024001003103180342030214540c0d41e402c540d02e01802000e4446401e412881d00c1003041c01d50880d606601941e89590301803080080c446400355084610800c00310140c0d01c1c40810445040c2d000a9000d0002030f821600c450105500003c0e51070b03080100500001100e01040c0040c1c1028020740c0d02602d181c0c01d2600340000004040c2c2c00002d243c4807c03412980d00b068025088400800d0191240b203004081130a0080c1844a9070203543c00f0380c01700160711420403c0c664803030303202fa00c011101000386841f41c01c01143c200641c08419480d0b05000ca040c545101d2400358110341c412428 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 630469433 1250 630468183 630468187
    0x3050606041208040807060c080a0e06070204020301121205040b0904091103071e1e1715011d090d020c1e1009081009030f0c030207120c08070602120717 67
    0x6510b50101c910910b640a9901000126040c0300040381401024002c0026207001c03011038510303071a40c0a6030303c200d0a03403600348502049400401d40310740702641e89054000344115100d6a590b00e041816040981c81111f16081811440c4c91309030040c0706550a60340011013490030508408103010088c03004c40d101f50352603800f81500c200540e804100000240012101411103401c000c01c55010408543c6c1040020101d02d1020380404200791400350300f1a024000540d4000c11400303545420300008071030480e09580444004989041000260104840218800c3c0c58903a1440c1030326444004042410005030001d018000552404e02c0c0131458201e05801515102c01d01240000c80a8400e0300001c00801c0e1004000c0094078002c0c00901019140c40c80248108045641d00600d03002404018609104400c0c4e07114003810720030410440034003a41e02c1a2400102541008603035055144140d403401d1140100c049901071012610010390b41c0500131540c14001156942c041103000d6540c074511084003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 630470683 1250 630469433 630469439
    0xf0a0c0c08030a0b01080c09010c03032403030203030615090a060c020111010e010b0114070317150418050105010807030c120305160f020405060d020f061e030408090f0d02030303070305060604 84
    0x44070000c50041e0b08000d800030305036210000160085600404000700342d03030280300c6101281d0f0011112035401e64549000a408120301060518994564203030385015203021002008140d00000190b00603003040303070384a00c4481c405091444c00d1084001060b080580001d007002660f0280c41d240d0006407050400c03001c24000c0540c0c190850328a060036000f40d07034503000384503503a580084850f400c001503a00e02c2894581c00b514007078120300e13292403031071a0011240c0000350104c2802070080e05005004005020a02d4104031080008081e01010f81d819480c00000244c240b400140020840b540303c24007180c0725182110300103680c01205800c0d000c0c400300700a0141803980200e02500c0191145990030102c20a0340103110880700001c06050181703030101d1110001d60b4031490021420344088901560300d08c4050a180c1d0b40b10b22564002c40003507404000c0c402001341d000043c2c203800c1c0303058a000c00344103540b400b00046805142c1c0003035010740041000c100142c0c031a400035940700c6405028640340680d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 630471933 1250 630470683 630470693
    0x504051c02070e0601050406081b0903010e011a0f150a020a14030a080f01181e0908040801050604021206280b041701060f180603081b060f0f0a0c0c 65
    0xc0101014010307006140288480c003100a0b041350410310a20b412824a030601c0c10141c40c4032000342500b407262004045100d1450315400403100c0000e0f001d0000e07c14207890b220880c3c0030b494a034900b05460050410725400a00782941440300502000304141d5503100c000842e1442640004080710460041c404500003040302100c400100001c604011039450080f03d10013450000003504245042215900400407800c0c1424010440c1c4074603030000403a0b121000c0140c1c1c82c400d10740e01c0c09810b1410405224140001d02018008071102500203020701ea5440c1e04100882c8107251000d000c90488901082c1d1a0800710301c030480b040b82d10304030028191a070072800e14540e170059100c0318811b0b10009060219203401c02c1740d92803a50300c1c0070003417100710304086050701d10b004203002e6105a1990100b0070f114042c100d405c03803c0115001b201e02940c031000d0711105641e031004546040810711520300420076202a07901640e100d00c00c50003410416440d8002c807075000d080c0d80000c0c1c0040140300113100300824 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 630473183 1250 630471933 630471973
    0x1305150d0603030c120e0f060c03190305180601180b03010207061e060603200a0909050406020a030507020a2406050301020c0c03010507110304031707140604020118030213050405 78
    0x2d80a03444411442400d407400c0d200e80751304a8050801c00c10503002c21011a21052920380703801074211a41503c8078004000d50385580901203040012004101180492a42540c8082c1c090003000034400040e00341001c01994444080c8211800c0d424920284294034038175a1045089040040000d403034a80d55494602c183c0e0301800c6444808685140641c40030002d521548004220030709041c0300503603582d24802005072500c101c115400e040028102c003182d20030040000079002e4540104864140360400744020b41000520a02003460140810307a100c0c00001c0f4000c4c119408003442034502e007491511081600084069010f00b034683c0d1000c6981d603020300140c2689004003008000001d80d682c00c241c06d442d805000541804802e082d210740820f130200498007525000f4600c4004001c02d5548107400d40304180c070181958101c80501d180d148008165640a00c0c000d980c0c0c1040e88403911124541020203100c001d510600c0f843d078103466902d41e03400059102e4007400c255800308003001461a250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 630474433 1250 630473183 630473189
    0x108030a03090c05030a0c050112090b0103020607030509030a141203090c240d0e060c09030d08041e0803100506090a0e040f08070b041403030717130507291305150d06 73
    0x2a8100902340f0443d46e00008803200048030070400d00c00007840c1c0d160302c5102c01041c000039014000c001000d00626000e001202c0305000d001e0200d4000800c44d0404841d00c0203e032404004d80e02501c5910846011504241c0e070141080c400500800214001005610101151924044101360b08070202c01103e00780035241a19402c030000c141160300003880c90070904014031048940c28184540c0740d043c1c0300010f0988109082d03007454111030700e07a410004542124030030b2481c1520a0404401e0400c5565030145004a00a06d41c4001d02a110070410030940614031401d0f802c00014801013000502c50518641c0040c01a89400c250f4403040d240d0311003980c40250251800740f600da00b80030030007102510076440744100300081d50071400c002000500007110780e681054500501c20202d900704501800c074036006036110048072510b45d5200806418500c800301c410402c15030042420304445440b07030440344009604c01c00e4621030703400d01e410896008002c2c881e088042c07000340045111120203108600103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 630475683 1250 630474433 630474443
    0x1020a0201060807170c3f19050616200703031403100909020f190603060605090d060e07081506040501060e0a060818031b150108030a03090c05030a 65
    0x714104429070b0720700411340d0701c410f891074140f61044c03000000c0032a03218904e101c215400059220840d80c2403000c01c110b08085e0600000e41c81c1e900c0e01c414000d00780c0d031810840d10390540d0507031824403241d000c2c4201c440a000e4107035000500000c13030000c500c40340d007041c403807003030905904802080307144a003144082d002c000019403040006000345a006442e84c030191038203030040c600c3c6182180c200d106141240c41544540d54841082ca0704655400305d00540143c406445044a85025101703c00e50a004e0b11400c40803071718285000c540303035100e04112200c0300300c09020703450900e84230b40d1400010b09041605001a0050100c04100840e003844101c24144004107088120708100c005c020407110103900070402e02440c0591754410b5141e90101c0022600c89003005000c903030f2001140c0c120343d0f4203001251514080007940030340060405114030900000c140440300701306181c1d650101084001e01036010581d106000030040540b01360085d5504520440c03000c12025550000301c0e00c1c00c41e40c2403080310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 630476933 1250 630475683 630475691
    0xf12090e0910050c0f0f09180703050609075403030e0a151d060705010f05010e0c04141503070809160f05010c0c03080403150b0306041e1401020a0201 66
    0x651a680241500020007060351803600d26107543c81754041c41040ca070581d80ba1804078103a840303503840c00500f10b401c41c2c2d183c10503600b1f450400c000034010700c012920584501c46840124008a1141844c0500350041042080181070706001e201c009000410120000e86c5c3e4000c040030f00100d0403205490360527031861605000504524016040400180604d0b024191200003040a074201c1c2d010042200041d08040307281405042c403c110840400060719084880000c194080003015403108054000440b01000181d13281d501003e01c12409407010b0b4041c40702407006200c2d00585a841c00e0140000130b1034009082e4443c8601141504100c03048800308034141c0811904940a020344110801000d900300c0a19052210102e003619890107054108840c0941100411990729100c2e03001d160083d8100e51100c1c0e81b841c00a481d06800d5103110107080c148a40000582400030f10940100c0c1e2005d0501c540c4c03200c064041d44c4102074528181e5120704000008001c00d0800e00c0200078413203556001103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 630478183 1250 630476933 630476953
    0x90406020f0c100c0e0d03050309150108070905091605150913090302061605040603020d060b0c011b0c02030c010c08070204060f080c0919090807080a1706030a0f12090e09 75
    0x400300c0301d84c11524803d1200c0c6852100041d51112406550150725080c92034503070703d510078840c0c0342c01c09038250203035034568000010441180c00190101120f1a50718140f01d159901d104140e2609030010b080c240826540703205200915101010380800c1c0c449999043c20800804006500382c141c1c0030341c0c00010341c0d82e6400303141416414414642c1c0030300f20000700c6c41301d201e48020081440c465486614209607010070300040302846500460001c007542050152035840300003540d802060800380007007407450244550f5000034000c000784040d10340c004001c0c2400d20201801903138030312000b0b03504580030b15080003c600103030303103621a407000f8010005680308080d043c040d15602e00422001000e102d40203000070400032500c0e5000d810008480404082100c200b9032501a18030302031809c00808121010480d284d4043d440948521049120003109000e921b404091544440500f040039001e281d40082c1c68010500b0b400082a00846500d40300380600d0fa00c04188560303101c01c1ea080d2002e82c106440003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 630479433 1250 630478183 630478213
    0x120f161a060a1502100507090f0b0a02010c080106094505090309130b0a230a17030304172511030c010906141b06060307170309090406020f0c 62
    0x100c00034010f443e003072065010381c00c3c0d800b0359554800308680348541d441d000080c42e028460300c0030800500700075601510301d98607461004665003040e00d135000158a0890b81084151094604904944060b201e8044060501d243c0b5200701501221905007003031f043c0c020800c000c1c906000c00b520b0542c1c642000c12806c104015900c180d0b04058085809680103000b4810240d0310001e80305401c00719401d00081000c21a80842e90389029548000504000484150348100e01340610042d034110441c1e80520081d160300354144c140d05c1c0351009041c154810f0002900260707601b14111140341103240840d060415118484500c41c001c0c140b0034403543d009000038001c0048101e00e04881e814201d0141440c03603590740009140c41410320070081040200350004125005442c11909406243e50a164020003008441a40c800382911407030300a1192450028181e4500401e0561010460020310301c0d0200800c108822544094416940e0b16401c0104411410742d1200a290b00d8940e1009465450700311019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 630480683 1250 630479433 630479449
    0x1061d13020901080f0705180a420c0b060301091e05071a12130501050f090d0305010b041806150207030b0f01210510050907051002120f161a06 63
    0x4040001792400042c0064590440c0590b00f074001420318030b1002c000001c00140949140b94000ca01111250081840425086845c01400468040d841c410702c0200201004101051030740000011090081d80740000d03012040da941040c002000405c5d00c013115150b107004800050344041c095610001c3d41c0382006401c4c05804002d284190100410340c0003201d0356105885586410001080c01d24009443e4050300c40c14501d034146c00c04020015850300c40201d4640080030f9a90100303078071600d0049460340384a4022903059401e00803034907081c2031030201d4003006c01c0744142d1401d02d8035490303003000f0810391006120200806510307801814898034501301003903200d02c040d110080b0a80c9250062004403c0c0465030860720070012105190b203c1c403410b281d4140309802e1014002507049c2407d1280740880007511600f61502203c0c265408059081c0980e650a480082480084824000340100f03524071310160608000041c01c1c1050103803280e581854824200030f51078080d40182060004500b0a00c0c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 630481933 1250 630480683 630480691
    0x13020307180b0a032708210709091517211e0f070b1501030f0c0c11040e0d030f060e010e04021e10020c1c0b01061d1302090108 56
    0x1074a0092420105180003038070843d140d41c028140c407800c90582c40010700b0300d202682d02c100203144c0e004c1c8495241000c1d6550041c207121454018565100550200d080c0b0000d01440c600d860b0129150329001c185006404034425611480c15041c0d03000840507405811214018003075400307420300420351202c03a2002e00103101e07514043c03002480480b070340e030080b0203030854404000c00e035454032755020009640e0340d88a01200105545454000e00201510060510040f04400d072414490304920000c0c036011282c5210111000540c403401d10000310b08506524a210030010700041140d800140010f441d1500c030855000c0041d03610508901840500e01c9250003502d802c1c108003c2d0382d45040342060203d10050310180c1f041000e58031200302c40018044440084a024001904208484070041d4440d140a8001d41c014a01c255006912040c5e103401200350b04d0340703c44d8460160f428000110b43c0c0344c2d5034038038501c0a1111a4880c05490b0b81c1c3c0c40700c180f450705004202580d9810305100040c00c40c00c02174 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 630483183 1250 630481933 630481967
    0x609150708011806030804060201020c06010506161e0b07081501050310091a1504030309050f010507121205010b0a12140c0a1205010b03010e010f0b0a0c050a0213020307 74
    0x20140002158050006030440360080325000c50809501c0700100209040d51004145400000b40014441d8064004d0607d90130100d0503111940c4c1e99009200d030622800681000e421a8081d50360001000c0d00c00e0304076034801c4155003440100f92a03403000701d003500c1038985001107517100c1c0801445403620415850010801c0c80c140d42981030500740d8001406441c05149038003034513203880701a5210701403505442010010180c50046204000b00d800650060100342c000600038031f808143c4e8108009041d02a007010380d1040d14142880c0c03501d0302800103035031000c402c01861803c01c444481450007494040c0c980e21100a5031640321440140c4440f100e07410020b1268182219001010020103242d036004000288640c3d46422180c000c65036000450855170025290038008503080c010b1402441c1a1001032445403400e980b10103c0c03020480540c810101c2d10401044880c49080c498140c851000e03120380300722140045550b00080f000c0241800140040e50b01200300600e240d4811503009900c0c1000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 630484433 1250 630483183 630483223
    0x7080f030c070c090c1706060c1204050f031606051606050f0703052508060301090c0801020304110315010603020d0612030c0203071d0103021207120503070c0504050f130302030f0c0609 81
    0x144006d0f0001800d20100894500d04200088007a214002100ea01c40341582c15500070103445002811550858080e40d400f5090036070180e10742c0d05001842e030320560103d524036851103280450480c6e0a511401142c1d44203032104054400160481c00342c2400303000c10540c214401c0c5020000101143e800a00340400d19103040750040c1908040a07038080414601c4c54510381c1030f078980000c0b9015003102200280319203117081000883e02010b50245002c7d40c45107400142007069082015618002481c0702c07001c00c960800100203150207507000b0150603058403400300b4680e955460420342c0d0803185400340c002c11022032100c030461800744000405001c0d003a1141d44003080c203201c20707005240140130080c0905c3c0700c8103002c0251481081030000030510a0f50702c010030720041c5403942c0c8a4100381e41c02c5482c0f69600602194518150243c0da206440400c190f132556038880c02e001c105608035117016025400100710924000680400502210718104020440ca05201603403030f01d81701d01c01e08006600220 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 630485683 1250 630484433 630484451
    0x203160903020d0f0221160807320604031218080a063303120f120c17010605040f05040e0d0c050c09010e1e04020f010507080f030c070c09 61
    0x60403c8503800d150454200c210500c124800303d009142010314002c200409840c13070384401313000000c188003aa400d100442000540e5580419a034981500640540c3c03035100c1076010b010b180002810003020110b41d510003920000002082160303019400c165a080142103244038025002190403040703a456040c00104d440c0b410b59180d4680004c9a0010140b6495104c1440102e140951240024180712103105d00c0c000c281b41011f2800c5102c1c403044610301080c4248401a44c020141d0001c442010707124075031001020101800146900360300101480a129145144070a464200e1400307803105803642a540c43c10008031003a80100780e0701c07030751042e401c2407421402000f0201d107807600c2075428180381d04000700a10342142001c0380392401c10740001c164800041d8038240c421701103000e08845074407240d803c1082c40d40e0184281045501039009003c10b400280c2a5116000038402c1034007a400544c00c0450341e51441030254002ea03100c241d100f801050310428084070b10500c600810f0888800c0000041d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 630486933 1250 630485683 630485689
    0x10c0506071215060e12010506010c03080712050a0506040b0307120206091302030f070905100f21240b031509041707060906050106020a0b0a020d061701020316090302 73
    0x210040080c01048950401c00c42c0b407000039004184030300000c0d9890107126442e010300401241340580742c0e0b40309442d8104001c409040600c03c9502400041c1d40d0311586134102d8800341e42d0100b018041404001e09480c0180c4000c816100f990b0282000800c0403a0390b042031020481961071070045a0700c40d40002c00704002d20003151004c5e40381240c0c1525000d07182c644000009900c03c4449400700e00c0071340004100b0038144807602c0d00c40d20600003078840c0050207480c0e03c140400400c100d8107900104040d580c1e40301245000b10084210341e81c8140c81403c42c0000500e003070007a1181900d0801162101889110700460010a517a02804035900c00031f040d03107032030011002e40d100c482e18200e005601d003101003414800c1ca03100004004001c1030304107580b00c581c0c0c9882d400911a07400240c98103031500001151803031010039503c0d14207410515100441d1140074050000f5480707004000803840e40c2d82c400154030844d800b981000d8041c11400103840303142c64600702d00d014030905190720401c0003280060006035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 630488183 1250 630486933 630486943
    0xc051009090e0f070305010c08240d060b03010c1107171c02031326060108030d02030603150c03070306141503070311030108031b0a020a031b270b010c05 67
    0x40781d440d000304412159094607803c000046107102c500b8051810003205011054200840a001070795984000e543c030b5030b00b80e154a040c000c4403945100c00c000044400e0f46401d42840414be801000000340b1610403000003400c4899410f2544081481044090b40e400740a100b140014440c00b0350901d44d082d08481c01c03584582c8500702042d4203542120700c100d0442c0c0b0800540d20300125180540c14141e848100700450001c2c84803482c000d03804100313080681041d000c58000d0480c0d503080000d41c240011100548046e40008254075014400d405914808698442906008400c4402c02907a281000340c001020b80b160740d0092031003030144815601c00c07a10380e041400c102c4082044203640303070b03181e01400b24050b106901001243d10404070010400d440013100803c03410400080302c3c51000c000344010390b140c0c0c04d40315010b035010111013000c10100c1d020202e4603104030f42d10084000c415489503901c89000c1104107003400b201c9554040a121440d072881186c10780300b024205541121580c1e600d095480c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 630489433 1250 630488183 630488189
    0x80c130605010906120603120903110a062c1e0a09051306050a0b031c030b0906090f04030c05061006090819080a02030906041206150308090607030e0d0308040c051009 73
    0x4240c0d85c2c00000000c2c9240c1c0518003843e4000b10032004200c0042c00109000d445000035102000104820070892800349443c0080352803076161b641b0444080a1142a29646c01d48100000300c01607503801010b0366942e11403003403811074088002c4280c40d81c3c400e1042d2800d00d90004116280707054144940c1e4492901483d00c582d80c4003001103a00e55400a007400500402d143c070a4051081800405108035084200c506d1a042581c04100d110f50001c10040ea50b170064990030f800c2034419010075641d0803441c2600b54000d000f400e140e034142c1403582e2180c2c6004021112050b0441d0b0651040c4855503011011f10001c1a0110060904201d80d18100194107259900180303c08000500020014004c1c4251045c1c201c004254a03111940c49522300c52100c44000129641c1d4940030440918101000000045c1c0b82c0100780c890034401010140055030b4070400003a02403100c00f40c141580c9541d0070450301c410520940c2d40e82c90604041c034140ca11461507400c51441880a0403076075401c0c0b5445081c070340072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 630490683 1250 630489433 630489437
    0x30203120403050412030207031b0f050f150304060f05010608040209130c0807031b0608100b07020d2307050f1003150306050708180316020d060b040204080c130605010906 75
    0x20350319545400e0b01c007840380c0e40c004404281142d00f840c01341600803070b4040c1140c1c000e035840a0b0046000060558610160164011010503680f040c0107900386016008070f860009005554078601d8943c50f8202c0f50021201110f44607201c0428804103a290700585004013070900300500c1ea401c2607800240060b00c01843d800303901c10b00c4202c60040c891005200303802860080b05990f0480e490f820115654080c41c56003600c4241c0303080c40040c41501c40c651003440b819101c2032040180b41441e010240e951301c81c010599002d034003000003401080d40040014280c0e4000c142c0c081940021148403828002a0741c0594820350703003c804c14045882e860102c1e4118101450002117442411a16070851242600301400007407520302000165900320071264040c2c0e4a088005005109084015a0302d10803034041030b141c01c0a9034200001810059181c9445a1081c20007003000042400031030102d1300a58021101580035600075480da05081d848100030721540c107403c0c040d203410300b0300280248805214480c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 630491933 1250 630490683 630490717
    0xb01030504110108250f031506021c03021e0c010e0c0a170a050d02010b150a02031b0f1b040c090515030402031c02062e05040b040612080703110a030203 67
    0x180511141001805c80316a00c41700b00c21244015600a100a440100d1040030a28008204d4913010340b01d10700404440d0140d004241400c0e585101240300c4420314414800c0c19000d001c41c1590001401003107107241203490b100c81e185d100d402a0f190035942e00d2054090076402c500245240c0781c031000340400035200441c4110300d003a0f11802d29030380350911551024040707004400100741071075810740190b80601411516080340c00030401400c5c400f031007030001c5070015038010080004404d58001000c0c560002c1c0d441560710a440c000d88844c18486a40e603001e402c41d80c4607025001c41d02e014030813540c1569291916000190406011410200e04070380c009201c0c0701c012002030219603041010302203403402c10b0702008840c128520b01a50b0b44e0010303101e0406814120345c2c04000101d100f11a00c20f25206207500d42244d506d03000500009000b240c9045401030740b02c11021420502c5842c500442c06d1050000c2541c40030305040040c05d442030141040099000300c0c1e09040440d6000007a1a00b08410040882c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 630493183 1250 630491933 630491941
    0x60905090a120c1a0f0708070203030423031209010501080a020a0e090703021f0306120203150403020c040207050304170708030a081f0e06030d02060603071715011203030b01030504110108 82
    0x9120b034075030503000500d410384001c1084c0c007038150015464015140d005107160305490740441564a00012940040140e105200041c0840e43d191aa141949403e006816800d12940c4c10b50782540e00c10048128595090300a2101401c1c0912885005120802c040c00007032240360300041d1039514510885404c0a103481c0880e580b52024807484c0c005507402030040307410050b4203581c2841c001e45003038a1808070b45440300006a5085820751200c42c19401006002c00000b200d401d120511405482682103105a444d280100c0d105c030310080c41142e008400a5407a00d2034a01d00c40c030890200c940003465070308004c404001159000058034818061410138014907510708075001811140715080b01402042044002070b45151900c6040c0220700035030a891071904114000e13603480101b9107030310390954090001000810012031919407100540350a641d40c0c4442d040c09012810020f81041c40f40000480c0c03a0b0007016014450030805040a0906015626103921400c046a040f81c18090510540780005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 630494433 1250 630493183 630493187
    0x13503040e07170601020a020d06020721090302041808033111011d030d0e130606020f0708010501230105070c060230030a020c0a0507030312060905090a12 68
    0xe2405400309240c0c016051415070401810394408100c40c8402c41190004104554400b094401110b9000342114140d201c4030783c1d07100300945c0981c0c1c00f61144145800d0004080010b02096400702c80726030341e000400c50450040008448040c00300c49803007c14102c403240001c210605690344014425400740b100a080c140c550380044c0f12140602d80b80b1004e01000c0b0800c0f0408001314007414003a030f502d000100c034003903000301500403888500307505501c000d00200b03580d44a4424220361050142034601c110611041c0042a00c409820000158005290000010741d080100b00c00074407451000f8061945000b113184031540b801e220000358500fa07031002c004030343d0180b01140c6000703034031a500344042951214000e4840350412840fa201d081203204d803100d030840c01031410b03140411005500d1b28541320035540c1c1009501441144080d409000403001c042902808840011030094071004003c20740c81c002c490888020b6007003002c00500c0c02c018880c0341a03000030300e0480c1039803040a406840201e4481 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 630495683 1250 630494433 630494437
    0x20103020a111204090605100905101b05010e0d08070c02010305060d0b09060a0b0301200901110708070612020a0c110307090c0c0516210f080f03070206013503 70
    0x2090b42403080d1103000c5078498070380d0000d00448080c100104021522503042040090846908400140301003005020501d0103081100b06800c3c141042400a84003001140390380c05c2a040c1030356940d654003030703500280005218080d41a03106240c02d010070b19000300013900d04421008041d040560752000100300c0e8817201e041c008181e8009150200701e1034810149035031200120b9890190034200000d03069642014021007030403643c0042e62007045001000e84c0b00d4a034101d10030090400031010446c58014009200200181c0081405440c001c1e060a40241248500d0821401602d10400c030510b04103038841110200705911600c0e0400c5400ca45002a103811126005001140d00e84540c072251541c1141d071001003184118180c5503c030122100e200e02d102c20900c103404181c02c81030310708040134009800c40008188200041150701482d62600d41a0f0f8200300205030501c00000207204035203404105450047c00d20203010401801480d05203c005181e060b1941c0c0860404e88200303404075000d0003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 630496933 1250 630495683 630495707
    0x1090213050d051b0105040510030b03071e030b15090c221211060f0a08130803040605040204050f152106151e01020613060930020613020103020a 64
    0x20b4a100384140707042403030f21001c6900d20a03004400502e250080ca500840a0b0f800315a001002d050115003000340079000360000210244d894003e05401103400c1420501d08042c0c003c085000c0c180e11411032811104138003014216202000c8400c0d0103960f00d07a00d10003030b19440682e00d01440c0d143c140402c03490310b00600c003400f0301c3d1001034401804110f80032501c00c1c4001c41030040106080c4000c0e0041846824460b8140320000b4075420011200218050584260030182d4224908020241d41d2120381d95504141d038200e45041d1540306101c00d52606014035900500910100c0c41d0500f0030700048003501450640301070040b44100d9000100f5260904e07105020180f80040d0307040e914106101c0384400039510a0b852044184812402c1c0150341420094840314040c1c00501041c0c980d107030020081d044006044071666146c3e400c40001503068116247d581c58801c0c910b8000f202421401720707551300e292280404641c003144c20410f03030006d0503d1200803181c0a00300145d480e0b41505040750180c418007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 630498183 1250 630496933 630496939
    0x708012621270114090a210b010e061f0f0f090302030105010806161b1b03080d0516020d08180a211d010c0210030e012c01060e0109021305 61
    0x9080b5402ca503202400c44030038100c00f43c0c1c552840c400442000f03840c44c0155440182c10001c54075007804854114291043e4249807075013171661008550740c0320160102c0034ac00100b008481d82c070502c905810500c0c2083c4c0a900c803508041400c190304180144a48403030400102045008400800700b14064000d000c0910380140081c0540e42c0c5580046580302c074180c07141c99803002c2d4a400c026083e485070030300c0013005903690341d4403a0303052482d00c40140741703192a18444c031711005400b40000010f00d071400600c4540c100040101d0645000b10083d1035401e0300c03902a50a54204003003910482d9401000c035075100d84400c519092401008030001d03c1c0c000702c035400400320b0720402c00354150084044c401c2810b031700302540e0ba8541c0c0401d49168080c60300034144440d000c0344108a46c00014a041e6040c0341c1c1081107890009100780c20084860700356152000b80410803155092603459642000303040c0300c80e14241c0b10003807012030714200744000301c0001481401a02a03000c40e0080b041b111146040000f04401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 630499433 1250 630498183 630498217
    0x60b16150b030d020c03060a1134030f0906231b1203150a0302010c1103010b03120d050901020901090b1b030a0302040513050108060c070203070e0708012621 69
    0x28030b001030364603292200c0e4031b40300348291400078440031014003d41820030303201d03030000b400c091064000c0307a001545020041240c50b902c80258611b213680754541d8089078081e50f10b262094008907805089a0001e8209801300114514555440280d00c10315420120010604a0365195a100a02c00a10800106042d5030098000c90504660f8180141d030203044805801000c40d0110760401a1b0702c54036100080c00f040b010b00c20710011400c501e82d00740668030040d00208840245400090402020f10134400c1d240c2e6010402009000940c820154003000001c003c502c0c2c2844c410011b0a80c003020310910710005000628081d4001483e0041c21040c107140044a480d09003120300038010b50803134060b05016203c3d66203840c00b0b5048500502e4102c4180ea0080c103150f8a855201c0c006c3ca50240b0303003c4e60107210308080003900d00030000700c180c80369017959101c25465050590307812014104211021035005075a5010946200209651000014514040c014011103034102045402000c110130614482 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 630500683 1250 630499433 630499453
    0x60114091e060f040611010c02150a02090d210908150403020703050709051608060d02240301080f010b01143723120c09120d020f01060b16150b03 64
    0xf48010b40180d842e20384034003d0700b642c0108036078201c0d0324500c0d0410050f8400240200019800101590045110380e0054686005540403134801d08c81104100c0d0044106410070300700d02003203801e1101011051608030f44107858080680d5864180200301140681c4078030101d8201402000703500c00642c3d004042d00c40b200e6075030017440c00130401203410204090751245c1003a1418810b0528a11412000b00240044442c64080c022101e10043d0070840081d10b03a0f4600940d00c540340051f40c002c1510034000c002c41d08140b44103c2c00e64190031181418804645034a4012200f440259a042216207102c000b0316044004207611005010070301c913818400c1e0702141e20341158081c6640002c02d07801c00380080d40180510410780380d0f01c100c0300c141a240701d40c44007250244402c00020100184001c1c000c1304412401d8803980d0800350812920030140e80865603a4908080a01400000f031482c0d2500742c1c18441d094900c40d00381070343c1b284001d000d661a048006080c040503480061a01c1028003100c213801c2c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 630501933 1250 630500683 630500707
    0xc030a0507180e06070e04062706051c030305060105120718080c030307060b1801120c06030c08040b0604090c06021e011b1d1f08060114091e06 63
    0x20341e60041201000702d10511804840d40c41c02100078412000f002070060341d6480340c080310034901480703c0c580d0140d11400d00013440e1714580c0108002110752504030942c1203004044404941d800e80c0898007509910f00c0c804001c03280111768080580d00750070045810f80da4000102c07554410003c52070b00d408048000c2c40303c6942e1060036103440b401c030803000b02c18050301da550950b41c0719800406240d040d07100304003280000d0440e80003641c002030064000b2501c000780380000f00102c40260840301d1015100c0c0882c405128035500c4640052a950400704910401507400900511000700081c1ca81802c1d03a0200c1c05949903940212104c513041614010b0307054450800948441030134845240001800c0c1d075aa604c40d00620072541c40c1c8400120300c0c41c00c041003880690f211440095002c01d442c3c0000702160507910303400ca1408144006e4001000346501580c009400c0d404094041d90401810751030040030b9600f124200c459280342112041401901103103140e018442101c0c0c0316810036070101d004d002000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 630503183 1250 630501933 630501943
    0x20301030c060f020c091816082103100b07050c041d0705010305010b07032d05070303050f19020f0d1a032118060f0a0207051c050703140c030a05 64
    0x7070742c29510f41a40d9207030018200c0c1d450004290f5107078007650600c007007410341c10031341709200034102c210f810399525000d1090380c1c0c048203186030f1000109030009000f0705907900002c0c40004000500c171891302e0640c1442001c1a4060219005580c400301002500809001040041d0301c0407110040c0309104c105029003003a0814008032940518610030240c0c0810103600a02486050b900c3ea05451303130900708903072030440d0810044a204130482d0034445442d0011a40c00c583c1036020100f82c0c035142c0e80c49290785001822290020244a240802c682c140500c184010b20038501d000207201025859a160307410944140c03150092500d042440c007071a011700000e51507840415003008800380c50055841800490145509040f00508904104101c1c0340000820000d0181c40e4805080c0904051300410504965444031200001603440a04104214944502024181d401c0641c3c2c1c0744600401e695080c0c0d844180b400000c013034400511082c600c004042011090840c2d009046407a401d03102c0c2405500d032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 630504433 1250 630503183 630503189
    0xa02010b0a08010e03030c07060621051209060a030f060b13150206040b0f04050a0f08030a06060504080c1309061401030302100203100e0907150f1209020a031e06020301030c 76
    0x70303090301600003228071042c0300b40300c2c0391144e03180514135550301c0e20354000b020b500149007155645c1e550800800d00900c5214103200d02e10805410300e00402090030201e1a0020345a24070705201d00401c900c200d00c1d02c49c5000d503030401c00207050119220010030300301e202a00840d0000d108540c004a070b0000607000110070001120240240203a1410412a0481c3c88820484003e40790b01007807004629404404942654040c1c003500c00c0c3d0381c4030300182e03aa5001000b80701d031080c0d400c06000300c02e01ca52081d451003600700070507242c101145414549106242c641084a280070712071910100741c082402ca80344c0056000c294000b8042003039850b60245a41d14036020f00050780144115000403002c001c042c8222405030905100c041d10b400d240001c031031120200201060218010580300184a041d0640d203003840c401c00ea00d8421205020f04001401ca02510407001c03949808c1422080150f20b41624609c1500c0d00020030102900d40d280e4110043c8140c2440200407604c000000401c0c04003080501050b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 630505683 1250 630504433 630504439
    0xd120c050a1e110d0f0b0411040504080a120b01080712060e04080c0f0c060415030207150606170c0403030305180d03050a0614180702120c0d020d020a030f05030411060a02010b 77
    0xa400180c00503c2039490800c1801851074101900f2a008600c0300006d065009100c0c00c030159483d10f4500104050307900c2a1f030b003100c0355000031810311305403030304000e0100c041c5240d400304208030200c500c0000d1210341c000d0440c109100820041c1e00d101d02d00354100300050700503a0680e0301d83e0300741491b1404403944075000d003040341c1c01001144450400003103502880070302c009100504050074544050007200ca50300320704061680c00c011100004500303201d80b03030084455003070024282c3d20744030001d0048650080f900e588443d0300700410150200718416182500d81610300014135954668100c403401600e81160b04c8540b00e42c84c0d4011503148c0c50741181d4481c0d100b03c04107014844c0d807140b00c0c000e508005907000345d1201c103034244120099810b003002507100405104a50a84590042c1400b050744207840c0840981c0040840d04201d0740c04000207194404688000e14403129035483c0100240764200215080000c00000b00c0e00703000c8100f5000c12a0200100026600c00c2618406402001d0400c00580 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 630506933 1250 630505683 630505703
    0x303043b0f010302060901270302120c210f070909060f05070c02010c03021f0603060c02060705180120061014100e15270d120c050a1e 59
    0x150212540346440d000ea01098003021181c0d083d50300300840e80c1c1101000320f041090754480d15450305280300c00321381c540702511401d0048508500502039001c40c0b0083e880e0055014544044c426103030300392000800d03510b425520340311aa08445d00c070304022400141c00640d1141c03040114a01d9800d5100300000e5104a0007001030910340c42c0e51740203641c0216162404a00907548480140d40500000340c500c0d8440e1041e01c603589041d081044200c90408218021540e036a281401003040611604000040344d00040c20305280900004000c0c0c8184071080114000e54840d41d0007603405902c1e40158600c10142d0b40e4903840501032125034030700701201d80c120b0756a0300510010315000c454004400c40c00300a030035034041d4541d2a4042c2d07100d4081c8510527070410400310306102009690005480c1c80c2c040404610081142200e00c2068001c4026843e486000d0810041e00001c808c0e0f079800b032813007140341880400203c89007030541c100220b0640c090705141f200700326002c041840500120541c0c2c03003000881 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 630508183 1250 630506933 630507029
    0x100e06130306061e0e13150b030106060c05010509030909061005070f03050a020d182102120303041502040803071202010f0f0507200d050705240106030b06120105040b030304 76
    0x505c51806660400d901100d4003086c4d80424402080142d0003074030503a01003a9000020080b0342101d03550784c41000001c2c040f0700f154081120a001d060f4001d18190011800c0011440010f014100082c0a0a1280c3c0d074000c2d8086e44180608240c80c51541c10241920104034030f8200a011940400700c1c1c18014020508101d5415018100782c482c84005110f0042019080c40c0e24280b00401c04203804612002c55118000142d684039242011a5030b40c801035512410289003140c06858080c1c0c1348082980140000d2020840000c01c1d5440341d90400d114030120320301c0c600203a0060203440c2400303016a050442100e05109150040344c01042240d40d051800040680003c40c034030a1a50a540b45401c07070740d00000154400d2010b40300540c028030690703142146062a100074180400d074000e8150190740d0040042c5a00340c491009210070a5803060702e444030644401d070350b01c201401107511032943c0c0c82c49401591010800d50700686419004059a0070030040018401c2000f002d068822840c0e0b40c1c40c070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 630509433 1250 630508183 630508199
    0x90a0203130213110c0f12030114010305060d0b10051c020d0f052401150e060910090b040b120907050913050a06020a05070c05100e06130306061e 64
    0x4a201e00c1c1c1c01c1e2075941c8140308690801a0001400c05034880403a15418581252800070008000f00b091042c001d01c0031028201c495070403c000c94440601030349050004000c11040c40144544d0f881003441e00044c250b85070f60010b11154240342015042e142e411003086a0b02d130a00f4070002c1921b8085038078010301455214654030b10070300e56800035001400a003440c0700041c1c20180a50505220f10b0a80307050541030b0950a00b2600d00080d95070b01d41000c000108015101e0418000036a2090300c0c15010501d190350203e02c1a21400d080e640c0112180346001c402c45100701480e034040c00c11911b500307035a541c0e03c14030303111150070a01c030806400c41d5100c0410760368640003d0340401c44101030b1002c0c5288da20603040110740310340d140041d6540d02410ba900030005882c0c2c4000c041e44420391325070903290344444c144003150b01015004207015502c544c01400241d0740184850001d010106c81c01c03030b43c8034410071260a203070029501c014402c80c200080405c0424904420100011070350b5580c50300c040d80c49c072034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 630510683 1250 630509433 630509437
    0x6040303020f040b0d1d0313032306070906080906010302150a120204140918060f040305160c06021c120c12050a0c140702060406030507021908091018050d14100b090a02 74
    0x6246923411200c442003000480307420412039950050302c0919035a0014141e05800e1000444443c0006441308200740001c070b81000d04582c212500038010300c02c83d030440d404903c0a0a0300815500c040c607001c6020702c1828496005061010914a03081d51510303901c10b40c181601c10b15148607882004414000b43c1270050f049000c41c80d05800d00014031087d29200c62030780c181c440191041d0200807040002212440710090504801c5109500c1000c50743c0c5050300090520758884181104580000460080c1c40d51002c0e8403600200381c0040000c00b1444003000307490b031000b82e1603c01607a0b401d00c010030102e1062903004001485064803101040c0001a001c401039105140000b0741c040c03400e00050041038480d61001c2c0e44450980120768414194030504504100c4002046980110000f4a4131050404503195502c0c142c4600f1b016000ba455050a00d070000594010603000d801030801c0340c130030b00074410b100a01c2203c944060b82c43d46c081004a4402800038040b03954054600351020880400891007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 630511933 1250 630510683 630510697
    0x1803121107170319020f0a0306060f1d1305040809010e190b0a0e03010f0e010c09030b01180912080406150602060f0a1508010f0c0207030506040303020f040b0d1d03 72
    0x82119107400c1d1403030b122869604064480003070301012000d2600808103500c006c20640390100034881c0c4404007414024191b40e803580003103040104840c50310080d142c015000c844040d1020a404800511b024040756116000c2804035074010b040c00b080c80b091000c540000e200465080c1e0f03401030500408070912100e1030400024200000d000c03c01044840c60318806010344c1461860181181801c440009003940c080c0074046000665420200106410034402d0103049403080c1080b2203d9891503c50038124041441003c4510913a041680980d074850740c0b00c3c0c00d0450380502c141c4a03540c00f123040200707107240031074003140d447d4581076010000c1e1003600c403050b0842d00c56038003c0500ba51900ea0300880320a0181c28400450780f02d0b0060b1010303190340c075003000180000000010b096000c040386403007654418203080c029034010700380c14404502c01240340c5030311541605001d40e5681e9141c100200912403544101003400c004a103045495000c3d400c010340500115030030707913a8850400c114544a100da02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 630513183 1250 630511933 630511943
    0x105011203021e03090d050312011a0909040501270b07021c0f021006060e13050408030727030803070216140f030a05011a0a0e06010e010809011803121107 68
    0x144604034a1201c00d0700c40c03d10b031142c9030140e80c00c0c2800300c40130419800b60501c046500360004035142c0880555481c0d50b03070040034640f0340e010100507090380c200308501c41c040000303005032082000101800380035000291100c02d0015184058041c088003803070416a0f05408484805d014004909450310008982001910015281080066403001134540d8449540c1c48400c6d03010384040e01301c40006074800c071001042542c94060492410508200c03a24024004101406180205200106560000b50380c0d000380c040c20580e0f0580c40741001d99140640549540c00c481e00110b10120420000401840c010fa40503021a100b1446014189101d06070b5409004d0007904070303003412141440d0448250b0135055000d000d47d204214642ca13040d082da031510118040040001c03c01c08010308000c247c0c0e070000c007528240c0425509002000034203482c40050054100074041c0089841c1c0740c0294455020300400c500482c81440d400d16000d01540e22442c1d9006802c1c1c909100c0040c048141c80407204125408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 630514433 1250 630513183 630513193
    0x603010f1a030402100c051f02031801090804031b180902041103061021020f0702150406050423090f191e02032802040e010902040506122e08010501120302 68
    0x95081100c03003406c1200103541503c60f801764281c001c140c2420305001c01c000b03400050381e00d203084402da5580030101940c84c4010b80c0741000010100382e9010555041da80d011812100800e20051007040004283c3c11800e00c040680030208101515036108000d000d01c00c6d0340500994105035500480740c0003c40705940c0141c0310214010056210b1405074081c206542e0960700840c4100d100c1c0d0080340c00500d110141008005141c0d815442e001c44100e03004141d0390500c078038141c10401c0040103401203101d8030200301301c0f020011107910035545441c0440d01c400707002d08415180c41c02c50786038070403c181c6143c0712101400e00c810a40d42d400e030140c00145a2040c100d03050b80c104001c0c022000394401000721001c0c58507601c00e00135000311050071000c44c05100301c0141c1c540e802c0192074804144182d121101d9607104020070022070300c1c1d010a8900c90306100080850941d02e52925890221011800c803042c582c40320392203900ca0300c20041c0f410a80f000a4003c001036038035503012214080728040050003603440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 630515683 1250 630514433 630514459
    0x50108010311010c02031006060e0315010b12070221030a1103060a03020d02030f0105070203071203051005040209040e030426010608120d060317070b06040507050a05090d020603010f1a030402 84
    0x4c01410840a2010302110750985000303000c07104a54460b04040c0010304429249221443c0400060444d40c241c0c04040e00194548580303648584506610740750580e00d00c4002403449402405002001c40c058040c550700c0001030b00e09000c241c0e200700e0b050a210741c58000011504040c18068138820365001c1c0501e40c0706030450b002c000a40e10400700803a8184240184202218401c3c0500d50040005400540d2212850718085507100c8135100c1e5001010315010410000c040b44889010407903002703840059403180030b0008200a0603803140040a80c0c400060000b400d1050740100007484c1c4041d0440170118540d5140c064240c0d00e5a218021040e80700342c0003c004000000020807000036220000961076981c0da486c030b241610f140700d54041c100d00c0800c4a0090040101c201030b4880342c119420006131a000c0b001401600408180314200000405c03200c04a4a56850450f04c01d50014a01c0b91250780d2200640e282d0403042c02481480c80c4c40c21a503280120511084d42e0040d60b008114100c0703910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 630516933 1250 630515683 630515687
    0x20c10051b0d091a1305060d0f050f011706010b0f250f060506010215160921050d080c040b0319051e10030f12030615030e0705010801031101 62
    0x85440040807205041007000d64010404024100e80d240c4910001d41d29202c2080c81a42000040d0803901500704444d5005104d604144410740c0c0d400c07039006446000b40d41c103843c0204400c02d005800c941ca09420702401e0544203000303038101d40105085190014001c91080e44554083c070810359681c40a0100e400d0680c032150240100e0700318280c000c8c1540000400d40404814503101c16141c0340c0c105000d00341402003030300901c1d074005400e0004241c40c0c0740b4548031880030500103010030300d80700200c001c0240440c07086450f1001480030301c00e4400e00001e4034914080f003480842e01200e4a118110a14400034011207456204909001d003a500f1715180600f0700c83c09902c010b00100042c1c0c0c444030001d54001c030364030860380524403a0607a1005d10155020f1041d03a805c029041398030421003180104000388580382880c18099008103207900c14100e80f2000e40c068907050b00010480900400c0301040f0075855400000f481a6070700403110303401d82c0e07034006480d070200a003c081d01c1242d8180e51401154 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 630518183 1250 630516933 630516937
    0x3020c04090314040e01030b1303020303190204080f060a05010f050a090905031c090204050a05150d0f02090115020d09050d1e1e150c02030307080903070203120301090c020c1005 78
    0x3901030305003030000d103e0030343c0c0d1142c0d541e0040e0091942001c08100502c01e000c0c0c9110000e5111110100180c070400c480d0314040c1d40da000c0244220040d18440c03403494000107054060398000c14a0804640410402c400181e468070f4003180c050710b081d8a0180002880344c12000c80e4012a0405001e0f01c441c0360030600c0c0709000d4101c8a105641910040003213010301c44e142c00038100b440c3c910702c40001d2000420300c100720a403280546220061820f060900c902c1080118600005d010b0440d800e0380c00220600d400b42c00042c074600042d6015515000000f01e03e9840e0104161041d000c1d800e6913035141c003416050b6400c902c0c0380140e075008108450305c200010002a0302c4981900c00022030b6060718529980d0103030450064405100b00440701c50385000304014040d1100241000e5481400110740f40c6800a60302e0100404900800c004d030004184201c20074002c991240742c016040d901c0b071030044404c00510383c1c420300ca43c00b00782d072600fa001c1200070300c081003807241690300a164403803000d420700c0e04032541e17 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 630519433 1250 630518183 630518201
    0x2010e06091f140f04030218060901050d0c080a050f0d0309080f0d1d0708070905390a080f061009030803070e04020403050706030b0937051503120703020c04 69
    0x1002071014940580100d02d00034200b00c004c9096031030b071350310b0540c814401a0168900400c0300c81c2d101c103040c4241c44c3e9a2a4a583c1565429220960005c03981d003406520180c69601a80d6140128001a0140180030440e8601c1c103000c001196614016401e003142210308804001e0030002060110b401e824007001c0040c40c1c0e10010481c00b26202c00100c0ba0040000c2d4160704c0c01119a00201003005405024404140104070b0900100728502c0c041501d044034854440240344e01600340007560543c00c100d0070540b107840000ca0200c9807144101c00016201c40810b4803e180c011800030005806072400d000081d400390a540d60b4045036a1855480d46680c2d00050185c00030301482911402d41078682c4e1001e00011400707503004118117480e01c031000d011103204400c0c1e1800350710317030004110070343c01c0c5043c0480600c040c10245506140d280900d01100d001140444589e0794202420302052055001034681544c0c2c0c22000d1318610000450401e50381e20681c900103016030400400303c00036203403c1e0321040c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 630520683 1250 630519433 630519437
    0x1e0506060103052d0103140c06160302120f07051504031d040e030c0a150204030f1e020406180f020a020a1106040302150c0c010518040203100906060302040302010e06091f 75
    0x51032680342c540702d00700c210588180502c00c9404c00400603c00004900908510390f18046d104142100000c1840361161111843c0c2c0307544212150002c0520800416144170f65a04207182c40c0d12200b10b0000140c3e2000c0415a403a102c1c0ca03810701045040c1180c5280101e5054031781d149241003000b0240d6000810020050f840b9030303183c6000c49030031400c2c0010044004030601900c0c0e0142645050300700360603004c03040110588140418000100d088041c409030303e030442645158441d0700c010440c105800c5030b00080d00300d814002c00199255006071071b240d01e2801064140051825907001000700c2c042c4440401c0103a03c5100d546011072241c120704000c654020745054070b004d031a5004112a40c09074203016100310380c0055903142140003480a80248502403800e580340c285108000641000312a0380c040c0b20325800400f1422280040001d0300061603420f0701403104541d5074402400941141c44240e010030080030404201b03103050f00840d2034080b401402c0075138401007811141c0c03801000c3c20b00142 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 630521933 1250 630520683 630520711
    0x2d090c030818030105090c060f070804051c060b0415091d0f2104260307050a03050a020d0306050604150c06020c010b0a080f120d1d06041e050606010305 67
    0x301250000d8018040c601d03a11400d8104900722205040c01c48000900410342e54010303619104065480100702c41d441ca602c1c0c84041d840340100e003040440c6118070b60005902c8055400035607105201041340a000174001e120401c1641d10803401d10083e41e90b80c03421500112820f110501101d04250f2240410074100f10b00e00100f0580c105049240000b4a9100310842c1c0c06420380c01c1038000c4000302c0a00e8100c501220b2410a0704d0b001040f4801200c405102d00000c100c0039100413901c008105a07040e0541080c2168541d115a0a01426a60004030010018080d65032042c01540c020b000d450200e03038002d09090f1500d8500000c60f544410340e15601b1041040109080c3c01086090000d000d00e00c00b04000000d6583e40241040806112a40a80000e0b040306042c001910404586a040e06402100042d540c0d9080c540b20001009100d142e400b01204801e6109a0307024001665417080740b24800b100300301c0d01c0c1220100b550440358400101140d019038005425540700e034004907042031401603405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 630523183 1250 630521933 630521939
    0x8011a043c02040e0f06040524060306010c1211250e07170414071203020d1103041205030405091f27050a020702181b1e0412062d090c 59
    0x112600b06448600001a0480a02c003a0780b03018403c0d0341d00151027845020b02c541c09a80e00701050103034002814803441010000408590040349640c0301190b0100c07040300c444480400190456036482c411048070700c2000c0340e0501006101443c080d040886a000b10302403441c1441481000100810240030083d002540c2e144c001d00058030b00d4012880780300b05c0701c0000031445a180c0307030054552000b4490404844018003194000c20722091070802171800d04074040c901074070309195104a41c0180b1580c1150017030f44c1300703200001c030280040e25000c46148070217460708240514043c4405240e10940c020206041044608411600510545081242e141408002e01150407500d045580700840e0781c002a0150848c0340642004441c28941190081241804e6554107510555110910189040000c0c0043c50662801d040d4080841c00f00e440c41d5103507255419a2019200d0700021201c290800c0c00300181071140825804901d8000100c40c40c50201c0100d110001c1c00d40c281003034030301152000002c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 630524433 1250 630523183 630523199
    0x80c070e01060f0314040b241c06051b0f030a0b060a0e03010c110606061602040e07061106240613031b1e03060504020a08011a043c0204 60
    0x246000701003036111810703c000158405010703210314200090311101e40c0410030001a0640076010340000d14800e495418154400c01da042ca00080c0e80385590042c4a00d40740d80302c0e800009841d05030903100d500103105031784920040b0010000316100c0d40101c507000303201d280403400080b80034661104d0a0800800c25a800c2c0c00800c5286e40003a014400140103181d00c200c250901340075101031340074549005015034880c00c081d140c035408040c1c80c040c482c0340f00162100300219584034000394940c00030030400c0309003601e44046503107030001d1040c1d00100f55610b0004070140d20100b00d031b030700c200c503c2800c00c12071400c806d0b1820303485c8038441140c9510500c140090000700994480c040051449495282040d43c0103a103450310b00c1c80c0c00e0384413001000224a46e00c0740300c0b044460b40804c90760f100b034001c580d81d1140c0c40018801600380d0400d141030b40c80d16800c0e00b0081c080500d110030001081d64104505a64090700c403900c3c00d15060186043c0074581840001c040300c81690150714043c68800604040d01c0d0012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 630525683 1250 630524433 630524459
    0x30b031203090d090308250c23031f1e0203010f0617092503051b0a080c0d20060313120507031e03021c06081209030a1707060609020a0f09080a080c07 66
    0x841d052270300452070321115904a80441c44110102c00401d000026450a841186541d803030340c0500d01e445d800c940311200c84111a41801c00c1d0016001e6440b07684171081e15110030401d100750390014002c401c10480944c00300031128028044040034000c0070040d544507402201d00240c1d45c45240082103c000042801440316042448842d100440784859007401c1154480309034010a5140e00170004221041e03803280c0c603805000b58400400d40e02100d2955080d22a1801c1c20041034000800100b0404a16000c1c107188503524440c0000c04030440d80d01804460a0040d80d0005010a610601109200b42401952440e002c1d8914002d850840f800d80c64550249040c28403035461500c0c1d030f0b02480000014002c50b10302e5500d40903100d08200e007400c0026520750006402901114004c040750584212000441c0e1a0b0342d04601c09100700f83e42c86800c04001c1d40041a60f40002c1c2e0920b288826881c0b003100e090003103480c040d00501808025845602040c0d0040e031000300c41d8854004005455941540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 630526933 1250 630525683 630525689
    0xc0d030f030c02070807091e02190315030b01060503190c0c020109150906053105040f05040c05060d020c0601150207090513080a030b031203090d090308250c 69
    0xc0d4112106541440140c2500d035120503a02c15500301540a1107401c80016100c0201d40c800c07003010801e83d081e45012210303403209094455135580006984080d0b102c0040c811011326540e59002c010b00c005180c022200c922050000504010300180100002d9209501643e0002289040d0008421034640244c040b915000010004202082158829507800c000200010030501e80b41101c1c0b190b040c240242a201c40e4040c21003444404620100000b204400c10441c051140001d007045400c0c0131611042400c207882414459801d2061600d19541580202d902990740220000da00c1400c140400c805500104c0c049103c103582072040e03002e00c4004000490003004441450b800220742c140300207060400c5d64205502c106c0c00e05041c05000d0a140c900c8070146034008602d00c0e211500702a01301c000d00038240e5882d0f454451202d000e2040048a0000e50003051100102c4410401002c0107842c030300c03064400582042000d02c00c000004045040d00e07001742d07000c28002e00b030f01d207440d982e03034031107210250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 630528183 1250 630526933 630526937
    0xa0f021911031e011e0b060d0510030503030106031d15061018090509160f0308090a08030c060105190608040209040501091709011d0d03200a11040b010305101202030c0d03 75
    0xa085e858442c09a080d11122007208000601a0400f00004151203101e805800c0c1c4905030b8032000104840030903204a009540d00805495407541e68441c0100500b061550440140d008194440001c0074001164081700c0e4440f2842c60195a51070108a1400c0c0f07911802020700c4001c005c0b245407450111480b002600c0c2e200c500044a0403d81c205502d026140c43d5110042401041c040c8110751101c03800d030044a0744010b0640d600d21400c00400d48504482c0d0112410b0301c004104035051a0002c21550305a89068a01e00f40c07030442451800c0d40e00340c0d04e105000104001c0750101e005420240742d02c07944079001d1000403c40c80010f41d1280302540c40e80c0c20007600c48001040d0340359a9a88003500d000d00344200c00402c0305500005000600b82800001c0c02014060005c421424440c050000034070044071207001c1e500b401c0803608152501e0414010f0f410b1142d440c03c4005040c40d80644549401098030441d0040c204d401c003885070012002c108001d070f80c18421900500030701c0d40c500c050507401314400e07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 630529433 1250 630528183 630528191
    0x10f210f09110604030b040807060213170f07060e12010e0a0b0106110309011707020c2701080111030103120e0907050c0c0a0e071803120201020a0f021911031e01 71
    0x60401d1509035052000b598401c040801c010070108009401c40d580183c2c01211203995449603107824802442034204006140f1881c0100085603c02031042c4225020090f003a10302d100343c0800c1e1b1a80b1040d140c0078941c045194040d81c0c1502c1c2c00c080070101008c88104000103094031540110500e028a00e100c111b1340b0141d0807005004079640222407210300d104501c01581040204e20002c0c10360f4180f60318038402c188003000045c20381c42c400c0026183d660f0f00a406140520300c144000a41e9140d903d15206000301d20200001d249141446004920a00740300407d0459080d036890702240d141038200c1004000304440e00592668070748a110f0301501c02516200d90302c0b08106070281c20800c4113046507102d4a003005c41041000010343e445984205640b0f0030b01c02006064444424070a00c0d60000340074940003444400800350150b006000c1c442064036108500d0b0a5417504070b03030f28070200e15980300800d040400000047c3e0350b0701701c0760001d1000030107403001010003440b01d03000440400d00b6052646e4403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 630530683 1250 630529433 630529451
    0x6040923030d092402040303050a030b01180803030601180e01051210050907050406090c080103060b06071703220c1a09030102160c0902040501050f0904090209040503030603010c0806010f210f 84
    0x809141440084504c0d40309505042c42c0d0b403070140040c00b50031038240515855404040d0960f01c04c9080000040d00590b81401e441c1c0c5484400b0b070769070412114240031695030000481102461401c45c4121852008600707490783c00c1a050000441c00c8030b070400707030390310490203260541d8069008151261009034020100e4600c0e1234204010340b500d5030301c00310800d07103041070012709254442020b9040d82d82210001c10001e07224004211a0f2059210103014524030011400c54205240d00840c004d807162060340629485e010321141c0440c0310300f08020130400d1401d030208020f0b0010b9244101c003103c6020701c80d0505200001190030b980c860060034100d0008410b04000300003d025400d0041c0c111650114207041c10200040d02c1440382c4101039820354400301d8011125a6a0f411020b0f1056000e81310340c1503408c2902c0d01c142d40341c0003920b403030340709500b48440d40d0a00c1d88542ca6061082364165205582c120b281ca1054500a001030450003000020640481d04400345018007441c0782d010b0840021940306d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 630531933 1250 630530683 630530723
    0x30403120e0d0b160903120324031a060906061209010207020913020102010e0303090a03030b040e1e19110402031b03131a071403151306090506040923030d09 69
    0xc80700e082078091105005c0c041c004198000c501c200e98030034605002512250070000c180d905070100d90380c000c1004018070040108406c03242c3c070070180000c400f905041c5885000070091400030447d02140c0100c42170002141e1488524035083c0c200d26980c000616040c035680214203c400c2c03c5545a514001003604d640c11544d091040000f1001d100c40a942142410b070310380c544604100f00c000d0209900c2d82920b10765a030342e0390301c000c1c90010000c040301c0d0000444030030307a0b14800505881002900480c01c0244d020704028145403521580300740490710318110300080100a402c0034103000d550801c0845440a15103804000b140103e4130b030714030500600501e01e04580b5103039410b00340e2054500c411007485181ca030040b001294044541003096140c0c3e07280380541603200c1005645507448452170f808002010880e83c0540240ca0405a0610456551806210982d0a02803004051b0852041d603415920080016228481180002e032450701c1c0360780d0802400c1e40d5042000756a9200401c113030004140e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 630533183 1250 630531933 630531961
    0x9090109140901290324040c060314061e12010209040b1f0804031101050112020909010902090c090102011d0106051c0521071b0906060c05030403120e0d0b 68
    0x510402c020f00c22080f01d210304c14008500c00d444010700e8080009440e405030303001c0c44103c0300c1ca420b011705a00c032516540408610280182c0301074550721100c2c103010403480d20034002d044842c00f0b1044e02210a071180414800e040307240f2000d1108003c45d43e40005016910f03410060310300010080096150f1039070780100402c0711083c1703150510a04039a030308050003600401d040c590341d0318241131000a42e500c0b1304045d21010b1703e41c082d26105505c0c1000100d0740280b03030748103000c007640251060780a55803408400c900b08c4000c2a0046d500c0042d4600203008450346070000c1c4007169040c030011441d4510800c84041d155080000081165107900c4103005c5810511005034020121007150380c40c2d21925261980c0f100f20784c05203a4180c000605466410070075660882d01b810b40e200510003a10001c643e00501d25150728002c409a8600344500026554420310301d42c40c559804c45c1c09103140c18a0359980c40389040003990700009022001031071030010341e11604000f1b07a050040d07a61004601d09903811040349 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 630534433 1250 630533183 630533191
    0x90613170c1e0a1203050a030c030e0615060903191403030408030f1b07080c10020915030603071d071e080414070504051e1501050a140909010914 64
    0x16071001d0a1003899903903031400034014000d095007400a2502ca0000704030030342684c1d00100d64002c80050035104240d40a001020072031280d0307904208141c1032040880640d040800f040410303902103400b080e070080c0448001c0000340310042040e071800c0070610203e42041c5803480220300d5101d90218a400b440340310504640e07003010800140d8036525056031000001d0201414441e11161040c0014840300a1200e00038900c418001029855582c0341c0360400c4107601500d504001d500801c4007070721b110b042c14001d40e003990000501014803a84890003050070381d00010490f40d07240c41000c00000d0500d0f0402210b0381c00600c80b0840720705a1a08140280654044140d01884020040c0c4100f0025500004032500150301910320918a09020103492400d822500201ea1041c030348410f002e804000e00030542d800103034080f1495400e5482003020800c0c1c00d0352018060205504016000010788900188421142c4840e0500c1c100b1a60902040340b04000b41c02c10108a03558860040030810703448070242d80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 630535683 1250 630534433 630534479
    0x4080708030304050303010e04060905011a01030e0f030d0c0306090c021c050909010e06040207050f06180a080706050c0f120a060b160b1902031e0108210a05090613 72
    0x80d5003859903031a0345e244414801d1000700600c200101e010802d950304101c004682040003032140503031086650550109100b500e80c0401e2a00d4240b03c58004d010610b04031101502e0065401e0030409440c0202404605002004140c0c3e1150042080c007650700c10080b10150340d81c01011041c3d800d80700c18002070852403c040c00e121080c0a003440c0e0359035649440d410358019000c542c00c19240c560208010380a40340f0010070034043d80c1500402d500f0001074062203003220902480c016880902801d440c1e400021000d440e2000400807500030407240c0d04600d40080c00c040b0b81500d85000c103600f400341d03a00042c000e146000c5c10032003404102d0306280146030140011002680c0740182642504e030b006106000001c000883c2c92002071145414146020514940f1210a540c0ca190001c1400000060000c041062215120011403140800549441c0705d5024000250170010310764a03452007604015800790800104000d8620b0035242c450280852101082013046954107250701d44420140b60444481c2c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 630536933 1250 630535683 630535687
    0xa0e0a060f080a080a030e10050604052202090601021203090d09141e06040906090203010503120a080f04170c2d0c1c1437240f020408070803 62
    0x1000140200c0d2042c034a9504c0f50541d6a034028900094000d409080f0b0401c020340035205030483c803c0c1c0b06401652180c074044600300090742d5464000c3c0002c0401d81a052a030b0a02110041e0050800003096a00103030140101c8104e0418041800180d0f4030071151000711f6000140002501900903800e04080c0071442c04c00b20100c0fa080c0302164894410f070b414540f0400c104004014240c64502c1204c0c05803610300b605006641e12084903401035482882624003c1c403c1d5004000e80c0b082d0b00c41662480303041c50b1350b1002c003500c130030300168008d0401801c10f40e441c0c8035501e4171032690340385a8002d29504009401920304e4118008540c014041a0307100000713514404604041c45c5803012030a190620300803030324510314005c02d92000440e81300c5400c1c0280100c2c07494081d0f05203840c000a202013812a5000011703d10141401802e42c030152800039800038202c41100d040006500f036018102e400b810010000d16207010b400300340280d950790700001e030503503500003030a0084036030610000e000341c24102d00440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 630538183 1250 630536933 630536939
    0x130617130f230610061101020f040b0c07050d0f02030f0f060c0f090a080a1e080702012604030f020c04140a0e0712050c0909010c020601060f0e0a0e0a060f 68
    0xc18201d2501e000030280001c03240400c010070220401d0308042c42404040350024a000812146080d41c54003641c40813900140840d14100c03414021141745490072802075042510300041841135801c031060780c410f98000e01002060303503281c06032500c1e80240501050b138203070b04aa0040c1070418110260005a5400c20846a007084100044c400c0e085403010880075602c80c5c3c0815040f000707005040d52254852100d05c00011051800210710104e50702a60b030b04200e0b02c7c1208041da851409141c0024180c41c401e00020f800f66006d18220780d08444440b0740c0740307400c0e43c1c0c051400d0000d0780200d034210081100e000300c042602ea410000c0300401c0300b00762400c104581c002c008a414025006100310507058032844103003042a018880400204808082c42210f200c0d80d1804540741c1c45c003081c14500480450b000a0b209c200140501090841d050300641210303400c01c1000c440760344402480c0d100f031104440c1d051000d510b80c41d03c0f400040000c41e43d844590f0501d0320a08054401e03550081405c0b0040c45424 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 630539433 1250 630538183 630538193
    0x213031709010e130e1e0606120a0303090c0314150105120a0f08090604090b1f231306030b18040209070f09031a060a240c020613061713 60
    0x60180c2d000301e0341c1103680984156007901a214080e0b0f40310040c000d030090310000e18118440c1d0b800710b01c540c800391411030365160113020a0500c49c1c03146203690340c031696038100072074040c1c2d010500c440e0041810b01c0c2940d44980350000014804413044441c0c1e80300280409403c0c6070310300b9050152000326080c480c16007011504654074102054081c1503a03c15500150030849041c0c11101d4800c4080c1c016500c0e01c1d03a90001c0b00040800d000c00d54000c0980305c002110341080080700c0500c2442c0c3e912000c403020510340a010680c4101e99101e04044070800400c4001800750041000600360341da4041002a000010b0090079004002d4035080b8003500418000140d440801141d401912813608940c2084214003c441c01a62580050001c0340340005881f11241c02d00060741c4540002d480850b00c0e1a41c65085840f15002070a00140b40200c01490345e0019206070424620340b400100039078100103240a01442c240010b9116002141eaa41c41c03224903041075a0595134800240e0200000850246c2c40da = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 630540683 1250 630539433 630539447
    0x5190506030c07020909030322020108041104060f0b0903071a0909040312020d05220c0504110c1618151503021201080d110f1e030409021303170901 65
    0x14491203500044001102c0c400001c0581d415a0b800800e480c40c58140262010b40701e50065540300100c2c2c0504800d140108900d0455804840d410f03507036a00280e58540301c0380f60602510388025806900e07a1000107520880e140a0400782c01c25020040c0d0f64082c01040615041460340100d50601c0c818840841d10b05158080e90103000d415609400c1d1940c2d01e1408480c8410705039110303543c20344040398203c5642e203d41d10141c86000c40d2041c82c03400b140c0c4034010a0340d19100d01c10050109480d81018030a900b00354100229800c4011040d500f40705c600040c0504180050100840662500e2010040c8000e00d40d540030b4102150705c03080144150100d80c0fa00810514052901d0780350901c00a1815035200754101d90414550005205040d40c444014603100c4241d52801000140380a04030103111001083c150311482c042d000501c498100030180505c028240390008589000a000001d0310350214002407418800030204042c2450540c5090145032007800340101e81c0036014000b8101e16604006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 630541933 1250 630540683 630540689
    0xf0614010302210903070215120601030c110f010b0405060d03090605070314070309060212040e040b060a230103140103080a120209100804020a0911030408031e0106020c0a0519 77
    0x2030003580c0c48a00da142c0c250b00f00d24003103102c11046100c0c0c04000c034000021025000561084031101105012003550b040300d400b23595854002400e29501152196000b640400c5080200d401e04002c80740c0204d022a080442c0303131f0704492003651a200c501c0c1c0c143c50035204540c0e10060807110801c5100003502c0c000d1415031203000b030714280000024031900b414010210710400c02e0214001541c3c4091500e001001d0041034410034015103d482c2e0880e500c100400c0a403016241820341c0c015007503513161903d161641c00038000075040901c070351010030103100010601c400c0740000814404100b4200c0001003c80b5050040d1555009061005000050030b40048500a86030b03407518085008020802000a101d9118020362140b5111500304d100c582200383d80d841540211f524801070b80d40c4013202c0c000c1d194140d848610203e41040000c0004008e1000346802000045c034440044121141d02c041c8280c0030707080701c8050b81c4003100d504a2440d100034a000500800d8510700d00c0d10f000b10201040301d40c02d0340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 630543183 1250 630541933 630541937
    0x507030c0b04150f052503080604020412020f1f0206070908010c080a0e07090513020109080a05030f16020901182004090e030f030f18150a05070c0f14010f061401 71
    0x102e075400540c400c070180c5082c0c0c41c02000d00421b0518201c8418000c005d4007004402007440740c400150249454402d807004c4600406c44880103000303543c208051000c14111503a8040c0500b200141403140114111118808503001001070341812000900281c150358425601a03041c1015120000e41c0800c901d50014041c55000c2200505840d825007008072641007a615607280004006c184440580940350950003030303c3c0c040025446119481e00c030094480302a1150340100072605003207104a00030b11004d20400500c48150300160300140c10301030203a000040c00292500d820b001010f00e44202001c4c002d18008241d288251001044890f01443c41802c194030386d50380500721900410304c121000200e16080d0142d88ac0f07084003284610540c01e40c1c0b82220910300e030300016403a0b030001078050306582c5081c0b000a030a965818041e00600130061140f800c10004255180016909501c2c103500355124045030121f040100850b10708440e05282c1d00380d4482d041003001c002d4505a0780001a6421080c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 630544433 1250 630543183 630543197
    0x100f09060216020a0837060e0304060f0c0b04020d17070506150108040201020c06092806020d0c050303040807020d0602071a100e0406090c0b04080304060f0306140907030b04090507030c0b0415 84
    0x80c10703901b0400d00c0c0e032201030480e90500b444512030f120040024015122a0703111307906c03901ca404201f1501800351160040c00b1013080382c0030501510386100c11a00051049100010b000ea031b5504200491300444d208541c0b030360241c8144000880802001004a5000c0c41d0448580c90284c0000f99109090329065005840c00103040f440c036180d007900b004045024002d0040080c00300c8504220742502ca2060400600910008440f4140b103041400d44a640000040d401d607100ca481d11100c903881304804a030302c07a1a0880c045c00060341030000c1d00d03255028070703100d480441d00038821501c0104004c00180500000130b0083c05589100301c0318a42064220100045810b51071820085020a5802520f0f41e0580801c001521280000061041d2203166950782d101c04d01400054042e2000340c0510702c0000600e030b4171b4520724149180340f5235112440d03190210340700b11100c022404540740e280c001d507607903041000c003441448a01d000c050001c0ca041007100f071910b440c3c82001940d14009144940c1080a5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 630545683 1250 630544433 630544513
    0x60904060209030d0e09060303031e090712050c0109150c080c01020c192d0f020d0219090608030703080612240106020c030f100f09060216020a08 64
    0x240c1d06440d0030b80009001c0752100c1180c0c081c0034045403c4240d03000d11031254800000c07054200401940d0062800080100481e418480344c41c2c090000185218030a1003040000140b6610101650034018020030292003c104403d0005080d95195001001c2103008969641d00e00c030303031007a200d0244c141c000c0c2c64640c0f01d00500461601a10810314400310740e1080c0a20701c441c0070010002c0b080c0045c426000b01c275545504444400c28501d0f007032200c114150112503800045000400390700341c50b03440140300c00010345550340017401c18207402c2e010790909260801c1c02e003d08080d92013003001628a0030000c504007025994020803038080108034500503004c602290140c0503080001c20803081d81120340c403010a02035a051008403809109142c01482140c58011040c03c0208480303403803900c000083e061003511b034000b190140070405001c0840541d00e0791b04030046002c52002d4041c0c8040411020b43c61049401040801111303600012915003203091070509800b1180028084251007041500790806 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 630546933 1250 630545683 630545693
    0xa0306090606080108100b0306040b09010f14061005040305060a020f0408060f07030f380904060606020624190305010207030e010206071403041502040b0d0501050103060b0c06060904 80
    0x8440d6000d410094102000803805030740001c90681030342c500408880d0040c1402c0d40c08000d484c1c0381404181c0581100700810081200046440d078001010400490000c1481c0851400c484034800c4011405000d44140480e900d420109040820010310b4014103041c29500c070140c50705000b41a02040607130000e4a5076180c0510000c0d02c008040081c00d86002d45410055405c9a00045802074006882d005810406900034402d507803201014801120401500092440001079a030f0303203014040f510a201c61016a89072000ca501c80e610500010801d6498030b103019280820240c80e1411a0703a6006091103450b20401003d450304104580704041c40d9010306070006003e1107500083d000303500000c0e04c00103040d00040350400045007071382290723055650070104668604000d03201c3e482990701007000c2030100300114103c40000b4400e090052405071340b07a080c40110340c0050003682c00344d070f11400100030a60709441990024039481d04d44502c1c104020741d5103071b01c03520000c0c110f6100c4c01c100000b10341404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 630548183 1250 630546933 630546941
    0x80f07061b0302070b0c0a020d030b01031b090302120106050112020f09090a02030f22110a050603040311010e0c06070b0a060b0f0903010b1c0b180a0c17011a060a03 72
    0x814508203411207801528000b0003a5008900c10355114010002190390f1504c5c5104540516105034064540d450b0442d0007140a8008107803824101603c440610a03140b03550019001c07152000d4807021602491481884240000003100e03c0480e40340c081d0030889a40c000440c690300c88111500180e5440484281a0701405034001454000158004020f45040b0707a500850092a584114084c5580e0700003111203d00b66065841c22803070303070601c4101e00103080c4280c0400d00320b0004050207a42500c0b640842c0d1a40c10441d4146c0000e141201c2c1c50403400401e10038070781614460300151040c4600720020441a00c42c000e03000f00b080c1d4032400015644046903021402030311242900c01d076a10340b0007091000366040704060611951034002c400041d881c0062054120400b0818001e890100513103a85411030802018804508100070205600ca101404118000340c0f10701d150707241d454184060101c14041c2852100c00c00c0e0326002c501305042c40c81c00111840c1ea001103641543c1d4000203842140a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 630549433 1250 630548183 630548201
    0xa0c1205071a0103150c050a1808010207060b101817010e01151e050a05121f050a11120a0506010203041d0411011403040f0201051215100309080f0706 66
    0x54045007201c2e000c0c4042600424102e80c000e12a0a001d40815010b00c0216010000320401080c800c01650400c680240c4c2d2059403480c0f1011981d201c5644e504460f82668800c210807640340d17942d00c490007120310741070780c02400543c03441c80c0520440d004024a01c0d000f11840c01003031010b90b10007294400c0100d003500014130711446440203020801000820104988550050004c0140d03604000f00751080703a1490601150342c0200920101e61402007484070010780c041641c00c0e140511f00003404000a4501103030210100e40c40002058900303260f030b00f0300b00c0d40f05d20300140c41d0079810498400c114008045140c0c220f242980700050740e40b03850006038031750b100c0c1398441c52210702c1403c205c03483c01856450181c81a4082c03000e1f000d60b98502001110720380c0700c0c500740b00308454061012802141d000a03030a0000303031040c103019103031003100d001075801d0580c2240c080303950540000c00d000303150a14040d50300c040c000605050094440640c1c072029207010700074021081110100d80d801c24001c40c2e801c40081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 630550683 1250 630549433 630549443
    0x11120103081b1609060b0a120c1403010303080405100b010e100905031f0e03070507090b0f0a0801050901060806060f121207200f100e010c02120a03080a020a0c120507 73
    0x6100380701d1142151490f85441810708541c038200000407441d207240102c3c0c0303400005035600c2140341c07000034230440100a11001802048459075001000031103450040d4040e5010381c030340d0a030358502031803c1391829207084c98aa5081c0d04000840510f82d81002048800403821208000003400c0300344103e0307000b00b0f03683c0001d030f1600c6038016010750075124201481403c0d007204004e1240340b03054458150399114020f0006e01c0c562002d83c1c10024404213a1081c1c461010003840ca1208011010009004011a402406069640d8024000380000903c07903000244641d4014241a142c000e00145003402d01d2503841d401a600c40310b40ca83d1448050011950600b0314902482d02c6100505154400c0d10308880c0c04020001c8000d00f002840c6015006c120401c02d004201c501c41c080c07040c0c07088540b045d0302c1c9200307418040a02055401a541d50034030108484400000b04411076140c2070080c44c12174050100c6010318810865980d070b0030b90103042e4041c0f02e50000410540170320100300850f69071088842c0a41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 630551933 1250 630550683 630550693
    0x21e0c100c0c02011211120405120703120b010f121d01090506060a0e010e0414240a0c050306031207023601091406120c150a0311120103081b 62
    0x3520b4002d60140c0c02c55000f070b6102e54681540b041a01d04468008003000361960052200003e00c4140c0110a58014070507001c0e11620030448403c19072a4002200850120302e02d00315178503840100e0312504c0c802c48002d191241c054106094082c1035001c0b542032041c540f03920f07404510000c0c41031018000704000301100801000300517040c51078550364203070b070250f100300190320002944030718019045040c0d070207102144507552560b560321703815045c403042c503001903006120004d01403103580c807140c2c5008201081d070200c051501c4924a82140c640030b1484051240610501c000c50301d0000300c40902c0c179441c00402da50b4010500000d0024011451640f1231788007005801e0050540c0d88d004042000100012110b0fa030341c03501c00e580300f0b9aa04c0b01880700c4140c01440001e41c0c41c5444031a051544101d038041d04c0620031128081038481114050305d030181c010001d0325510b0725600d845419044000c040b4480d007410588410503000400601c0060114403010071000c41c01c48c0da1a080c242507040c43e43c00c40e2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 630553183 1250 630551933 630551951
    0x141903022b060503060708091b010e060d05100b1806070512030a0c0206010501050c03220504141005120a08070614010e09120a090e0405070b130810021e0c10 69
    0x80a0042e9005007402409244041142c0034000c0301e00d607000b84480400b9049401071541c825149036042e1522504006401180d80c0700364541c84001c00043c01028800704061510108010603020103500030070f410b4100f00003030360740d59042c0380740c03c103501800f16412942c52690b400c04628010350054035400624000040c404c850940340d100030345041c1e01c1d4003900c2d01d50b03031784500548071401400c1943e180750b003003080720a121044c60002d40e240401100820203841d5110340101d4100c0d240003051341c2c0c1c3c90700741000b48802440594030b000d005000459101140c131081c021410303282c0c10085401052180d000c107202c0c04200141c5c101464041c038801c0620150b607500c2c28030060940d402c3c1c41000d594010880e1400c07402c2c22150407101c03c89115121051103d02d010f0b900740a4241c001d005403401d00611030086051410b52000f404036100300e000da54121401c3c0b8008074102004104610001441002030042021051420390200c0314100c2020380c4451860781c1541c201400c01030485d2005240155071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 630554433 1250 630553183 630553267
    0x1218030c0a0b0a050c0d1d030f131401050a080a27031209052805060a0b120114150402120106120e0610171c050403020114190302 57
    0x4012280d00448140826071030300d6058100315001581e1602c6005c07002c01581034441059040341c4005000380d15103c00d1120308440460039034004100014042d480003c0485040002d02900700240101c061401040741c0d00c0000030301144102c00303906090155000000d00d00065030303403207901508000c281410148004000d9040c900d039400600324086100103441c1c3c0c444841e248242c02041360701c80c004000f8421245038103aa40c8031903070010350124080c0805100011410701034076001d051070003401315040e4040c0c070800443d14850f00001007184e14150f1000100c1e92402c100c0e9801000c007400602c0c040040101140c0a882602031120000044000000701650b2040c02c0c0f41001c4d02c40a42004841d400c2100c0740d171594002d660301c082d4803070f8505c400e0024020204400b0a5104880d04580040f8580f1210720b20401e12032031504046500860104250b50304046420101c14903420000e1402152100a9405035404044041016030101c1c40b030032004c80c40c9640c2500c10350f100e006507034060002120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 630555683 1250 630554433 630554443
    0x3110f070f15090b0c0304050a15030c08090729071103010b0604061e0306080d0801150c051c090f18150e04080903010f141602060c1218030c 62
    0x10403460004080703001a9250302402d9000c612107140c0c0c0c81c1008245442030300c43c2c0c0c5030000e2031509250b001c20000000e580da1400c01d41d0000780b00c101000b00d000c065140303001d0100d07070591000c8814401c203801008602d4030086192000d80d102102c011003640702545448002208025202400b03400c0041d0a07024845011020030642c00e01302c0090000d5a01c0c2e81c24080503004030702c0742030003240030440003c0c415444884505541d205929000490681d10200ba5107030100d408002070100d522000144899034030940038500d00c9559003424844a0465039449645629005100000444c002020011a40705d5081c1000801d000c11790440b0a40d2201c0a01001041140310800c100c2e01e482c15900c203075044111541e080720200c10302141550343d5a10783c0c0d802c95118004040d8555030f22000058000c5443c460b940c840f007804000b8076041d10b000f26442e8000e410b007400c0c0c4003d55205204201c80040d4800844081c803042100c9503280380c83e83c030b4a1030354420fa64001d0142c1404081412021a900010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 630556933 1250 630555683 630555689
    0xe0703020f0c100608120714010902030d0c0b1f06111c17010e0c030c0309010204030209010e19062d080703050a050d08070f030e03090a03061a0a0e1303110f07 70
    0x400304a1199111304131555442040320008600000b84426008154125070342c03410151448c00214418200754000ba0804207030b01d805401156403864034005200295003c15800806560b160012030809948601011458403840c030070000b041460b100b03120410b200508111029540498103000007050140c400c3c904d00f0601804000d00400018440b240c003081c041c09039809802603417968a072100603031015440140b4000096408210002c010303115019a94020444c40ca14200c49080904007521385440c03808501e603640e030402c14244800040310fa40152030400d043c440040440880b20031040c1d008095005460f50700401c54004180540800d80b5001c503407140b03080c4c440b80b40004100ba5138a0005444040004415107c100c0c5058029803060040342030f1102101c1c00c011002000030001066600200d885681b910a03104882c2a418140c02000104490b113030401401c0245034461300000400e020b5003a11f00032810f100345405501048600350148098441a9442c95900799881810788 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 630558183 1250 630556933 630556963
    0x1908030105100309021c0309080a080901141215040e010e0d022a271810060501230702060309060403180302010804140102090604080a0c080303040c0e0703020f0c 71
    0x5800c01d460b580c441c0c4120043c0f90360042c410501d0605d00c14030982d4440054508900348000b00b01c0101c0c000c1c408002c542030040c072031040e066540a040000601800c044e00036015000b00500003401c81441c0e14200f15441692510f2500000c170703a0600041c0980240842c05c60954601800b8401e85900483c0c1c548449406030202c1b502800c000060801c00d0039a0f81d400c5040c400340c0740200509203815051100502210f09407002c04507100e000381191064252801d04444103c8004850f91040070301c103101c540802c800c0b040204034540000a401142003c000b4102c040440f004290b10030b4001040c2c0307401d03a0f0017502c616100c2c42c10130310b52076681d45c0a50341500442c0b054400402c202c4010000e13041940d506079221002a1150790303d15001c8032465044d104107540a000b80506030f2240c2d030281004280721401825404e18030b0400c180d2603283c6030070044040c0c100301304000120300120660011075000207600609541c1d548400ca000340140740440d4800c91000891240319a8005842444000e540c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 630559433 1250 630558183 630558199
    0x30c030f1b080d110f0f0a020c04180308010902180904050304030b0108150f012625090e010615050c0102040b27040b100e0d020d0812010f0305120703021908030105 72
    0x21150044e418002c40d2983c11480310100456080c2000320800780c0807610241c0120354506804d8030008040c2c403070381c2e4101050400300b6001c1809060744540700c0350050100c00021440d200d80010101e12184c02805410700a6245101140c1000790401c200e800841d0064646002540c540340ca80e0b4030703107800c80000c94410020102052400a84074071a9048649440c1d00d00340200303461075418440048115030341d001d802840c0341440303160040c0c80d40140c4001c40180706c580250031702d102101140c4500c008160244c1c5018400c7c09550390380d02009140e0369841c01d02e035881310120b00a107806031145410200300d01c0408600507014401030594407070021201c1420311180510401880103c8800d41942c640c0580f030300501c40d5509000c0d243c8510958800344c40c110f00042c0c1900801d89450303008034100ca00240008a80410740c01000307030f00d409403080c04503601300301d851074603a0355407030b8a001d181e85a428400202d6804060080111040b1445000145074072100203044c01c4900e90024468076004140d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 630560683 1250 630559433 630559451
    0xd030e181f080a060c1e0203043008091908100b0315011a090d0b0f0619050103020a030b0d060e21070b060f0904060203090c01050304030c030f1b080d 66
    0x11140c64501510048401081070940a1300d404000e04242d80d41141401400c0009400202c03140b0ba01007401010350b0003d40c2d03618035120382c170982003010311032001c1803006e0b01d2031005620b494016800d141e5600001c101d91511281c1000920340380780710714000041c10311010b0000e03420602003500088819200d50800803802c40d40180341c0c07205900c0006403610b02d02c0c900144002c40310081c02c0c19080303204a001a04008410003c40e902c1c0d000380c00c05465110480b41003000301050314000e207034000b1050f070b446070004c0c1202d0b01c502e031008000d01455040c190081a40c8030a00d11a501203622880010310606043d921400c0c01c50042c54a005802c0141c01003c1004400303c240c0440345d03034401e03051050149000c03455150b0420200000e040d0030b50101cac1854842c08142c0c0d95454680c095130140c80300694908150350980d24245160076981c0c1401001d1042001082d0022101c1407442c0e01400d0040c854401851b08407008610003010940031884440483e061002d011301030607880c60303440b03010411411 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 630561933 1250 630560683 630560731
    0x70311070e010305060f0910090602031f150c02030c0a0b09030d02010b0f04020706060e01061808010c080c03250908071212320904050609150d030e18 66
    0x2400f0252155015030080340b5111801c0d141154004a05c00c10703924120260680340003942c80100090f6101a00442404001c28440d00c08102e044404010015150320b1b044120b0780702c02441c8107910900c0780c14507a00007552800c0c07001442d840360040c0000e224a48441da4640300e6000b5142650280c0f10341d0584039081801440ba05049540c0203201c076458a940a0800000c0c0d44005000c0f03680d0bd44401000a04510b00701c1d4140c042d10f419140c60000c0607200100d906a0b094543c40b0b400581e04107003000e00040d405c00280c903000090704200c0740e40c81e5211049100040d40f000c10800c02300442410034140560f00c60f501d00248c9000009413003503d5650410100e0100c00e480010b4000040719000d03034080c0380105510003054850310940740741382203800ca100d1459200b400c1c002134016000a102030f894030702486013640c03010303007115440321504041e15801c600c1c188605545000d9927034120142c1c189802821400764a42c0014421a1b03010800d1001c5c0ca07230801d00340c0d541c02d01c0451100050032064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 630563183 1250 630561933 630561959
    0x71514041a0403021c020a060c020607021203040201141605120a0207061e0f18060e090c120c090a0314031305061e0d110703030c020d0c02060306101407031107 70
    0x150036600034012008000f0350306495402105e0b4000c1944101d804483c0000e00d213000c0e070707041c040864001d4112803800040182c204290f504103c948520304008120040c2c2e0440d00c0c5444840364400640d482e143d20a403050311550358017130060014070079907000040c0c01c00118010b0140040e00e078255014156280002c2d40c000b100c5c20328501000f0031311108a102d0600c01c201e40d0402800503d001c0038403c1c90142e0308420315089800400000d4000e104c09000c0e800c01c09080e43e00040428045032420a0f200812944078001801888290000141d04c01043d941c0c120f03024041c43d081508040b004002d880c4240c2c1d281c0c4503d07402705203541d24100000700342c80c101c0c065442c0145004041403040304901e000d458941e001a031803d490701d030b580c01d0300355000d41d9080c05041803610030703140052001d581304d0f0040e02e010a0b40203000108410036949900685074802603c0e0007030019a070759111283c4021040e102044c82030103c015070300c0046409800d060b80522401002031a100c25100c181c3d4841d00c600c0d02c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 630564433 1250 630563183 630563191
    0x70501110a052a090c030103030f05041212051908011401110d030b040923010f02040f0b030402041d07030c080d0806100c0c0f0501030e010204060207030206071514041a 74
    0x142c22056041d2803510281c00d040c1c80c0002c0082c610f03004040f4002c000754035450140e96000e1030f03000200c01402050740080d45440c0200040c18064100307860411180d549035401200180010317011001d8081c3e1a000d0000c0e5400d04041340700031203806c2e401345001001c4480911807204290310313049019449500540c036010040c5044c002400c13080303000c0102500274080400580e030300581c0e200c0600300424005520300d841c2050701000b1200c1c00064180960a449100c20240001c1d4070400c0200801c1040d11180d004980b40d000c2d0090f2aa035441c00043d00406160f112480c81174148808c40340503400100b40390090320320440200c603c0c0f94a5841d81591608040e00030004500001c011a4580c6000f00795080107140f0307458100004e144075039403444040d4680d0301c04002190440c40c01d2000b90381501640c140804114021420a49845c5009681300e115200180c051500001c420081c01801c40c0202841080704206100b4049500440c803510081280c0c01d6403810080307100c3c03c0310004120707000350003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 630565683 1250 630564433 630564443
    0x13060308040b07050f060a021c11031f05061803070602071a0c1905030d0e0c0d260a050301030c14030c06030a020c060123010504030b0a050c1209070501110a 69
    0x4050410301410b54507404102d0503541446480d02c04041d4010800070a4401c2190000160712040c02c035440900b200485810440c001e8200300700500c41e813a2800c2529480b01209050080905030b140e00300f440000c26420803900014001070754140e419894011880d00903042e004c0782c5500780c2c0c8000803070702c883d418010380100d1844d0200040c00303242108081c14259a01105455000c0c000000c6800ca013002c4102c200d590760408204d1034004a0741d442000c0b200007920001e400103204080024080702e100c0b0b02c0061004c0703c03040c01e080c1e1140341004104510300c0c24491031030740c1d681c8a010103043c3d50001d06c400c41b42e515052001040303245141c40011404032000e402020500317810b07030800c585500001c050800c0711f64203010104602c0d00c00c202c241d00034810344c82404050644100c030710740584c10360010b007414030204000405c00541005600b617031000070303050700182c0c54545244000700d40c454400803020340d8140e00e0921041d00e04c041541421107a0903205e0011640301801c00c03d460384144500688 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 630566933 1250 630565683 630565687
    0x614030903070f030908031b010b0105040602060c071712010e0a0b061b121305030c10051b070504060602150a0e120f0403020402070f060f061a0c0f01061413060308 72
    0xc0350811840c00491007405c02e0211582c55042c030300e1031034103c08a10001d401503440c50480c4400f0a00c81c40b40452404e00e00945080d060000207540e69001501001c04402d00184005c240603508014602c2c410a50030381640d80c0c0014020020b41c3d403401e003e141e07054040030020503c0c00c1c84030b03c03603c40c00481c0a80040d09101691044011400254403403007268007409200540250910000f0485840d01c503030b0114000341400203051901d00d104101038040e40e400c2000a8040e85c100c42074032713038100300ba20510080d200a45002c90401490740d101d181c0060500c180400c0c002d4020552100b06258410b2030b491b680d842c0d103910416202c10000300009508100260b03000c16484800920310700c0010b148080ca090f64aa01040c00c0303900c405401d4403240c4500a000c000c00c0100d008225004100400502c0703610706001d45da001c85001e03601d2040c12241c0008010041c008240b1080c401130ad0002c0c02040300300e9481030780038400d45001c044544a200e07019840d034007510303152007130005880d0401e83d128 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 630568183 1250 630566933 630566947
    0x308090f19080a02160815100501270305060a1a1f0f02010902060d05090d0903020a0909110901060905030c09010b0318120d2702030d0302090a120803010614030903 72
    0x154990011039402c013140100c07100e65480385a440b0303240e0000c01e5190010210406036508000c00200090800c0c086030b81c818004111907030f4040340c10390707041e940c1c0d20000101b074a07040781e80e48640105030300060507030240008100219016503c1f440c0c110788032100c2050900d01010412490802031065002c580300f085404d240024480c1810514010050000281c2c1c0000e40c2c00081c51070b041801a02c158546a03010081d22007014003202c0011300f1503050000000c0d0035640002c1c1408440c1c004d44500a5075565200c003481031102c400d40b07018001828002195840d080b008181c000c16001d924002d1148906000c00350410425641c121340343e12542508544030b40050f035110201c0c0312650442c6101e01100c02d0181200607005001c0c07502584400036030b0341614030307019a00d043c10a00707580d102c49000c020040542c0700400c040b0311644641c50b0041e0b481d20000c0014003405025001640d000030000c800404100d101d00065040e55000c0d00c070702050f0780c01084c280c40c140c4021669035a540e04280851 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 630569433 1250 630568183 630568193
    0x130b07030f1101090b0408070318080c091513060806010b13120f0b01080304060f0906081f08150402030606040b0a1221121514190905040308090f19 65
    0x1101c0300c01c01c00072400e4500d0351070f0b0205c4840155401d860300000010120101500a04103240ca40d0011058121061500a0140c2c40302111002140584c4050340001c0103044002d02844002c0801048200014030000100c0d00906c4107020b4070380e2a100b400004501000844203492600880031414000750b400e020070450803030030740001100c0c010700c15102d0000103040c0d4600d441c00f801c4420001c5450b6840c2590040c6212481481d00b02030000d80201030225580c04070040e641300582e604800c032006041c0701c0e0340545034481c1d8061030250040c0a84044d40d200000c00243c01540201c045510545808040000b128501c00b2026881400c02e4030030001880701c1c42240c2c0b0010b000701c0000d414200b8061841c0308030405100030b1800211742d040e1851001d000307031140d2140100d4042e203d00c0600d0812410140c0c0801c10700c0391500c118420303100c500c0c1e01102220010090481210240400d05003440c001e810460290394039510303401040701002920400286480203541d040241e41811415a111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 630570683 1250 630569433 630569447
    0x50118050d050c09070f080c030c04030303021e0d061d01120f05100507081e07090603020d06030507060e13020c030a050307051e032706010626010b130b07030f 70
    0x1c111002d000c2c031032207506a81c4e245000710f4402d50346611031007a0a07200d180018040c4c840180301d003030910014000e100140d1902d400356010b0b203030306050041ea1880c925002ca9402c070403a05232603d404034001607a841c1010303503421940817281880000312200101c0880000520024010410307400c082003039141c0425404401858000c0c0200241c0f0741881081100030301765a8100c404030003003a007800500603100c1401080303400c0d5035210f9203014402d003881c0000828000c0079224207820540c000c40c0d0301c030301000780740e011200a550050881d000282c0d035640103080e00940c008050b05c01c4085a40300c0031544d842d4003c0380d4201800c4009142b600420b5981602c0716080641100d040190134040980c0402041805421441c4504000c503107034030f030050182002801d0000c20b08010300328503004060300031000070164152501c1d070030504807602d10344620792071048400d0300d042c8040500400004803042c43c1d070024000304220b030351510001a200c10448286200300040140000d450001070b0300c0491007619 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 630571933 1250 630570683 630570709
    0x6090f010f0e0d080709030c1401080901020306030d03050601050d0e1b01020d080601230d050a0c0318020f030a12120c03023a09031706030c0d06051017010c02060105011805 76
    0x10075000403926500c8d14003101c4002e800c01000e0340c2c204c900d850810b40c4c0210540c0da0000c2600002d505c3c510300100406e840d840740d03040c000c00b80f50b250030114007180e0040c810340e95500d01803c010042c1c51012090a1b9503060041c00074507500003105c1039020154070100300e881440400b40c0710b0301401d4650100440b100d0000000004070030981503150051000c00341c000307202a105402000ca40d50401000c804219801701213080141445c014003003000c6d502d032403c1e4060143e011a101d40368024020b01180c20201000e100606440003000030703441d42c64100380361500f1400b00560400840700f0801e8150200d110311001c82581c0b08140491280c03283d200040900100d00144181ca105864038680300c0645141c49000c401051105154405007607040401c00e0b88800120000c00c1044803510210b00f24000d0031f00d019203916101c000084141d11058011001007040300d00031a049809400b0f0540248220301c1d4050045c0607105c00050258490306481070503c0c0780c0b05000500c2c901e0070040050000c180d02d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 630573183 1250 630571933 630571937
    0x3041206050f09160303050c01090f151118011b0f05070f050406030c090917031905060406050a0302120f1b10111902010e150903150702150a09020306090f010f0e0d0807 74
    0x24a40000526450420310160701c0cc035500107000108400040941d2a003108d90314042900348001d4100590407040d03107404d0142824000074090b41c070200d82a0640300f0310b0002d01203259040300b040400030009507400440e1100009004442e031590f041105a8420784005031a13003006c00428018851264401c080f960306c11742054103412119001c45042e078008072210080350303141c01c403003006468507805065030002048400300301c15070901000955039006400007078000c1d289107001090300c0104103c8014694819000c4400c0b40740481e00c20305007281c1241c0002d0145074460980540700d4065518080c043c50460003a0043c22052401604034141d81f506c00c0e03040041001c890304280d11519210509503440d000f000d40d07111302103014145042c0840384407500c1c8141540070005101d03404100030714040b4003c1200d00641d100c2d02108006001c944a019505001e110144499420000703207102004005000a00c80c8441c2e41e54404103c48902c000004250854200e5138007503449010900c2c4e021080d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 630574433 1250 630573183 630573191
    0x24030b012d0306080309030d03152714040507063203071404211112060702070f030201120c1808010b0102011b0e1203041206050f09160303050c01 64
    0x1400e2900001c8500003920315404082004009800d5414007810001c1c14400b00110301d0050100f002c00e994450b0340d8564030404d603032002c400c180c40d03250f007054400034006c842c020354007141e00300328036418100c0e4565845a00c900d0050003448072202c40e0805403003190028064030680380b4003002502c0c00d98202c0002d0a50360341c0203900c20100d0741c0040400015040d40c079000c170b440e880c0000340603040e000f0782c550751880004248010801115400143c04040c2030501e803540b01c040f000e141407407540c9070000701641e000460403600c40201d4800a1240e00c20300c419821566401c0d905c841c6500c51702c5483c00060700203032160500040561158022140040d4503103800000a2008014a00358030a10380200f0450f035140e10a15a403980d0901031000203000d50124902642e00c1c0340d2000e40352914600800380120b00111000400b07070000d0040d200103086008114220100c12b107070800003041c0441d148200307507040e000428000c940010b4401c900e0780c04080114021820b40d10162090740110400c08200d64031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 630575539 1106 630574433 630574457
    0xc0f04030f173a060e06040b06180402090f0405090a03090e06012010021309140f040b040f120503090c09090d0c02010e09010f08060124030b01 63
    0x8100c08100c002c075443e0f2411041d40c5003140240704054a0140001210700d20490010310407042100c04210340e51811041040f14080d00703c0a0407401460403d040a5041035801801703a00b41c014541400005650002070540b5411150549103800101236202059008a61540544112511440f4624020000915000f000050150000b407100d0b01c011140000340401d5100e03c03041802550703503000450407655503026601c00d10890910f45800b08000f0000c21a0040c02034150708000c02c6c25403200d40303031a0800500a4019500b0904641c100c0380080c1480010000400032a1940d540302d1800341d0115080c50040c002040c00b0309c4040d81006052400400c02005811050a002982c20b10701e0004a8403038000849040d0081c070204001326a2030900354040048400d444200c0c1c1a0b41e03260560201140d800300181c042180303420017206941400303070f08141003014040c074250107240300b = true := by decide +kernel

theorem cover : BRFrame.Cov 630395683 630575539 := by
  have h0 := BRFrame.cov_init 630395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 630395683 ≤ n) (h2 : n < 630575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
