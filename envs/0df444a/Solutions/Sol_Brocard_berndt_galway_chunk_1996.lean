-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1996
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:53.538296+00:00
-- url     : https://prove2.me/submissions/6741a6f1-0850-4420-bc45-485d8038096a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 358812949 ≤ n < 358992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 358814199 1250 358812949 358812953
    0xd0b010b0a0e0103020702032e020301080109020a060507111504030b070306050a06091a13031401060918020d0212030409020d021e120103030804020a050d0b0a0501090c0e190b0a0c 79
    0x710398410b002801c096041c5101d07500003a8440210b02c00142c843c0700c1139a80890310182c00c80080541e9525020115200d50310f4010b00c41c000e004a040807806600c50400c081038090040d0140e9041d56485000c1001d1440c8000911905000d01100400d00120500c00800001c01038030005200c1c03039007542d00140303c0d0721308400c21102d0f1a15a0005091000d444428001c00a09015400140788400c00041e550011030001d0b400c00f20040d0b201600c10154140c1d008400741d01900048103d41c0d14886c00d000c01c2c940c15200b80d0341c410301c1020080d8400c0c01c229601c0010304204094018040106040d2030406640384060000e9a0008400703007802d6500107111414030881c4040f1486001c015402507080401c041d1060300720304010302000d02032000b050005011580d8160b2800c01411014001240b1324100b0300d8100314000040c0c8502007494208000481c440b015841074a840d440c0341d035200c8001d40034013000d00c00d0160441005050032100c416011a80e24001d0000304000803035aa54408215001c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 358815449 1250 358814199 358814207
    0x150b030406020d050c0a27260d140306040903030905030d092f01050711061c0b121009050307020312130f0b18040902040f051504020c0d0305060d0b010b0a 68
    0x5003a410441801c0c41003c0350194050109108442034081c01c9160340740d1083c01d0700c0222165408208c051010110f80010344030310806c45010725000303000f2500d040c1d00419040e0b840c192142145070720080b060000071842c0c50541c006d0407807140a41800210b1a07410b48510f41582c0c80101000c0120f0f032600d41e88400c01605841801703075000c072810440c0c1000d20303030640d404003030449040d0b8504120004c207602007800482800f400300000004d15182e81c510b0002200366680007580c1150601c41c4c940480c0c0c0006042c20341c02032040c683d0802c0940480300354182440020007070300e4000d0301c16200c14803a500041e1020440c00108282120740380380c41d0070600000090802941c0c2040795452401107013040040400c000703072341c200414050034112050054011034024090741c80041d50007400c2084d06901c400f010341c41180510201e82c911031034201b400e028801648030b0072090000355800f00011004841c4a40d00060f04940000c000c107013000301540360178030455002c4e00301403070b200320000301c80c1b040c44e0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 358816699 1250 358815449 358815451
    0xc0606090c09050303090d0605060112020a03050a1112010608070c080f04051c111005072a0506181302040b0c1b011b030c050c1e03060709030b010306150b030406020d05 74
    0x1044005606e00303040c89020543c203007401f800003417940f41c031500440d01d00d1b030041c1815414480d001004640756489104000c01070f14007500e484003403e14004503854600342100c02ca4000c824006080742a59203000c00c21030320040010140410041501030078000601c9000040003500b03100f501c92502e80d0b0520701007107180700c0d0081e052900740b0700401000d4006400c40780e81500d803010031502c0051181c1c040c681079486118900c00141540c1d030319105000c0440c4101a407090301c004044c03820040329112000c0c0000f5210700f0700702640003200d04041451031b14108a0221003081c8426000d808e103562581500580d4228449903150340d00404042c3d12100c06a51180010f50f90901e4100540541248507095000d04041c024041010f24001c803402d00004005200241d04003800301c44046683e40320400c50003410741c60140c800c2c042c98012450541c2301d42d0690050341e401c200007c0f0140d1841da00c417030082400c0c481000a0140350840000c58003181d1021310303c9180108805a501c5844440c0c1600f243c0d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 358817949 1250 358816699 358816709
    0x906060506040f0911130321050c071e09020a0f110c0117090114070e0111010c02030f0a170f0108300c120301320609100c0606090c09 59
    0x802d0004000104850000764101c2d850b800340000c41950b980d484071540c0c840c04011a0149414000000030050b0041c000301e800516401c02c00507542c00140210303214444d4007003414065111510601681d040d0f48a484a468030010006100960368208102a42c11403026800480c858140b126505a0401402c02e18101c0300009090501c2080c00060007100c203c0c080604a41d46150005503000400d500c558280030308010200518903140130024001e118135000e8600107082c7c55900c0300f9a4070140211b05071142c00b5000f450030000034620100362504109130b100b003080580203458401080c1d11079854010010710111071019030402e140c0624040e02ea20304c15640c00c80c0b1055051501c8a4401c03e0500841c80c0c0c410169245481309000f480c0200d044003003582018004000240341410300b154903201400382e0841291014452001d044038102c080d5100e40010040298076520b1518a0a0001c1481d0354104407100c078030305840f10b9080b1142c0742c0203820421760300c840d14825603810101d0800102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 358819199 1250 358817949 358817959
    0x7080d05070210030b040b0301091202160f0e060105211017071a0405090112020306010f0b16140109030908071e090b04020903100207020901050607030503190f0f09060605 75
    0x40c0c0c0e81c0c1c082165541c1181c040e40030180d5404c5185e070381c0c2e505c076003062903071505c018000e2003000801d081910b40f000c0003e40c14000341c4a03100100c911241d00c1c051010844682140c0c04990340c0c5403001400c1080d9004041d1410010200034884041c400c1070350a1010314081d0b0310481d46403500f0750720300c00411a00d801030010454000d0140b440d4040001c0c01009990101213410501101c098112070580200c0d00181d52041d0010700220750740000103d5410709500840c2112113036640c07054808413000072801b4800320800f0070006c0c0000380e410007a900c2d080c0e9205801e1040700c401540b90351421100900e200b200000e28020003001950b500304840302c09411600c582040000080c03202014040c66032041d114060381f00e1440700c1440c0d80e6581036a603e91800740a40e1400306840441600941c01000200d01c46e1800d00000310b5141403282c140c4144590644502c0c2c5142ca89030072070002140c00c9200c4100d041d49135400304007070892901408115080c908400300d860803c900d0a88240e03001d9811060080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 358820449 1250 358819199 358819207
    0x60212030c0a180803070803040b010510080a0903180e04120201020c100e0a020303070830060607020316090f0f020f04030f030504050418031b02011d1f0207080d05 72
    0x214581c80e040341c50300310300d5003804101d08003030060b40c41c3c401d4041c1c0e10a4a05001c04944031041c000c2c0280114031541c800e100e42c3d14280e880f030041040288054149000060008000800030603c6511240b1782500908141e1603400420380d0031120000150080c044200e0b68400740010807201c9600c42c44005540c1c0025400c043c80158443d5481888501c1980020b454140c408801c44040c407110704020b4010f01500c2e9240500c0c1000e82c0243c5c40b8183e03a0174040618414808415032642006a2000444585c400700c0d4884070304006440e0805401139a040c0102050140c010360b1f0851a02d00400b55004046149254081c1c524100d070030303038030100c5400d0380104410300c01a08a5000c481c01c1e0399022314040e22120040c203044509020f1504096001885c3c090074015040d045540c540700c3c0c610947d280181d0343c406511030b0010741909107000703020071081d504019261001280c5586c41c44000307041c2044c2e2040080060110003445207846001da00500c40030321801906001824840501d81802858 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 358821699 1250 358820449 358820461
    0x309080c0315060105070305040807062a1101030b061c0b01030e1204050d1e05100c020a17090301091505040201080601020703030c0308060406153203010e0a0e060103050706021203 79
    0x74842c00100118100000050a07204050040d41620080c0191400b20703492192038580c0a805601000400e00443d0a41000303100396200207814010055400f00c4100300c3ca2030440c0c01540030b0921010320b0303540104140300b944e010207000b50350300c251011200b50105164140c940050300b101ca0f015040031aa40103043e001d45030441481c111400c90348150750311106020513040c03010101031140c0d505c5003c980c1848802c828401d00148448016034195820051007000b11810380e0360b1642030701d00070030401c840b078581d5101202160161104001c090700100d5880f809541b10300900008030620307800755580f08140400c1d0350384003000d80c0d0300560a000800441c9e08503140034244c8042558024204070084000070341d02c4d00c590300309000602900f108140001e1040700c028011072604005c4040483c000f481c043e0040c400c000d0030311007070055082214a143d09102070a0104280146450340320350b10360840d20201c1c1d000304102d0b0300a50080019050581c142100281096440c02111940403024014010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 358822949 1250 358821699 358821733
    0x40501021506030307212606010c1b0b0c0705220225061407081e0c0421141f091a01080309210c061b030301030309080c03 54
    0x140d0008103081805692040b00003842c61003407000050110600b0032031700061981d580650007800d1034541341c944c0004604641c4400030f0450f005000b01d4501010040313141540919020854180a04a42d011032807600e002d02080079907075032005a00c41b100003620b1800300307824410000a02804c031103550141c1203603441411905c010000360300e1080c0e800103040100c484a0040d654855426103c103d00b01c3c41141000801008440da024800c4d0420780c000501c4148a491030a11825120f034030381d82c0101155a010a15840040c82000b0082e0200004521810070070880340400e10514020158280030380f414208041f051003c8003c581d10030404005491000000241028655840016030b003a103410020b01020020800c07246003400e40c1c001040015000c80100901d500c01d50f40b1035201d01ea681d070780003480d000140c91410150802c9110704428075000300100a0b040d090030303480e030b13a60030060305060440c0d02c2a4012000703d4107003002009071007424407210112003801c6010345000c00345449604 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 358824199 1250 358822949 358822963
    0x8070b0903070612020c07060806040e0105060a180f020408031908010501120504060b0904061a0102030705030d02031803040f03022b12140313030912051c030905011401030b010b04050102 82
    0x1344013443d11059081a1141d0560b040c0c140d00e00101e40c1d16680ea6000641000411b0f510540034504103541840810310501505004101c06803078070711142d14040702d13407810b001c0d108035401d40e07203480d506d10031000b0420380090000750602c2c0000e103544080202c03135008000006400b0b03d040c041d42000420031680c02030b0011903540b11140d0701040b155207500d00f51000f4020082e00f10ba0100010092200b4841e159210020200040321701c891140401001a03030389008006000344607510400c107165640290390095a000003803108901c41014000203194210f411640051080b0240c1d01000c20079480d00c15105003e0030400c0d01c3c034001c04044500c0304251201c0c4480050601407400002491161143c9083c03501b0a01031400300c0d072a0f080413841d40d0003010b148401580000c000507000708810b84011008801154800c009100c4211600301e40145040ea01400000f8103a40e0b480c5103002c06c02c00e0103038808445c0181d060000a605618000c0c540c000181c01101d0180000e0000b4080343e42c00107068 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 358825449 1250 358824199 358824209
    0x6170606180106082a07060b0a1d04080912070b0d060509042f0a030f0b0702060c0a0c02130c02030a02070611071a070f050a120e100503070c05120408070b090307 71
    0x3504017507451081c500c0141035a200c0d550342c09400046007024041107a001400d5154204c495411240d603a05940c5244044140c0e04181280d1000105001494541c0204688074010702250300c04060b0a1030f49090110035031041c1ca85980c0040d0018039144c070351040e500945001c4071201500d050a4860440002c0400410202540c0700c0c00743c40e62600000f03100f4001003c0007095080001d40f00e10b45130400903004182141c010301d40e100841c40103400031484130300c00c2e6002c0c44100d04244002404840009200c1d50a907040595640440c11102c854000d0070711266054005544c1d03070401c41380080c0742003000d604c11420444111607105401a0100740002181d0340c000101035101a0748025807654400c1e808010811b4107400404c01c204a804208208002e001e03c080100d10940c403041a12003090000c04158418040013040001d00c1c025806160440d0007864003210359140d90395a107190070849500c000c00c2c5d02022404101c883c0d800c000c120050016440001e0501d152400401d43d5003a15000b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 358826699 1250 358825449 358825471
    0x309090603170d06081f0609060e06130f050a14060f0306150303040503010903030e15010806070f0318061a030a080a050304050f070905060406080a20040617060618010608 75
    0x720140004040d01310601508525083d9801c0140c402c50400214803e100c5c4090410308090001601110700c0c13090504075aa400684c280c141d0b910420002100511024807840c03541d01d2414a040070700c1803140c81d124040c05140040c803c41003d141b2300d082e0070000c25040c41500c4100385004c0645012139080c0d00003010b41c40008480002e03a00090a40c05a40c01140d095880c0460510034540d040d00560030b610f20050607584801404099032441c001d00740101c80150b030020020070b0402d80b080808417605141850300050f00000245c602404440c650000d4587c1d41d1288001410016446100030610500301c0003412008503503559060180039040d4520144080403001030184801805100c1444440c0010303901200d4555011100600d010380e25a4000c600c0d01700e0201e041c24002990690040d080781000b035401d031716490b04800d0080c801c21039540007a1510340002d400041c0700c002030704150170640030b445c9074070340041400b44070758601c4410b05404c140342c00100034880c1c010307509542041e0741ca09 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 358827949 1250 358826699 358826707
    0xa03120521060f040e0f030d0203100e1312090302180109110703021b0d0f060212060f09061e030d02060123010f050a05040308030c0714071d04050c03011404030909060317 75
    0xa03441d0a01289031390502c211f0100003030b25a12240d2540c001c0d44942c42d22a2b04c59442030f11070500c0c419058040348e80d103040146020300c081c04503030000c5141e01c941c2168500580440c0c0c0b65800704980f0142c0c0d1200349040c406001c0140640070143c050804c041c406082440e0401c4c0c0c02c1c0e20001d50b03501d00030340c070f59201001c410701e1101c2d1601c03030109549601d900200d10442c144802e01d0410005d60100b00351550710742809000c604503141424817005003280c000c0180312a5118401048511054050854001c40d030301031076224251401d0058000161454003d800c3c1980352800410010444c0b54400315905280e0744107060030b80e04038401003050042d924000380c95040d40310040e42c05104a40010309406808001c00c07508601e82c00013003c01d548906060006450440c10541d551f920038003038008509250485414407040902065600c50300074001c8800d03649440d00424212501061ba80b09109070314000c01041c0f64000c42150700414580104212440c555141d001c42d40e181d01d00085d580d80c0c0001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 358829199 1250 358827949 358827971
    0x60f150b07061d03030109060f180218030f0c01021002040e010b030403020c180403020c0901031101030902010509040c0c0219050303070803040f1202030c01060b040f0b090a03120521060f04 83
    0x58400c070448004010601c541d00105030f6100e60726042403207802c24240c1880c0002c941446031019080c00c8540711440c00030040070035001d040c040e4200700f043c8480802c0c209071071401940d0801040c01c42050010143c03a50802500c0028201612100c599420314010482004000c007000415411034288440e496101e813100e18040b8200f444c1104410780c0000003450468840d81c00340803c9000b180300e9021544052032903014020310072401d21015062400d40b09415405500035040445054030515095160400740c40004080754800742c0441d00051705030910f041141402500c58002c42c40000c4402041031928000958904c0b030964010b10ba0b240120202c1c0402c0200714131503002540c01910900c00c4e00040300001d44c0c07900000540303102c0398282a400506501c42204a80649200f140904007503800c005090142c3c0d80b19210741e41e08120011400408a40454003046201d001350b0b0f201540c40c01180709020700c021001e40031480c0c1d00380c041d09001060b980c0c264141039284068a02044840c008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 358830449 1250 358829199 358829201
    0x8030f0d05091011031909151a03030316080c040b0703140c0d170a0b090c07031106130314032a040b0d050a050906070f1413030f060f150b0706 63
    0x8140c3c0f82000f030500d100c0e903c5090703241001c0c0d8030030b01c600c00c40007242070011150041034030160500a000344d900350101d00c454941a801c10070001c651002507480340c0c000000400c0c035507801140c031444041291211600406e0380484d07810703005440040e0781400c1608200403a071003886055001400c0c02081d8180e80030000c408415241180e2101090f1070007507000b05c102800b4680080c00200f10102c01c0700003e50402c01a110b070020048000e08445c950741d507005503101d071582c0705400039000d0120000c4260840c810401c90306200301e400e144c3e8075100360345602c2c010b00614840301c030f804448079081c01005490301c00c0c0a00440a240035035016500d150641140c1e43c9148150740002c0300390140026a11848881c40e00581d006090140c01041560346d04440180c03224815904000051041e14034428068850000f000116120460b401e283c45000c0c40c2c40301d40002e807584211141c00d84103550200b03004044c0314800c08042c00c540140210400c025071800c84010714000c100c80000b01103125020f024007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 358831699 1250 358830449 358830463
    0xf01110a080c0309191a01050108010b0403030c021504120b01090516030b040b040c02150f090a0f0c090501030308041214300c040302100207060503070813020d120908030f0d0509 78
    0x51003a0f90f05098803900b0540122580c007501c4000403941800002149c0d4031901e00340c0d04070791794480800c1c105800d40e41d080b5054074440741d090760300844171140c09500724400d000800082200050215144d01030b480c1000941205901900c5224074000070004080c0060f540300405007003030724000489143d050002002000e001603a00d402515102481d4461074000420000041008040040f40c1c1e81d29590b500e442d80040300e1581c860381040d0026400221142c0c1d491075441c0c401c0c4000244107413188203078403c6074404d83c000e5001898000c107002c00e2002080402010381118508200500b80c0d240400d107040c0305415500040104400c240030f882c610f1100d4624520903140030452480c10048500d0700240c00600081e840340808a940e210014000203a22003211500c1d00c80ba429551032500c180e0311000f00420031105a24201c0003140140c0c1c489000603903040c49030174500c100110401c4020040c0c42c0ca074001c07005075071003000000d410380008400c4d00c1c05a140400040303103d41e24040c0b06810149 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 358832949 1250 358831699 358831723
    0x3050603030d09320a1712040305031806040b01050f03030708030a09051c0c020112380a030b011203020f19030e010e010507060b0a05060c0f01110a080c0309 69
    0x803400030070104120302c001d950300140b00100030001c119003000c9000304540e106041c2c491340c21342c0802d440780001503214401034145400b0001441c1000c003000c3c900d41c0e5100b8200d038201c0004100000704000404c1210000050040c0c07803004201610f030560f1341c0d02982c00180510b601c6518540744240c1c01d6a402c20071511081d0f4041a031544a0a0207800d01d0090b05d03d880d402c40d16400741640c840360442c107008014100301d0003035550182d400c200e9001564140c0b480421007910740e0312031000040728030310b4600354041520708031501c1c2d07a1140c00c214800d9070519000c000ea4881c1e040503004201241e080e04200341035400b10900012101d4048c5000e0f1f10700101034019118500844880384070540c0d10880d440c0c80c0a02944401904400c1e6100458007103000d010b006000c40c0090101c0c00108820750301c102c10054018180103415619100001c1054001c2200280b4950050a1403c1603010a004810700301c0d000b01712507810810b02d200054100340c00101000300e4008040005a0b460804000d0340307003c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 358834199 1250 358832949 358832951
    0xa0b0a0b0414060f19171e151915022a13020301080309040b240d090203071e09180f020d230705040b090c0a0233090d0906050901021e0105041505040f0303050603030d 73
    0x2041e0342700520a9900345108070072081c0005104005054000f088185030b580410810a4140c0005d8081685042e80c503600507420401d0904181504610303880194040c04026000f10b4540169a040102741d0314005900f900840155034240301c034079540c6032070780c001000b5500d0300c0d40c03554042240740c1c0061440c07040c041d505100d540700c0040d100d101e031046002c0c018013141a4054030740d2210040d8042d82c041c0016004440d41da00203600104026102219a403440203199614083d900d0320780804074125401310b092031400030f0034001c50000c4d0410034000200000c0c0c4041c00396104110005410000090900c1c840c4507000480710b01062003070242c1e9200500c075000000d01021401203a80d640b41c448180105100070000100b201600c0001d180942d00906035202e040c11811b15004461710b41040742c0050662140c001441c5400b000c1d10854080b0421010000606203080e05010400001040001424510b820103100110b5140342416007010740508010403c0e48459010a2451050613100f1700e0007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 358835449 1250 358834199 358834219
    0x60c170f030609090f0715180602011d01050f0a0b12010204080c1c150c0905060304060b01081b030f040f05010c080a0b0a0b0414060f19171e15 63
    0xc402403014600070041941e58010741da450401660740c0b112480a61800c541c05942c007040408a80300d440b8100414501d045080000280f60340030101016420000150351074080f0820380b043c00d04c016458505070305009101a050996090600d41d0018100350480c684441c4403100c183c8640070002c00040c22080215607a43d0780c1e411072074030f40350850501441080356041a40300c00c018a201071761510741111920007034540c02d10300d8170700030410400e004003072284810340014190381e002e01451080c1e014140109000c2030f800001421184002c040300b103045001182640b001003251b05030307a4800c81c0260114929221824503547c1e101a040d40148190b083c440c1781079420764440d207442c0c0906002c035010b2182c5a4040104110402140074800e142131050000b0002c1c0c901c104140006080301411251620000141d108095400030711095108115158641802e40d0f001c0100425003101004038003260800341080ea000e0f55000028003022070004000c2a45000c0080b44c0340380d801c000400c94480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 358836699 1250 358835449 358835467
    0x5030307121103071e090906060801090c020105190911041109040b0f0d0308060d0c170c0301020310051003060504020c070501120903080402010f020a050604060501090c11030301060c17 81
    0x8025100e52450322801c0c45460102c040710201900d029022075140c0901000455070000c1040020805e00c0c8104040c901c0000740581c110302c00c1801401250350f4400c50380d810401040203a0300c030381020030308580c540300801c691480103140c2d0762417484050501041c100070303e091242850000d4416030390b000d031602119440e0001010b0040003014415901031080c0502641003100031001c0d04201c940106a204050300001c2c8194101d69000c5002464808015059196840b21117415000702010803503c0100345030b0341d9010040d01c040520210029495850850000408a04203115031401051219a2050541c3c0690401d901412010740119241c0310050000d0b07985441520a240c04525541da203007045102c103004400c081501500d0345407058a070b940c01150400310a1999000b18094a07401400040c003d101540c0103c3c0140404103065040c01c1202c4202e510360140f803020f020728a800380c000000c0200640c0d04542080c00e020194240c0c904004c8030452503800c100d6003042c400101685 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 358837949 1250 358836699 358836707
    0xd0b0127030f1401050c21060306010501180b040b0c0f0105130201030c02010e1c031a0f06131d221a1003050a080408010b0109080a06110903060709030201120c091a0705030307 77
    0x242100b82c0301d1f800c078041010a441009180000d88240b90185c00590060040e0750056031020320fa1324090b060105400e59400174820320b9003198000744802e0000040c02224040c0800403400062a500000c0020303040450741c40750a40c0c043c0c040207042c1501c8088080348507000398010444505210180c03041c0382119440c1a0340d20103c1030044020030b141c11407003415106a00c0202c0c25a48010b001000d00d075561904021403134103c0801e840c0300c551f500d070f4085034850030b210b440440c0c0d059004030300c5002c2c201941d514001d50620962410b102001011900c040b8076110711105183c01040958121a2211201181c0c10340b9182c101034271768480c10b840f081c20400320300b00030800c81c1c22240003005000b062600444090109110302c5049030300c502c0c07281010500c0d075400f0120601190060300d00d4141c1140100e0f040c0503045072540c0104120b80c50420541d43c000e8041c207802d113107065040003241d61103000030742199030364000c4000d807a642d0044c44c9a0100d0000440d010190010100c030303181e01d0504c500030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 358839199 1250 358837949 358837957
    0x1409030f0c03100b01020c04150b0a05070b0106050a020a110301180c0e1501050d0c020106090e15010b0306060d230c0c0f0312060d0204060b0d0b0127030f1401050c 72
    0x140030f0301c1022a8071001c2d40c0a032084121501c4160302806104a07030604010203403102e80c400c84440044400005003114552000300184c080c1c41c0c030f9007034442a050800507480300c41640048140102040100001c55011602d412000d5003c9074542080720560042401001c592040c408035900c4c012a85050003090301c0100100c4210a030390070301c0b556441000d00c1020880a120303e000c981c0c14400c45101400940141d404082e251000142c1940d5603074040c3c09458140c0325404842d04030f40000c0c125002740c0c080e401c0c058442181024650700b8034001180142c8220420702c80b4055603208201d014000090000220340e540d10300c808094140298803400340d0740851280b8003144a50a40c800000300088240d900100a030121450b030780d5541c80a02c001a40100c20803680305070740d058042405c12040c8042c3c09075003441c070000118902c90200240840103000840855401c41c030704c83d08910040c03c80c0c00c1d4141c0340d001040c1c0b10888042e14010019025810b021341481d402d01c0108030560600308060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 358840449 1250 358839199 358839223
    0x5011403010b100504060c03141305030c04151404090f0c0503070e0105060f03060609100f030b2d030f0706030504030e0409170309030403020a0305031809100302011409030f 76
    0x82080705440c90401100d04a40e40f240300c00703d10240010070449004101d81602903000307003091b140c1d403680b8079101103142d4080d13006107102a035501018802c41c1020042c601e0b00f10000c0d1010040c901500201503c3d00311b0b280728400d000400c04042000d9a11580c100081456118101c3c8a10307190f907241c0b484200100d8091180248110b01000a0f842c00c06110541290700140015291100d0311002d99503540c070080c08550800c00c04c100e80d10258651031602001e50100d681c8045109056000c002d040d1400401800e00c161904407400304981260480071541e000c0c580740303c00781e44a0381400300341454450040d64606004000d40020030540540025206500c43d030f403040d84e00070482d81003004480e20b0b06000360821080d01c0b6030311416900d18000755080007080046a06299890303000403030b4022580c10807140ba402c0400c01910f01d500c1c0000301c503075403042110030404525011000c2c5038041d90720f101c06810010501c0000d82d5100c0c004046507a03038900501038a00c80d94131080b0290b0f84815803864 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 358841699 1250 358840449 358840451
    0x30f02030606011d0904210206010609060207180507170103080301030606050402070819023301090e0a03140d0507030c27060e06040e0709080d050906030f040c090501140301 76
    0x140302c0d58030072400b0056209401140300d00a11901c01030112842d0001e00c22107454034103070002c1601088000200044099030780c01000d1643c10304a005242d1000c0c0d62101c401c2d544100400e0000c1d010813546894201100080000d00d1f5581c5603088900d40c46540640b007a02c4207050000c01441035a000440c1624012841032001d15650b20a2104920030300700d025000700710034042c0107082c41c10150000280c0d101841118403000006400e080380d200313148091845000c036050b0708003058080c41249401801c51140401000702c0c1e640143d921000180001410016100c040180348201c80041c0c44140121410420192038000b01c0030b002801c2d070440c441d0104501d2200711588081c040846800b50045880c10a402d624040c0f0a451030344146c0701c01a403185052102041c05104c54824070b11400641d619079603424078011074282041c10043d5640100708040161000a0f21740b0350443c0d8020050b4284e4008a41d05e60509114415984d0001c52082e814030000050044909600242510040300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 358842949 1250 358841699 358841701
    0xc010e030703090e060f12030702010e0a03020307180603150902130b240c1519050f0708040203010207120203090a0f0302031e03070b16030f020c0c21030301030f020306 74
    0x681603900e00a031003000300003c010660902403602111300c000e030041d2000d0028a500030900e8001642c0240e0914680c04d02e60021a4680966901c0200c071a0322003000d4030b200c0c204074115000700303441e01ca40303009000c3c4000310050651011000399101e00700542d008044d0034601d40310740300400082c1545410680c4205600c0f4010520078855125041d4070032001010781504401c684941840500c0300344035070302111300a1103004200403061044081503d0020304500710383c80c1050070412040e8160001130612403401081000b100c1c2c03400061600101c442c03c1ca03507040c0d41e4a100007800b900c81c98900800e140d522080403004641c0010141484401c111900012952100c1d24500402980d20019602d50312a200e141644003403d4158245042031405407481c00d019910b030280e0440040c0d03103002003141d51100140c507280e454866075101c484d03829019031601e941506200c0d174503200c4012840c811415564600c2034210300b0400c060b400c400200c2507e0701c03981d40342801c1d140d01e51101d41c140d00900840c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 358844199 1250 358842949 358842971
    0x1060e0606091008061c210f080114120f06090c10080f0601260604140106201e030c0106080a020307034206081606030519110c01 57
    0x24040c0d519074440541000b50364600d0705000c1300c503248081c00d580d401486406e900030700c0f0141004601c01082c010b4151140d4000203000ca44040e04c80000d140e0300f000f1210f03100851050b40040d4160444148003015417aa640f46400110900c2c44c5c000402414820f08003209110a030200c0e01512800185042d04c0c0c580942d0401c1c8135501041c080c4503000039110307a000444500d00038035001e030801c01c10324003400b402c2c44c00c62011040f09054600c0d0250390783e10608000c45841d00e4041c140d04002d041c1000c5800e540340406c042c150300c466008030303420700304564a507e14000b4200041040035070f44491510091045e003120540725808803075a00890b500744400031480d401c001504655495000e8000c1800b180340d500d450041e40f925020886c18a090303801030070028986004143c50222010542c0121586000c1c2c2070406c0301c06542c06819190800c1d206a4060072195191508469071030801040d43d5868103c03131549814103110051905290002002507110f20b4005003800c0360741c0c2402000000141c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 358845449 1250 358844199 358844209
    0x309090c0f083610020f03040c0b1206060901120507091a040609061d03031c0b120607030e0102090a1d15031209041e050910020c0604030c0c0806070201060e06 70
    0x301440540707041e5000e400102800c110100e56141c854079105856804c040c0d0002c800aa0744505010302c280d21020042c441405030b07001d98403004100c0c000c1050710382406400c0c00c4c0c1e503444000707001c544106d00120b03441c3d036a640100c050710328540c44030104010910381380070f02a04140d1107003d081c0302c3e07000d94448441c1d03003824a000c0794240c82454444040c0d0f03030300e0408111804d449003c110304004450312807103d05500c0410142c4004603031002010b64480340000c1d100e084440c19141075201792050001c242c005130000c40d955070400503a190100365031200e04d00640c06403085945141c5c01007040b800005516055642c1103110004030039418403240c40705550707507140708988110f81c0d034550001880403000a207120001e280041c0e001e800410110010609007400b4460384106180d025164000c2102200d07050000c07141c01e5124180460500207178000e0541d603104018001801d1110480254050080c4041072070014121802120540c1c48d2030710009010b8592403190740c0c4003420200c08034034a8502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 358846699 1250 358845449 358845481
    0xf0509010e1501090504050307050709053102061305030601030b04021008011a0319020a0f030b011407021201140705090f1f0c080f071a0f0f0f040309090c0f08 70
    0x4a5401c21200b0f90030001044010b0801820840d9244400c014640010708203111701c00c02070040c682c0010301480c00c0760003032207204004a40754818000d4095110603500d021220601401e40545000d0b4540c0b1100707291b0701c00f0080326001190300d403148800010400c0030882c98607120320f01c241c0e8240c181c5440c008040e01d400c0710a00070940c20007501845112160040c0c80035650040000b001d02c8204031300403040c80126413019102400048921420640a40d0140591185c940382860704280d442016501409140590303d00207110300c1c4801088251420250081c00d00d01c601900c402c40e041c1019140608181d01443d210ba0003450100407500c3c882c50803e880080203c20340c09405a600501c010490b520f86509004903040001030050312103135070050026100082c400d442d01d901d00b86c0d00820a0b034841200428256a0a070280d04003d0b101281741d14a540003101e21400300394985580c03500b6901d00711540c11200a0354a010110050150700030f0400e004c080403902c8000590726000c40c40c12031139003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 358847949 1250 358846699 358846723
    0xc0f070504020c07140103090204090302010e160812071b06091406130603090302071e0302010816050a0513080105040b04020f0102010b1c0201140d09030206090a0c0e07050d0f0509010e 81
    0x44008100140103040114030405c0300e051400007038480c017940c00602124000c0c0c00540040c0e5543c074000c0342035401006400e9204c2490b00d1440b441622341055682e07104846240081070401c08140c000030850820112404200b84081841182ea00c5010003005030b04244901c615040300c000d0000caa41c20200200da001035003c00c3c0c24100c483c10302c0800c0e000f410307502e2012001c40c800e590000a51881040e5208500b510a1462074203181c41e40c0001090710901070700600440c41c242c40c041c0711040d0000103c4502e081641021500c40c0c030b480d030391807681d80301d1a400030240d542080c0801040102ca1a02c040c4503500c211014039a450046004908844111002c160810182d0840c861207800040c84010f2261051500d05102e0444c1c94090020741c02200d00d1400345a00c9000140803d81c05025140d4042c00c440e008050030382d00c90f110980e6440c943e10410704c5400c4a00040780580b48030308200c1d01c94049a0409021603011254080020a070494150b60700b5441e025280000000c045403c030761040e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 358849199 1250 358847949 358847953
    0xc1507080702010804020d06060f1a03010f03140f01020a390611040503070305010c0201180308010614090d110a0b0906070605150d0b01060810060f030e01110c0f070504020c 76
    0x600c070b07600545107010701030400d03a4040d042c5908080001c0c0d0f103001d10009014600e021031052890300b401c15400021600e00301c0c00c1128244010b001004500c00548101d075040f003442c40000402002003410100c1142001da125400052001903a98002040304905004159442c0d800000c03130344081c46088170081c08601c20740349003181202040c81170304603040d0120512103c0c2e00d040c1e9a080000d1600130640d01c100c0741039441d10320744091142c0a10079400c0965004c9000280242603a40013845100305029500a1201d0048810b041540c402c058450510b0064415402082141400d08986040304281c0303210b810140004036031000100140e030848038010706198240784c03141d80c4000180400812903000071804200c406c0700c2d1340d40d010800a0103402020380004e554104400107003480750040c0420000c01000030200040d5a1100400042c07801e54030b000990204002003072030242c007002401c521101004a103214803000e01065501c045d28902045580c1a5035440922082c0d01506039130360095 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 358850449 1250 358849199 358849207
    0x207060c030807030915020406021b042f040306060b09030f030c1e0f0601060507060507080403120e01240e06040608070308390607080c03130201090b0304050c150708 73
    0x980203800828100748200010710350706c4000c0b08450101d805c103a0019005a110441c00c1c02d802901940901d0300f03000640d0300740300c0188441207c02a031406d0f0100b0942078005001940c40311139192060703502850340050140041ca6880c1c1c100310964020302c0c1814843e01a2401440e01c500d000404c645113005e9002c0a00780075030403000c440c0100d0342100030b101303180c0c007540080300da411400303010050107002e940d01c3d41074aa030800e050100403504010200d00170b21060000340000300790016001ca1800588941c00706444401c1184540500244110460350001880c0400305500c0454030b000182c448621901c00030343d44420812040e15210320505209070801306c804d10200d4080300c001c0c20401c002d1169503001808400d01d0090314038000303000020721245a002c2d0030701780f0401e00500b60000c00700d2910100c181000030700355080d840003034200340365a055400c8000841e406465100001c101002c0181c0d12490b00f030410ad611600c070280c066120340c4c880c841714025900140c00761180c180e0884101810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 358851699 1250 358850449 358850461
    0x115030b150a050c030d020307020f010c050d1e050a1e150b13120503070303050a050601140d06030213150b03041a0601030b041b03050a0e0c06031f090c0207060c0308 73
    0x4981c03112076070700c0800c1020090811441c4c030410040010080804005039030386000e180081c1400a01c102c401c0180e411b08500d03d503400e602c4020344e0344500241000050318041e84a00d40d8182c400d44294010040c241002c210401e40d65500080550603861204040c15918000c1c1404444429003034400c1040c028005200108080c03016060340c03034200e02841d41390307902c80450714441301245008403072a50001032a40105541400380c640c2202c00b030300c0244841e0030301600280c000b40d814403949010000218005020000c2504404000c5402600c000b80800d5409180c1c8090601c000000109010260b40000c103040035000b120310494100306240c0034228000d00e1a003002c10041c00d014105074a50b45a00310564441c8a90303600d91401010482055084100160684500034a403907a400d180c0704503841402c00c0420305100640003160582d5483d550200d030711074403080d100784481c800c50100c41d000c00c1c100a59070011320105072503000c60f0b5841da40e5400c02c441200321104020001400300002c62a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 358852949 1250 358851699 358851739
    0xf0105030111180d0f1514090307111917160e160309081605010e010c020c0402030406090803040f0309050d080405010318080307020304050f030c010212030a061d0115030b 75
    0x10008000405081d008030885d128501688002c0798282e81031101100814458440c1d4410311100381d001010741c024038540141c4075a124003e255001d0004145071200c0c050956680300d07907108000100022103225a02c40310540e4101500111a8403244203414903000204200c160200440f00391750440d0545a403035252003c90b100004c038010041c1a107038003d07880010b130641c02400107405425441c6500048904215080d607180e0183c1c0b14a5900d050a0b000c0f94590100e8400c078040b40540d005652516145814002400000405001da81c80402480100050300b510707400d10602984d100e040298840d020402d041c0c42e1100d00810401e800c21081101d54000e0300503c101022000c204110300300300340c644010707546c0b0480d24040180c20000d428030071880d0103211000c00c0d8200350000e200b00c2090500103560ba2010300f10405014101000050210083c2e80240020b05060450b14a0010a01300f03134610b010000c0c029110800d210101905009120384202810064010a039880c0c0d05070b107100d616 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 358854199 1250 358852949 358852987
    0x30406050c070909082218092118080c0d0f050c0d03090801060b1309050c04030c090c0e180403080a0212160f0c05120d020409140f0105030111 63
    0x4896010b140000103074202c00f88105200c0e140148081585c80c403000008110203065140c00219200f121581840700c0041d6104c04401400c0f081e100060f03040143c10890030405000c950a100b159000300710010056001060004111200c0c080c50320b101d0302c4008150b19401c40d80c002d180c208002c1240100494804550200700d54010b10658410211a20203d03080f04841c800590106603285400c0080060900c5090004e20028407002e0528040c0305001040901c5842103120f5551900040340c0d81c1c950040455008561110581450325540d0900c075014040002030712010524031000d103e25800e080300002c2c04500300034901f120030390b07555500342c0f1180000760003540140d80c00d10004400e84111034040d03006401d182e0445000010051005004005105123501045403203840301002840000719410103032910301129407201c800a001a00a0140ea4008032400d03003009180400c2c00c4028a09601603200e0701c0c0801d400360b072a84241070990700500c03d01d0011040410101850581c0796100c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 358855449 1250 358854199 358854217
    0x503010e13020d020d111306080606240a0305070f0e010c02010c1e0c0302030601080102090a09050705090a03060b040c1806080a020405031e19021c02030a0507090606090801050903040605 82
    0x3d000c03181850700407800007640f01608460300c4e07031031b188090200d01c0d04000041c0200641d01003070103440c0c103000c2050f40310316001d000c1d0b03070081081c410005064415071101000c1e00c1c181c05240b5403a064201001070240c0310560305c05000c2010082100441c0c0d2241303141d10440441a12169030b032448503401164903403007003102a190724445950201d081c401e55060003070b950f0b00400110003114250f0040606040040e030010032030340c0c8100407440300b5448070070310314003141c0c0701c680000b81c55a1a4002075515214018100303a0000d00704801008014140c0d021002c401001c0e107041119280c0003a0640b100724a841103d44a0400c10204001c4180f1a8049030f60140c4103100250803e561000820310713100d261110581e2804500400e036822007020490000b03c07800700034020801a80075008244401c110380050100f00c10742541d40019510100720410381c1d158860101c551035a51915100014030300c90082c10005880d220300051103503014007a42c0c1c014440603000d185040c4c0b80000503109948403083e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 358856699 1250 358855449 358855459
    0x30402240a092309010e040503090904141b060f09010c080724180201111e0d0908011a06160c03050606041d100203070c021903060c0503010e1302 64
    0x8044142a40d1405006920040e445580080d820888240307510100b065078000c0101c2403000d0050740c1e40d90325183e02e04646c0750518114041d141c50418500358410122141d802c46030040c180f00403c9282c0c1125000480003005441e0704400d940407007800160b4007400c182e0f00940500440080001d01002000d03420014104611113001a84d90740d00140c001e94020b4450b608100341514061a52002891440d0302100041281e0b003e15200d001c440c900078407003c1d04109010169082c1904c08001c213060911810301c01281041408031010340d101c1104080303134009501c1040c00100824140520100c2c00750a190f074020120100d0705000c1c46800040380f07164405a080f483c0e60210f041d24111002071401a80504400c1c5031031401c0c0f009640e000700c0701502c85a40c140100c00e1504000c40c00b1051004034540159503a26031400c21500c0c00301090b8040c4d807040410f441034075490034980004088034460101070100400304041039600780002d00ca82c048404030b482c000f03901c01181c114803041c00e0b440140f07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 358857949 1250 358856699 358856749
    0xe1c03021f1e02040f0f0b160c050607140111070f170f03090105090c1c241a04050f07020601120201090e0a050a0b0303032707030b0f220305030402 65
    0x40d0b840d01d01c1016103100b1900c607600003010300010601140308005041c1911254001034070b000645034183c4521134194040807040d00b4007504126030600308100605004005903114220307801c0041800b4007a10b080042c80d8030b041320040b0610508410340ea407041c1c006a28044600c070319100d103501c0c1407070611340c024196020400708441140713500240d80a45090400000c1c10310300140080d02e84a2452062442a1000c807043ca944080a82111581d550f01c80048110010401c03a5400c01540001d6281103840c00d0800310036013080703800b01e60640160211020302660716070f801386c46e1540758295030080058210000610800350341c3c82c007402400d4810300d007600c1e21070764422000600350800d0f1028040340307071106e0a1040030031a0303005c0e9511101e0100e020b103140d414051002c040e490b072a4442c0f04c5610403a00710400c0041428418840110b03000700a04401e807400c483e5150034510100d170070701544190171b20b00a61044640c185002c415501d525a6807440d01c0b47d400f0014400d29401c1c0011510782c0100b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 358859199 1250 358857949 358857971
    0xa060e06070602120711010612080307030c090305030409020d140603060103020607080c01020d0c0206060a0608060d1a0405060f0903071211010914030a11010e280b070e1c03021f 78
    0x1813201d0712411290b0f4030300c028074003030910040c2998219809803510543d8260a0300105203031208030b81d0840054200040e203802d030b07801d06650707079811580064000c0c04081400500c3d10581e80013004115140441000b414446051501c22190b05580e060b4040d0321400040c40182002001000202e001b03102080c140000a000282640d001c0070b0740050b82078a54200303502c4030313804000e03143d0010001c0b0f411003211400c0500040c0f428400500c6544a001c010380c800d0144665142c043c050510002c0030484185080e0030550390380e10b415645803404610741d0700015101da030080150703a40d40ea408502240d4100c8004011120b0080992141241c0e541c0c0d64580400501d001680081074a2600007458807240908000b900f030031000190381409904003000460700c0c4001184800b01006c0c50f03c40c0a01c408210500c0c0b00c00303180303060001003c40f50360f1010700c18001c0d00070701c00b08500d4004450500c194011030140070032600034444010096404141e50780036000f04010b042580f400c2e203580c0003807821080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 358860449 1250 358859199 358859227
    0x6051c020706060906240e0109030609050d230418020d020711040f09030801031203060b0a020102040f060306150c140109060209030705010c0201080a051f031506050a060e06070602 79
    0x20300341202e40943e40c2d0b00410411805000c0c050041054502c074880141d4040d4101c5804211000380b5801c001c40070424940a038000d8034418091600040c08201c0c4081601c1d0040c4d4420140c4000f20100300d000c1d0390010300a41d400058035031a0014503409003030910300070402441c00d030100c0ca00d942032a000d00c08594842054409002640e0182d00c00107015600101480102da0300c4042c4400842c0c204109030000c00e40104070141105d60109441400d40004a0118000d0525801034a0202e000042c0e06141e190305401074401e961102d00081ca0003070f581c9030150115a00b5200350184250001000d410490050007148609030090080035401c1e0400d00301d50782140c00c807503c2240d080380e0124004115080820407034000d040300b8200070304c1c10a0207400103080c102d030003008a41c41d41d44410004d0140420344001042107581c40c010140b90544030f10303096801e02120212450711a20b0b0040005d1a0b24100004200701c61003a03e600425075104800d00c140d070742c0400c405840c001d0702000031014840d81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 358861699 1250 358860449 358860457
    0x140f060307150e10120c080603120705030c0312010e0601031a010309062703260412051e04080f12091e030a030806150309060703091103060414010e0703080406051c02 73
    0x380d64070822158003007840700c1c040b103000740740c0e040c00c06c40300f11f08109041c0c9001804e4204c42450568460307e500700361800f50b02d58800d82c10035083c40e01010416a03d610361000403a07050310000d21156945641301d0b8011421111080c00302c4040b003c0b00c00c0f1160403940030364003000300c003401104003003000c000c0c07801c582542012010140c0b05140c03043d07440d882410782c018040a443e1450120724014801400004110801c0181000e424046003840010020b8025001c0391000c2d0306d49407000003c0495020404030a4000307200e0007040d4000c1503207c450f40100400c0320441c04d601e035010356080103125000e2141900132084c4001e1081c1d200c04032109240e5003040900e078070074032a5440c21183d04d03100e4103100c03400b0025100005114018810300401314404a089644018140390020310b0981600b03007550180303005c031300194160041006010501c60300d510816210780c10392000380059050303c2c411a548001e80c3c4005450390b80144800d106031880740b001015101c4d5510690f60341d405c02c5480841c200d0740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 358862949 1250 358861699 358861729
    0x50d050f060a09060b0a031d070806011401050901170618091e0d0903110d321245030c040605090f06060c010c03140f060307150e 57
    0x22451080001c070340303014102c0c0b030003500100e481840320038a480e1040842c1d000705003521041c15140e4001000d9646040c034030700d08020b80c0e0b100711a40d141da2054119140c40c000e000d035041c821042e000031400c550095049038506441070b5a01000d80d401065409400d0402030401540300540e100380340e0fa45d050050405002d0008000a40040401025006206d890400f0b82c080503070080702d244071039075800c03c450310211307500052008880f190380c400007a151030403080000d02640c1412600407101c500480650312212103420f00b400e074041420801c0760741d102c5107201115841001c00280090600001030720307012580749100e00000c1103a0200071202c140c904000442042108070b442100c038a0300304034200003d282501e0421840c0d00303180c003140c0f040c1d40041c040d200950302c10000c512561a86c0d0129019001030348000c000354820341c400180948282d0307400c207410700b000c0f0012899a540b20200503016200050007031215a240c40700c03008421010007004000d101d0100d40740e490b9500c039a029064150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 358864199 1250 358862949 358862971
    0x7031a030d091d010b18040603141617030f1b0106030317071d010e011701090603020405010905220323040e100302011407021302070812070f09050907050d05 69
    0x7803c18002246000d000c0b01841002100f0700c004004002d118021110081080783d03107840f00042c001c0114003c2c013801c0e0b10042a402e1044991001c1400100b00318144c551103c0e100c1140c1a03480e40c1500014510b01e4420b0142d410421005901b00d40307500c000c01414201d0500110a0490074100d9400c46825510541c04100f04d51fa218550020b4070341150361181c1c0c581050400c200740b82049241450f0f1400201c0e061218040e142c014581c050f000c51007100b080949616500c2da12640d6030006083d480c40101d000d075081100100f40c040d058081c1d0f5120758046650241c00900714005001c14100034003013034052000701645030f2803141c040c5040c2d801c003814075a100d6139a01c1c68481101c0044900500c42000c0f2a801c1d48240010b0780c0c4601c900d00710100200540307480da2400d00010705440c01c80030207030100600c001003c0c02041181c1c2c0c080c0030316258100c0c4540d05640e40501c1601c032211692044400160400030900842c40d240c44102d4020040b0b240c4142000e0309056802d08980c1c050300ca1118131 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 358865449 1250 358864199 358864217
    0x1002010b011107081b2806030605060f030627040803060901080a031e020708010e1029040f020714060103050c0d0312020a020111040f1d0f07031a030d 66
    0x1540c200a494141c20301c0d00300204201803134040c0a5499810340b848480c400700d1400c04003c9940d640c00700081c4044103020000c0302000c075000c80404840c0c142c2c490140444e08240c40000c5a182038400c0d150f1266903500040d20b190744001c1040300d0310107115012650b80001091264a448220342910302c80c80c8140c02d016681d00f03000f020407040d108160311040c12581700e0458000003a43c008500701c00e0b2025480c6800201c40c2d444026420300030303182c01280a640c80c0c03aa81c1054410f00081000d219030911404100c0350611603050090280e00300f0031402c041000d03a44201c028242a8401c03180000e60100040c2855504e640c1c110489003110090300d041c0d84642d00620600a060181c0100c50701e01301c40c140d602d10010381c1c0240070032800c05101200349501241c0d014009000303400403500480c4a220041c3c3d1651128200b80c030840b41030103030105810111100b00c54048614112500505504402000c41c0d501c1c82c80881c0501440d000111b40403014410200c000d4408204013240b80c0d0150700d031a080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 358866699 1250 358865449 358865471
    0x70204092f04111c02041a03180309010807050c0c1503090f0706020a0f1a1311030c1e0f121513080a18081204080118021003020a0905100201 62
    0x80700140c036a284210f160441004080ba80705086510200282c80c04045281251039401300a00030b6030311080801c44052034804034481c0c100b00444c0b01d41244e0500d00902200342a520b640c130b000d40c00c540350210f031964005c2800e6034080d41c09040c01008560840384013181d080e000c83d00c904150308640c0c54651003c400c0c044088030510981d01d040512000401166180500095454090440180c008d903c8021510f050010741c86644007070b00070541101e669814883c0e0b603440d0054031654165180c0040c0c0c0344040f00e500e00810442400c0000802d5202180000007071102c854841004540d408100c0440081280d25640482023400340c041d070103070000401d00442c2c140c1c0100010100c28065020007005000945000281d40641800d0710f850a03030605404020110100643c02140f96032091030360100075002d10f0401003044d900280003e1001e10200850b0814028503108000c3d48500d00c2c443e0003561900ca54003400002d51146071a000f0503540d000400d082810804513400140d44448290354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 358867949 1250 358866699 358866773
    0xd021306020c1203030a090507080d05030708070c05070603050a0b040507030b040b01030204030b04060b031005090102030601091d010b0d0b060408010e06060111030406080402040906140106090b0a020303010b07020409 95
    0x218801d0b0a6402c8101c41c407124544644a10000b032410300c080ba40e40384010b0900004000400184c1001030807609a4041400d02604a81088a0700c50000d051040080e030300c9840b5029452000317500400400086090802c181c0103040300900310f5580c60783d00c2c214101ca07542c43d4080c880c0180c401e91400500c1c80502c40600003035500c603441d01b6040c5801040104009600d6000240d8040d412560000e00d003659407002070b04001012a038146054109414091083d506600540c007400d401d8039084d2800385e1702c1c0c01071048504041301001100300c00900400c10b401c02907004061002000c08001488030002000892542145d008610f0aa5455410244040d002c1000325044003090030300bc000e9102009031142c0c1ca10030303400f41d4400c01c1b413602d0104003151542d130010403556a02c4042803240a801d140100040c0c40b0910450001803900c400c00220114001c00320f0303211010300da000d035246a09101d00f03844903a002c4c038012078125941c0c51100c0c021074030030034000907130081c0c40301c03c08110b14030501c00b030f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 358869199 1250 358867949 358867963
    0xc0609030c05010606020111030c090a1206060e0a05010506120916090501030605060f0307060c020f041404030e0f060a0c05030c0a080a0212040f1202120d03020a081303170c0d02130602 81
    0x71083d07a241208d004905601c01c02030303030341c020040780086649280d60300c04522103070312503401340d034100550b90310321000c20986401c002c0581e0a80c4141510039a079901454041d54001e104180d00044200420201e4100c91b5903180e41c03005c078820031100e100038000c4040c504004a540084800c958a00c0180b0410106001e0b0f240c03c880100c5484001320b00e000300290300c0d01618170503101840412080c0000319100c8500400d007600005004001103001c160040140580490b0100d0000d854102a58003600d010a8209040200600428100400c0d031200352140c1c0304c5600e082d03135030340b2044c44005070040c020458078112502c19503605071200e501c20b4011b442d2072004440d5414078a01444148036545409920408640512801184034422230001c034081ca0804002400b450051240c0c80c1c1459802d60014950002d240c0d0b40d41c1030565504503a464081c40041000340020300002031000a01c10700400d0940180e00035075900d140c200005208401c90340840c80194400030000d00400c030898060140c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 358870449 1250 358869199 358869209
    0x203071707080105041e061b030218010309080301090906090f2a030210140714060613020316051b150106080703051005041d010501230d03050a0f0c0609030c050106 72
    0x81c090f0f800c1030f076141c4080c0b0000b00c400100c02140ba03d8003005004858008c0c2041103501640180034080c4508028043e500c400314890051440750f4602d01d0315407192080500c0700307401890f4241143d0a02440700040c0c21106420f0383e01c00d440e1142000810b80521003c02002d200c1c2c03c04c100702001c0000d182030820010350a1090307020448504201584800202c0400c4401034078001c20200d5011410f01400c0c002c03058042d00c010030010702107000794000181e041c002e0400b200c0300d0a0b5030100160384d0f420380c4030444180b05003031001288884130034010310280240151030f40d0504040c4060318808c131700d00b0340d00c105106802d9078201c00400500d0707085603440780c1210036890280640d01e0490740044504a80b8414a401155904e48035480904000100044d0101c40c4000340020359442c2204a1179884040700f440d4551010000c070840f070314105020321038a6038103490b11400c140e01e0610544200350707092120710610070000ba140340040d01520650651502c02d480d0400c0d8060281012400c484240e048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 358871699 1250 358870449 358870451
    0xa020c0a06150e130b0402010c02010c0821101a091809010204050108060f010c020f030304090908030f070309020108040b0606130806043819050921040614031302030717070801 77
    0x5840046541d403000d041c0d200b502800c2049c42d411403840105c42010040c40058410f10300828003000c400050350101c1c1411765004511510b64503245801411803001c0e10402c0c843d00c00680ba072000091150010302000300d4001d00c10104221280c40440b90110111a025000d03580050140034079a0401d400c0c0d504204161b80755040e141c070342070010748181400480039204a00d00c030310600150789d040003140e014020b95881402200707075030b00d440c032015041070f100882851200400500050320034440c0c140345540580d211440354555031500c080d0524068000c6400810421800107100b036070b20200b00041c01e414004000c6890581400340d4501000034450390b41210314084400c84501c186090030141e20b09001085e003584801c00480c01d40060b40c4500d480075400d0108201c403005002c90b030b008041c60561024040610304641a850301e00c242e0082002003200364400a2469410340040c550000a501042c80030b040b03d500024038000b400d030b10103071805000118510348102d09010250003000781c800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 358872949 1250 358871699 358871731
    0x60106020c010e220e0a0b090c060f030703020405030703080a0e01170a0b06220510180b070203010e0a0605330904020a0f08060109061d0a020c0a06150e 67
    0x40002e021101181c1c3c1c00388a141203d00d041002c11356243c011224442c0f00d0800c1049490340b030031954403000e0f400703001d0b542a5030090001d10b640d00c0102d986844000000e0030705140200603007855590350009055001019030038440852152401c01206010714050004d0580b60b181351800180204130031340d1030f9030400001000c11403100c07058524554103c42c82d40c20201d2110f100c000860540d00441307a210070240490050780101010646114040d22820342d80c1c0740300e00030b0103803054400034000c04200ca8003c0b2034000411503860000064004c4034801800850200000300f0030900e0000054019a4940c1d954001d100d18281c500e04c0d0746262002e2002d08901d8841040e42000d210031118002c607000d60502400101190360390b0b10944044e0404c1100500400c2e01c4001c00b660703409003400b03580c0509103415008614001f003170580c03030310113014555080302c250b031000840d50203500440e616040f103114110000001501c14010310240e14540701e100c1c00801c0c503000105140d62000f400d44075000321111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 358874199 1250 358872949 358872973
    0xb0708040e010501050a120509100f1d030f040509071707030b010e010e010503011514070302010504060f05010e060d03090b040b071a090a031b020a0803090901091a13020909130506010602 82
    0x45880640303507c114500082681d20b640c030890508076080d80c0206618602010300709401c5a9a009003100070700c0d071400c0020b40b000780101c03e0380c9100d00c140341801c0d400c051200704210318003103c11960180243c5001e5030354000c25150041080002e440c40c0e80820b40300c5103010070550303100d0701c1401200000d00c0d000300740b942c01000103400d5100601400d10707011074500301000290b00560468a118016000309545c07607100b13050007402010160b500f21041410b1003e881c0318000b85000740360685001b4040302c19642c98180403c26200085074040742480300d098400600c0d11101e0300988020b100ba451202d0f9610064900b20b202d464402041894210921007402140c0c40e0000d0b0541e4000d5140c10148000c0d108403001003401c0c9103680340250702c980c0c0c0c2140070600c404084054a00303c030094902c4d00c5980d1700c454031907095900c40000000703000d00d9096104036a24010051642c05081040b005140903100d901140001b541260315403006450203844ca001c0080c200010340c010b00d00781c406031040c0351000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 358875449 1250 358874199 358874207
    0x615050306011710090e0c0604030b0f130b180c0604081b09151507050a0f0b10030b07120f09081e09130c030f06140a230103090c0b0708040e010501050a 67
    0x501901d111035588051b03004100300b08102c1c98040810081c0780f151150743ea0b01c4d12041d001c9089896007400150240440e82d40031980d402480441d500c07545550aa643d002c0580000d61102d030103802052088824059140c0c49080050018110100c09420f205065110303010700d09101e0281d180c000ca03c00b108010705204580310280001d5400c031806007681c41c0c4142c4a03070003801940000780413030203403040c900c0400c610b0b4104000f070140310b10b504c3d07089a640c10f1510004000b1611001c1c0c915003900c07001860041c030566148211303c00703007540054400581e240f0a02100c800010494801c8000100c01440e08084241e40818040384000d4034646a036010206911000447e50310140648030040f21254900030703003043c440340c5d9000d43c040043c10382d20303000b0754620650b080fa8540141604503000c10388800c400b020300041c0c01010030061600000200440003480010016100da07008803101080d4060410001c0420b40c0c0203040c61511103060000891401e40b040e40708505000040243c00300310340e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 358876699 1250 358875449 358875481
    0x10e0118031e05100f0b100206040b060a0b16020f1f05030415020c16061106010e04020303070b01031a01170a0f1104020d0e07050102070f0b0c0106150503060117 71
    0x1c0160002000c50446849004082007104000c0c200d00540b100c0000d10003c6900404170442410f030305110f50b5201c0b10900217a016400d40040050b00030740700040105407014542604801d02a104510940d0b841015a1503a04010610f909080f4040a054294981000161a80c8030300f1940c180041c0c0b9400c692200306e402c921490802d100c03002c000101441030326000e6607180342c26820203650f200c841c1005651202a01820304a1003200b5103004904070340f00382c228104901d100710003005140d080c8215000c041000510482e407500c01000402c0000395a818601d009521900300c5110b61000c3c046119180201604004e0112810000c84000c010000414401441c1c018050000301c2c9158146050390320503558001e90002d00001704083c1c94080c035806580ac01c9046425920301c103032039000481c1ca9401d240301e480c07801c1c000c1400a1140c081104010259094000b0000500035642c000c0b28042040d08840e080c00b190002c0200103145d600f00d940c0c4048086d9202e4462114034000645146c480300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 358877949 1250 358876699 358876703
    0x90406050a0f0c0206060a090606020c04020705010e250911040608091c02030903011401060c080f0706060303050306040b0108041725080403050f01050c0a0e010201020904050114010e011803 83
    0x14460010038104240c6038000720802c0c65640c400e10010305140c10203036503400c043d51510701541201500040310706040c49560b0568006a020300501c83e13040041102940244c0000d583e59540d81b100c00d0011001002442403080ca5403c3c82d0b1008070480c6213801d12020341d03038481030515041546074070103002e510044400795865420403901c9501d5840c4502d14008501602026010303040250703c40303158000028203960b11040b4003e0100b56001c0c400c04900d60340078401c0b0400314400c4104800040ca000000e803440b40f081c0c0c3c408a0801c0c44503201c04065544a0788140c005c2980003044c00918200341c0145901c80400f82451419800c00f651000d5035201c20005cac2140c0202c01203107d012511694401603411060700c10030100711503c0e810052010f40c003500c070071117803442003c1d4920342400040c081c07207200301490f00c60f041c03d0903036000096803c402082840741c1155030030810200c9655442c4a002d001e02032403448044100d02d11400940f060300b241a006040c049800660801030022804d8242070325 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 358879199 1250 358877949 358877951
    0x5130f060801140d06020714010c0509030f1606050703050f0409021b06040213020c120c010509010b0109080c010305070504090c020f12040b040315060521070b0c03030403080c0d0606020c0a14090406 87
    0x401030500e5044008c00f0740d4041015400c0806171103170560f1080207091a900210252081e01d2500e0388020303641d00f0040c0905800041d8454200303c2e6500400280c00994024213102d4981420405030040e81c0d48541c101c102040d40c041010b40006180041030007031510000024005402c02d6000502904411421905559000600d4108580050240501c1040140d42440e19a1040c00d11030b1b010b09402c5603910310540c03031701030b46100e99071068814400702c03900314010b010101c0d589001103014000040111092140402c000a50790800c0c1c403d000312588258040c0400c050308980c19801c041001c48c240c0d1100c0000e00c02070140e091304804450460b58011084e40b40d5001c150601c1c000742210394000c6504c60100102e0b040f10702d21041c0c0c0030404850410030390f400c441e1100e0105403617002d2080082c66960041c400640000c0c000d200c03880c0c20155441030b26003070a40d240d1100c8207a0344079810800050f00028a4142d5900300aa41e4101800c0125075078641d203192940499003440000701f0190800d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 358880449 1250 358879199 358879207
    0x112150b040e0a051b0301020909070309050109022e08010b22030602070f050733030b0a180501091b230412030e09060901140105130f060801140d0602 66
    0x207503540768014440e8101080903104108800c0c00e0041c0c03214130b81c490403000d4010900d201412460b040c4200d50300544d00518581b43d94540308002ca00618003114110345940d070b01c04c0c1040c05a0f451f00000c110f0a0a403260001e0044400481280100745c2181404240300042005015107030564050341c030b2000e002485880542c1c00080700810203000f50744060708180c800544a0148404520f907089440e000f6800c40d15003aa0703c03a2100faa038445100c0c0500525000384042246c1c0084180b5074899508a00c0d001c80d000c0c281e100010242c0d4900c0d80010010101e808415844140c180101801841c40010401c0320104014107641c10307041c0508038108100030383c4461400c0310030300000c0c202c040307010007206910b845d11102c11080342c000ba87c01c203a000c1009a44a945240307028035981d4480c0c1409000d01180c0e910f407503d000c117080540e008440c1804404d0140003903121001207150b00900401c00c02c00003042ca003d2014180381c0e010303000401138025400840c20300f40c5501505c140103a40c00000144c0c1c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 358881699 1250 358880449 358880471
    0x30a0b18070e1f061d0103051f090524061b0712050c0414070c0b0a060b0c06040b0c0423010509030d020a03021023090a08030f070206011215 62
    0x4281040e04000c0040c0100400c1c480102d0030741088601c400440c40e040c0c0e40913616880203035140e140e55904082e140c4081415004154840d4200c141c00c9220740503448180c17040758030700d240d1150307107600000d00b1184e4510412500c2e000c0002c1c40c9030380380022160300100307040c108003007040e0384601035650500d5101d407801911590703401c0108000410b008030108070b40101c1c0d8070380f0700d807144a4603c03824891030030601100900000e182c00103008011644905100d60890707554800020002000d041c0340554a200009800c000e60008041c0c012071070014005074a400c1c40c20344c2c09010042c000510440091200344802d54a2804084280001d00040e2543c64020310040b1840d21030b00201b541c040c040c0d20f8400c1d21703980d00040c0c14032203d8840d0b02951060551080701c00d0489049160551039110076610844101c880031702e1580e0840100c0f406e40e42000c50075100d0149943c410740b007143c007110000c42000107140e418004503024203080e800c4440d006e42aa241c54001030008140514051340d1050702c2e80c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 358882949 1250 358881699 358881703
    0xa02121303091a0301051003020406020c13060807140913120e0d021215090303060d060b040917030714030403091e030b16080928170403110f030a0b18 66
    0x2000d0140c0f81038244004502d034103070786030004e10417940102c0000720765203117441c003a00955099414035030003000c49289510070041e00c04482280704039940c0c0c0e280700c0810a0081070203250003400c040c000708000300160000344000c040d001402c800210240c001075400089000c0c5580e0300d0794049182c0b0318180b5982c0c1c000102030381c103800c1c0300a500140c031510140014401161300c40328005c011000000d42d80d50f10449a80b2440300f210307119400000d0302c2c8210005080341e13000e074140700c2c2d0190001800030f109540300460680d560001044083c1c010003004441039200d604c103000d4501100d0000e0550905940c090107000d1a0f0003250b00040c0d50010540060848004110085800c6041d405060801c0f08182d26958011040e110001302c0d410000f507040b100025810380107414502c504644014189050241804041022a450805111400052860f01c0c002d040a9030160303000b16000400d0703004221040c2d00c040010b6002c0c2e0803d0090401084040c9400d56010a00c69802e044001503459454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 358884199 1250 358882949 358882967
    0x70f270b091302011701030b07050a0908061e010609030c14060c100c1805031c091a09010f0c050d0e1201050112051509060c09012010050a02121303 65
    0x54012840104102030158070b025041c410324000c0c0c071552510010340b021448460001d000140031604a00c011074011803082c002030021014510300f000c82c032912044c1c1113050060503617030100b02c40c1c000c0300e80308410142d2000150040030142021440309113142c3d144040d041041c03103952003498800b000b030401921803408a03000551814191802d003081010100028110040c400002a18469100300d030b44610754503410a07140c00400801c00038a100c07091440045c04480c15604000d40d00c10300040103280201c14861401d015490f2544034941e40c00010100c0e11030019160030090101110030103e20041040705c02e4806070b00d41749035403401c1000415095240c0c07011000f1a50302e00800000d00200c00d540c1c401641c2d1042064803110007920f29460000305040d45d01b40295002500801c0880980c100103140300031040c1444451180f409050110303d80300c1c1401142150040c6400000c3e48455101d50f60780701e5054a400c5041c00b0001d990101c0d0711030002d02c07803854036407070400c13030802d140c0036140c15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 358885449 1250 358884199 358884221
    0x105010c080d050709030b06010e3d090303021006060c0b060402090604090504020306010b09130e07030206030a0b130c0c02130b040912171b030a090c06030e070f27 72
    0x2405542030003a0020001e4171076100a0340d07580d1008002c0303106907103d1503031580411001000c9125500120940407843c0c81c0c0c1a820000344c001d4049501018840b030550603244240d0f035202e0b0328080c1e140d03013400f030f0411101e0400308084078a85403041c1b05a80c0c0004400c00100e0700310185078519504e29000c20028030407200941d0388520040f6001a4150309a00704500c20381c401d4054941990360740784100707034a008000e2841e0f84001e010445c441c007807a5942c00481d4000c1c45000b11a940c6030390f034022400690095a0480341c280e01d908a150842c1040c585c0081c4005102c001000b039002407080041100c0440d00000b07100d021480d00d40800c0b5203642c1c119502805e40104100180076961900011a02080e1464000700705d03c04800c1e00070402c6204681d200d42c0c0c160750385c0c0c0d14108440201180950000308002c0a0390341d9045075801050200000d00701819054800040d08410b5004080c81d201d890352041e504c43c06501030602a0b00e101c03050701107281461070007422000c2a142205006042c0101070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 358886699 1250 358885449 358885451
    0x51b070f0314010b090f04080918060102010c020604020a061808010e070806070c1203020d151412060c160f17030f0a051303080c0c15010e1e0105010c080d 68
    0x4003080848220540c0e0084900c15001009518081c2c600c00d4241c500032440036500802e9040003c04100b201003807940c0c014401c070b04403440c104294001a0000c1c2c0340d044038600811080703007000210350302441840201c0480b40001c1c461442c0c41da0000c0c4c03400300c0900440c010480d11118204480070314081d000040c1030110002c0c0003c5d101c00c1051070742e90f00640701301d200324070504c004140d13028000e40000e0a0aa0801042001e201c1c09d82d0040c0c0203940145c0c003170191507a4423075241e03400704460100b84020f010002001c54445110004005604800c0c00309043c841e0489400d2040600d04d80048501e1100034a501140118141c00d003540d2110302c91001401002501d1011105400440010b6104918901d4920341c1c68542011031000c41c1c10494070344045030b09007001d05021138042c448595108956500040c0740c1803007401300c1800c0019100c0e10700300805d612030060150721183d6080b2603021795030101400b85400341544642ca46ca81c188900c6040c0310000c140c10092242802c12204944101d01c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 358887949 1250 358886699 358886713
    0x2d0f150a030f0807170301030c090c0507140c0102010f0c080a0c090302060304060203070801060e0108070e0a1d0f06040504051902031c08040c1a04140402070618050f010615051b 78
    0x2050106903000c040100c1720781e0400388180c070b129048681524181d94100c1c504440365030030442104003c00103a01c42e030051060902c02d0400040c002000440c1b615801405015181c00384400682513070850142100c21a00304a080400b040e03000b00b48a512040140d4046680c050003103090f17a03c0e404540020f0340000002080205001c0990003c5002d00300d15a680703907813a84d035018211040829080e0f202d000900d65008520614030030b160400f8009002048070321080d545500c0c0d00c1d120030140f0082c1100c2c04100040000304075000030341c03c0c0e000c3c802340c509002d14980341ea1144c1c6c0b107110401c00900640c030315200d80c0c41951020005a0013007000d002400e0340d40180740002400414007203030200e40c400720441020400c040000c80c03441080c41d1a01d0010308003402e2826010141e1412842c8541095003800501c001c01e6aa000301c1440446d040320383d001ca81c0d00740c104241004d19100c013000c80750781850f5040000203540c21030907500d91039034030704182c5800b0100114100c0c0e0001e000520358a00c1a00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 358889199 1250 358887949 358887953
    0x150e0f060d1b0f0f05032e080a1106071a07050c0607030e100e0c01050a020307050a030c0b010e010f030206030408090409080406030f06050306010b0715052d0f150a030f 74
    0x70306800d1002e0860301d0308102541c414000300c410300482148100090402d1000c14001c2020050800c640690344581102001d1214030640d04404d4582c040092584034100300c0061045030000411841c0083d9215840c02000d9124107888645146130400400d807c0b10000342064030070810303940c0e045034802c00e5403041d0410080003000303032141c0e1091840754020f0303d005100103805485290103041180c4003800c2944080d000540341900059800f0095005c200b017141300040040c4010f000107803107610b401d441800e482c00c00410024050300027400d0580e0901c010310506420920b42070490754125070460703807a507551800c401e050240e040c4203a0418100000c482c10003810078041c0050320f1050380c0130043d4013120340002d01518918401c0b00d406030030a60042c0140c1d0340c9000140340580c002c4c81d2001c25a031101c00004200d0394221000382c00c034120ba0340f400400c520217000d000c1454149070030944003400c1002c091840380340c000d40049442c8044800d903016607100d4268040065400201640c400b0521b8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 358890449 1250 358889199 358889231
    0x51201090b09070f0801140a03021f09050d0804030f11040f0c030509010b0a0513021306020109120c030806010804170403030203030f0109060308040e09030f0409090b01150e0f060d 79
    0x5401a1080c419580010a50340c41084c10f01180c0b06203680e0f221440e440d029440c1444036061140da0780040b504035022015840c1c810040f1005803001e004040c44614848d0020100c107000d82000c1d2080c1841415000414640d4042d1001d40c0d401211038000443c55141c0301400d0016201101d41003400d000d074000440480b42d05c140745800c1a610123200d240e0390b402990b800c0350f089011255012114500900907814540740032008020001c00062412180340102c81c81249144d01c8040182c0d1921440001c005e2450715a44410000f410400d14040c2c650354090a806d400800b01810007032460001810b01a0891002030015280b558140d60340c0d449080081d203940c0200c4a400c80b008184000040400843c4101c5040300d40024140b0700309420700c02d070f000800030094150032161200340b00001400000300000c000401d0f0b50a00014005940e20b082000220164080f400c008500380c00310700d0780c0742c00000d40070031031034100d07440038110407100001441c2c0d010303940940c2c0e07800b0300d0700c64148400000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 358891699 1250 358890449 358890461
    0xc01090c170d0801080a0b0415180c060f050f031009051f1a0703050d02090a0f05011101110a0507020a08030d060f09050402010c02010309020126070e060f091005120109 74
    0x10310400d454000300725041c20f0300c08120a00c0b8803003d82c0c3c420024407002c40c0c406144590814480d0b01c6510002240740e10860544481c81c0c0740722408254140b90204001e0400c564000403d0b1f1030800c09804201000054400d01410b800040145030000001e05c8010380080254040c00303801501300801d0414100006240c01d0f0001c400c14013040708040070514281156410b02c10144100266113172155594045409400c0724030040a82602442240002d595481c0c640c005019010000b012451424000502c00449254071962603450450507909601500c0110b5100c140c032030900039510362882c4042000910a070f40012085d0002040360700742c0b03404a030081821078185410070a0403d40345c80c02c04d01110801e550085c00b2840680300d507001940280c00c00a10740d40141401218080d1042400d55210149c40c400d0500700d02e404208120150002540e00e82d00e0800d45003036080050700112442903200b0412014407076010030740440b0b1070b03601c20b804179904241808000510380d65215480005001e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 358892949 1250 358891699 358891739
    0xa0f0606080f1209010f12050103060f1a03060711071809110111030409051008010e0f0d02070e0c18030a08070501050c03040b0612030d09030905120f03030c0c01090c 73
    0x9442500032610b80002411005100c5024080b0f01e014048030055521400746000316041c040c1c1b43e51241c801c10118812a8001c5000c0e00d008202c0341c00c544c43c0401142c07400314a00502080303c0c50303842d0032600d0008900e176000c0340740d051400c0940501c0c00318924000c031680c0100320443c041808040b004106801c21002244584200071085003445e0041da00b6002d0180d400c401d982c02800704000d0401c50380c0205030480011001010701648428459007518038644080c7ca1710350210900d540d005400b00004500b01c54a03202800c2c2060500782803e1145102410ba49044000442c410407a008041c014610340507008080310031450329031801d61004e4000d1a815500342d4070744070001d02d54880c000104c0784655400a00310307020365900400c00851420b010310756a00c42c8401c0c44403d080351b44902c29003071458003a884030a0005c0c030741300800c614026290441c0302c4a4018000c03500300100000709880c1c001403640901501d49030969142ca0040000c0c640241c20350001c3c9100042030f081c100c00100500f9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 358894199 1250 358892949 358892953
    0xe06211b130f0602010e03030a11040302150a0e040c09030308041a01080a061407090303050a1106070c110a030f0210020f06010b07050613110609030102120103060e070e0f010303110a0f060608 84
    0x83d80e41c800990032075280b11890071980e001000000d5080d4041e5004180448124155030b0030203071241c000c40c00101c0c4d0a416400010000903135482c0c07242c0c2114078501041c40444042c400721038813503c01401c82603144001070510405101140800a58041d2451070040f250002e212a40c0d440c001280e07190020002500c2282c0780400c90520540301c10545407040c4401c0e21980d103034920319501103401d0707880f0398148010858180e440900c4076005001c40e038003503201581c03058072803601400d01030341002c8680011407280784100c4d0100000b071441242404119011600031440c030b2880003060342003808038200503030745019030400072600d400d0810141c03407064015802c8410b15a146443d40814059451002d09000700c261071a80e00d501d840001045210350250000d414220314091640f0f1020081c1c10490f41a0b88510140c0841c0c00100010801002c3c00c915800c454144200e03205405c5006000203010400803208130b0001881c200090280141d200703040c1d0546005504000b07008180c0350080071054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 358895449 1250 358894199 358894229
    0x1d06010807020a0302280b0702030d0e060603072c04030f12050601090b13050607150516050706090206070803040c1a090604260f0307030e06211b13 65
    0x5184000303240007002d581038009160340c80301180c07040e120b40603806c0b00590030942010480c0006a026000c00d010340c00540055490f41108100076042c4c8904021689403580408200481b0303a4000810808a4102c041d0041040c200c507803942c0302c13002100ea442200103c0e00c40501c41015030008a5501203020b03a501c1d10201c20320808100300b518400ea405074005581040d040c02540a107e00501c0304a1380080c0e2850416520720104150f600901070654842503020020740d00d80b81d20b40101c40d4800581403c52602c00b4a8143c041c1c40c0c1c0c01580340c00b401c85652a02100119101c1070210350040f6009030985407246060320b070030f4465050364010560b160b881006d00201c440190000c0d80e0b1600c0004021604140c10003a50003589055040f09001100b02c030846d034600480288a803070703000034444010b50307a18107541c24003401982000080c0f5025600400c070000c1030210325040c01c0903c0c40c002d0030030304158488451110741441c0c000e25046d101000081c1d07092002c80d08018040488000020403021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 358896699 1250 358895449 358895461
    0x181a0403170601050a110c030a1412041a070c05130902030114060f0103051005060a0c0308060f0604091e050c1b0a0803060904080d020a11010f060302030c10091d060108 74
    0x440002510b0040c0800c1092100e0000680282030044206090308100c60104490800280c0340c07200126050f1610341459185428001007030108180b03085c0d0b200865840e0034640f4411799500a820022000c40c94408100501004417035841c01000f00001003000340d50101102520300100a1440120b00c01d61a01b01103680754100080c006126510044c00e124502004000640c0540303002814500d00c0d00b0410004940c0756207640180a07070381d034030f1780d59255480100d00d8050a00303480075002c42d105582040821090b81c1e64001150155003240001190840c00140415210421141c428640b41c6c00c1008104000c1d40f160b01421070303900f82054440f10300750008110380d120400080b020b82041c6003013001070204d003800b42206030824414090030f4500a0030340e43c1d01c030803a0040e01001c00044c960400050602c0300034064040031001048082000364a5503000aa0f94802e00803001e01502c241c5030f405246a0050500034010911800025491807801d25020083c9004a0b0b081e80030a9502011480c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 358897949 1250 358896699 358896737
    0xe010c030e06150409080c0a03110a020607020114160302010c0e0f18042f1e030a120c0602070c06090e0103080f1c090b0f0603030c0c04181a0403 64
    0x5800041507014008075203400106100144002074903035001610303050b0405c001183c0c00000d0443d4003041010b4104141c4500d00140a4008140d5001d0f440c0d11109042c405a5281c5c4100d40055509090024005041c18441c10721405400c421074411195602100203068064000c80c100e0b100c250360342d00c0741c01106c100300400403122403842d07600f20110f9210007290300031001c190358100703000700b500765203442203d1100c10204006d0749120002d068400801c5d100c03418500700c101c0309445492060300c4c914031004042551410010000b07064101c1c401c10700d02c1030b40d000e1089002903581150040d5079a0b452802c000540300d40e00e10039100040c00000300058038254510009041e82c0d400300040340703010750302c480d200344640140c00d40c40c6840b0300d410300c05d9024101c14807a2040a5110398090310075450003200c80000d0510003400ca50090b00b0411611841e070001140481503080300b12000a000c42034104c010030442c1d03048200418000400b445032401d6011005e54511407442952001c003028007110002c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 358899199 1250 358897949 358897961
    0xd140f1213050d020f09010308130b090904150b12061b070503120714031503010b040c0f0c05031b1c020703080702010e0f0307090207110904050606010c050304180e010c03 75
    0x1160031880c0c60a0005250100c1c080030f525000a00c20780352074403040002404c030403007a40100d50301c40340040c00703010141e00c2c0300d1080010f0805009083c140310111010800306000244004c146d0100c031118002501c41c60340c803130510302401800302100c2140c180c0d11150b982a050780c0303035102d030900744491003921041442102e00150b8414091403c09007010b01e031104080d000b600c264203000304100c40d0429440404044c5119800d51a846e41030044180285421188150b14090180d0300380100c100505c0e410180240804c0300798a42212604000d003841e9085005080c0c6500e00d00701c0c495400864117400041d5900c5009031001c03000d03010a011130099a130f411f20f40c40010b010b041e0038400440503601a418074203c0601c098440d0101d83da003480042e040540e19003280341c7c0b107640480c000042c0164000310529800d07003964141c41d203003090b803280303503880034000c1480d0704100032030303500008203c030510940c0d00805220f1800090b129240820b40041d041d1508080c40395071030702c10f485c80380f40d00c030740209 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 358900449 1250 358899199 358899217
    0x301260a03020d080a1e02090f0f0114130317070507060c05100209011e020304150e0306010e130609060c0f021f0203060105120c0a080f090312060d140f12 68
    0x52030440c1e103030300044c0c4080b1002130206200c0c2c0e98691030b0611a031640c10060b1509040c0360320050380c4204080070046a0f0080c2c1c8540c90151210400b0503c3d01c0c0d030004140c5d50b299186000e490b4403010700c0c05070950105001d400042402000c0001c19465010010180101c18854411b07a15407540b201000c5949582151010f0056841002c840e51154070079402010100310625101c0308140d5040205104200044481001070b440005e0400c04803401880b00c0f10000740c1c40c50a051349002500c0029a00d82c8180a690100050040411a42c20800200c41c130300d1a48480103000c078604034100b000c01050400c0088010900c101d40c00d81082d031000c60702407a0052009240200100c02022041c000d41000f0b103403a0500c00100f10108420000ca03100901c80d007010035440b5030301c245050300100650006009000c0b502d40400070b00110310008001e49256803131924400b0396a580705400510241080c4e07a002c1c207201030820142118a00115000308100007850864001001c5041d8003002c5114007296 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 358901699 1250 358900449 358900453
    0xd140f04080306040c090302091006020111042912090604020406060e0d0f02030c120c100f23040b0a02060405010b03062403070e0f01090b010c0305040308070c08030301260a0302 78
    0x103c1030311302a40022000f206516200c040e160f00c83c0c1c0800e0b5150404ea44440001400010400030160309019060507805c000d80d07900e0519242c45903040306d440007441e1011181c0c101c195054010240c01060314211000c000e5031200d035040016180d40c9901003074a090780514180207001c03841c24010081c1004455014101106030b480a07121081d540ba0b004004980c180259060201260784808541992130760900103008003081c09010002424148400030045c8100b911031105400d03042008811100414441585c09021154420500303214580000b2483c070401700e5061102c0c3e80c0042c040b480380d882030000700040b808150030969955022552004001c00d00e400b60014104280549449010080c04548000740c40d0311100304100001ca48400c010000507004125035643e038003410450040a080100d0715285503240108a44a68040a8000d070800501d040402100c1c000e4040104008411369840356190f07070b40f4150109110260340100482a440c0c03030603514010510f943c0499050300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 358902949 1250 358901699 358901701
    0x609010b010e06090103060b0d02041d04080a0503090a0515010603051023011206030303090b070305010b0405090c0702090f2d01120f120203090a06020f101a060d140f040803 76
    0x1c0080f00d6101007607140c10140c484c030b000943c80c0001c8000e00340340c024125000d038681c2e05142141030060a554500100e0b0751955040c400491048401c13500a00180e1400c165a6540d50528900c2d004803142c00800d00e00c1803200c1c1c2e142c041c1d106401e041c143c1c2d451b55400d001503181d14900454900c3c0b5800755502046030000c00355500b26031102d202402d80018142580311200c008100c6003110010344c010360120303032560300c0c86e4200b1810348080c992181d464201040654100000b08003030b8081d50051901070002c3d0f10200b01035000309000e94241d95030060040c0140d1404045e94081c0c01000d94108071003006260200250005460000d00b4012900c6a0320040382e1a2074410004a032003051b0035210401401940004120314580d0b0400c040f000390015a615602d18090004040e5254031120440d080191174000c46000030520301501c80e1404000b01d40000f00900040361850001c08a59220900181f41800d12100b6007190355820911a40b02009580744c41034159204001c580c01403002000708 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 358904199 1250 358902949 358902977
    0x10306142415030406060f06050c0a03030c0c1b0608100303080604020906070213061e060c0b04050708011401080f0307080d1a04060303020307052b110f030301030c080609010b01 78
    0x114210148107001404200340d182c120155400303940c81501d040d035899444443c14050b00114280050081c28117241492500600064058a4a030302b94001400c0588a00203032020512a241c160005600500450f04410b4005c03002c83c0920264811103021a641c0c0c00050050008600308000703c07034050700c50100c07694410b41000001d40c06801e0716603000c1014440705016803600f001134a00c6944c07000c40000c3c3c2500344000a0310040e0011811089001c012000340111540724208484450b03001d00940c02c00d0f1901c0c43c1060400280350000e818540c40c00540c60400c04401e00380340d040302e90540594003c02d241080741a103d200780344010705200c608018484410001e03a01840c565a504900c010803581040e0005083e10381d10b61054006a10125109003031000a1150509026155000c03c113094080a4140c05010300c015600e0103000000044000104003400040706a500300c40c02d0380c0d9a9130b10307441c00601015150040c040d2610602e40006d10001051140d1424024141c59541d0840414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 358905449 1250 358904199 358904251
    0x708070b0d0513061401030b0121150b04020c01150504020a0818070306052e032001030b0406121725020301020903150117030906030a020c070f0b0301030614 69
    0x1800034007802d10203090f0071000c200584544103280c0f50a50010509515608000144040603001a4022005507024004c035180442220300440c3d400540f5100c000001c40e0381000406142c0c01094001c0d00000304481c1c00c1c0c0c01940a1341d1541c003112609030384180c840051104038060805e1120101c0d2880010039180f20407201c00401d900c40c0c1358200c1c1c0e2241e80f00d58074442515002d95110000610400300e10420011161280c01407454101c070000c6a80e103151980700b40030540c03001202414019156150030750344280c00004107414050000d0200540e1005601642c500740c2000303403100d1011103d02203aaa20380c00488a50ba044418801104100d6a4440141450600007240d0640d0f080240c041a51828095030101800c0044400c88075071500c006402e1080032100c660009070410407044c2c085565034010f4035005050360000684403803c0c036064601d032042d19041a03029407080d10000610841481c020350583e44542d10a21490000c81540c90080600b61800d041d5039102d1442001c419800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 358906699 1250 358905449 358905451
    0x4020415080a080a260a0203060607021c020312030411060d02040e070f020d090807030f0507050a140f0a080c040908160305130501050406051b010902150c0708070b0d05 74
    0x100c2003500258540d208070440c600490030904480480e030114081c208140c1202c000e10861742c441581101070224106528000ba600500c582202d940c00b1000c01d0043c2c480c402503459050340941000400c1701407144030a500440d07501d040348280f25008410100303031007040c00e907030040b035000c500e100c0590300f270b00304101d041e8000c2d40c03540c00c905030300307020000d520a100c0034014014107103500ca00d0078910700250020700b00000d100100701440340c02582041310701e0340011a2021a0f40040d41d0040c0b604842c600340d42071030328645c440c07540281001e402140f240310325140610442000c480283c580d4920f24148500161039108160b00c80e00450744604490030160007510f00c40e41f0527848a460200041d6484094807401e610507400a500803807069143d42c00241030384080c0c542420850300300f524281c1c0c024018414281c080070700c1021480d0300c0007800d4094009043c0258000c18014204e04c45007102c0304e080d04545414ad0a80c41400d40001e4080f001081a50a90386030400a0340b9089009a1050141c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 358907949 1250 358906699 358906721
    0x6050f0106050c0a11040f090f0b0106020f0c0409020a0b04030b01140901050109050907020f01060609061202090913030c02030102040303110613050d0c230d1e0207030b0a02070b0a020a0f050909040204 88
    0x70315050350074140f000c04d215500c008c500c14035500305556842d05103c11800f00517042030095600071182150450000915030280740030864000c180d008540c4041822509181e10080600344086804000c000c200c41c0d0080c1070744c080b03104040c840814001008800c0c0300a214080c003140000c201409982442584694010160300417100b069000319412403c681c1182c0c8550001040c600050040da588800e040c144446400c50550800c4080c80c00142e407001e018100c07400458a03065868200b40c0201b088010f45900103000310344803a80c0b0308000d02030f1018200d054030103010b9103000030281c030080c0b03001556090300400200301917030741c2c0c0c00140c0311a441000140d0b169101c0000604585100b201800c904d45485005440ea80c000a90003410346100d0701100d44440d0014125038841982c00100f001c2180e4201610329180d45410b4001c00003481145e00c0540060324810030407200403ca50010036075804e856584c0103055150300b40032955800303020032059008208001041c05490140c0005081c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 358909199 1250 358907949 358907951
    0x11010c0f0302030c39010603170703120f0b0a05010804030c06020d0f0e0a2303030f0a02040e040507030528020909010b03100b27040308180a06050f0106050c0a1104 72
    0x22001c50303002d000b00c06110131784103040d6010300300e080c00003143e16060380090308404000d12080307003980d8410f03507500c006880040d500744001c43c0040c01c0c144035501245080c0380340f600070041102e9040d03010703010713085611a060180ca01c01c080040c4551140000d40c0c880e40e00355039014401011950ba80010394000903100400b00e855031070a4420044074071880c81a003c3d00030091212104524180000d0840d522450342012028280c06281440100031241c0c400300d2601054201d654501c0da80c0000d0185800041c500070940080108002c40041e4003019217020304204d45116800c1d8140303044481361004003000444200011800504011000c00c1c1c014090b040082101c005180200f80f92601c81c0000881075502c800500c88035092040407900e41d4074040b07505070700252a9801105004401a000804001c0094000b03503121252500b42c10304505000256101c0198600303028004e0603082d1400142c4441d01400000d14030f009200b01c0c1e54800040015080b9036245880d00d6030143c45507443e0903001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 358910449 1250 358909199 358909207
    0xa0303020607180f0b13050a0b030403052a030c0609060108030412050c041518090f140111030a0f050a02030402010c03120b090a23060a090b010e030f0c0111010c0f0302030c 76
    0x168000b01444400745c854410300607110000310068906078403940e48054003440441c1d90070710540440004990340190182010341da0f0362000141fa109000032454050002501404202e0202c44003000406a545403378003102c11035201d042d0280e8848200380300c0c24030035500400c41080250907208543c507840340030b407090b0351903e403891380801c040da44045038121131392184150030302c035884070b08480c01c1c80c8192140c0200b010280540d0f5000300409803007006403035881c0010a03a0301401003504138509041c80c84441796101e00b42049410301030f10804807086000307820080090b00c0d6a18070300c2a00d108a80580da015548105520705660401610180031a201c0c0ca828035030b581034541e548050300071001400c00281d0400c002d1800c1c100c1c0440200c8643c520130701d030320030f001c150780d9005400e0741910081030001178405035610068801a03000128a50540211848000c206001042c00f0242401c2a02e8138142c442c3d00c0c60600e400c031030502d0004e030041052034400f00f20451007940555030200c0c1c404080d900e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 358911699 1250 358910449 358910459
    0x1b030618012301080f012003040206070f0b060f0103090f14030d0612031106191109030609010906200708030612010e01050712110d020a05070f05060906060a030302060718 75
    0x1e01d02c078955006006103210401000090f20400c04580e05005010080104107240501407018490500300c2006010010000c01e056664800480b14444c6c0d111644d0b4071045075928008588200c1215141e200b504905812031043d4024015544c81c1e030780c40369a0080d10b035841d5461240602c400016100300788001d00c00016102502d109000103401070401c400c0b44140a80b500801000035420055140c2e0004003d2260981480c2c0c000700070000c04c648007241102c8110180100c0b80036980d002507140c4142d0041c0020b10348194041d8000c0741c01140d042c8080c4802151801c080752080d503c1b156400010050319011506101c059900843e005146070340c045d201d142c0040c01e5500d1901d2980d01a5500d406100342690085a4000d01c001d01d40350034020141c89440c1c0f25564024026040000c0b600021020a0948210101c034241984009040c0b0f4910396814072580d07902048444280611460001c28114a03000e100e060803207074140d004084a94450504964050940081d040604800400415 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 358912949 1250 358911699 358911731
    0x1719030e030d0522050f01110102090d0b011e05060a080901090b04060f0b090601050d0b040b04110304052503060b030708031b100b060405090415021b1b03061801 71
    0x2c00c00c0042d034070591a0184480001000500c0c011000c0c0e60880c01c490404c02a01c41010000041d0340134201015818070b00c04030300d0b000e4400d140e0303980d9001c450000d00384200400f400c03403281a10039500c02680c20050903213030b907041400755002e05507024500303101c0314030321038441c440303030b580c002c0f1050700220340c1c61916560001500400e80b01210b06640320a441107003070110780b05201d00b8180440c0c407903182c0d00b801c0d400600144503410542c01d500d52a081622415111768000c0d03150701102400030042d80d6003110800e00c02380c00c10b45048866000703410100a00110442446500441d94106000f40c0741c55940c0d48001864500111070309801000000204128280090900392901301c6100108004070001142040604542c0c0c400350b501d03001050540d40c07605801e560540344151241314407603d40c3d062541c0c10030111003190010500002e58814150b40f000751000160081800303e603420549810350701c5241702c00c1d101d9190550311400c00a003c030030010b41c40340e10180840000080c41c107030b2407031906 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 358914199 1250 358912949 358912963
    0x4120605041b030b0604020f04120501020c0d020d0905091e0c090a050d051e0307080c0c0405070318150e0304090c080f01032a0b0c0c0103061719030e03 67
    0x24404559038401c11081c4410304840449a540c24000c1103412400c554450f40741900190485005683c00300d101c0e010109584116805803141140c048a2081d061400c01d010f0344c050840d0380c140d03015a01c4030143c09800081c681d0088041e5803506047c2c01e0401c070621038600402088200f00103025469078031520240008240515000c2024650f1400050700b440b00d5809036500c05400f4629444031100814004112041c1c0c0090344410b503007800501e20007040c40c42c02205805002060f0008841c000002f0000b106192030030b0a440c24813456642040540c00c0310607154610140d0b805660070300d000550400003c610000044400140d44408072148620359000b54008a0405070703560030301460b09800c0700d012603010030b041e00305500135811170780c54030f05140118250340c142c115101800c8042107400c007100c00103050303480c6d6004d03159244500080d03070703075003600041502080c94120041030b00e605802d40b0540c82c6010340c0051030b45040011140011802d042800c5e010046440300c4240e25640c240000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 358915449 1250 358914199 358914203
    0x160b04030c061104051f0c050303180105010b070210030905190803010801060803070201170411060711010f0509010c031b230f0c0f091008121b010c09030b09030412 72
    0x5450391086510b032503030480b0401c0c40c00c941800070510041140b991800e6405243d40840e0004124078505031006945150040b400140a408080200094020400e00208041e11b03260020b200f10f99884038241554803c502019409c490722060899100780241c000b101e00620803c1140d10808440403c69011500002c0482c1c00313000005c010030949000f40242c001070180c200103989041e913540e00181840120110781b1100d2403203e4000740510495443c41456000702809056581d480307490300075000c189056150b40421010002c440d1981c2c42541a92401201a1120103040b4020340782500e448010100c45006540325908260015906010300303e000c0700341400c40562031a6000300b481c2007000100710b1300c0341944961b643c001c555030f6030141c14800400c107031402107481d21040202e00300c080103034201c49405d204940351468090154001081d20000312108001040c102c200303600d00344e030303a00464480001d00e0841c0074400302d42c0d011202900030500f0320071689450358805c81d40840c0b5000d1481 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 358916699 1250 358915449 358915457
    0x9010f020c1c1406060901031b08030a090305010c020d080c0f07050106060804020a06030e06040206091215060f09040b07110f06010f060813020a30080904060605130902160b0403 78
    0x44080040c016514101c6000343d001070030302890900d0100c4c440000501c805042182410700710301880e0300301d103111700103444101e060700c3c1c0c1c403c1c00701005008003005110441e610340ca4120038007141d40c80800c001c0b0440e0016520800035403110030700031402c2d820840c070300c520112007082900000b900900c50b40005250640f00d4030344074070701030040004011040c2d01280a0504181c404440031802141f8a40c2c031560440b1324684038845100032505041206280c0031941c0301e080ca01900c0440341c41c3c5100d1003180101d61040d5080282d00911800c1101600d008004400b03d8000c10242806500b45100201100080300c1152080c11800e0345030840030303800000c0c1c6400040c400d000896000460343d034044031556080f240d101e141d6011030703c0914140f0031148598080c40e080101e50480b004003900960301c05640350b1002989040c0a8210792100e1003461040c1d10340500016514001c4081c0c540020840c454040080d16110b0710001075400200c1c14001d00311103480030743c001174858a01900450103662 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 358917949 1250 358916699 358916749
    0xb150303070501090b010602063c090c1e0616170318060601140702010e061306090503060a09032003122a0f180a050301020307110d0903020609010f020c 67
    0x170041c5101c00180c0114046400c407400f0024401e00501454200d80f1b0f080480302d40c0205800c40d000f094180600388070b296541030f00d090040203040000c9108080c0700071507244001084d06078500420030503501e00c10b40c02c00818007480301d1070031200189924060158500301d2a14803403150000d21a8000c130b0b100d03802c090030780c1a0740700c841600b0040e07103600210030700b40010101c0c2c0d070800164450045038002410000440740d282480c2c2c1386c0400740c40e08043d0782e125420703d95403103240c0600140001d00540303009100700341c00105810018041e11030025007648036218600c801030307003d000001c0210559845803004114401810703060211103403061203140071a4180c8001c6150389400c02d001001034012200080c00b50848805101d0202c1e8185822514100242079035240883c0c83c0c08a03551000341d241d4404410481c7e2150072900d440207600201c404d860246400842c19180c081d118000650030110502041c03e09500960344540400311500440d200d40d03922800103041840c802d00c1d40380003510301341c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 358919199 1250 358917949 358917953
    0x2100c121a13050c071a010f050901030807080901140f090f06030c07080d0207051b030d0216060e01020c0d0605190c09060f050d051503070e011211120601030305040302150304030c0b15030307050109 87
    0x4420230b009048200e035529030079491503c54600d20702070a000549014030000d0b01c880d0a0b1f014038122200c01071119402c6071100602031980302e854100040d0b03d0701500003110040301620b4190308603407049202001c0c107400c209c1c407038580d0f1009401c80f050325140781e6401c0005401280081190f000d2100d0400041069101404141070500c0d210000010956100000440c2c2c01d00108d00f521086e24803500d40010540c1c802c10040380b5003260303040800e8000001201031030a108080e00842d100e00c1d0001800170101117010074000c2200c06030340c407140028034001d0044c401c0900c1280c00c4070702c0c0c0c291807400300c1c180300c0750078200002c031074041e500d600c0ca0003000306521600d401d050040700c0083c107041540c400158584400c0902c06108803500904c09a04041c40c03208658940107100301401e4070001301d803101d6850741380250555005000503441003a8803c0c1c0da0503031044080c105c9205907810baa58000030300941d0383d080a4182e028100c10055000c803040342c07026031020005802110302404c0042111070041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 358920449 1250 358919199 358919219
    0x19090b070524090604030e0f060408030c010b010906020c09131e05011503030e09040309080706050304151a090402152703070501091502100c121a13050c071a01 70
    0x80c2e02c180c8a419501000000301010840550254040c100000c112006e0000241920782d03952065030301c05804640031a0f01d20000010740010360a050003006440026001501c01c4070700752082c2401a0307c5040c414005003048415244c00441052180110390600d42d60b0240600c00c0d06290310031101d0212082c030511200340aa080140c940c2104060301ca41191002083e0284480b4200e00806a520100c0c00b014451030b040002001c410301030724030300340d11064014120b900a0314241c6030a0500030306016001c2491054100c00f10b805950901c1c2c84446105000b900c050041c416a4441080002060310121030310091400e8080c01c00607102004d800341410095094500c5820f010344c0c0b1684090009980200c0044141d83c502e00f03442c80ac008213400201d02c0d00340c0b800c0c80b24030811306015a00c070040f50001a00c94031282c901d54140210042c00320f280d504000301d6800940d00a46180d10840d05010a502c1660086586004203182070490384540000b140030740880900020340100400c40d071442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 358921699 1250 358920449 358920493
    0xe0906040203100302210312070e03060c0a0c050c040c02030a12050c071e20101728050f160f05090603061f0908100204050619090b0705 60
    0x8640071419402c005014868400d40c070301000f4010081800b80520542071405c203422441c0d0b04a0850341d40e1220410010b0004005495407000b0600c00000004649004100180f141e2a00e8541d5802d0803131900c0308a40303032000e00ea81514140510440345050381c4450165012555040c1c00450780e410321244002c0041e00f001c0e00201d10545844140304405161800711400550400310101aa8000400800d2412000d003001040141a0108100f18101642c980c2e440000200ca030105100346610b010f40d5900000c886800c03103120070f1000942c00c944e110074140360840e0f100b846014910060003e280495500796060012500f00d80208600b02801000c4600f040c505881c1c400e00d8803d501c1c001400500640881c1e521405008c0005545a140c840c040031341c4003a0780484031040c1340700f000c1c040c00742261400b50030903034010b000d00303180400c480c4c0c0200c908840c8040e1030b10745810220901401d41d110341c04082020070100c48000036584403104041c08500d4000d40140541100b02401c1c0003c94003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 358922949 1250 358921699 358921711
    0xb04081002180409080d0207060605010f180501110a050f10061d07050d02070f060f180309050607050309100f0f080112150f090c030614090d0e040b100e09 68
    0x1c010012249034040c0e12000700b015140a031000b0032640c0d168907002e11103000707844082401c0c91010a0100521040b0380001e0112142a2640b00c160700c841e9800320380c0503d001c00802d4400740c1490040040d5441512000703001620901510001401c0307965080c1040c02d9005411a90b07881003410641e5980c01d4441d0780014004080390034801508500072401c050b00041410341403140201e060b2590131107540455540070f621000030b6565468a181c81b0340107049031441d400199180010b00c9a60303100c0c1081c507580d0290543c4034540007a25240400000d680800012102030000b03000140098842a007100d145011030740321100048129070000b041c0820341741c4110204600d41004001c040a0b582190f200380d50024086100e4040e5a00c800c1c01800a00c000e45441038548441102070001c0c507228441640e10030002030181001e81500f1664160040c0c80703500e5242c0104080c4030245000d441e8940100602910228080014030001001c00d00c1010805011a0000c071585080b4070304a4403090b8009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 358924199 1250 358922949 358922951
    0x1050f0a09080c040c0f0804050a0f0506070305010f06020c1306080708030703110705010804060c0e060a111207030e0d03091e030b250c020102030702091f0806060d020d02120105010b040810 83
    0x6516174600406a05d20380c0442c0c02071141620102c4c0c02c0c040c052012400d082d40100d44010140083c0c50300650311101250171000092030301001280308002c2004800c1283c216a000748010103070b610400c180300f50049040086d003680c0b00000624420144034050080c103100c405107072115254140542400c035103480c001d805800ca800244416a04060010380080d008a00040c242080c43c40c15145060249480350780103401180000c0c55030343c01110f011525500c076059619a05c01c2d010300e00c0741c0b80a8050010007040d9a960a1a85424211100c400c01070007450050325280d62100c91403a41c0d8031009507040c440358064007e1080c480d41c0c00010760010030f02c2c01c0c1c0c61000784461007014100110004035004100b023104084081d60301c2081a03c2c000c54000385aa1000d041802d1840f5148444204031115119035400c00920002c0102c0c0191141d00e000d00707407000100c0141e003002029028044201d91007005d066031801d18410900c10f55002c0c00c110112913030b41e50b090503080b6182100c6002104211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 358925449 1250 358924199 358924211
    0x4050d080702090921092805010905031207020409020303070c0b03060109080f0627120903060601082802040e0901050906090307031e0225030b0112051b01050f0a09080c04 75
    0x2074100c01c4211507201c0d030301e281703150311202d41da80011a080202001e00a0402c003d45400707818001000e141000c07200262550208960350780705054441540c148440d1500d081444170001500700381d0400b80d1582d1004003500c1c5801411341d1780c40c144000c6a00000e41e821070100400030503580003110304014100c11070040034400c206602c40769450b50300800c020000101d05100c80f030a8014451001800104001641d400543d4a0805003080d04a05680c1d8443c2c4a000040790003035004019045c001d154144042c1b41818240803208000d241e46100340e00d48550030031001a074650b849000500417140e00b030020916081c040381d1145000400f924031007181e04108004070000e13401c40c01c40c1001e0b9222002041400406413000d9041400b0104c100e00c0042400f0500403040890107400000d4900c83c0100030096600e5044140008240d4200104607a0118040c0d40f5140d8001c2d88401803e1014900079281540c00040028a5000134000001090013803c06104a0078148020035800800703540c20000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 358926699 1250 358925449 358925473
    0x203070306090b06031602011d03070605070311042112110709061d1f0303050c06010603020405060a0513051c03170402010e0d0312060f0905061f03020f04050d0807020909 75
    0x200f444080c00302011b5072107000004d041c5138001e404c1101550000800d8140b9030300000c075015100d034018101240c00301e281c2400104090301a01c6940010304500344101d007032074102464412402031808030035042440c01751002d030008140b4409070411718500e0b641c096500350000025440c1c00030a0300312800749805d00e902402111070900c2d0242c0035080c0b038800c01e40f850b00d60811402c5210600741201816800240e008400c3c03681100c01070002c60035003000c0303440036030361a03a00701e0890003207006040c0d001c01c1c20031001146138401c10107000030b902c2448001d14040d86e20030009003d40351950400c006a0403c600100625070061015075900716048110340441c5850750000741880307140d8440c14424046006880c1c2030611440b00705040a040400400503d034440c1d843d8000c03a149032140440030381c100030014600d420400246034940380d004511010b40896008140d01075008641403441d03055003404001501e03550401c0248000c1d010710801903a552550041c0080e05200070320700381180d4080880064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 358927949 1250 358926699 358926709
    0xd0309050d0e120106030b040507140f090a022b1107020901290703080f0601020d02151302280f0b1603031803173301031104090203070306090b 63
    0x141c4008518060030607928103000120480354031200200d40350301c0c103813002c0200410341c480d050080340035400b12000c0c0c0b6681d000b24400d0401e0303050002c0d0060402d00c0c0c0182c0604041400e2900001c8140b0b01500300061401c1100540701b040c0c1c1c1580b0469000e2204c441862200c0c42200f841d81000710203030303150405540200e036032514107204903032a8480d401c006501c0754282c000140d032860001c0404550303850706418020000700094881d00c2040c0510f0300415150344c00040c5026140905402038180345146800d0520b210a00800026070682c1c0350022000581c0c071700d5100310750901c0380c1500f000311165000400100b88819005407035201c95821081c081d001d40101030320981e0700da01c00c02d00486c1c04a4a0101c015007140c203020040040c540a00008040d04410103102400750001d900d4100c1e070b40c3c8030350305050541c80075001c1c007101d404440c0816240c1c0c0d2400c000104200c18180070038564000030b0f110b1004d6101e40d0000130703500d0380841844222a894011b5800030242d2540c184041092040012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 358929199 1250 358927949 358927963
    0x916091712070309050d1a0105090702061602010b06040810140417030a1503150c020d09030b1e01060512060a0308041815080c0310020a020606013605030d030905 71
    0x81403050702044503010140705034039a001500c4041c1841c164038406160840010b4080504191784200900001c101801c02c000001d100c0c0540354010212904c80f111001020b2601c03140903821552580720881c0c00b40c071008000c000510068004150301803000d1200000c0311380c96011541c2e00d110300c1007400003040b020400c1080120255219039035035294515640010862100108451188600004280041404800d00d0010382c25000e0251401c0503000f2030f00c8061b2010080d021456080041c804a0580c03c10a90f024000c1c0c10300c0980c0c1050040c030204051400d90041c00040c00c0080d00c03540c1541c0d4a0803158000105490720b2071070500b1603542c514603010358010210001000581151004005c0d00020301c2d42031410340c2800440e4079135007041d03240c091864040c0c0c080e214086420800303030100d07c00c44024000760ba02600c9281c8421004461240341d4010b80360810180c01c03004900803c0d1003440f082e154980ea005503008034078010034181040d194014100c01e0520300100540464004217020f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 358930449 1250 358929199 358929223
    0x10c080621010612031205010b0d09020307090e060106180e0f0624090a050603160c050a0501020307030603030801050105030f0106030c02010216050606120a0f03050904020909160917 80
    0x203100119004801c030044a040001036a20035820094002018450168040401c1d4025134131020780544c40e42c02d40702555421702c1094203581042040c89071084141c1d0000b0003d601c0141907401340c3c0d0f524003a8205130b42103d8450055038015400410000360800402010340b002c44e90bc214a1510b0703e204803006002c014a00315080d00250001039040d07848503400c12650803030040e60900d00340b0868140203d6004844420b010b019101c0c004034581c60729009591280007003012540030503984c2c3c81d04031072107d603400044900f44a801c2c0e2070710007d0b4080c00614800d00c1242d0b40020f156185040c0100f4098042c0d00031814841c0400078412842d9502c0d0f5220305641142c1801319021000010485c0244a5a0b60340700f4944000641c0004214020516500855003140e54469804441000310744070181c0b418010220820f000301e950000e4065000380550910050005045c16860008240c5456080301c10050b0260000103d0812a40180f00b03c0003074018244094a20004007038210f60b1034041e0340c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 358931699 1250 358930449 358930459
    0x80106080708031206010908030a080f090f0a020402090415090b1309030f0e060c0a0516081203070e0a050907080f07030b01140906070c0b0a1b031b11061803060603010c0806 76
    0xa01780c0e4086c222102c0108407182c200c0f0307a2402c9813000200310703e10642d0080041c685820104d0b0f000c25000070501c461240800151840000e19420000250b00003806c007900592240c0319481104018036032000200340f402404150100250204a05c0c0440e100318603030240d203090a840013099102c803200b911070215042021030360f00020002003190241504001440c802c00440700100b040104e02e00306900d00d1952600c0100d5250841c0701c0d01c4441c0690b506490300d105100143c1c2032880703401228038440c405091030034840d0719100802c0303044408a56540100e078590041c000b403030910500c416889030940c40d0401043e8000b9000801c541780024601e609001d0116000340702e6a10041158030095010000711078030790340d444120740580c001402000c04a8003000b0001d00c6440c008280d111a5540356403000c000000542c840c5401e43c4200d001030b50414840074070420b050703c41c4401000c00951043d031039200d0380344001c10146010307001401507000364100004031484940044040b504003d080703031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 358932949 1250 358931699 358931701
    0x30f01050d0201020a20040501080c0312130902122706070509060c15091207081204031b030302030a20030604021c0c05070204050c1201090b060d060b040801060807080312 75
    0x4074680382030001c025046c0304031000601542442d030074048a9400090302c0500c03080c0e0b40c8909003921054518161a01500402011000800c203000104103184403c5100303031580b0b885601400890b04103441c1c191000d2120824040c1300030180d5854003000c0c20301d0780a900c0d0f180c50903254030f844640c06000e401c01c1c042d010a8a40c800d0792500181c0c0c10ba50140021900610b0801c00e0302102840d0540b03040d840760040086086e003908404040755107090b004024249491245861003180d0382c0014010790411400750040360106003526080c940c1a4003a41c3e0150f180d0800d00d06150485480c18102451130300303003e0414040050110030b803648520b0845006890f190f00505140c415101032050b211103624103000e401505070044041c0c502c1d18002e443c10045c50792a03d4125409200da2035000510321004801000b40c45099040480b05802c0981141d040100f60b00380f0300d00350b90403600300c400c1c002c03800b00701800384101c2442454000d10106005012440c90070700600c4e00d9100c0d81c00c1d40c0004c041010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 358934199 1250 358932949 358932953
    0x1101051509130605040503040617130b1302130b0a0b040609030f020d0203070f03030806062a120f041502010207120c0f021203130e0c0d05041a131403030f01050d 71
    0x410841c2c1c4080e0400e10501851510b0314005840b40e03ca8000c00307012680d50703112442c7c805980003000c0d2003041c180360742c0d0740910040d80b109174400d0300080075010250340240a5400603168003801c00000192500c0100d94030305904204074010001c0c2e0807007201c40c0300502081006a6028401074120f03500801c9243c80c0394214000701d4569615610080d405109228000070700b160780c0d400038801c0740e00030f40d62591141c03500b408105039449a1034881e4180b101c0911240d50781e170030740110114107050110481f440310042000f61451508510301e40f0041980105041014011000c03034071212981c03030f200071860031105070b844c0d03981d100c1c100290b07104102c801e101d1041009900d081c0280390540040110641145440320325580754000c07a4104804841c072040040c400500501090040120340b800701e05040c0101e8422006120041c800e84e60510046400c5040103d440d1445002c0c2c42040c07494003444020307042000c3c10748020052408107500400400c0011103d10628906540c03040325a5414000c10b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 358935449 1250 358934199 358934221
    0x310030b06030102040b040b04060201060902070803041101020f01061d060a080601120c09020d020403021c02060a0e0f0414180c060304020d03030b090a0e160305030f0a0c1406071101051509 83
    0x141c06c120740b20200054046030030400d10024208407003807903000b4405980c9641541c2d00340d019492005140304c0e000e10121f07000800c0b2a100c01800081807049600004840d120f26003510810340c4440c9213111031309001c80785986070080e8940d2191003610030041403490003222650300c0005100b101c0d00c681075a6009402c000e101c404090041c10031a105544032a07a0240c4bd4000f5809484200d200754000e00d508030441403441101100582c0092110b03003490301c03603001640d0240c0c0390040c003507100d080c0c1c2d0300d035500c90b030360301d10a40f0b51144030354020010a10300301c40764251b540078401940030264000409540c99985800460f1361259054801c1c25482ca018a01a80a0456101e000e58010111002c2111240c0e03658040b10f079035450001142c2000f081145000c011000c18000544560000c1200c00804050b8000802c00d002c6146045240e040c500e0b01d60f040500d421000005041d0014024010f4050b071007040003411360112402005281058400c00120039980030718a400341d64104005140c90481c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 358936699 1250 358935449 358935457
    0xe010b10030c14030f270a021e1801030b06010507050a030e0a170105071d0306271009020f04060b0904050405070f030507150f080f10050409060b01080c0310030b06030102 75
    0x382c081c0701903c9051071040749862440481d40c00c048145842882802c0107200c500000c6d808160030b019040341c02198007071002c003803001c074026054401d40e86806805c0c0e480c0c062100d141c2c0f40c03452180c19001c0d411403514500990b07000e00003d040080c180314010200c1d80c0481c00602d2580c0c50305001c6511040704001c038890540c164008805801d80b504401d5180d00103400461080b80c0c2582d038604142c0c44130100c0d4810000794083c0340c1d0950300c2a40010303841500c0141c000c9085400060701c400d00c03441060142e00d066140180c280a20307450390b55880031420000398030000c0d9801258180f007a03604090103a075580c0906403103984101c0e102c801040c1440801d2021101400308030140000d616140d080440d9282240d207d05015000c0c2c1e0300442408512414141003030181640e070381ca00c5500c41500e921680c1c030000d0714201c040e0510130000204c80c3da0324850700c0e503000c3c800d44010a0700a030000000d400c0c041c000b44031001490041041000c0e03200444400b0301507903440442c0c27842640700c5002017402405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 358937949 1250 358936699 358936727
    0x51504090b0d0606081b010504060906080c090613170a030f08100f08030901080a060f120516121a07050a0c05190f122c0f04090c08010e010b10030c 65
    0x4030f003000200c0d0000c000f107000c0f441110f20341b120b081003440c62001150075100d140f15460001e101c03c04184002445861403580158032082801d060803101e40000c0c006900c20811810520645002008095001c1030741158510490010b0110400f040d05c000d404585200103070010448070900150813212400b41010240c03c000740f05510403603c0b802c206036a03911100d04030380810903c50001710060042d0140e0717000c1d0740b068203082503010b2510b449440c80f03113001da0741200d50340551841104810304800b03640c00101107017800f409200c8030504160140018071042d0405c0181120b04010040c0d8000c001c40300407070010320380745002c08960300f0000d05200b1a51400100144600d0058050040c5261000b0049010390b1910031241640803040d500901d1400038410030500d02041d503429009803812a1119000250150781108640b500240884400c42012100d40750b15950901114009100b5602c07201ca6420080203070001110000b4451000c1901d100304064071000187c00840c400e10040c55052 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 358939199 1250 358937949 358937951
    0x606070b07090512011503080f0d0203070207090b01051207080c120406050906010609030b06010513051c06111e0304020102010e0609030306090f0103021011070819020a051504090b0d06 81
    0x200703001070010314120031446458483d441403103080c2c003039410603c01c5032510f4034003072488500d85203141e51341003e640107228030540760710040c4490702404421b40015880741d25a80c0c06010020b0400038060119021442c41078108541406032440003869000d0a5420a1003400c0c09070303d50b52007540e40e0500344640100320941b14805c5051104000c01e03908110300808500e4159640c580e00e03031808407480241440040c0c1008003c80120b215540501c0c028814050301c01480581a0b40360408568054011078070007070021482ca800106003c42c0f440b59030042d6524a1099107429a440e80306a540e940d4500d403049d2000c00080801d086a0003540940034a00d2500c064907003514281c0f007a180c40350400c40d955402103050388001034000e090600b20030305032580105140355030000311000712501a1012025880b80c81007403404103c502c410080520300c4221200c43c001c0c958030380d10501c050746c4080e0b8002d0303000e1268404800c1e080303024002a04e06807407a0704c1001076400808000295600a90310000d000e071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 358940449 1250 358939199 358939201
    0x52a19020a0b01150203070807020d0b04030e0102070602011a040b0a0503120d050714070f1a090d02070e1e070c02040f020c0c09060a0603090201020705130213060203071a0606070b 79
    0x41a000706508003881d00a181d10b111980e40c45028035485462980410b0040e0010484100014900c0024040550000d0032603411120305a8902c452040f055509402041412a00746900e60307040110401034a9244000d100e003030b07007400b05403010099207502c00340700c2c649540100d100381d210b01140c080108801002c5554045060440c003410b5070080d0301c042c00560501c0002682c03e80260710641001c4e410020445c5821416103c07650300c100200740c1203c821041e05401e5a05682030120703180100c060071b010700200704c41500e01924000380360f40455082c0e2508410810045016042c03107090700d1b0505450f01d065540c0400c03c88869a4180009500c6440c202401c121181568068100c038854138085505e030034048010003208030812101640e020600301c0040c40054802d030004072101d44180111000e0548403c005045000d8803400e060940d980820a0f080d855500c154030401802d0354000380d031501c0504d46078240ba01e59070340546203004d081103012400c682c0f00c81089829994020480d80a5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 358941699 1250 358940449 358940497
    0x150f0902030705100c2109090908090d0f0c0e0a0c0804021003091b0618060309111002072304060609030314090d05010c0201090c1a040509070512070c0213052a 70
    0x486d08144132900006a045040459440700510411103215001809203080c254a0002c1114400001d1011a4a2040c010300c2e800001c2030255400003030280807505001900e0720800b01320464068168050801007a40c00f4400584c5448207051002840d0303280100c2d028010741000c4034100c2200b1050846c032103c103600000e00300ea00403000c0d1090b42d040c865850056070356040840c19210340c0b0310060301d010102c0c10750740071038034002c001c0b404030015a00546a4941e904c1d65003a045d42030100c02e040084504202006040c60140f0681000e400d07d0b00307044036014159100104101d20300d0050056402d07000a80d4215565442000f044007039000c002800707550701c201c000a000c0d1403000c004a40c0b03007410890110f00e4414048184c1c100d09030050300f25003458036100c02c001c0c180b03d018006a05114080101320642143d9002591103001a5204c4060b20131b00c91041c0031040402d401d031132215503e030005008001d10413480920b5101c000d08a400c0c00f405101004200c0f81c0701e41c842465544000ca140e681c0c4c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 358942949 1250 358941699 358941743
    0x110d0c0203060f16030b0109090c09031203020304031202090a0b0313171908060d0f0503071101080c030411131a15090f0118080604150f0902030705100c 67
    0x1054038401da080e0b410544a51800e044030200a0321120304400042d803141030b00611980c01011602c905240001c00380d0340c1c9a1074407003291a581c1c3c0800001d800401c0c02d10901c6000c1c003c04070f00600c0c9c0d140c21895454941c4004180460752450a00103c0d000280d00e101c075500e4941d4040500005a20345a8078200311041100d028040318084031181140c03040380960304040c2042d903405160b80440c0d00504d000c016400c0300c51090060600c0da0146000000c500030a450036072a51b4418420802140d8072895400c06031078040074051054100310a0314200000e91400805494010b5132055044880f24881000210320080a81c6001303c01440d04071048400030002c0e88611041c4020303900da154004107070a40c0500c41c81000c228980003c00c2c07401102840d40300707120ba0b4032000740454502d44081e48440c1d0484c10001d05580698108501600603c8110640c0c401c0600b110074500c8100912082c0c3c2c6e020036154202c80c071403070703124203510039001c00e06500a4050041079544105002249807032189841 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 358944199 1250 358942949 358942967
    0xc0d030c020c09010f050409210302040f090b060708160f050706140f0f03060123090f1f050a02030f041203090e07080a0506060d050f0106180b030a020a110d 69
    0x60040c0700ea0644042c0c00d0900a00d454181c607120b010032a540d46c00c20050001410b40e0000807180961240364810000003c50031209111031507560159132240740c405590600c807540e4000d030070440c0c034240f4035501c190368550860312030982c05000c1c65202c0340094000c45520000c03000c0500b403035a200c10010101309002c600075081d40c83d941c1304d000e0f050710140f46c1c008060050030747c90b85048400b000255200c2c0094809194000014900b800c0b45500c001ca0b220001694940389020301c0101284e600d40e07500c1d181c60076000100f003d498043c04000703001c028080400201483e4018040d000404084051080c03040b1410480307540b00d5503507243e0f03461240f0151800d030300100380e0001c0c110b03034004a1040c0303e40080310f015003030365501c0861036164002c3c094004c0c407001d400700768001c0c001c101c10351040074240105417003022403040d414119031400e0005400e0100510354043c0080c01a031040c08030750340f1041500e4002511190040e11801820002c0e070701001d5a0f0315036041440b420241030038141e4444005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 358945449 1250 358944199 358944221
    0x7030617070b0f03090a0816030305060409050a0f03050d060b0403020312071a090307140606040c020c220207060912030b0d021f18080a030215010303051b030c0d03 72
    0xa0340d901030400d00032603160a81d0380200701103800204003050b021510003016503040300302c00c42500c01507040381c0d80d41001c0703a1180b8507880440e10800e002405044d0544030300c0fa488201a40d05000122007591201c4e01c54138444001002c4110740101e4100b80b61184080e105608042e8204201007611003111603020740142c07104a00c284500d11188420324040000d45a030700e84c4c080390040c0a03803040b098810751110000c1c2107501740c2c0300174007001000c950410b10164106200c48003804650401d1014002512040702e205800c0d9801040082c402d42c4640b000c1c12580c2c080e0751284010780c0550110303074010b8402c480000c3c0200d4240520541484071001c08581142c0302624104100301040090051080c031032100a988060951540c40f0900ca0041c1c541d55590003500e80300360451180030078881450182d81000030070707070700c140040310030113804000300790f20b42e1100e01c0100029803560ba0010007a2060f2085590503400080000070102800c205484c0d5040c43d00080c1c0f91071000810000340288002c200d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 358946699 1250 358945449 358945469
    0x607020c0a0f0311060c01090501110316090f06051b010f0b1e060301090e10050901050726071404030b0403020d2d030e1501031104060611060a1107020603070306 71
    0x200181c0390b410500e00c0c608481e442105003048901c850104481c90f04070700c942d04501e540350703080071000031030a1140a030203064502002d030b124140700700302d40c000f0350f5820364200c14011000c8003807040e041f2110030003040b80e00d00c0c07030f1030b640d901c1140150032900001440340e030b4601c2d0b00308540901106003e40020404c1041918103c00d1010b00d5031034060014641c03034460760001010401480f1000f115000352084002d02c604413043d8180c030303054290882d81c04450340a19070359600c0502c11225130042149181001c00c3c5540079011080801d140a2850090482c5091120395652821406010429a4020340d00000000150b15103424080e4990039000c4000c0001100c40b85c0000072100301e10540403424800c50010500440545400d400520900000003c1c41c80341c24184103801d19160807550196100c1c0841d5488804803200b03100903503000e50000303424498010701c00418080700050b0558400400030012441101c0114442814411403001940043c000020025160b816405c40340446010082d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 358947949 1250 358946699 358946719
    0xa030503032d0114010c0320060103050706050909011421011509021612051306030b0907020604030c0321060e04021e010c020f04060e01030f0303050f1b0711030607020c 74
    0x19402d42e848404d01808403036908104078000594802d4108800c418800d0070000081103101841c1201b42071040c107201407a61188005108225050061000400c0d0034100181003165560000c0c1c210081409104144a034010120442d40e43d600307103520041d01490092070035a1844081180600030752002c1c2c1400840c1d4108c0001d501c041882110b08501950280003003041c3c607075403810b445417030000c01d40c820007900b4843d45c8016000160140002d2a0300e27100098264801000c1c8599070340002c02d050700307640090b810040466001380c101c4441d80e900d07181816411411024003150081903205440300e541ca0300001090421440005030300a5000b02c5415070108011035101c0c1c00e0700c0d4581c1882d0300240d04a44004018202880c0e0441c9000c0014008510305460700b15001169000f40e0040c0c504480040c600c000b0303d032301072094a0700000c0003045104a4600440b07100b2909120011b40b408200d80040c42c10180615a006c240440b0300040c291412030524000080d6642c02004025100c4d4410403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 358949199 1250 358947949 358948021
    0x313110109030308240604060e032a01120e0304030303140a0e1b04060909030207030314090319030c020909070f0602060f0402150d14010306060e0601020a110a03050303 74
    0x203a0007046903419030328003180d5650011400b41080b00303031a2000700d100080528501e81c2c1d0b5071002600c090012541e0b0b201180030071034101403078011050069901b0014100d80d01001883c02d1101d280040c00a090100c4c1a0091098000050070324182d031481602010074003004060f40354000c428264011012403605484c0c1310f90341e20884880c81c0705c200f01d5034003186d10040b400e4820103007002008801400003840e15503030f44102c0e051300c0250f0422401070304100c0c0c0920425410018602e074551801c004a81030441e1003003c25a40c8400501c58140000002074460030107204152001d1825809001c281c00d5061544105a0310302c51802585029041c1042c0452024130001d450b510802c6d025100c2c2c0e4554413a9000d221507800624488806100c00300013011041d15a80500181050180360103d401d6145083c4802280e4036074212100580300b0b1801d11079140e0b0700246042d5410f403c034011114082103a8009902d070174039640f008105000100400465600e01409254031419803445010612844 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 358950449 1250 358949199 358949207
    0x2040f0609080d0905090601020a172d0d051902070b15120a020f061201060c0204151202040b04020912030304120c050a0b0a140108030a0e0319080c0a0803131101 71
    0xa950800001c138000c0080007246855600d994100030103006a030540c8800d529202c080050801300c034103039440002a91491200300c0078409500c07000c013003614900e003001b03488500c11610414000314081c80c0c454000c40e40310a080c56003666080342c02c440031555103a0a18000300d00c0481111000041e840c51101c1001c14142000103003007041c038001c00382011500d1075003040b02c0440c6143e560394101714140400102258100241c502810990712402440394080c4100020344114000b600d04441201c4410080c10068044a4024030b5040b600404e1000d60700020600900449000365030008100036a482c12840c088003c0d4056401030302103050f0102020016240241d5411008103160710542d021004910034421684c0c000416003000325907540c80882d0111010800c0c1c10410454000090610322203070020f0780c10f18802c03410360107041c500544580d034813a086000751019044010009000d0700d054000e0242d03104490380400146e8403401e014a0103c600c03100c11404480e440001401d5002c2c643c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 358951699 1250 358950449 358950463
    0x60f0e0a15050607060f0e15090c0a0f050906010327030810030b0103031803060912030515030601090e032502100201050424090b040b0a0609060b090d0302070902040f060908 76
    0x20300004d14200e0540c0d1400000c0036500319a003403041d980c290140b80c26405108444034a181035001003014101542c015051400e048105481030344460010000c0036040c0640d00304889003101c011440d0703903c1c0b03001a80940545403000c07444c40e98204400322102e06c044588102140240e4a590059580c0502d60300000303d9408082c0010070304800400c0080d108609070b0321540c08824001040c5a0340760368071030a0715038007801101c3d2014010100b44034680d2611416900010817215207030000c0c010800300342c036101c0600507840e5a5894512511000704100101d440b038845d8070305e4104401c0d01031721101a0090001000300d11071010348203e90b40d180d1050090303d000300e0b00010201e44040b0450044030f01d41580446108c40b0329124146580407406610b28544070724041c10064865240c560441822100160882000c00b440d1000910481038900161400e4010541da944114540c501f030581c41c2c0f40150784102c41090000401144094802002c038044500300e49821101c503131194a8a500c0c0c200c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 358952949 1250 358951699 358951709
    0x8162319230307120203040501060518161808030d0c020111030103050606130e030304050d0201051303080109020a05160501020a0f05040501051c110c0601050928020a03060f0e0a15 79
    0x5106200d021400c1e904030000c0d90044054200f0105842c1c3c0c000d4054241c1e00200c40075650340c1d40d07952040050381000009001381c0e140c1803400151605d0185211150072003102041000c100441604502045540da60000507118540c2200d0300d900401000c04013074031010406400650030b010650010007040406d803030607681e003d0050004d81d0344140c01e01020440941410804580b07640301450039240900c0118010cc1c0144040d1800403032155010b420358002408880c1d140b4450200000420b9000784110b05641c5020030159480d441803c00303c1c0c0c24001d6007444600a9224000035040100542c001c100b8a0880d4590281010031048203a45038025480350034085003040045402d20001e000d440c100c1e0407917003040000d0041c1c04842502e015044010b011003294003540060181d4946042420b5000044014511145440354482c10040c0e40040ea44115980c0101e0310f0f50045002c0d40050740605a9200c2c2e010012340d5645680540201c01d9552020441c5006000380b844841039020380d094038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 358954199 1250 358952949 358952987
    0x7182d0f022a0d0203040b1804020912011505030f0d03050c0705010507020312011406040510020a05010f2a17071704030503011e210512040f0e070f08162319 69
    0x1060454114051123269068254841e60070070054001e41d4815440b8255178078950000188503040310a00da124030b0b201c0d04070b54880c1e070180044581c14a4006121620030040d864041850703281c1e1109103102c0c1c001d100c4020711035400c00701006103da07030000c050400e01408102e203201070303680c070204210024042581c007a081b9104203c00d124909003c01c0441603640148100d54420003a5241c0508460907010030b901295101c1c0300040060b11010681d04902010210701a250045400003910000c040e515140c11000307044005030100b800360a104640040f68404407590385804e29008100c0da100f4014010000c07100f50303604a0313184681c03010100742e960014002600040c481d03100c0d501001c0b0944100d900b0b104101c0d8010700c18122501900003071880764400100d442c00d0440c03c203030005008040b0010406031074400400c240c0e10540c020f070004044401d9460b60011190101c0742c008156400c4881c4c2c48540b241e081c240d00d6410010510501c18988524500c203c4000880b050600030304095152 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 358955449 1250 358954199 358954207
    0x3190f0f050c0f150a0b04060f2c0a020a110609070513020903030d060911180409020103060b03100e01060e0904110402070507182d0f022a0d0203040b 66
    0x2500a01c0203140c106548411292041200042149054850f5214202c0208110203101d000502400b4482000c942150107000050410203844c41540c4039104000d001c0f8003517401c5010422980c584800101c150b468002c0c102c1c80d0601c2c0003000b95101d5020b590001d90303a02050755101402041c42405400000302514103035261208201a101000c4000c20446a0800c03903107103d030340c080000b007211000310500412640c2c600031303004040b43d4601c51210315101003080324240c00c2d906020b80d0b410600c03044400142d07400d818001200202003a820070f210200c00003003801400501d902c1084101c8001c400861080c1e80c0300d400c11144903019000302500104a0404100028000c0d4550644038901401c01800c1c44203d444544c07400301e00c1e41c81441640782038400780c102000300c2d0091a903200240e810110b804148115402d250181c4c4c0c4032414407a07640c40040d0b04d014502c1e23804448265a41d000c0e4444081c6191180240c50420b030b01c25456980f182061810103140040141d5048070100b01e02d807420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 358956699 1250 358955449 358955477
    0x61809091101030c020f07140907080601020a030c030c08040603090b06100516020d0b07091e0b040b0a0c06020f0c15093f0c1006030b0109020706060807060203190f 72
    0x341680c0b001c004d0075400307105019440d04008000c0503004200147d003003010417500345d041c001d043c0c0c0050100d00070002c4250803c0616600050444001903051401e0391a03101030342001c55010f48a1030300140f85480c0000c00080551703054008010b0b00d80951440c0342991107500c02c02940c545a4843c00b008143d05220440103004c818078101000f0340058844070303003075145507608170007004101d4070640401c0c3c8020062244c106081c20001d0380351008101d144185092041303104044c003503445a954400d00001e583c000d400e200b01544615158020710a54661202c1c1c50940c50703e4000b9905400184180c0e0300140050045c030100a018010102c060f00d000318202c510845030103510200748400142d1540d003080038950300307030001101e207114107111034907a08080714507030500b201500341003d40c1d401e1442c2032002c0f90640866a04480c5c40180059031920709141c620040c282c20350021a0303034050f110000401940200c01030031505101800e01e004040f105900740c034034084c070b1400c100002e400e50030301000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 358957949 1250 358956699 358956701
    0xd090317061c1e0303020c0f0d0504030b15090702011b09050904080a020a120305060a120c14010201060f080703020306012301050f09040507030603140106030b06151306180909110103 80
    0x1d40742c020802c210f400d8840e603444808401910808500003503000800810b1003034140510081030703d0901c0503010700c42004000801e540164000a000f038903008003c40c1d4001e120300446c07103860f500540259031030b207420300b4080e000340103007105032002e6811100c034010039a200c0d086000940d0001400d00d44140c83e43d403034201c000c0e0040c1c0000015407241c40380400109480e010101b06108047d500810703680b0f001c00c01e109503580f4650040b0800640100c000001900041040c0c044d1440b6084401e0301100100040f400740007075178003210075010f00d0080412240008110201540c2c001c6d0111030561366940180001a5440304019400303207000200502558424001021249201107059091110000000d0116041a43d445000c039036500383c00c00802011280f41c48d80710103044000c004d4031303184d40c81301b184038000280340501c41d604003400100740b9040c0000780c8520740c0c0c0d00d5069401e00742e01c48030080d11040d24484400441c0c21700b0300c00000c084400d4041e28010b194000c0003440b0500e030120042d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 358959199 1250 358957949 358957999
    0x1e08060a1505060412020f0607150b0118032019090b010509120d030e0309031009020d06020304050d08010f0b0d050a0608100c0809031e07030507080d09031706 70
    0x82a00e000001090790b80c1201500240130b90a03604545904c403403040014010400c2d07400c82c02003000f401003270085443c1140800e40e20401400108038900100e0048543c806602502c3c502c2c0ea44001001c030034030030440d503540d43c4510f6a40412040b260300c00c1c10003500700d480741d01942c0c2e1030040503414003958140e508a4214440103042c0700d0b060950002c000749484002055805045e030183c10241d8480398103004002d400222a0701461030b0601920104e500d6502490b9640500b40e103502c0700000b191103120000d82100d401810464503420603241c6980c451961000314400950603200205100038000a4403040740c0040100524100c100211a8044d0070018818100c1950383e8030001100707107042c007a40040340c240c0070001511440907800900b86640c0604840140d510030700030010440c109000102001075031000e00f42c1c541c0c20502d0104d50510410200034108032010070308030b035a50751075000340394524071075210040410b044c20b00c010580344088803440e5000203141105070000f20016019 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 358960449 1250 358959199 358959221
    0xf0f0501030f02012a03030207260d022a071e0503060a0c0c050a051c03060302060706110c0a050d0906020102070309050909100e030307030b030f2505040c091e08060a 73
    0x111000482041c1400550600103030300380e001c2034000030100c0800c884040e010281507151002e0a052b10046001000180950b00409000903400561428054140d00c502d803503c880c45040d1021078144000741d1901c0311024801c7c03000c01d6104442c40100580707402030880903075601900411280d6940b829038405440810302c0b13001401040711003507021890502020703d5184c024401030800d42101c48000100c0c10b1800054030405203030000c1400141e584104440c0d0f40c0d07800000100c0d00f03081c0240d03031611500c1382860544288c42076100712400c001000c501048612200e8542070300c95944e0351001d9003230780700e1004001c0000e040038100303108914080c1c0c0032503080281e56003280d00500c000720500c02102c4203200d41c000b2035800401002142031b4103001d021000b10040d00601103203161740c4243c0c2d0340d454900c1e001040b5150400514100d400781c04d50f045004180040c424003402c1055200a40300510f44e0080c040d440d440410078811444c508a008001c50721490028106695070626180c0100000380d80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 358961699 1250 358960449 358960487
    0xc0f030203060f0f070806011b06051602010b180a0b060403061e0908090111030903010204180c020d0f261504050903160f08040306020c16050109030c090e0705030601090f0f0501030f0201 82
    0x3d5027150103849507006904ca205034800200c504101102881d894950b101000c00c5a0410060101c16181e2101003420301e40c01d001020703540c1e00d4105804001e480b0240001d83c0110b4082030010900c26141c005510980340c2c01204000780f50302e186000300f56038003604083d080e050200004103155100c0e07980c3c0c0110903045c0081c0ca04100b0701c5000242645d0082e8462001c13a81400c00195440b0191301ca51034003294640000d0030410460603015189540614801050000b5002c6140c100b18400086d5041246041801901450010844100303406540c040c04c0c001c0f490080015690030000049425884882000012445103a0784130402d00c01d020f00301b00c0f0415014400080018560b0020300809885c45000e00392688000500000c050b4990f40014100071403006d0030004114103091f0002a07920110307001c07a4806030f07801c9862420040b42e02c010f8241c850700c000000e0940c8141c5c081d4038142680750050005800c1c030711001007034070002c2c003001d0504070400407c10010741c010043c41c10103120f1011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 358962949 1250 358961699 358961717
    0x20d030e0418020a05191a0708040f0305060708040b1303020a020406120b0c0703142a1e01021c09050f01050405030301030317130312090c0f030203060f0f07080601 72
    0x1011800752a0084603102a40c4400241c0000710b1030501c513404054081541c0550b070003090300407015180040e41c410f6804c800000c17000626a00350b2501190809900f024206d680c80b961403d10b20000401c41c8419100c41c043c01d404036207128410121540100d820441000540d04c9e002134541d255501401d013241503203d213020072401a202c5014040080c0b0054640b440040c44906214400a00027084002c3c01e120800070000000d4003d80d100c840c1030130071104551244404c26982042000100008a03004078103280340a5009000030800b60306a002d00e6440c1000380c044545500382d00528104030f07082c080d10010704411400c00d41c00501c0c400d00030700480b00c208848502c210300f1100c003070310b054a5903000000103000307240e0808481c07289450944402000c41c0780030400c4145000300003000804001280184890056181d04440303401508101d5040c192595005080d40f00c00c02840101e0003030060302e00040080c80d01b0700d80d15100c4c11900380095550b54a01c1c50485103680f00611050500038180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 358964199 1250 358962949 358962977
    0x8070f092d0213050a090c0e03031908040f140601050102010b010c020603040b0604020f030709081903170612030a02060a0f050912070c0312030b0a0f05151c0524060405010507020d03 80
    0x100303182004192006c0005021a00b55600525442c18208a280640d10410130900b0a0100d0f40300b050408140c0d25001c48a034607140350100c0b81015500c0301078402ca2000c4da9001144c81c01048150407581c00760000c00100107071000650300e220074207101a60042052000402082c5a012a039034804002800140742c40800c0403203102c1500183c41c031200180006d4004e0040c4002000b0201c40344202a2106142a0803039a00404001c56010040e801204071008203501d5256140000e6950700a1401d0302d48918080704001c0d0b80303420445001c031090f07003004680038061513684110f5000c3c084000141480226800c60500c040c4e20002c01180e00016001d03000011904501040b0b20351100c1c0d81e40031601d00405002c000015226810107044029083c004201c0ca540b084c030700e020315000c80e1500da900d4001550f42c0d00c0c420b08140c41070440460424003040300840c0790072007081e640305460240703040b050519402e11600340207600a180c08248104803140240c5010110000c1040c824601240c481c8040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 358965449 1250 358964199 358964209
    0x140c0418060b0a02030d060608010f06051803060108010b03061311101202030f01090b04062607050319140718020f07240b1e01051308070f092d021305 66
    0x588440d401604041b9003041924140e0044200078041c901c1c1c0f4100079410024a101c00144902c2030806020001606440311036032000d407800403450003015201d5541e0348071501406008801c030300038800e024600010b94458140000c00102c60340104403022809910018440c000e941c40504038280402004d08401a0100380015441a0341150201040354503001d21001a200a000054032075410304105100c500c1c100c910480104040c90750301c0c524400e6080300d480c1171040b01d800c0030b0341500845000507061320709000315581c0644200e50403110f0b0012200825124078035030203a075005c034128118444000c450b035005000d000341229a030038542031542d501d10201203000c560010b01d01a25102124101d8120711400101460640c2c0002290807484003c104031002c0d496014103215000c9801c400303880c030001d182d40107800c00f04103e0b020385440302c034807040d120014840c07199138508045487c0c506a2040e003c800704003400c02e110170142c0d071500f1038000194009041c03120296265034000505079a039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 358966699 1250 358965449 358965457
    0x903030619180f06080312040204020a0e040501090507140a08160908011b0e04060e0402090c13030b0411011706040e0c061c0e0106030b0f090309040f0f140c0418060b 73
    0xc036502c00252035221203008801d80f016980302e086140c1007440030308564000d840045612035030445c2c0060b60380c3c0c01c864090780e030102c4c0c034107465410074504000490030f1641607010300d015880395140e0b5140444610b05445c4280b0400c034203040007413401000f0840c1c41d01d2240c0b040c03240d0300311400c0040c81152a8401c907400c503510180760300c20072201d120415071510341100d0f104500480c140d405012050070125070742c000c9640540024042c40f0328100080603c5040800c2e00c6000440d041da040695035241020989198180d0b41a648200c00c10f15082c41503020f1742c44000100c07520050182180e440d0b01c01c1200400710001985010300482c01c0e914082d0307071804018038505050300703100164050203045240031208641046013040c2c0c50140144089211800f4090340300014111610b0250340700401e650841c02480ea0721074100703040c04000142c03a041a04554500c161904007004200f4051011102e01841034a241d08105001c02040c442c40308409900c102c0000550b06c041246552020300300240d030301c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 358967949 1250 358966699 358966739
    0x3052503020d090608152b05070e06041e02070501060314070e0c0c070b0d0603060c0e130c120b1c0506010317180d0515090c10080903030619 62
    0x1c2c1800780c00d540002c89a405068580b40285d0145080e80e4160300c9000b905540074800c445503e2804601010540000000241d91109070003100103403078401d030350380c4050003028059404040081c1d42410701d0300c00c1021a803086070a00301000040c0280700300a6101900542e1103548480d030110201d0b48500c0000c0710740304040020407440b490002860100ba00103082050030031020003c0040025002074a041582d80c8090904c0d41c2e0104500c58000518203648004c03c080c1c00c109051540fa60001c820748825081a00c5401400d0044100202280c0c00c2e0950040814841850810345a10f01d5010148410001d8200d088000804040c41c0d168010f1020803116944110014820400300106544e09203c0d50514281000c00d00307089a1444a1042c030103901030310207800c41c03009104e801c00c00b42102e90014282040d0070708044100c5601d544c055107026008910342e03000902001d01c101041d80c8035102642c05141581c480da000c021100070b0202c000754001040050102e20405a1714111103460303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 358969199 1250 358967949 358967953
    0x303160e04111c050103202101021b0d020604150905100f1b020a03080c09040207030f0201050622051b0c0105040614010509360a020f0a120305250302 66
    0x10b081c1d0f945800c0c83d03006500840b090705090000400024504440202043d00c010710000704101c45c0c0c0001c100380b01c60440c3c544001c921100a0304040180c1035000f02000c02c0c80b00b0b100e200003145100c100360b1b100000c024440c010b900c00700001d40402c000500460b07000080c1e45000c19180465201da0749041d40c00c80000121a95804443c42803075007901c1040b01c0101c034622201000c108401c0080c0d07c86004140c094280040306001402114144c0c04071203000300000d00c00c45d02c078a101e04000f005220b064502501542c41d10010807240d00c0c00c10819040c10f0040300204040c0e958400c000d1000d8a00a400c01d010b410b41ca000c000909100c0f00050040001d444000182030b107003d040120907609110945030710701c101900103224644036207044582c05803c00d07285060000000c4c50700c02100002c14450020f81d0ba100b80800c40c0c62101058122205000320b0b12102c1446a074810880c00f44102c0c45450034008000c40d41c040000e0264019007a80100081c010181d04029054032041c0e1410304803c40040e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 358970449 1250 358969199 358969207
    0xe011409030f03030a061203020601060c0f0c0b03040213150308090f030102030117160e060909070b0c0313050307080d08040305090405010e01031a0f13050703120203130909050303160e0411 83
    0x30300654030a59001f400e20071301c03200c48000c058401030340310316043c000e01e0704000213180c49409000c2c020b2040710203030f40c3c4002407029103552208004440c0c0c000b55012449074607550b40c0d1f24160307851070164003410051505038039251407841c4d8031104198008002c4a410080d202240040c2e81d8080c4082e500800c03501849490385a09440340b2400c1420b100c2c145848824a400180305088040028030360000c030030748403614140c40d2071241a142c01201d030b0044111113030002d20305003040d5011003d40600544420004002600c0d501055144d0140303010f4195180c1c006411850303440e105500e40c64005000c1d041c03d81c80d00b0200c1002c2000d0b51001d030000d003e00030341000100208000c0c41c1c400d044006060390510b83e141443c14819000c1d0601601d44852181c8030008002484801e00c50440156405802000d1103403040d00d02079182e4011112410850140c060300088008041c041d9440300c0340c0c080701135850b550350b44840710035540714042d0f41f100f0013650341034600c1c080e1603602c203074606111200e0b109515 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 358971699 1250 358970449 358970461
    0x20a08011703040f05060313021e03160e0604051f03060c1d0d1106120f0103060506030d020703060f2403020913050a0209040305090901031a070f0e011409030f0303 72
    0x41c440030a00c00007842c1e10400080011070030300900c8a040e1402114842d540e81c44a0089901840071740b10041c0d130180c090314401082c50000841d81742c00a0065041c0d0b5004040f6080c10f2042c00300d03d102c0d850074004050006101403800d82d00c52603110f6a034a0392150a0f00342d4458406406900750011604250341e00401c0d214260004840b101c1c01180071000804010030002150052802810040260003100040c000310f60700c1d4405c1c3e441c0d0300d15401000066103800b150f0300d40c1c4440e00b0301c81901c140740742c507001c64401c0c200481e511403417188a400911030140b07140c1e205c000801c81040c1c9404034a9440c180715003c1851b08401c0e07400d450102c03500700050380c1103004010301000003402009000c0d1240c0d1034003002482c0411a05045034046079440c4d0981d0b0345060981c6c461064085c030345c0d4046009000842004100c0d03411900c41c4203a20781d040c00c83c2d81c03561001e844404480c507000d808100c82c61400310a640c826050b007121440c0c10404d035400c008400002c60b140c0b40c8000c10440e0740d50404410848 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 358972949 1250 358971699 358971719
    0x1d0a0e10060306091a150408010c08011805040812061507060c0e010207061b020409080c0615010203090a030210111204080c03010b0604030f060e0615030615010806011110020a0801 79
    0x2d0100305a0402c00d98006012207694102105c4040e8010b00200ea205640110076100b07840041429100a01c04250480c0000f05031141c05d004d640c48550703040ca60154044028402c1e244250ba0182002c0c0c03500c2c0601ea01401d4464008001031341c81454028040100641100600f0015204070000700366461900c10140c2401c0f0300d041018115030090904001d410390080240c4c2c0c558038000081040e110340d03400442d02030300460b00058000c85000480d140c10140000340c10b80310381500060a4180d1107035030012610b038071401e03100c6a40510703030200500140c5050000d414060400d42460b9400e00c07046403100c0e081c40d407200800180c54002060030010b40c0014401c82803d020114000c200b686c01c4407000841500550102401c02c50341400c0791401c00c1507a03405503048000e072100b280d603945013010704980d40412030a4100d009009060228505401040c070040f9443d0050b140c051942c0d4030701004483c081d1702c00380c5406141c07240400121106030b4902c01001c20442d1307070b80e60740d08640c14044010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 358974199 1250 358972949 358972961
    0x605060904030509040c0201020c030301030c0f060305010b1c0b0909100b03151b07060218041107050d110309091501020f060903030619081009020118061d0a0e100603 73
    0x54010080d000c2040700095011048418060044900180000813820101e00900486140c009103110020010007400428141c0c1301c21201d40784880500503450700c80860658100f0312601d00480b00c1400818002006410741804213000c8100026540c3ca03980c001441c1010141d400300101c1d04000c04602c0e2540090065040c00c82c000d40080240382010390301d0340c42000008241041c4070104c3d10f2810f025040820841c1c1460342c02182c103540720341c08041c03c040100302031484a0711640c07030035500b21039803610141030750800c0e40c004014010106001c0e005445040000c001100180001c0180d03030702d19510194454040c1003602124a070440360b100c00a4030b0001c07051020140c9500c08000c0100603140007089035030105050300e10b10410545003000214043c01500520441d008070482420004450350090032305034001d0f42e500303401b00000030044c080c1c81340d103000e020700080121400c1d0b8810584d003008000e41020244c00d0301c007015651142d85004042c244d40c41e01400312600400c0110940c140284 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 358975449 1250 358974199 358974211
    0x90d030e13060f0807050d06020a0c02211c05070f052e0b0303160f02060d05070f020606061e09060702061b01050702030a0806090702010e030d0207020112150e0c070501060e040605 79
    0x4001940c101342c001a58200041f0005100355000913403107110a00c14140641d40c154040c00200c1d03940c900c1d4411603100001450050103611075180f8041411245d1440d44049072101e8492614108907a00c03101d003041002142910780d8407407001d080c3c8000c80806a031485691010050b4000c41c1c011000742e0050341d002c08a001d1282e802400500c132a074000e00440b4440c158000013a242d10080d41c408207250f401140c044000c920314100802c02401d0300400710084014255080d0f40e00ca507101c40821260b0300500700c0c801503d950f40290060180007600040c5001b450051580e0308000460f070010b45e882d880b01c40300c108100032800d00202a50340034010705402c00924000381d03040c4090791000400107030008100a204554100c08984890700030360001e42d0b17010b068019607a890041324202d20180d4400242280011145010f5035042c0003a48103100304052042591142d40c1d1a1060340d4030240c0b030190904440c00f00c05c01044002607001d10031a8000e01003205040d003103151600b0100100d0768000d0036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 358976699 1250 358975449 358975453
    0x1202160807030c081209120f1c1e08070f0c05010f150e04020904060b01121b0905040e0316051f06060909020703090b0c0106090911030f12090d030e13060f08 69
    0x70110240081701c15a00701420588498180d1a08000124a0054180080d07090f500070300e117003d91240c200092a0f00b1401083e161100240300601d178a00e403612154240c80000713600b50707010030311461049401c000100c08038070340748a003419036859040c2110000b000b0600724540c2d52801001c248181031462004084541a0f821189419000300c0c03480b2000078030080071345903108070040e0181e00814000d5900190180104001e16004118050409607040b00b040459000c05000130385103464080c01c203034044813001a50801403891110780240d43c900e02c5c100c443e402107107003500d150350000c0d103a0403040c1d00904021406500d0a00094000b102c69085400d0a42c010401e1202090f00120407030b04403181400ca940d51056031001481c0140071540040f1200c50529030a41c00b80300c01e21020900c19142107055500c200c1c02c01440d15502c10742c1c0c40e01c03004015000c1c000c15a2610700140c40341c0109010b810102c001303240900c002644851784403c03403a245c540e99241441426031550340c0030094000840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 358977949 1250 358976699 358976713
    0x30506090604031223041506050d050a0b0c090303070602040905010f05030c10031503080d05132402040b0a030912021209060304060f020406020d2a1202160807030c08 73
    0x10001c050b4601c110f0000035a503203c421710458152200240c02102c0680181ca050a05040c074140c400b080c5a07444002c0d1403810484040307958a408031075482401e82c08401440b10000c1545d55071300c09400244600c0b1820014001d010031030f01d044c0000c05c3c5c0c01c0c1c482e120051350741c0e04201040007140e030b040c1c00152000c0c1d6901814000d645002030b0320005d0140c1113a0309110241e44107402c0303015024410b0036001140c9600d4002040001c25009480c00e00c02c0d0b030b034007400640c4c0d803180c5d01c0c003071b0408010016042a8021421031218428080e4042d100030b0002c0000d850141c582071410241d40c422007070700002a940d40141340500241902c2540700340400e2024250b98013180341d10350024000d031441c01d03102d030320004007040421000381e201d80034160809a09540700c03559600040d454201030380344400410945510603000702c0c420040c0100030312034110410140041502c42280000483c0301100940c4516880d0548241802d01c803100100703071650013414820f04518052402010305c0d80003410a0380419 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 358979199 1250 358977949 358977953
    0x17120f0406110a0f030218040216020108061c02010c030311040303110f2b09030c09230f04080702060c060906090d020c03071208073002032106180a0501030506090604 73
    0x462501424445482c0241c7c0320308042520007202e45040d080349900c00d10003d142101d004002015011140c000d072205a220380d140003d018514402541d4007100c0202c51840000560240446241d11070003031500090344a00074103505c10552080e00160045203008003118145001049030903641800c00d0007a141400091103a03d80b01c28106961181c1100380309400e42d01c541c031420312500215080000c0e2846a076807a041580201020001c01e5018075245610311840d4003000115401120102540105942e40e6110301c1d40700d0300580c004aa2001c41080080c00d507283c04c0243c60700845004028244a0a00302c01c8180741403403500c0004255040b5040c0004140d0340815042c04580840d0408841c44850740b924003801d101e118001841481054843c090b45806401d803401d0710f007070803910010340d414095001da070759018072860f0340500301c169120032041c008c40041c020780242c40600309900d0355a02840c807403000201201c1d540d00031692040100117021003009060341082c0906c014000904180d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 358980449 1250 358979199 358979207
    0x60f030b06063a110d0c02070303050d0b01030f14090c032d0a1401050604110c0a23010c18060e0319051e16140d17120f0406110a 57
    0x511480c42034000c8030307910141e10038520f065921030031021002c2000b40c001c0c0c95070700c0c6007140c0000802d59078052814440300350050001821030252505616400d0500180707154010251094070400c070704140c3c0b1000b481840e8001c034010540000a4444d28480b1441c0508013140b40a8511070803c2c4643d210800c00a0200003c0e50506d4104082101c01b08883d030401c1d90f414030300384240030010500d00c899402201e0100d019400140500b9044030b09000003612041e110f11240101d0590340c820350060f90503000041c2146804031452610001c00b0f080d000c11490200c2e003120307070600c201c0c0081801609000d8104064100440150115042c25032240f204e0b44080782c0d031900c0c2d80e90344611900e8200400030900c01d04026028032600f03242b00e207404241c41d101c800c039241c80d9030305882024629007050208400c0400c06004c080300c140541050300c800f1803502c0762000e0300c2c0403019552410800308130003102000e010301020700c22015507068400d141014038000c0121080700d46008200700d0b050003950111030748 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 358981699 1250 358980449 358980487
    0x906151202240a02061f14040e0f07060c0611040803030c0d0b151b0d0e06090109030206031510030c020a20090a0608010f0b030304050603070909060f030b0606 70
    0x584103507407401400751090a5005150032102c1d07140d00007151540d001c650010304244a09070084c03414102224600044100402c2e03030040c1c1c800e16000607101c50315070410381d00584040050004a030300d01c1d076541c40307024103201d4150044000140b0324400c460501659004502e244c1c28010b070198901031410305510384a00026122204001d00000e00c600020700c250090031072684020b111160003015184045466405020161307000d07010b150390400501c01c085865401c003e02915461440c0000f03170100b2a040e0b00882c103142c18000d0302d810200140c1c8640d4082d5118180c807001c1440d411000c4c1d03040101c034181647c41c070320405041820502c41c1503070101e109400c20354410620070a800b214554115400f2015100f25082440d240420011581a40042c411602554000c101030845c280c0740c01e081d02c084000c400d030598802c100401130780c1030a01c0290350040d141d01d02070305203a456804100036030714150310084000038100820310038081460051078000e141115407521f4554132418031754460740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 358982949 1250 358981699 358981703
    0x201180819230414030c01020c062d0c120c0a0b04150e010504060b0a0509010b0c16030302010b010210020a0e1027080d0c02030717070504020d09061512 67
    0x14840003481001e4011403010101480090301e0022034000150032000c01c0e0440d2281841e00040f41c581502c99090105035088078035010ba000e0104106e84806018103584055444070165840d440301154240760070011a8560303da0703518155407118042d24052408545a4242e01040340400141c480003000140500100f070740041c00b4120b0b41d40b281031107546510142003407002241015140304841070103510107407040d4460716003000012010310074000d0f07144c454060b0320340000e40c00006105511010303010f42036052443e01141c03480a02c8508400354181181d100320b0160707445007071100070b030741c0c06014405030490246811818140c87c10801070801201c058258002c0e9a03050380342c1a103d11440441803a40314015001104680100307545894580510600f00d0500416502c290030600c13480000d410300350001c00800e03a0900b44221195040360310a0215903a22500800250940759030000d00f0100c0b90520000840348240e04141042d03640e00a000d80501024280c04d10012002d07130a2440a55 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 358984199 1250 358982949 358982977
    0x1b050f0313030e0a031514060d0209040510150609060e0d0f0309211104020307050306090a0915020307030507020f100b030106050405040c031a1009180c0602070602011808 75
    0x34090409880e420f00c4003104036000380515801206000f00d000118441c00c042200800100d0b10580624a032010b040d10070a030301080240807280580340840e50a42c00c00c0c01750040c1d840d0311543c0f0f10380d807003291141400c14000204075030041046940004200000349070b5402d120418490f4070380000c21540d400c41e40244002501403600d018103100d1039130840504404a07000b02030f0800e0700040c04008010040031103100c00ba1000715802e41c00d190095a0040c0129100c1c541103451309000c00180400090039100c00b16a00c1813003038040b40c2c40303050320031944401c480f0059680c1054a00142a43c1e00106580e0a65109141442d2100400035007441058442400000c0c00307106200083d0142c041c5e41c1c4800e034000e0074074040c041440761019104088a1188041c1e00304c1920070790806518905c00c5802e00c018007001001000080f101d60408142400c03522501c0c1c000310030680c0c41d4000180160400740042c0d2100b40203005080d0240720700d801a03803204800c000c1100c5160744040342c034803807604d10654903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 358985449 1250 358984199 358984231
    0x20a050105160c1701060b040f090e030c12030708060108040213151701062d0e06130207050c03070b091e0d0c060c02031009110409080c070305011b050f03 68
    0x4041001e900780c0781c1a803000d10300304444c3c0d45a44031030038400c0c1d0140b45210395207005000134034101c44c1411201140c0003440c40c56076070f0b49060003980c0140307601c50000100b4002044400070540052041c150303090300c2050029104c0c1000c1000800c1120020302d035505001c0b0500a12000d0380d111780c40d070b42100c030310b1360310100d0140c508424040152b6544d83c028514207200b107003111110035040d0466410f84c0c1c010b0211200603150125029400810000c42117525007107103100740100711443c04416405600a0b000e50a034007103500414080742c4c040c0ca411f4a09410240c01c0c01c18500d8240107080003483c10710362103130500090800140710945a5005a140c00c014005042569115160581070f0f0b00d402469600171f0682d07442e80a4070310024890124400e00a401421111444074850b418a980d00138a2039a00d100c600c0b0b05010082044402c241c50107a824040390510071010480781014512a030000304881907101801d4841c4140641c2c0f40701484410302801c008242c0d160103a0b43c1c0007130101c10700028 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 358986699 1250 358985449 358985467
    0x30c0d090606080f060105031002030c0403060b010201020f03010909062009040b0f090702150906040f060b030a17090a05151e0c0106031101020607031b0e190f03140604020a050105 79
    0x1040b1950000e00e10307000b280714900040701c000c60f22504854059090340e00400118501c50120310007254403201802d418041800828541da0104400300c10600005240003030941311280e40b50401d0307001200041d11b0303944000030001c150190070066482506603038008941080303001e5942c015068402d02a599620804100b555101401d420a0002901070643c2d070900800080d11000518110100003885101056842d0b000207040c91013550080440307005100036a80e2600035000f900c080c964580b1071580d1490114240c00f160303c10703030040d01000c96910080301c0c041c41900001648000d00c59031441c4095003291400d142200e680a108600d03a450900310300441010b41e004d8040e92280941c6880300c0442000a48010148131a009030201c0f080380d03940b60412002d0701c1c154071800e54848060091a03200350f0181540387c0c3e407803000500c40701c0b014901000c4034100000c0c581c8044001c1c08038660820a0142582c4c41c1d9400c85100405804070303150030340208039905402c1c86018100240002d0b1601 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 358987949 1250 358986699 358986701
    0x9010e13060f141006080403050a121b091a1e0a0504030f0c0509090309130c03060302040f0f11040807030f2f120f07090908093102030c0d0906 63
    0x10b00328030ba41c01c0151840341031074080d0f5404201d6074680442a60600400c0c028020322626220316130554499162107074842c02260401d803180310103006152551010b844800100c01c00c9031a0101c03e40d0340a0172503180038102140402420001c8121070401c10111180d2460340849580c0b04c10702e8580203565160494044030b861280d940050860210754022800300008040c0240443c1d004035034010144d101c030b0313014545900c00c000707000d030340304615911035020030545800c034003da4451418001071031b55498001c98141c54980c8201c0108a40d01c98030918458030710f00c102520354a14040c02400d1604041006554100a000c090306c0d00609100c42001c00110300400155661401c52602e9050014083c49031045000c1c080c491040c0840c1206c03a40e9a03034001806494584900e004003625860104100300070400b100041c0c1d118281041080301075111620042c0c02040c0000d4041c68410000c860700c466590400c031048809401002072140490881d0250b41500d0307000d91001501a48900e4a58 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 358989199 1250 358987949 358987961
    0x20310021c0e0c0915040b040501060e0405041b06090306150b040b0f04030611070506070e01050909130f0c091a1003020a091e08010e03070b04030c030908060c03041109010e1306 78
    0x10b62003130000e410821410100102c000115100751005c0c41000414402c0000b1390301c1c02d000d03210001d07620016079221b528142d0403181d001409103080303c800410780d181c8440f0101c9541c00000101b05064410020440c903485080003003c00f001641980c1401d003040580c03203110394840d150b0751410201e2030f1842c20441504480085070701000c10410901c00e44052402a003004030144d034a40038145c0000c150a005100703045580c00165262031070100e081c0100281518003a0070000c0403600c0c0c1161800003041042c1c45c0c203059004a16442e50309103080d1011007a02c02e1202103102300714250011561079196848401400e4030b55040c0562200142c2c14102e403444515400700280c0f12104c0c0c4801d00f5a210440414181c0300d8400080c031103031107091411913980c801d2002c0100a40002d60010300442d21625001000e14071920305194a00d51310302c2c01d50300d040015180000e038000c00101b0310013001011902074500780e0082d558000a0341c50206290400c060007414824500520000d010800010394088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 358990449 1250 358989199 358989223
    0x121205040f110a06080c07081b0105181504110112060b030717090a030c0212010905070f06083105011b080108160501030c0e0d0f020310021c0e 63
    0x100028a028280704401c0c0c080e000c41a0745221203040b5a00c024241040d5080994066448450725500c84480c450308a40c0b00720800c2d81c1d21384043c0200402e03039540b0000719001d02850000031403541004007040000074504006648141e00948841c4000005888680d6101b42c0048610342e4074182c20005031805d40c03224a0484080d49020070103c0d021808a004e903004003681da03a40b034105103036880c0001c5a07280c15504803050343d000d80b55000c00688a50200c0130401c1c4040c0c42d9210300c0780418421800d44d40d000c1030441d0300350007040c424482d142840c840000100802d18146645c1c1c10310b400403c82c0c52492030074484011010580894139000200c000450345079202c402080000350070040c548402d2071990b40200040d91010000855a06c00a80c40e01440f60390080c54624516100045d4010650f8000140900011159101b080c0d41d8088461039600d01800b62101c40440720710400d404c20141d10f1008400d6481805443d03124180070b0500c3c1000b8080000c00624200720018040c64416000d01d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358991699 1250 358990449 358990451
    0xd05072303101d07020c1504050d020f060408030307030c1e18050607030809010b060f0d0c12050109091b060e01050c010f0c0f03062102011d04020307030b03061506071212 75
    0x280c030348204035600c140c030b10525103a0b0a1b078405848031010417400550300300c92015161401d01060013581341102071502040e02c0280002c18000c1e020001c41c0c4690082d9211825607000030003005013040d090700407205c4040b214030780481c240068882c010344400700c0306d0110b020454810581c0041c44000c00c1c01e00e0182c20b008203521b845d1303283c07031030010002581160640e0342d650804020302c0fa44d05050301a00c00c81051909814104103106010200030500100f80d5010041341b10881c2290714124401e0b2800703400c2400700424050102c0c24041782c141918031903120783d011010300400800760300030700d0742213145000d20b0001d6407009040045070150158003c0c0d00d5242c0c1c600440c0104407904903060000c2859103480034418299902d00c1060191460300200c20000f0040c50040015072180030150701008542c00c80ca01d80c00c01c0740c80070400701c0e001102c202c00440d6130349407186c5461800300b1071564000d00c01c141c400031200014001c90020702890038002c2c400c83c448126001e40d00d0040c0604504101c1c41e02c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 358992805 1106 358991699 358991729
    0x40305030c0f13060e041d07051c020a240906090501050901030e07060305180705131d1603060c0305070206061207030204020d020d0507230310 63
    0x6801081d140c01003010000c2c0d003c500c1d1002c4068220782d911215036503444024402140c4210180146240310704200d036001c20000601c40050381e0069605072898172800000c4500a0304401000303520511003540841e0091820820b0750301214074070041001e00d038205ca02550341a43d0760140703e0004d0301540e018805540500000d06441d581898009030107070f04030500382d050000e81e400c00c0300002d85039024804850902d200c0b1222848142c409000210315160020b0404103086450521281e2980a904540412080d0f034240c1034040106507600c1c0200c240006102d0003517408102d50391460300340745114261081c1300c0c1601c126003130b400509103500c1c1c100c100051b040162100002c1d030f11a001c408801031700c0300c0c009020013001100317015071102c15002c81e000a40348003d12090411124460030800781d4200c003452810f050510303404036a6038440401c000ca20404a41110604902d68a = true := by decide +kernel

theorem cover : BRFrame.Cov 358812949 358992805 := by
  have h0 := BRFrame.cov_init 358812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 358812949 ≤ n) (h2 : n < 358992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
