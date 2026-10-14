-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1290
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:11:52.214417+00:00
-- url     : https://prove2.me/submissions/26419972-7705-4d95-aee1-28099f426f5f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 231834532 ≤ n < 232014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 231835782 1250 231834532 231834553
    0x207030b0601110a0206030c040f290403050a15290306090c0310020307090b07050c0f040603031b0602040b0c0a06110301032109120b1b04080d1d04140108 68
    0x5810090b1451608002d52215401e07130f0040c00d162000756845151080d015081903102c11408140035040c0d40140e1100e0560034100d08500c001143d80d10000469007541440e1502d1030f1798090302d5007940c140251000765034035209140f0440c2c0c0c0c1c006000c90014656008030a400013030b581d410039034070b07100c40a00921416001540030b01e000120004140002001844c08540002c00200a1b5100603e100208007000c0d0000a42005c81e10151102c1c1d40f20b44058100c0040c0c040502000f1407006207034030710450030841e007000803e070484d109a05404840f0908490303002142410006442242c0c054480b80f240002d82001c004404036591a0080c4110018441c1d01000c0c2d6650405000a00020305404080500c0c04c030960394102003131050784902d0600a0340281d54060740002c40301044020f6680da00424200050481d11030318001e110300510030781c2c0d424241449040c5690f820074118074000e000a400b401c50044040c11840b880c03110300100188009a035025416013402c00a11400c04c092142c1000340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 231837032 1250 231835782 231835787
    0x4050a1d0714040b0f03060f180309010f03020a03060b0f070203060a02030403020d08090f120d05061005180607020a030c030c1a03040204051f06020309010207050307030b0a1d010203070207030b0601 87
    0x34040390b880181d89658101c00408210052041088441c0d214061404505c0f2503141484098032546004208922910b40a109081040c8103104201da46810030424503000380e801c00480031b007500e081c2c43c0040e00d51203401800d07002802e035030300044005140030070071040c0c1105440040003214400d50558105c3e4580319006400da00040d60000c015812180c11407204238071509000350300c908004212981440108159420850003640404540000042e070101900b807034050f40341c00550641d4882148082c21100403c0c038040c00e140319000f440ca1032812006135540f5010341c0c542d682c0041003c81183e41e240380c1440c0d407025500c800c403801c031980080003400341204040305034800c405014132031469640750300b00f100511008000d40769841802008000d03204480e00118080c181980096079034004140019103401900d9101c2c0d8480d6000c441d050000801c0c0340045600311140080115a08414050340c418203460407942003036541c404001c11403040e9001462000b1680a4034443d411070720b421004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 231838282 1250 231837032 231837043
    0x11e0501110a020607050a141605011b020405101806081612170403060903020106050301050603030a140906250c0b030412080403030209061317071a030405010b04050a1d 74
    0x110034140c1c202c4a880d40150610764010701e0501e1007a030a075071b80b04100707690b503503c00500c0081d00e2559034448002010741e00c102d240502c0240a00f403d1032144c4001460300d1100351102d8090003401183c50310041101d0b00c245007070b180050289040341c80c2c0e400b1a40c18102004003e64421804107218466862039038058640c0c0c1001130355101c4441c81740d482c559803620354011b490303c84450303240d0008010000128001c1d01c07904607290322950000c0366891500c0109825076078060500c40c030031b07002000300c1040184c115a50001e8806410002911a80030b103000641902413554078844545c26000b036514101c1c00060000b0120384116048403032244c803000d0452aa010450b002001c01d08c0011440c0019030041c409980d00030321a29015280908140214030550070800c8002c5c904140003405004000a000400401c0144003005294036460200002c81c007030f6000c0d07541c00e4a44c4000004ca002d1210030f40000307500c00d00c0038100344080c0c2841d410080040210700c480711070800c10401007000b081d5003c41c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 231839532 1250 231838282 231838307
    0x50609100507050421020409030519050f07060e07030c0303080a18080702010e031221011a030609041106040e090d0f0905060a09090c0806011b0b130302010e0105011e0501 75
    0x1141802c060800304108561040c03034a0101740c0229626042e00165528064800810b201c0da0300d0030745540f0303080703801c40700030880c841050103121062290303415984040d0152580d442d004607000c01d003030714509071190805500c1d07000608180c12203c404420725800003840c2e4000d81c4000300404c80c0180e9017044c040d040300851001062242d0803c403070700140d0b02c691344549405c0002400d85240030070b8001c180380d0b0765002141103110342c0c91030704004146c2c1e1105007680c1d004000c6125542c0103101d51008a01c0c540c4401011030340f1403000640403a0500c8910b81382c0311600100038280c1691540c882c07141d00c00020040b503002040d03220300507921303401501c2008120748401003030319201e214078101001c0100030b4000c0b2050f03008200b1039010004184115020f0000d1740304040d101c62a10f800c008000600c982d0a41c610712103006500b011260000e013038203000c55440b0080e4458001d0583e15031600b217001d090024a0741c0020f40c00d110011070751410103082e80504511410206254039910340c01034507421007862 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 231840782 1250 231839532 231839537
    0x30c0c0e06010e090703021303210503040b0f09030d1a0a08030703080a11130902070b01061806030c0507020904200d0803060904080906040b030601081b07020f031009050609100507 79
    0x403c0e0414604107500f44541113040f9080140c1040e4949109603160203003944242c6143d22400611300016180d148140c0303d803862454450b20310701e4180c8030603100702009400780550190141c0025221402407044d00c603007500da1001800041c55140000b02c8007140b04503454460240c41d072001601100c000101e40e54164180c6624001d9503a02464400070811212219009002080f1107114a0030101d0920040c050100300182c0b039148030700705109420750580201041c820007001146c50302c0c1d00c811b21102182c5041c500032407060031704e20088840b40a101e4000350044030100511041040e5211510009400101c07514505003030842003002905c1d9a40024144801c1040445e007103081501c0219801402411110318045544002c20901e600550052201c10000301c2449025030b8006642604000d080c0d145203030768142e4014014040c0b2918000900c22028010070b030709103450a2102c0880b000280b88100300c4060103081080d12500110354410103030003401c94070b4040d002c443c85403038090140c83c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 231842032 1250 231840782 231840797
    0x17070902162006070c0e0603010204060203070f03021e030a020c06030705040302190e1e010803070b0703021b010501061106090d0206130c0b03160e010e03030a0c061404030c0c0e0601 80
    0x1500e510388504401160012145100d1100c0180c030f80b18a4000c1c401c0f00e00c01c03031160407072a1500310081000306001d40007a00c66401044200490740d030010940d061a40c03c40c84601190100c1e02e001c1c1d18003c1e8100341614061042d2440501102001c005044070324015000d544c407506052040040c07620040383c120300814000c1c0018409401e00700d0302152100d4218081036003607a121013000d0720101003103c01c41e00c0707030b51510040c0100c043c04e0400c680c01080d06100460404203143d5419003125002011b4404040d8041491000030802122600504800da0001c00079542c4806000700841c0c081101003141d0303c5038a0100744c0f8003200180c20401100c16038082c09160701d0b214102c144545240d0fa0a030399441405502280c51522040254010242c591003800c00441f035000140c00840320441040c14080c6c00210404203071004000c4034281c4440c0e01d070018205449281180c0100044032007908180100820807003015081000d00c486140603440e8a4030a50307840c0702808078920100d036900d00003407a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 231843282 1250 231842032 231842077
    0xa1d062d010302040803030a0c1107030503030c0315150d0b0a0509040618082206081618030b04080a0e0d110409030c05010e070906060504081c031517070902 69
    0x103025500e0041414940546443d594161942ca143c100b903450000030355450441500890700680110095070040300605144c03403541e201d00e034803030200801b00c40860100000054440310041316080b01150010014202003101c81c24100c5150062000240c0c01881c2c00100c480f0742c505040082c00b190300007004500282e8480c1e4891020f420306c03203045903400c00281c800100180e501000746c110001221514040b4400180301104d58040d10380c00141400703442c106120aa05040c4900c510001050900544030b040c541c854903a00c410395400503084010060500c0108812400101a041d0b07040d40d03003a074410049420405615050b103c000c1c08600300c2055489030341426004050f00394001c0c20041c0141f8165100c803803d42d004680c030750000390004107090000b160746126420117421503142079414107007004042961101e01c0c1c40b5040e00c9030540407400c00c0c9103100b03821112100c1c2802010103800c0350b45030303500e098a100c0b1208500f031794081c03160081040d044510944d800e80040303070200c841440d407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 231844532 1250 231843282 231843349
    0x1409010e0c0409080f031e15010e01110f030f0405040b060903070608070c0b04060c03050c09301507090509040b0f04050c10110c09091f02090a1d06 65
    0x14003401c01c403803400e805c2c072801680b42c910101541c811808200c0c90004030781c03038154805001ca030051820304041108070072020305036801062080603c1c02130030080001646030311010b06d49107101c9903c4046200018480002142c00c2c3e02078030032aa070548060084004c4441040740c6401341c084941d40685c0b21520800810340310b08a4107810603114100881c075800705e500c501d4050001194140c0e50303a078452042c40310455241c0301d040d0b489892280c08505104200001031600e211130349a020841d4041600950001c684055070075020000d07d00319072940c841207640d4910030b202118400e003c156044000100e9084c1a000b05100e0f41e1b00c0100307558965070319040d4408000000e44291018822800c0c00380b10380d03c4542d00c0100400d003a46901d40c4a44003009443d2800c4500c2ea080b80c054601c03101801700f0800001380402e80c6a4607140026070030300a03000014000c0c081e01d4003040d400300c0d4054002401c0d03c1900c600007003c0c04030030442c1c4000d9941c030051207241c0140040c56150686c2590050007000f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 231845782 1250 231844532 231844541
    0x120a02180c070c06051c05160e03010b04060e040b090d020d0f03020d140a0e1902013209040e0102090906040e160915050108070815010c080703031409010e0c04 70
    0x200e09100e07032030519482d074603852043c4106030011404a80009044c03040294001107480d1000880d2000780954a490f1003507091215001841e141802038444404555540a41240881c004064810406c1c15901c411b41188010240d40c20740d40c561001c40806c211980c040b468100208c030b035400a205082c582002140c5c141034810384102059402c6c054504170050708e0051103000b4095443c3c50b403140c2080c5426a0032075030b1045446985920803004108600c1c10b168156030450340900700388001c268030166103141e00b010031181400030b90741034049800c10480ca01c0034018152058074100008440343d55460300704d115910615500070400b00002d05280742c0f5800c0001d80000c90343c261100306c0000341c041a114022a0000c00c034141d10780428545800c01c0d4040880180000d02e0850a503007480c1074081e0407154040c1c4510705888000b002482c180c0d004000744501c1d039030b1000e1000da5412190900a00400000f08803510030000a40442d071b01c040140500c0043c05200303005011300b10421001c010041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 231847032 1250 231845782 231845791
    0xb1203030403020a0f021807020607030b060405090402100315091a0a120b072309030c060421080403080f09030d020714061b0a03021f09031403100e0c09120a0218 71
    0x20000400d1b2400c1c0e15980391f1514043c80310390300100a241404e0401a040c4c400320f030503c0d80252424841081140d4464a80c19005901a41c040481e06d08004040b0b01400c200b071242c01080d84c81c25030005148410354001610081c50307900ca080c142d66001d04103c0c074001d043c410f03030b0560b24801540700081201c04880540194a45c18124003480c0d4000408140805a14081d100c0d00404180c0d00941d04080c048041d00c6101141d1007440c00e400d02080b01d491200601d01106440400c0034603101300056402280e001d03680001d50682c03100c0128600964590110555034000c2c0a480e9079401100d000085160940c0d011070140c0000729607a03024001c02d6044107015002e0007400ca000a054003106001c03810003e400389c2c0c054400700700c281500c400e4942c180c01c007040c0c009107418042408280d11410780c00601401112641d603d4070344400c1040d07a21829080b05150302619814041821704000080c14584d074151070381055819001d002c1e544881c2c101001941210030302c9810640d18000d041d8843c2d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 231848282 1250 231847032 231847039
    0x2130e0a1b021501090c02030f07030c08130612050405070b0901090504050c04050a0f061b0807060f020c01060e1605031f08010f180c06080601020c090a0b1203030403020a0f02 77
    0x1101a0240401c540d010304003a809604884100b40c0b10160052445000d800049414000710880340f034029580c3c4159801400340c0c138000705002c3c04040c410b40000343c1443d080350641d13894900c11074240b20421068424080442c2403c03280c20380c0d014142c000c06e840f4a4001018224079807810301002c00315444114800c0c1080b4000b0350200c0c0950b80e51091600515915220948070f5003880203002540c442a00941c5c0070b25070510003001199800f48a80c0b114040c008002c080c10042884d100e8a1405009030082440d400c0c403140c0c1c0f281c9120750f406081080c10b01002803215517525020005101810380c3d0713107101c003000c4001204400e070142008640094100402e229011014104170202030000e4202c10f090783d466543d004c2032504a8058000c0600014800c001e0400c101d66400c091600b0f144102030500c24410000f48441e8002d020400019402500064513440d1006000c4010405410001c0c0300b01e100300c003d904425000810b43c1e118a526400a0144210340e0706c0700135001c10800e008992 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 231849532 1250 231848282 231848291
    0xc090b01030b0303070803012d050613090e06040606090c020c040902190e06010f0f0e010f23070b0a0b090103060b03010906020705060609090c06120a0b0a03050a051002130e0a 77
    0x200e91400c10080041c00d006001b03140d140d5041924200700001040390341d0144000c0c04400000030350b88a202c8608854049a40d1b039a0782c0c00483c240b02d1000e80382d6005140161038261440e02801021a405200383d10911003080681d8441c28483e00300c1c5c0c1d1040490f001640070410b01d8419040030340c011f104060009104400808100400c8000c0390510340014030501200b20074070103507507002500d10440c05141e0815070325100d410013000300320b1001a0280c074100800d040d000e18109001c0c12580055282c16003c94101351002c17091401144c2c015241281d159140b4000541c5906481c4a03044400e40300410780c000592950704c0704806854591103150740740d51303501c40328800104588020f21046e4841c5000d4031141c50310104000650390300401d803049981101004841d5a82ea04c412948819608020003195459030761a180c0245000c003881504031001304008414007000141c5140218818011203038401207004108060b80900340f043e260032107880341d0500c00c6040030314480b6402040c000c030008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 231850782 1250 231849532 231849551
    0x1020d1b081207051e0a0509060d090b0c0a090b040e07050c10020a091e030b0a0c020109050703141603050706030b010203161103071202060a0804020a0e072a0c090b0103 74
    0x2200020141da101d0045a00002c0709801005c510f0313010440c0c410f60024860410300c1c081d0340644030384646c04c0440d01c114000140c861040c0c0040e4000c0300c0f950b82000000c0d41510304001420038540c0f201c036019001c24218030300001d003a000c0303800f25015146078608028550303c0c1d1103000e83c0d10b500315034a50a07941c09000441400d0501c030703202500c1004800e554600940d80340c103500c9036102001c1c4040441c003020000050001c180c40702d01d0941c10505d080000a5104800074003280185038401d40200b0342d026510b00003080c8917007081031406901c070130402c0c1c0323803041c100c4000d44e40d0070714580c48000c01c00e0704401c004010396400f030b90000309a040103005403850200445c16001f50081c0c0120101d5980d072142126140c582000c0010394060104100d46139141e04040d0005000b03805000b6101c02001000d5000800319243e08400c6401032490b54203045040c10400c2d4040e1020301c040301c103c01c4440c014040074104820007039030003030050380155070184020704101d4070b8409412014407040c14140c41d0704045c3e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 231852032 1250 231850782 231850807
    0x1a0f040b1305280323031623060703020f0904021b010507050a0917010b03060a141302130506010212040303091a040e0a05041b090509070501020d1b08 66
    0x7480140406190060340e1401d2900700728003070400c003014201c54055240040c0c0d0b080507074101c0303800383c1e030700500c4160304070303203080010820450f1306440542e440c0008a00d024620071a541c0034081d691264401140b0480091142030307403054903105010040d0700c8080402c41a60080d4010540066000c004030300c0d003114180031805a03404114024039082c0e00d04d1058045890038881c0682111007460981e1900300340c990000d101c60002e01880000f68a110324501c545c0c0c03825800103058440207002d036007a40c94907281401c01484540d14240302d402465002802c441440c00b517900341c2c164014040c03440541d106104c00024000201041d041d842082c407420f0420300428080c0000310300c00e81c0c40c1d54680c1c2c282003a2000c44d00d254a54030310442020310051160380e28000c2019070114500b80f0000e015660717403d040c00c036922107000c01d1a0480070351002180104064209600c2400b05400711506159514012a90380706d0a00c0c1540016540c002d0820000c64001c5c5822601d5008031005400c0a0116289 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 231853282 1250 231852032 231852037
    0x3070308070201030f110306031203010501050708090612010f0f0603020918040303151701060b040b0f0307020a02090a1a0d0302030405011404090509030c070603090b010e072006061206011a0f040b 86
    0x12111b031285c003008020080c07a0411448408180014400e03007107500d043c00280603400390300c4004248042c086000300b119290041a204c000203e5400001c2d65691245031000307955141c0103035810342c035a090002c45e506010b070007200e0100358041e100d0fa200850354200e02c9103121002e01308504140d1141701c03e882d00c0d10070001c00c0c00609200d6001b54807002c1c00d01c02c15402c50300d082d40004843c000c103200c100040007010003034400c004242e4a03481e41c2c2c6d030f13100c200482c20822001002036204001d20288108909168011010341c12609251100054480c0400071009110000100141e100300024480d40d44580e056003804801503100508141d21401604c0550380101c5811049500108030180944001c0003c08000d245908080000c40505e40710f821345190140240da104214130000314101c0380c4190038001e100d8018520b9115219030000d002c4e61141d80c140c0d24140700303103081e06007080812408071790395048601c0c00701050b000300c1281801007541d40100070590380780d0710144000180380382c82900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 231854532 1250 231853282 231853301
    0x30c150e010b040b0108040f080333131806021c020d0e06180d0807111b0a0f0503060a05060d080313020a09020a02031b160e0a0608030903070308070201030f 69
    0x20564840c80b0741400100e51681c0c10107810172520806000100e192401103642294100c0e1665a982d0f840c2108090300c203070f00c02c0c846604000d1034210440500c030904540c01c502c5200321111058803c450f00840c0950715086201d0706e200c104035400c1e40020f02d02da4001c1c66a070141c0a1086400c034a0b162120b81240c00104905036180d80b1120200440d8500f071200580c001025010340e850820041103040d69880703122040c43c240840c40021480b068000c0602d4840c0c0329600302210000704601d44800ca143c6811682e40340a034480810214074002200941e40c281e0741c01500030400f6585e24020040030b810041d0159130440003810800000c60038201c01175200d95414120410000510300c180096401da51380030940343c40c414841810003035408401c48189101161000c4900154030071004d0921100c1a6150700036940e80c0800600c81c04030140f054858440300c07400f0040d01e503680d0720b0181c4901c15816101d6154000d11010b00028102c08040c0c042c1030b0040c90001140441900540121468910f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 231855782 1250 231854532 231854561
    0x601060914100c03020f0d030e0c0406031203050703110703030c0909110a05090a05061201030b0c03060d0209060f03060a0f0b030c0109060c0c0b040b0c06070c0b131a0a05040c08030301050607030c15 87
    0x100703001127039001000030f10201003081d5420081c0500d50b0710341040e00728000540c2010992920045003141d0310031b40180701d40c1885107010a0743c44419140140007418218412808503503044800643c40805101d40e01ca68052002c18500c1c0051141007243c2c9544184041d035803141035244041040d8403190040c1000e0044840c8000b460350440c00d1180010b60020400310f041c6200b082040280d0700d8104d9809001c9078180c0314000551540380014000040e030f18a00c6800d4483c25007005951843c43d000302902e1a00e0b900200300c40c8407041c0501da102d15043c14142c1c042001d42c03d040002a1251012598940c096021041800e4440d2400712040e40f040d03001c4403407224089500d4402060601955811203403e04100700441401d668468400100502c94044004003414200c140008091608002c4003c1100c074036852420380030000c000c3c50240d0301078038800680840459499400811207042e508010201810f010702c0342d50451340d51080741c2e42241d443d000e0b500078179401c401c540240da40c01c0201d0f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 231857032 1250 231855782 231855791
    0x10609050c0c0f011104050907030b0405070810050105030c040311010c0f0302010912050304050c040e0a080301120c3014010e0714040915020c030415020601060914100c03020f0d03 79
    0x2d1941d1071510716604055021a40b50110281c1e08403911811a000c07a0402d03101d078402d56842030020b0f00146030075503091303170854100401c002000740d00840140c42500031000001c5c41584a000449082c0012110760300c5001e005c01c020700204180381d01d0032400c02c4051407c0a40c400040e038811281d509444802c40141c0c0d1911481030820400140b0b0070001c81b01890301a05601d420780356295960904c0002501560b0b03140d05480c2505811f000b1941c00c40c0d0080d505640e070b03503503902101809083c2070809699110b1038540102d00c0c1c6000c03c424000d580359441040f10401d0312040c04d11881030161108464004c41c819520908030400c1c0034028807141e20601408003a441e0850001c5940d19101c2c003184a9072038480010001040c1030145800d54600410040e1100e5104070842e10318031580c0c01844007a100781c100402c0c4070b035000581905a92156941d1103600740e40720f20a10409017078000060f4041006070081e20541c0c4a5250f1450442c01b07441201c1c0f034080c081c00e601e0b003011025024080000d449 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 231858282 1250 231857032 231857047
    0x40914030403080406080a02160b070e04060e090606060307091707121202010509010b03031e0403080726040320190602031b0a0f03080a0603021e130501060905040e010609050c 77
    0x3012103550300c007c87d101c09616000010005412070410316000034120801c100c01b04120501c503456020344040302030810407801d40c072800a400042c504484100355446850001401d6090840660780074200311f072a00801e603400c00030028424400418100302c90f01c00d1041c00070b1508015189948298040c09070340c1715003480b0340c1c402800d480009160f01c905a06141440000340c0780081150f540c0300e503270f0303105070036500010600d0301040c49180c0c409003c01601150100c180a01800c0c92101034450840d80d5500d038031510000071044c0114840500101c83c503201e10007003412200c040d50001d03c801880012648807a9444c00032501003500b0040043c2c1c008200301301889566074400340b41080380ca000b060001440d0f929405096580c00004040056200108881d50070a82020300a150300804841c1016808090b1070241031a0520441c0b088500580520002c1c000d40b0815040c1c2d00995a4082998180001d11014140c10407240e6142e40d40d0b56000190400070344603150058541018150740c4146 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 231859532 1250 231858282 231858287
    0x1e02090f07030516200304080a050102040503100501150e03030d2903030309120f040e0f10140d080a0c020a120303060602030c100b040f0507080412050a0e040914030403080406 77
    0x20080703807024a607081c25081d80d64210030481417040100d49038250001800f010306065014907070201c10702e4801d418000c8100801034000d070090307400560407a0921307c40d00030424103452081c8181100e10f041d107503a0440d12446244a0126243e01070101e80c0b0342503952071460f0890702c007244001041d400d01078140c0d145441c48403111902c90022002903007542041190a80c60300580c80904481440004084501c0c19880c0c064070004d11380702d00c18400925041c800c141380c40d102220080c0080007280004190080c6812007649424000b40c2100c041e061036a403102c81ea644100c40813000d206510360365100584e2001c4081025006585900c0641401458082e00b910815000071095400520034140441000241040c10460000b008074143e8415008200102070400d40f408625080008206040b6000010140a20321500359403c440c54098822150b90088100c003074001100301400e0482d501d00b07070700501c2d107060290401c490b21311004400d80385954040d5100725203050002c101049040c0c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 231860782 1250 231859532 231859541
    0xa050d110906010f120902030c06030702010615030e060423121809090a1e1707030905030303070905060705011d0d080601140f030711070801091e02010503041e02090f0703 75
    0x1802801c4c01c4030f91400481014010140f00803240304119940d07a03000c419950200481d2034400c0c40609040c0c1d990902c200000d029140c0d900035a40c40702640c4e030148104511a203c4c070360380c500c83c10001c0c016986480c1c0e42c204036540a80c03010340e0140ca40b038100351040081401300c21340846001c41d40c590707a8928003007041400000e18110900c6404c120b002c0102d0800f01003075400b08581c0c40249841d85e0a040499400442039504000d0034441081513545006d02c4500700403c4214020b8403150441d82d0345070105036a85c4070447d0290001a80700c1130810050416401528401e0709c104008201e020001d044500e10b00c0c040500503e0550141d11601900707a0042003664208031300b072070400079601c010042c01c541841503402d400c094010000000d2805441103107500d41280140040d02d00d40c55460304924068452032505403014030054204514080342c03100310440710355041c7c41c0d10b820740d0380d50303201d01151220424009044829882d11000180d64005100744a10001039041019080c0303003000404a8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 231862032 1250 231860782 231860791
    0x605040504111204120309080403030c05060619150c02040e0303040c08070b031308130e0118020c0a020402091903032a02031c230403050c0102070b09010e0a050d1109 73
    0x10b40c000c000c42a01280501e40341030740280c020806a0b1403001d4100210014503501d070020b0301c4007002182c04010194004c0f001c200d894050345c1203800c280c44140401c0b03a0306000071038814001c0c00c404410032843c016035903000100101814284124034054000c82c003a2056006044625080001000208181208160080d04004004040b50350500861007028480a0310036803030014000c0019081100c400200c4101c10201411040955540d402e41c3c01c40000c2800340010010301c90b0240c0d10820707400c5c030940303941c140203400a000720b00302038080c04020b50003a0341407600b1400b414602c42003007034454542c000841c4aa62620070381d01c00041102611620a0001212412810320b0980541e500181c0c0400212901d61594010604200180d805003000800c4d40b621b4000b03007805101328031003040500112805007040d00c4080c10f00f42d004a0f15994a400f527061041e07804d0080030101c1d482038610600b1180d0240c0180c8500781c41c4e00002d041d00d0f0503d20100c0301c282c0070236030900103410700d80d0f400e9400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 231863282 1250 231862032 231862061
    0x905090c040f06110706051305040c0c0308060315011401140307020f0c0f0d060b061308010b1e0a150329031b0f040b130c0801080d09030c1811040605040504 69
    0x115981c494001e4840805c0d200714400c0103030124080e20f0b02c1298441e0301000b0180100200309201e00b00c0781c040e110f280d901d002030b0b0128001e00d0010b01c60b4100420110b18442448a02400700e03801d0010a101002040d10568100071038000303041b807100787d400001c0d4050340241e00244260710148015030301d00520414018050081c522004050391600b84910040795403142c40031680010307240c0400e1050140c0c181c5032501079240da40c001100c00c0194450002070300152068012482c00e030000c000038844001e40c2941140c0910401c103d0142a9600c40140c0f044e60b26011501c603042901d03924008510241110754542c0440c030200d000d03d0100103d0f441c0440340c850100a400400c40054920085002c46901507a07d50203c142d407540ca1012401b02001540020840d500b000400246101c10074000e091591143c45800340070207000d080c8100c201d9a100f07004145aa0412152010818441f0070100e442c5454200184502c0308030001303080135042e1681c0342030700c1c1e6140030200001e990089091044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 231864532 1250 231863282 231863297
    0xf0b100915060809101a130203010302010c0b0c120106050405090f070e061b0304030f020a0611100c0c02030601090507030c0806060f03040f060905060a05070219030806010905090c040f06 82
    0x80c03819000a40e421110b02d810310010b2540c0d40b242e828103010411814541042c60900b0f4655080b962140150001c03000b80c80107008084112030043c01c910003030101a0116542c2c01c80440000e0380e00c40f00f80d0380110812066030402811550281c640002170308400d011030000b18080c821b500301113000a5001c3c1d5084d0701c998690410a402402d1811203100481c0202c0000541c6079075241072100d28928a4085400c4035a5240c0c1c07400d054042c004850700c02c81c401c0c0c5911030300047c400e02c101102c2c8544a00071010300b0180000d002800300402d0b81421240900c800e1402803c090fa4007801554000c204480001c181480c00c0b020003400c4940c0300b0314203010310204100340f02c101d80b19142581d0002107480203440e034036140c0c2d003800c1007c4805031000800043c14401c9440c1000000301c0c0140c0038403094a8140041e4552100c2a40c40340368184289810090310300c442c0010074810071079190001410305000314a2500c5802080382c100c021034028942c0e01f00041c0c00c03c0074855421807000244040d02c7c0001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 231865782 1250 231864532 231864551
    0x80a0e03090d1202120c010c020f03070506191e0e071d010b03100b0a09060f051224041d06090a1203020c070909060c020c040b06040303030e03070f0b1009 68
    0x58051603089000341c280d00c0840c0381e043c120341c002c000a05090041100c0f90341c03224051600c0b03601900007401480c0050241900101d005d4400205807180c1c06d038003101400c000da485c0c0c000500014818804000c1c0991140808001e0416404090307007107000070340c000304844100c1824641303000c01c191701400182040281004c00f03030107407a00003415a81107400d000c1d40e944032019201506405a00300c42c00d42c005c002610902c007500511280121019034581c6038101040e103070282c9807806000045141c0982c1e042c0068400c0c205016909000640301030018280c1d0342c60380c00300f01111005603d2032000d0205080200c0c1e030382070070040260300860602c010442a199a503400f03e2149003801590b042c03580100710101c0001c401e20081004d411021420040160282860b41c007a15416059030098040d00c043d0802500740b43c05000002c1a018000c280b620b4550740e0100e00411f8204001c9510b07010038000500040ea4071007103c004076026000e080010300f0480140c801d515403d601101c00d5525141948 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 231867032 1250 231865782 231865789
    0x316260a0509010e040b19060f0516060905010f06121719120912050a081503120c01240302090703052208070507170111120604110706050106080a0e0309 67
    0x3915010428a01403400c1c6000c400171501070402580450360201c03d01e1414810b001c450b1540d0320031142c00b540c550008000510054540d03118030407203003100490008000c80400d410741c0240e44c800340700718000150b0840c002503840c1250340d9600b125205620742520002404003012401c1c1702c1c0402081c40526041c81d4000c2404182340d220015003e20031405000e00c4402450707845059103a8201c00e03804c0c00401c43c040000c00550203014000003060360407000c41d00324034a20701040d19040019000780180d04105d01c0d19010b5412114104e1803664030f0740e4810340b56071000320004802c40c0594602e0402c160841c030408c8036400e4000d0035a03040620780710410a005240d140681000b070310100c103000e01681e00d030500c080c0501c903c40024010303205000000030035040d0802c2c0e5008100c00c800007003002410f134a000e4119031096414010080341c2c4d0750081045490994001c0f006420007060a902e4902c2640d600c1c419070303400768019004109814100503030725610340214030300a5202e2010354900f41708000007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 231868282 1250 231867032 231867037
    0x9030c011407060204080d0914010f1817010b091b040e07090305010510061e082202120105040611040e19020f07140c040905070b0c0316260a05 63
    0x640c100500508400e000c100c144044a0b03070a07420010079541d607515040810390303640c0d060358100001641d0440026540520103269444050f05a40c5d020f0003201074841142e0410200da0840400100744800040d21815000a804131002d43c00001c034120030f2310400c11000c1040180031145070b4200d40c41c1c86040c800101b0486041e80e880100c0c2d160182c448280840740540d85030401041c940ca40790901150985040c8104100c3d031700ca940e645518090a0343d0400010301041558010940c40004600c81c400b001c0c61641900c4c1c203000e0112010300b02038002801001807000d4208859645400b440180714450144c00040070242507041d1425141811100317910710010301109100b5220b5048000170070b180e4045901c1d42d0300741e481d02e6468081c6070501885d81c6100148400c0103100c0d00000304102e00701400f4203c03949400c03101074201c142c40d01940540551243d20700e104540800c2000074442c403d00d0501403d06405031345240086090003050300e10320300640b40c406490510500812050f03607848000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 231869532 1250 231868282 231868303
    0x1204030303020d060b0d090b01081c0c140304060c0b0708010f230a0801020903100b06030105120313031218030b131103060106050309240c09210304090b060903 70
    0x1c0c0103070344801c5810b6000040140d500300400d08071300010401d100c8880f64010201e030754028451280c0d00e90381d448245544450780c0f40c0c2c0c0c03650300d580d0345003001d0401d02412060b240240142c40160301440c00040700f81c1950f00c20781080d4049224164000284115042041da00c080396082000465060440f40a80c0030340c0c0b80329800c1c0c06404540015855114203a0b803509190028040000c002e48900c007283c080e40042100390b01900c1074004d07030003e0300c2c03003401201c4034128040d021b40e1850f42800b00384003081c0d0b92a002d1a10b24802001003902d48056510240025401010100700c6419000001802c2d1241160004020540420140041148080c1660b00200c004401c0f069000c110705d00012003034645c2200a03410300a82c0000540150810000c6100e10424402e0700ca0b0410700300c407045000b48402059024800314203001070310595645000b040d44010003410010940704508408050b806684000c050306e400200d0308020444150140400c0d01300101c842701e083c1a0100003280d0758021182 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 231870782 1250 231869532 231869537
    0x3180303090e09031e0a120b0f0904021503040f030e010e0312090d0503040b07030f05070506060d170a170709080606060706060806040c0501080c0306031510080a0f0b010812040303 79
    0x4000c282c1901e02003080f00c401e40250800baa241c0c4c5c0c05103444901380d411203400d071404100107140b400c0c61005148604015144010960a1854101001d01c8440c0c080100100c0e00401c5050880d00559140f902039440b651090030422107041d00c81c500100300f1120079071010306102481d05140807581e0040380c00002e07009203210260f215204000064862000414042e003a07000008002c20303c5100e28004003240380c06611801812000500b04441902c940c0d00701800340c0e041500440d4103858104030180ca1613004903d80ba003203445115240c07a8941c01000c4100208160742da0030701c82c075115900c5440c0d10400c03038280304000610313114100d619101c0007030445101d8040000c249041042541c0000b000c2c01d0300d54200c40042c0ba25280c40000082d540c01a0750110761440001401054050304407442007a01078050081d4140502040407220405001000d10355910900030400c1e6200700000c0e14202d015010310544643d0314200109440c1043c2c00c01d8000d41c0041303030042e0702045001d04443c01c8a5061 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 231872032 1250 231870782 231870809
    0x10302040e071d060c030301030605090c0d1b0b0c01021902010b030c0411040b0c060901110403080a0f030b030f010f05090a1101081902120601121406061c05010806040318030309 78
    0x1203d04440342d04240d0481e8400780105180419120000145058034482c2000300a03a0b11481d8259681e010030800700b0380d110b03000c040d00c00001502510340c3c00030005039150300c480307003510703454803001e0341d0000d407018a2681c0d404114400345040031201c070700400110340001c000740c400d11400300c1c0e268044100024010394903004c9600c9649003c404560091941000c1e89403101e4503416520b0b280c00e4240daa40d001503013004da025083c1c820940446040325880150f19180c400c80d00000d880e4810b01c06c08060600d591030000203d00e8030244602c10360300c0d500f00000262441d24410701001c1712000751400000f03a000080c542c0c0002ca800d8101580d10009003403800c02540c841c400895503914900d01900c2d03442c0007180d175000700e083c00100036001d56001d80398400d41c0401002c06d10300325a4481c2e0704031084c6100341c0c003080850810034002c1c840316103401c9100d26600c200c5031904003691001e038022a4164400010081415440018007001d01101c202c1905075510319180140145414051031003600b824 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 231873282 1250 231872032 231872057
    0xc01030b1c1707030f0f110706030c0c1a0a1a030d0503061207080105061f0e040b06090303040b1b0715030b1c12081b04030f051f020403020f010302040e07 68
    0x191a52a49003002542c5103581d810161500420b091642c138a9100495166414048041e003e03500e015040003400000306801442c0080450107400c001c4014818007940042d09000709034001c4010400004d00046001503041980d0180701300d0302d000c405881f2811408101080a40d004105041c4540482c94400d0b02d80d1100b00004105a00410801c010b82c414042c1c0050242c1d4190840e510400044425036031040101c9402c1c0c46000741c1040b8900000d0f5007542040052a00d6840130700300140c06000356080c10758503008685594015008404541400701d6480f034441d00d014480884008044082e14400f450000c1d00340c4200c3c0d50803003613800d05840301c86580f084c1c3c45904404070346000500c02031441e00d80c175050111000b1302100b0300400044c848000104d02071719503c1c026408151a112070391410b451622002d120055621040320240905d5140141c016940a408040440c000000607501e520314410030240c81301d07011031107041c135005000c200a000c1e01481d4941d400007142c100341009000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 231874532 1250 231873282 231873293
    0x12090d021905060c0a1104110306012003040608060f0103060308070f0201050d090809090609060a060c020303040803042706030305070f0c241d060301050613050901090e0c01030b1c 79
    0x145412142d042440401e808401010000e051000b29000e102441500c10f1b04901b40000c0d10705d00c11140da9211800c101051165200340040152482c0500380380c201c0c1a4219001401c40d4025445040001d0745401405001e2805c00e000c181d0501c030900b01048010701e15501c0341003501400101820031f40e00550080c0035a409032049500b0042d2804013000700501c20310f0195220b4201c103002a02490340380001030018140301142d14007607100100802c000e10310b046004c03503818140030012a010f00040c4000a203942081026001400303916070b14583d11483c500036420039034a42080c0408580c100507041000c01d821804969880350082c0c00b240055a141c142100203490b40d070300600090010010480103a00d0044c1e2410310010710b40c1d0ba01c086402c1401c0c0307042d03c4640c0340d480e1a60007801040101f00b1440e020004045100041c072641c00c100c2c2da1040003404040c000da00c425540c0d5125031001007444c00030300c80342c108082c0900b0100803041d050310128107183e803600100d2190344e10800c0000e05016 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 231875782 1250 231874532 231874579
    0x90a0f03051602030d0807120905060a0902030c0910240801050616050d0201021c0902030d051b0a050606130e0a03050d020c030301030c09050f07020a0201050702040b031c0212090d02 80
    0x160080c0c1203400d0019503240003000586d08075100d80004841e41c0c0c004400a0180c040c480550340c20100070156034560301811001007145400c22079051081d454070b694142c0350b10f50f0003841100ca408810281c0381c94050a5100c000c20031500809044c010f840d80d000f03060700311002c1703419110103a860680b42c004030540c101900c00b2040c030183c41071040c03080400ba842e42c1500240300041e15610204410381313500041c10f080d5001c17000d0095268022016055129101d4000b400c1d240310b00d070203a80c4050050703141950401d00088019640c41c0c02050800005081c400b58402408032102d80800441e000400c0054488480340300007070400500103405481d0b0801034054402d00e0070f0718800d4a80c4c9507501d00d0047c0b4100740324402d001300b0609000008044207900702c0c00511a00841e0040c0a16108a90045801c2c2d88807100403680280e50b984544000e4504003c08039500c8040c480940d83c6150b1a440039192070712a10b406003484c0010401d40c0a981c8541040e00805039040d0382e4500080c47d1124008001c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 231877032 1250 231875782 231875827
    0x305040c08010e10110f030f04020105090a17060601171302060409060b070507050303040302030d0509131a0301060e2206020d09050d0801050603011409090f190605090a0f0305 77
    0x150f0070a2041c0008140102ea030039522681d442042081d070240407103c0215005500400082680c14030014440101c1011143c1d03000d48145419881c00b80c501c0006110151240c00c181200e0000300740c0058555010000c40d50842800d081102440030034401c1031040b26001400181e451b00b26040c560110b4640f5000c0c1d5001d0700351048103000860700d8400403100790300001e0003551a4070400500140608000c03040f2010350341c01070054000303854100d00698503540b20001c49a00030f41508841001c2e50081d2203517a140502c20300d00146260100320070182942c09540150410342c02041c280500c0d50b41d0341c021142c0d4071842c7c2001604090290a00c40000d004081c11842c0c1d00307040c180f000040040208500c060320466441350001a44c0395428021613000901071940c00c1031080c2c40c0f9800c9460281d00b20b55208016400300c0d02501c10740c50106042ca00c01180706038081d1852031189d010003210313001c0c1e50b512552040080c0182c1071700d515080c00b6483c0c28107000d401c1c440c0001d19145204ca04c8901703038110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 231878282 1250 231877032 231877049
    0x50c070b04050d0f0302151303081006090b0313060204030b070e0901050307061101060302180105120c010c111c0b010f09110f0a140309100501080102030907030209130f05010212010605030906070305040c 89
    0x1038230f0b044445040a09000b84128001541e420014280002000b10300064450a96072401c001c0c0c240503460580b580050045018602c10b007101c0c50019640d80020405103105080c0d6001c141031402010b01690702110013039100301010001032000d52000100f14044421030714040b014100c00d00c519a0040c00140c1029400908850046402c0c000c0d00e04e040341210b205903101050f1000800c64180c0369034508840c2400103400340300180202d10780248808070380c03400074161310040d01c514548003545014414121007100c8058010480d0061411105004015a0350b05103e4008186141c14252040801c0c04000007400300c0c058025510521090300b99000c1c0c1025103603071303041140c8020b55595016001c85405804c2000201e403014042c001d403070103064801d000b409500e00355400c00074036880c007d081701940340d010b00c0300c41d0104014a0321240000e00460006944464100c101c40c3c0340501600403c06110b4200301388155404002045988204180f900003020307150340c030380203850021503800b8051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 231879532 1250 231878282 231878323
    0x11130609020c0304060e01080702060f18100e100b01020c0913020603011d060d1101031e020d1a0114040308090d08030a0b100801180b03120a050c070b04050d0f0302 72
    0x40c6140008018000e840058941b0707001e50442000464241c07038102c0c1c080e40141c110401048214180d90318850f004005100e4200c000d40c03001c010903280c54662102c94034066100c00401030741c0c40c1d090044044030303201a030f41072000010080010b13580b032030030480c114010000f680c000f4001c200d0101c11501015802403031280d40e969107090111100c09109118004201c0d19070100344180740c0402c0c03008034554084685418074400800540c010800f000c070288460f2840000e00d103180c15240b006002400040c100000c11007403002814551a00506203181401a045444030b030078030303041302510b0072240d01240340b607030780c9114034007003081902e07080c10081c50040c1c04414840700e00300d5034000114580065403000007035105035904441d50b41c02031251101c46401011007404008541e00202c59403000a000c0f90303448084140740c13007241c1d440806040006003000c40c41c0c891010341480020020724401200d80d040034101b000040d4092041d140040c512505602007008141c020310001100c2980d003440802d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 231880782 1250 231879532 231879547
    0x213180612030c031706090a0c090812040e09030c06040818032b0f05030a0902040b1f0f030605011b031704050309010905090f040210020f03030a0c09121113060902 72
    0x340303405068a0101c022841d004a550b140c10740005c95a4880c1c4001000d04421351629000d1500402512040c1e03c200800e0440200b4100c0c030421004910051022006654a181128207554004042c042e45000d40040006851075040041c0c44c541080d003242400e951940103844202220000d06521034140c09000e41c00384888106c03954071800c40c0910801c0c50f240600b0315100700d078820072141c01040400d209101240f6007800590146014030700c0074000095000704080011100c0900e98068444030481c00703c00c0400035400251500421040d00303060120604090000c0c06111225401410342c88a00c00301c181490b100d82c0e03030001000c1365111085c910342000d01b0542d40301c0c0e0005001d240800e05c0c0034400205814424080c1c2d20070703920700c40040166100c1c0d50130040a1148a8102800c501c40e202201090f031034180011805040301c9400000d000c1042d0390f004d230034804c4642c8041c1140324207101000119a80c28051120080203c9020660b66200c0030b0741001071610342c02c0501c0c0c1034804a900c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 231882032 1250 231880782 231880787
    0x3060e0f180d030501090e0c010903030516060216050c100210110f070f110a050906040906020f0f070b06060316030c0306080102071b0b0c07060c0203030d0f0c12021318061203 77
    0x5416281505010307c1a9149840044c2d555595188124000f584010040000c0b9100d64060034020740c8031529403460054544515041e604040c0030503032501d5041c2003e108100041150000312482603814011504500c030000e92540d16000d00d5035080ca840d06007840307403074501c8001c649000c24200d20951300c0354160300b4a90940c80810008403104400160042c0081c0707020503607042203650081a8424540cbc4100900000d0700140708122020b64081c85000210100703c4045d000318103680c0740301d070f0300d80d4000d08013603003071007030143c481c5018a00030030034054200180341c004040804a0b05020880305c84c074000c12001031000364048880d40d480824042e00300a0454180c980450400050780c601c02d4803111090410b108004850b40980d02175041001181d000f5101000658002030030f070b86c00c103129640c038581074444210100b0400b951341d444d2800146c0c1c000125134030f00d50009400b1400c016084000c01c0085c180d42c01603a1001451a00c401001d240d99042140680b41c44500320091010701e1502 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 231883282 1250 231882032 231882041
    0x3030e030105091605060d0209030102070b0a0c0302070f020d0f02100f0810060203070b0406020904090f061d030a0315030512030f07170408070303020d05010e1603060e0f180d03 78
    0x1554429424007001c41c0c1c1407040000c3c0c03a046901c0380400300c038044d890402001125844583e500521131f8003400b243c1610395080c8064001140290f8601c5007074588a501502124070345800102410703c1402454081201c46521102c460350655441da0345440324204402d010b440d180f4001e62004424070321f0142c41d41d02c1501010b89050700d072240d030b09544440740442ca04000b140100001a801400074038041000e00941503081806a10700602d0031100310b000c14190b4001c00c03c1543d05800341c0d94040c08010b01413203503900d10500e0351002c0342c103240c105c403415450b48a5030310050101512205101000a5200301c6030008550080407070704c16601c9001d140c11280c004403080000c3c020351000003001d29000302141d900e0040d2079840c1010f80d43c1e907960346020740d41020200b070f0105a801d02101a00c014240f09280c040c0c18500c942c03101a1924003101070621110307040320700401d801c04800304400d520540c1e00075049a580700c00382080790380b0411546c1648a848580000502c2407010408400350158407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 231884532 1250 231883282 231883307
    0x60f020d02011a042c0109020f06180405190f0606090512100f0b0d050106050405010605090a090207020d1505010f05010309050d030e030417060609091c270303 70
    0x30346006810410080c1d08072004119402000201900f03d0245071400307501030500c1180f45840c850b21100c000110f560380b41c40241c4d11403040d80d50b031030101080d450682035080385404101e0300b0a00c0c1220000c6420308000d165901d482c043e03504c450218014203200c0d4080700300e10400c000100096640c041540700900140d100740000300d00c6011020031a030610100c40402c0c0d40b0710f50024642030302c42800c00c000521000c00c0d040c09080da19511605150386441100075024000d0700049401d070b051070200021100103170322903418004200420840d03034450b5880b0000301c2d012a0320041c2c680105001040b542480000020127206020b048201c985503645d000300d041e40e647c0e87c0028041500c03100154101c90310b400700542103a00c080c0070455154401c0c3c018184000c0100113403800d156030b0360894442c9050b56288904c203500407104101441c104800540d500c41c903000002e00700c420390040f00d44034034292105154200803a102442040112441c00200855203100f0180d160507030380d040041602c0303d841c0c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 231885782 1250 231884532 231884537
    0xd090b010e06101817160807050307060e0f06040e040311190b0711120a031104060519030209060f0702030115060206060609031509012a0c20040501060f 67
    0x1000030552031450301c8410700c0307158094090806825896020f56207000c801400006544a0080c04120a60315911155142584400034140c4030100c0c0044034006406030403110082c0e0145c0e4013000950b40c00140b0f0011680641440720038003a1841c089600d00d5072880e03500d90004400500010040001e00803580300d18001e540d5205c1440318103000c00d8036546032600c45400644000c54071808a110700f10307040e401a0303090410005c0c1104000102d800c0052208040c0903859010842c40041901401050080300c41c03162998541400d205000c2c1050290000140301400780e007410400c00c40c02030b41240c1400c94000c0c10b15031519001c1c0c8042c032140c1d2110008030301030b5003064405900e40d000168881c050f00c1c0c0d07035005040251b650109002803038021494050b81440381880079545540700400d000c0c0526003080c0041001c1340000480a02da03d80400c81d11641980300300101541603002628100c0154000c10207128490003048440b0184191551646d02c035103058000950380b6040b0786e1001c4040d5454 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 231887032 1250 231885782 231885803
    0x303491a0301021305030d02070609032301050903130e040803070e0310020c010f06050603160e011b050c010219030815040f050702101b020a1b0f0e0708101203030b03120d09 76
    0x1ca00b00e82701c4e0014031407000410f80c100401c0c40000c400c0002014010003c21644800800107100c2c182035407415a00c4c3c665070b4000161000b038850340d040209002c1c141c24550f02e0b610782800e60b5140024840200f44400b042540c0040c1d411541d018000a18403100101041d9100e612801b0030600804041012999140c54003800054505041c01560700ca0810040f211614049412040c0c1701c20b00701c005828100101582c040a0814450360f41c052450f009400030140141c4ca44006460300388081ca41c0c0a10380744c2081c071900021381c08001d4552007018800c140040c06005000300d0050030f00120010708040c20300b41009010b80d230005803042007805494050100d103941e2044043c41d20403074160803005800114014000c18840b40740fa00b19411101140354030a5562400503000e10700941000d5900840e007014014401d50080016802c50340440f0704a0380b0b076103400640718031a80c61100041c00c1c55242c24418816640c280540d078044110010050b54501a500c4890014816130000b00c4156000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 231888282 1250 231887032 231887053
    0x504140709021210050607030c0204020d1104090b0303091309050c0d03030b011d03030f070807050708070303030506040b09070c240606140a20010603020303491a030102130503 77
    0x20391060340486001604452900e01f0a03107084800e400b00580c181e80182e02009480140303860352040403036505844105d04c0d00d4a042c02010310650f140200d8140c4030350b00520800400e40c1e2941c1010020740340004001521a1652428078100310701e090465900c480403001030401c0c142c254000c99044002641c840e8031212070080801000c40c0304e24500750301035109102104410310810300a144081c064003525080040554410f0302e48005608010011340040104104154150069940011080300c2c00d11080001801188440d98020010410004640c2042c0c0c1070002c54841b0100000d140c602d00d906164168880303901400c194441d0030b0000b0050856481d10a43d41400c0c2ca5002c42259519544d060700c0302d02a40c0c100007100030200d20381d5610000040145c1d420001489a080392802c0c82c24400c03214030409c1d900101a00e040808801806c4071104240007540e00070b06521442603000600028003000d89043ca00e0341196203400d90305c005002c14504010074851400c60301c0482c06c03105038110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 231889532 1250 231888282 231888301
    0x604330f02061b0415030605041a181501030f020c060108010b0a0609030506010e0403140304050114130302120307050d050f060a15050d0c050f03040c1a07020d0605041407090212 78
    0x1850340b14400010060106100c5017418070742400c1840750368a004200503448030002000c44040c040914003918020003400d10908000300603042c401130380319002ea1a854000c000c14101d144009800307040581d5000c84c1e071045003903541039501d5080c619044410541c4c403082c201d4024050410a2442a00c1c210300c0010810305c20450780003541c0d40030000d0302c40c0781d180011420034040098022400d00c015030082829104005002e944510f00401c00800c88a45c2c00c00030441e0070b0b1024114001002d0444e03001008640c000840c1140d01c41102400c0e039030707039232250304c21161401f543c041c0c01d014904220a2005800d0800310190240328111a0b000c50945d4031035a0501c123600440c00200429001d00c000010200d041d8055000c070a480d00b02186010755080401b11142d208950849100500c3c0c0024400c0f181c0103d01050358801d0102c02c80d14100365500002d241c3c00603103000810080d15180000d04001c40391406050801c0304c0012684503544a180c40d40c060b402481044450600a00000e100d448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 231890782 1250 231889532 231889561
    0xc030f020103060b3408090d02011b060623030a02130f11040e0a06030f0b060613081b0402031b030c04080a0503030a050703060302010906030e01060b0a0e030c0d020604330f0206 78
    0x2540400c903140b07030558030800d0040421001500340e052007980c800cbc50040f000d0f5011b072000414428100020300506000207031400030241c00c902182c034034001e191000c3c40c0d00c002074030140c8990110f40c102d154102d25840d1601a211420f1548003003410012a0044165500c02500a0303c411000da40c02d42d80c0c3e0940c021044903401d12002e07000c220341c504040042410166010b0700000041c00d4203280541e92600406080000d520507150740d0f118100d02c00701e164031255081e038805004c640552540c01c120170380b0b6103000c60180945001c0a40003021484070380621007118001c010103415602c0860450425640b0383e00201c950000c40c1d805c7c100002c3d030380c6100e481281c060340c0c1d05031203c50b003030b0b81000b008400405503603d070b09015658909000c550510b811029141c064615960150038940744014141400d000d0312a141c0249000140c5000507540d0000303540645003c041a00c90070742d640c14903c220356a4007000b0b885d20080e918808403015a00040301201c02401e5002c46da041e44445400c3d4004c03c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 231892032 1250 231890782 231890887
    0xf05090609220506010f150206040c05010e1809070e100b03070f020a0f05031e0309061501020703060f0b040b120d08070c08041d060d0c030f020103060b 67
    0x14074507000164512520b420641e01d01048080056903024541d42d03ca00e41007082c1c01c625101203445200b04412859039000c118404114800380c00c5031b00701981c941c00d108860340602818410510900d8569486031442d07250185245070b0780096505044041940301d00c081d008111440c170204001464569071442d80201700d454807031002e442c60380c5800c4111200070070005c1250841c000c407003446010507503c2c881c04051500810245983d00801d081143c0000034144240c6030b06a028002c06c1030f01700001c45c00300e0b803001003950000c888011100040b0706102c6a5040140032074034182019081c00303140ea1001041040c1902c08014120a043c1000991400305042c50450340c0420a048603561141102da6044072550500b90b0140160707980e00c0074590420740107018001000b81c101070210001c5004aa080700e001e4030344884510391900d6070003d0b4a000d00005e800302425060040859100350300a100404005501640701d4001c1e05094100048080e1107820681120440345003400c0000443c0d00344 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 231893282 1250 231892032 231892039
    0x30a05040902130b030403210608190f050712020301060603020702030316110a1d0a11030c0a1b0303091401020301051c020d050a080d110a05030106081801020f040f050906 75
    0x1020700d800d03001c0c0d01a520400703000084491595000448040070310142d4000e603c26102d0407401402105198451010f54100300c540900302001000011404905541451420011114202002d0401760071440e0b02c04402010382c4650300e000030303403401880c06109405200f00d009001d41c1c0d903104403c40a81c018a00041d5040c0c004001034800301310214182c03510301d4131030240025030125010004005070581c0c1d002c0c1480091941c04480a45003542ca82507014403442d00800c14541804019511400010982c10310810000351824000d40642c0c00090b0050f17028007100000600e031324000700900005401207844200207802d40c0e1141c101030080d6410380314090700012003442c0b03c1840a60781088054240d800c1064814000003180083c0508044a07000b01d200035583c030380110006003200e1079550281040c00c014010604900da02c41e0807a81100c1d0103103408100b58940852107000001c441c02a80115840010320072040301c00d08015004803021441702c00181d99945003440b40c4204100d41c02d40d403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 231894532 1250 231893282 231893287
    0xf14030606090301061802120604110a1809091101030e07061b0303020d0c050c0f0624031c0801140108090a0303111e0403171306030e03091e01030e030a05 68
    0x504015014090038040203002090640e60341e9041c5241d41c0f55621b008404540014610f002c500140c0b8100380c0098003940d0030041c080c003e40304581e603802181c82c05c03000c0007008012980a5100300c1c4901c005800b13489001c0010700e00c1c030724022103002c25107450303240400d00f80003648440d10b00102d440011030390170351100f01804140c64450040404004001c4003070603403c0c0701c05014040301c5d1290401810148d281c0301d17070300c54046e05942d24000da01d54450469901c100c0800501c450080c07131800c044c40c1114200150950904002402c080c0b583c440c12401600c2002e80114290348600b816040712680c038440c05800360780c1070044850081c1100d25054035446105590002171003548665072445160181a007040d00c02c1160b1072214000d0194000c00b94404241801841030542900191034404030740a4581802d0441160706030b0811320403002495541c2040104081080c0f0880d5000e84006200c02021a00710f20752591340d91038209002d00091034a405150500030001c1203903149400d076150b090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 231895782 1250 231894532 231894541
    0x2031206090709030b100305010605030d140315130c03060609030809060d14090124060c0605060604080a0308041101020a0209040b09120406020a0302010c1e230301030b04030f1403 79
    0xc6960005090b0004100030b102001000c6041551240c0c0154103050088400d070f40366081c003600350340d139581081e84650802846151225005000c00c40f26210b2030144075201c2e51400c618020f200281040c098101c104c2e0000f58100c0b0742198400104034045440c2040010b46808044507070210a01004241240c01c20112076079240c03034405032000000c01d59011075458487d800505040406481c10003980e9114a0105201400a403e05c0c07004802119441041803815200400e510060071010b0511070f540c5003c29519180e40d802c48014021000c100d03280311200303180080c00650304407800d4441c0000c884194440e588082146405c840d0001e1442840d0313100c6413a00c05030810050050b54141c49484001d10048440304050001482e154029000c2034400d42800390940d00c0c1c0007104030400c1698101c803002c01e00780c0d40409101441c14500700c0140402170000c4840b1a0003404014007001c40840000100314103520420311480c460354078032824900100090b03c003503031994031410141500f4000a27 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 231897032 1250 231895782 231895789
    0x12160903020616021203040320010503180f07140f030a020f01121407050c0c010315090209041806020406140702010801060c1104060602100b0a0506040504020f040e0c030402040b0102031206 83
    0x2010f0181900581ca8102641d6900045030341c803002d82201095000400c003001405050f00440004680402c0d1401050001d000001e240388402403c10303244812612109080790410410540c6440b10901162032403911000b841252a014900c1d0a200310140074210300c040c1000310b052800c0e690f0107008030888070700c41c100644e182c000c0101d1040c1d0040d81c0303000036400510311113125070240350103884669540f140c03290540d0038400c0c1c2c480950f040c18202000705ca4200608a2030300202c44c0400d5005071240314250000e000303800b0700e10f00c250101c030310351900000348415a0f0003402114541c0d11501c003d108654009005402401400703030104d44418010015076000d00d1100818501c50302c002441443c4a100040441c4c4581e0040c1005a1100d45444410180b40c804d06d40c1c1040d0882c0c40d00440380c0381c040040c80901c070b54000c0d0341c00b441d00440c02c88108800d910035180902039080313140201e032800c051060f45640080310141d1107203003404800e540b194004011100740b002c4880da030700341503580d10060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 231898282 1250 231897032 231897037
    0x51303060e0a2901060f0816090807090606020105070f0c0206030a0209030102120604050105061314030a0519030806040902100c0201140a02010e1e031603180803121609030206 77
    0x1800094041c0c1e400801c0061003180e84002c40d9a4108083c10702c08190340552080402c058000c2000c4c090300610314004550040c8610740d100518141d60841404003860403602c0c0300c1554000029842a1400440e6180d40b42c0c00120984040c1e0b4000c004035510011300b1036035070086180d000e011840c46000c0c00c02505080d0000c686c0b01d090604058a0020703503101007422030b0b00074050380c45102141010b200080c503040c0284c03401071004880603800c01007200401c00013140c0134428440d80c0c9104000407002d0f901c0a006100501f0b80010944418201100d101440c002c00d0910407070000d5810400200f2500d018400d4400c201d80142038900c040d80030744002d981c040c20340c420590502c040c940d81c1c1c0d07020b014000c004003141e540c00c0c1e0002c0b40720707800c0e005414038000075991120411030402c145010320b01000400e8501c07807082100003500d10b0007941016125030303812844d50002c5132052940442d44000000c010080504000c0140200343d5481071003102c008903042a002c00501c600c041040035280203000b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 231899532 1250 231898282 231898301
    0x1140a0f2a03020f07030e030d02010e03091905030a0302030408070b07030e120c0604080a02130e1903090b030708090607020f0616050405041d1e0a0f0f150b1005130306 74
    0x240146400c0340b41068414a0f0003108080780082d4030440c0c40c641f24107041c0f200501240e0f03540005d10001510745412602ca02640786004c1c0201940030519001c64148207403100100805803e542c00201e507030400035101e500034003c03880b041c801e5000004001d10a08210341d00d0b01d401d991281c80e0740742038104028203421008101e411074495601c80140c9503403071600800c02045840c2c0108207402e030901c14418410300000e2810490703403401e06901180c060109025200041201780050154030307904d0241c80e0b80925030003503541c010f004000c00941c227403c403c9841c01a490710f400c642a543d0f55050407655041c48000810485e0031540c040b5501603814000151140c02c582403660a00351520041000c40c0c2c101c42c041c03081001c118904c1100c420b41442620710a240e90850907400415490519070342d0103958400400c0700305290000c0c014449181c030383d801d2641c2d10071324410381d40c01e2101d40000688550000c980c8203030100f40c951015103000e9011180c0c1c041580300314021052a50b201c0700000c114800c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 231900782 1250 231899532 231899537
    0x8120a2706050d0e0a0206030604020705030f07030504051f120f09080f180a120314070209040c051f02060f0a11040803030a14090a11040e01140a0f2a 66
    0x40d44080c000000c0524409032519559464840c50155404810746080c0344000315182c12000c0004096220001140e52040c02928056501c80280c44c2c114a54450251101d148640101d01a810194050010000c0f0344080b43c4004c404000406801c0201c030b4800c0d61140401d0100400c1c402d1108282c00180850f0100c0da0000384200700c5480c0c02c0e01c0341d404034400c2d007880c000010b4803040051030803107681c0392040240d541c0003e96042500800c1c0c80a00d440028040c4003034054461000150750b030455087c5c9502803c3c050050900f4a00800c01d51018040c691007010010101d04407924889080b002545841d0300801c420f41320201c40054a485c0500b54010181d100c502c1c4501a8001e403004200a01e2130000450341c4c0c2c03070000c101000700c0d10000c41c009014184c940c00d04c4503005001a40a10142c0c000704944500200d0000040080a8481101d600c030350034650086d20a8500042c2c0c0c0740310b00031301b5038140881103402c2d00700003c446801000c200481010710300f10f91100180c990700e0030b0200060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 231902032 1250 231900782 231900827
    0x50c030d0b01091205030c250b070501020702180402030601050429030a02060714070504060b0703210f020702030f0d0f2105010b0a260a09020a09090f02090108120a 72
    0x80007103000e90041a0005d071165840000d00c441100820000c00250010b24a424101110842414800c00351148030304421060702141d071005100d001e504488000f5401045200d08480805156101d914110f40c00d9121780101c200004990800b40100101d0f0a03054500e00141c3c4840c0303081000c029150303090940c041c42030024000040c1c82d4413008000882c010150000180580c004e900c1c03800c00d4503007000f40a5801c3ca18104441c41e0310344180c070040390b0b00d428480441c520307820740700224040c3c420714092614180400000325101b15401050b80d14000e07020b40c1c1d8910303200b01c400d03540c801100c488000018554841c5040305485013520703448000000340105100c0e08208204403e5400a030083c003c540000100c01c0740407500140c1c40c14070780c2c0c8050b100b4034055000301c200c0050044010280c0040f1916810010304650f9088826000fa0250300000c00c07034400b250616014004050380c00300e00400c1054004203280302c0c0085d40c02c0251110b0b2000301d2a00c04600b4003218502c2d1a42c285840c0b04400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 231903282 1250 231902032 231902039
    0xd03020a021305100b0c07090c050c01142205030a03020a050f03090d09080a05120d06090f0c09081207061805580219031101060501050c030d0b0109 65
    0x1080d00c0d01d1900000b185000c02d0a007030103e100f4089025070b50048851000c20840c90b00c480c4c1d000301d00da008035120034400241018803410103444500c101207001e02c0a5203041141c0c02c1004d107500301c460048205090008401211034800e010031401e160010341603078028015002514400c0d00204840c469614225041c464001e6074103d1340e4005403806c0740182c000c0d9030300700c2c9220740c04502d68001340380100c01000c02581580354141ca404030b2144c40012020005003022004c440c51b00700300014a40354604102c08a440c203c0800281451910310000400600c80010141350001d40350708254098400c551034240c00344d03260801030031203010304101e83d00c59000c0000410010700bc4c9a0785004403540807100d0184100c03180e01c41959803036003040b080c0c5121040c9651850079070040d00e1a13803000c408408460442d8002a0315018102e40c104110b64980101c280400d42d12800c41c120203c0c05031b00034080c0c0380e1a84d006417094014080108243e5000340004d400c1d5050380d8100d00c59055060400b1500d01d0384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 231904532 1250 231903282 231903289
    0x40507031104080106080d0f080a0504080c0a081b0d2c0405010e0414030408122d0a021504080a080a0b040c030b131b050d060e180f0601060801050d03020a02 69
    0x50f400703203800e40d40d5880b00704040141402402c3c40400c2030718241303840070414170000d400303210090320a580c802d9803007000800300040c0c24216a003400b816000c645d007407007a510b00301070103600c02540503d0403e26000140740161001499980858050b182c2c200d0000c004109010f0340c180c606c04071008180c0c3e241e42c5580c145c5503407140034041e10207003440304418a0b080c103014454007104000c444207139108120402c002c00b030205602940c9800c49c0c4820360b94100b90ba883c801042250261131040c102e84c20074001540016000620104802e0340070384e452840c68640b1003050040c212800782001a0410405021034030032410742d580080c00100001d010301000e00032904680f0070307030381c00008282c0d42c61400e1071a1800c00b40301e5a40b0700300e15206014210407001080c461060040848007440004501d0058040554103d58040d0100c50b00b6000240307024100c100d80c100a01410024a00070640d400e0840b8a001c10306038160b03045501d0710140b40e4030b0b01c014002d2800c1030350b10980850044514800042e80d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 231905782 1250 231904532 231904537
    0x60313032109060c0338150d0603170a0813030215040c050a05030610120305041508010509071b02010f0215010f0311010c03020c01031802031507030b0406140405070311 74
    0x9025400014500f0305104e4003030308540c005035030489803038007503c02e028265655039400f0f001c68001c0c1e010380e01441d0000700802c2041c00014001c0c0d5510f940403d806012030040c2e4824000c0340d0140c0d01080c908202c10781601840e1040445c03a8001541850009414820040c25010168800d10499011110742900e0850394081601c045503400c1c55444200410315203004541e01805040f8040e211b01d0402540a83c9400313500e1181c025004c070840d05003001d050003541503d00074281113015590000301404020f119100c240116031161103581c000c50103c070320664074590080103010307081406ca600c640054601c01a210428400c511608401c000c0168031940701d107008060001d420041c040c10340c0303001c0c2081c00032007158a04102500c200400400d5002490307d000d44021b00f03000803100070980241c1e074000c0890320040d403d841080b0840c6040d21071400814440d01140c0c2c3e0802051010f0030421040e6903031303445901d4484104a0002d48c161600b5071050341c010145090009040341d1a1039946208e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 231907032 1250 231905782 231905801
    0xb0f0d0807061505042c120306090615030403030c08070c03020c130e0d0504030203010608010b15030915130b0a0e0a0b0c0d050c18010f050715060302060f040f050603130321 76
    0x582030034411186014081000c00380c00e46e02c92016003448125181c040e0b1950200501162144003941e0104106446030b80c1f4680d6030b40f2610040c00e540c1e00d410b040145c050700401071188001b462a0b00090f41951207498243c80c0c0c030384d056002c1c1450030510010008807095400d80707080f0650351400e07422031044c02000119206019074a0301030311585180101421500f0603440510664107143d44c265040c0d40b240c101a01c0c3d192101c01854a03a11100d03a2180f074040031480282c4003071520404d00420311340e006180d41340ca61082c10054517903034400c580b850560302c0b04285045603911840d00c0e20009229070030201c0d031080c03040354441e0422021480c0c2d041520016a10151500c034009443c4004689030f103c0702506180078200380b045102c0c2c28034020b105200d01e04c2c01420795030041c00d150110110300e410413802950003c0c646a11170b843d4808400c0c00b0b6106103d420322440008078000791504002080c0d0303108094604e0080d4840f05c02d520240e42c0820030103001c0084001000041403840030741d11403179100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 231908282 1250 231907032 231907061
    0x1050f0a14040e0d110609030a05120702010e010908040315060e0a11130e0405100b030d120212010b090f0a05030d230409140a0e0a031d04020d0b0f0d080706150504 72
    0x441c85d074442054207142c1d025022540540041100790803168002040b11406c400b00b807500c1c41c480d40c40b80c004034010b128040d00c2082c55400c050f000303018450500c1c09041500d004031228607170000c150b02072b00101d401e1446901050604800040c02541c13955208044092941c81181d01c0c00c03110340400050302c101c039046903030042900300a204c1400410410301d0911140002d08008e120650000030355103481924440c010040840c0c0c0080300030280350155a81a4402000010305584943c442e42242c1c016140080c0505a0140c40c500c45281c4000b003041141c0004d0040d00720400d1995007100d6200c40c02d0103001d0817144c41800e4040c00400e84000300020720360b412000440341d00b1842600c10f181d6028201c41141070420303100680c2000301140300c680312a450b041c0050601c0800125003115072080d00300741e5010f4401710341c1300420085500040c541820480799060400981d408100113152100c10280030108140300c0703d000030320681d01414072100100103031304083e5a28000075058882c0800c913801e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 231909532 1250 231908282 231908297
    0x1808120a0b062502040f1404110301091e020607080301081f1b030515060d0f0b03150a02070303020415050c010b150d050a0e150f01050f0a14040e0d 65
    0x180054070700c1001c25210044a80b00c0ca03200726040a101401440288030102c2c0700000c5400302155a02d50140303040800c000740034840f42d81c1000c50400d4050088509594500030000d60710718914040c85200c94541d801030f05008a07802061440c0f0a41d42c400d0b9003260010420040700340820041c401842c001d00c2010300500054a001c0c00c802c1d8280506210b40c0300060a088041c000e10759000800c8092107458174002845070b4400c03c1c03a0100c41704015429810000008114a901070283c12018420305103074002e1002440050500d0303a15003910749100002c10200c03004c10b21300e4031107400078005a0701914001d41030645652503041d1400c14026040041000041d490442c1c684c00e004090022608465071900403080002d0303060213204600d545c0c0380706030b51640001c0c030b415500e84c03040c18602048400c4403003d102c00c0034a22420b144c141c501101e00100c910000440c0d2905500c46c0c030111a0280000d1441c5161100450842d0f2200300080c0d0b2140d211461000400da003007000500c07810f8266664003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 231910782 1250 231909532 231909541
    0x1020c010e0a060b060f030402060c01060528170a0f111503041a01060e041d06040804081005040302031e1b060a0b010302070f110109180204091109090703180812 71
    0xc85148004442c02032009000c0b1204046e8010706982e400381c7c06850b8a40e0342c10f280200603005104030f42155a00004024000305000010240c40d0a40da00141a11002a45401752402001900080024941c0c40b01840301c00103030005011158903403080740403071540304074180010030041c20b450304401060030200400c818000a803803848a0303803403a04003841f503d50400d440181041c04009140740526204c2100324600422549880c205440038400d40ea10b6080034908904941d10030320520200344101c024500071400c2c00e1048134011541360f0029845d00340780041403a1904051120784e02115801d0155825001034807440c00c1b103886082010304524501440c541040b11144242c0c1810144144200300000d418078904c0c03a0429041050001076020300300048820501e50f8102e580c8040c070212414014030013940160065909480c800d100000c0980ca91508a000f005c8165601803c00c20216503128001d6020900460b0003241c5070600d0010f07611031400550142c03103c0702b4600882010031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 231912032 1250 231910782 231910793
    0x30c0303012c04020907050c0a0b040b041103150a0c050408011a0a08010c0507141f05010302031203040f0b15060c0705040b1f03022101080f0d080702030f090301020c010e0a 76
    0x10342c103a428802c0a071018241030300454403d000c01041c000500400055034248040308100705111f45511041c035a60519051802c40302c40750054800711202c0e14101c13071000f018500810782c04098041c81060280682c0c2e10005140940302c0f03041d80b0403e1150030080400e20300d000b801403101e560102a5951010f9042c00180701c800c40940e40104000d91400b1201c450940c0c2c400101e0713901607040708400070310240009410b401d00144861501603080e110f5021610307621a5084103048a000300c040d01c070034070b00103000d0701c080b07100446005100340740604e07052000940140b08942c00510307002000404010080104003564889802501198400003007003002d847c060181662040058580900c51140200e14010b280e80d0b54541c0c2e814140c0204104000480f015120340012550550a5241e543d48180d06a00c07401804050302131b40c081d51222583c040d0041c0340d114001c1ca580d81c01949000c040700505210340d0040108a0b6040d5000c124a2407508401d0081c1c521521064015200861061608 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 231913282 1250 231912032 231912089
    0xc0a08090c06070201031d1905012a080405072c06060408031c0212010b0c240711120a020c100e0d02041806060f080d1b14030c030301 59
    0xc5031554071803200e031803075500d48200b624015642804c0106448600381020580c0e030b116800d80110038420304070701425201c01e40440000d028040c03402000300b80d50258003080000468940031002c3c1c42c80030480103005d40b040c0411580070340a03d042d1410552030f01e4243c2c5028615101022000b5001113201c510180000b4800b0703001401212550303e86032070406001e4403400388019550f01086010f0341a112400d068040316094400d100c101e80556841c0d8032000c041341c001d42058034091140340080c42e000b05c00210a500a80ea41800b0140a991009412214040b00100d081028018140c83c21f520004c03240140c044203080d0380240146140c040f091220548500180f0410840700710464040b81c0c43d000c12404115030180c41c04035000380b840c5848040b41c0b60500005002a190010014001d03d1880422041d584008103841d4440e08040003224603c0440030440041402e5035040400590915540c410310041c1405413401c12111858460568209078000801101203042544000c1c058502 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 231914532 1250 231913282 231913291
    0x20309010207050a0f0b0a09120302031c09031d01050c0f060a0c05030708040b060423070323010e041a0709081005040816080d09110f10020a080a03060e0c0a08 70
    0x1130b480c100030310300620b520b11280284550542d0003000602c0130780b507134421f0101002922200100c00390301c13880e80c42c0095607a4081a0000040200742041e0792290703840e401010072040c5c0641d241500290b00240d100690350034481d10785c0c144582082076001410003802090102ea1000f00500100e240080023402074401c06803948082050800800c81001d4200700751070b0300b01d03421400b861042c0c1d4441000c00c2c01011a4000304450303524011070103000040e0202e059204a046030b506001000850030002d022680c0f0f00208540c140d08400103122040d055500e15600c5405030051442c00b110901c124015203c06880b01800514940401e001c2e85004204402500d81480420015071800b0303140c401c03c0c0c0c040c041a2910145414124005001c0c4410984500f422a4481004160101e1400c4001e07680b20090482c05624490416100c40c5440f03e00c03240314030176507000b8005150b0944e48548156000003105814160365032000b017840f42e545582180304020001c000c0d039a0320052440503203038900041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 231915782 1250 231914532 231914539
    0x5010510051c020103150b0307030606020609120f0d05010e040501060b07030509090613060b0d0e0a03020a080313061a01120b031b2202030115090302150f071202030901020705 77
    0xc0401c80754984100d4041554400c0028042e40ca0031403004070f018060307480100002000303600000c00d480d1540001140104040c2e1010004035a984200341d845480461f06000303750490142250702c8040031006001841040e80040c2c40c1072280c5003000301305c1d50300b81c1040081d0704c441d00400040100c01d204040c00360143d060f00604101722584c000b01b6a110308281c0c2070251140d0b40100d6020349414080040a0041c2d600c28001c01d41c458154140342d820503103210500b03d040c81404442d5450100b2205811038056014240c00502502c9403142035002030011500ca03204801d40308040b994601c01c0155848031000124003092121000411f5103818004440d00f003881c00c1c1000d0015900042d40c07400008660706441d607014105d100140310803000706aa1142d00998000c21742070210b83e41d0040d0305a40449010b069a500100003c41c1c106100e03000c02034202071010482c80140702c003400540080f07602d69001d20700e0000c16603181c080d125810702070580940c0c030100c0c40c1e003815038060003090b000c3c04068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 231917032 1250 231915782 231915811
    0x71a010905011a0a030221070e15031f08070b0a03060603150317070f050d0206010b0f0301350d140c0a060c02032104061b0e0111160e04050105 63
    0x184103d040c40062803100f0081880c00103025001c40d0003070701034800309104a4402511540a41145030b04035908440660018a042404105902d041c5450b0540b0b01c0c50340010a09564400010010348a5a6034007880000c182000c0022403800810181d4040c21805807026143c04039042d000d002e468041d0816030606040024400e041e2000804600c101e942103001e02a03100010f0748a55102d10072024080c1080c60b040d510f210600030001242450f405142d400c0340c0013a0f0b40c03900064142d00900a6000c001c4c03070200300400c10020508100001c103040f02c24070b00307145c44c1d40244441001f1035590020307469800041c49e00011a400c00000c040010500ca15a481c0c0b50b2aa102240c50f0264040003c01d11566085e148441034401c0081d03400380301d51242c0c0e0240414044c2000418841d00300c500712080c9007400316840030281e82030707028915010991148402d8201c0c010054030540708504007919544586c1440e81d00341d01b5200c02e01c00080040c50b004034158149400c0603401e65500510001026402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 231918282 1250 231917032 231917039
    0xb131e050c0405100b1612020c0319050c0402040602060f15030c0105030a090506011d0c1603050a020f030a030b0a1e12060b030604120e04050601050d09030e06071a01090501 76
    0x109034100011400c80c2c002500e80c0d03c4c0d500b001c644800540080703400c540c1c0400d82d4500000100044440760f40071b03103400c60302c608440500700c1e075600b00046020740540105140b0120380d28103044506885200d001520030a200040114040fa0400d5000c1d0300180d0050042c4440d4a4801244540000d01c0213145035841c00c180021035501c2c007581001364100b0000100040000c91264800000e0302e6020b130544070a03507503900103403509040944c0030740e140005400100b01d8002584040380c03240c0c81d5010045000404070381b01034501d504880d03507000c00d42c0103002c80900421001d01c010013000d5190785000800039400020300c1902c024a81083e41000342c00011f64004400c460420001c64000c4401d0001c52419442c14a0180c440001d0143d094842c080030302c8100008200d0780310a4100303550310160181c225204100643d002500e18602041b000c01c61088400646d81010003414000c2c20301c0900541d03001c021030031035807207003d05030741940392125030241c0004ac5541c0b950050600c5070007070129506 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 231919532 1250 231918282 231918293
    0x1030c0e01050f09010302040906060c05070b071101050d0b030a0605011d1b1e03040c030201030f140109020d02040f0b0c01060e07020c1903050a0b06130e03070213090b131e 76
    0x14400030280f201d407021030340c220b80d031784240c0454014000000007401555503401010707202e00c100d090300300c540e0b009132800401c0d00b01c1a20161488242c0001c082c0d180d40c400f4400666196108038220a642c070341391001c5000544040141c20400b03841b4042c00141585860a1488801c001c864205500b401c1c44050020500c1c041c0324100400c1c0940200704c0d99410701003c2c05081704e120240d10ae80042c008000c010503c04241d40761003c503070003070f02d003801144402200f840c00c44070002e00d91100d51202000602002800740e02a02a0010759200185400e8507010350141d413500b29072005007c02c0000031003020b00f01c02801200b00402d030307500b102d030013070300704410046e4481c0300c0e09528034000c00c0e04181c6c08000340b00c8446254002c40e041800e403941700601d4240500e401100703e03007181c0034101c0340d424094010400c0c07054a00c0e0300b420304051414444250308010100c1c0305107038968001da89500018000c51400d00210b401409800380400ba81100b603d4450f103a400f00b201490107030001031000c41c01082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 231920782 1250 231919532 231919537
    0x303040509270c011b200a080313180203060a03140a06020a0302130e063607081e06090408070c0e010f0609050301200d02072001030c0e0105 62
    0x8200710340940306966108281440e50030910b442d5100b4840003a108040034001056900000340d0a80c0d500618101c144031481001d419000c0003040074602d1000020202d0100f419041010001014100b03099a600811443c50b00050001c0500c503001c04010405100070b0303940b0100c3c0040080d8203505510f46035001131403440c4288405000c101d001d0f48411148001070103124002c0e5440b40f01152544284a0020001d4008480e03406940c60f01d004007041c1c021010a4603442083c2c01401404461643c444100c90801822448236042c04a203500320288900d840250f072007090940d80d8040c85142c09018101c03021130440c1050406040841881540d131640d015082d8007903005100281c2d40c0c0840e140c140186051980280c80310340380c180012540b0140d011103101140c1ea5580da2010301340c0c50b041003600702c41c5a401402003010005008400800446d030140072103031444c00005003000020380390541100d0100303440c1942e10840d00e2402ea13030b03583c2501c00c0300c0b0300115a1400940030b00302c1c00c0010b011032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 231922032 1250 231920782 231920789
    0x606030408030417120f13050601090f0f0606080f011505070303020c03070f03020f01060b0f0703030e030f0d0204090c020d391a090303040c0306050709030212060402030705040b030304 81
    0x41c030000b0014007071001220007843e84500d1400140d80d140009504840c035180301350350380349040c1301c1200802c1c1e00c00d0303c0e44910402c55801c04040c0c0403036403800605c40000c248407480000d00350f07101c03c643d00c041c40c1c0e60300c1400000d02c90343c0c480ae011440d0040c0c0340d0000c483d0580046011131210741400c0781c01603102d800d685840c2d5050500599920140814500d5070140080003000c2445a48c920020198041411585102444020b2100a44030300380740f0440c0c01090703407169074510b05001020100744a90420200c09107488113891071b04441c0d203512802c603030004021540d0f95400080030031400000344240c0300303203030400d10240025808480b4001d00f14001044070002c0000c6541018054040d0151421120096141740201d8400e451814032884c00c02c6d019005442052140000c810303c0002c03044903c10343d4001a49800c41d419030350340400815020f0982c00802800303090220050301d5140c024545191491300070901803516104061030844241c01c503a0217070b800c01e80b42240380d0f10f00206a4080e03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 231923282 1250 231922032 231922043
    0x90330111209010c0503030703060806072d090b03010e1e090a0303050c090303041d060307030b0406050405030d18140c0604050f040b0d080d051605030c0903100e030d1406060304 78
    0x2a02c10700e900484030000c1c0b110001c3c129020000a004003240c0580c02074080350380e140d0075501540d9602d0803d58110fa2811a04070a1903200c132448001101045d4200007056120b0400382042074890b00d21201d603410907000a107228050605000d1441c111035140518a240b81d04501d415250000c0b410f6101c60750310b00002c06050300c500101d450f01c031102d0207403a504500541200d481d40c1d0713101980303a24094002607100d4091203060205944d424041004801e82c1e400c50494000307911190b940c07000a100c0204159100d000602c680241e249407030003050060705e00c0d95075141880016082c100c4454000040d411015405041000700a403503010959045070000c80e038103005064240d000c503000d4000600e24540c0541001c46100401103100090001c1d0f130f086203820003035595080064071040e0380a00b0040080f603800d10000e107107001010014021141e01900352040884140300400035079903109041501e0b13070004140258035281d10b1013a00c00b032001e918a05001424098003041c1e0522019002411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 231924532 1250 231923282 231923287
    0x30c090b010903120e12010606090b0f070203060c090108071106070e120a06090b0a0b0603060d0f1a011401051305040c0918050106030513050c0108070903301112 71
    0xc4030380c014804000107580200000e01c50b4084041c0040c002034060032054860706d1081078800001b00140310700d4068951780d440c0c58500c903080500e00d46440d0482401c21038840000c00c05640140c90508c0b4080c010304544585980740d821090014140440c01403a4508000244080c203400c02c0000401da50400901e050407010b06940c0c0010030f0802408111030080c52190054400400c00c20b94808060796014001c01c0c0c5a46c3c0710500180d09a4241e07002d415404641400814200d04d44480540c404502c12040e84810414035507901c0402100814a210f82c0d800110041250040030001d030407140d4000d1070003501d003950041c48034810340843d00034240150341c0c64901c8184580200c1501c0050030002103400b85443c01c0e4401c4801920f030034042d00300024100004540c004d144000060750f2164448094981c103800b500044031200070081c0400108001100300001181241c400704107440316414006c5190060b00e102c0010440c84940d554003000380160300a56120400b00d5442030002003172580ca039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 231925782 1250 231924532 231924551
    0x70f0503040f1b1a04061709070b090604030204090303050403020106050a0302012f0303040c0f060c0305030a0917070305040306060608070c0809030a06060e09010c050f0414040f0501080a030e0406030c09 89
    0x748603540d03040821010440c0d50480c040001c44c0340644201d40c05545c600c03090702c41c0315000e40d0028100381c0740c9144c10751120105100601d0840003801700807401410440c00d05076280c00080c1660740d200d1b000d0300032a40e96030501c41171660a0003890040d000c26918040702c070b07165600090160f8600311012669442d0803c1c60700410044030301800740b03001140c048036142d003414103104440c08424810b540810a40100c002081c602454a004140d50107440b1281540c6c0c80803183e0010b407140a0341251008040a03c107802c584840014008140c017903591240c8a07421842d007030045601c2d40d0041c2007409145410040503c7e17012041070a10f641c4080500d4039a08e4440c0801c1c6840c0d1900d8001300360038100000030501e0000340e1659403154855400910940d9105031066a075440303041950400781004001c2807003101c40680070b15a050700003800004180b60740c0500741040310000c0c1c1080045400c100707500024164446034017002500221401c100152440e0b07030303104619446201d442c0300d6070b49174480358 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 231927032 1250 231925782 231925823
    0x20409030e3c0a03050d11010c0f09060e040e0d090f0503060f07050711130c0f091401050901021203090106031208060d020d0311010c0e0102010e034e070f0503040f 72
    0x50006562001c2182c4071b0b9000d00a001d040d480c20701003800750301d40c6031a003041201885038000002e5805140c54010b01a4280300e4112000c7c5801c2021580241d1501e841d00c0c0c0040c010444a03103e80c0d410b581d1407040070b0815403c001c0e200140da020307500c41e42c040e105200c242410301a005400140c207061080e070320803040c03404040c40950f0301c0c8507070351204090011084800b5280c1003c641c0460320750314901c0301c608514051700c2441e0580240070420b6000301c82c0b03a5155000703400401c001c080500440b04199244044064180c0c0b0858034070141d65102c0b9010000c1010402401443e1104d600301200c0a1800b00c001c42e4145280d0b5001900c10164041640217050081c4030340c1c0c0294010a0003404038050b40031028291210310b1075054015803914421000c1041c010080d40d541a5041140c2c5071040f14100e01c04e10381c58110102004814594200380000f1400940d6034486401400b4146141c0d2034408000741c408102010080107208080040000061100c503c0302c3c401c2d6444000382c00c00101d03d0f62038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 231928282 1250 231927032 231927049
    0x90d050702120a080a03050105010c050a150f0204090207020a061d0904170a0806031b0303030a05100519030c0e0c032404180b09160e090a020409030e3c 67
    0x40b421600400c1c03802c034103209034000148072007500e030b407410700c440d0366a44011210358030050009032980c1c0016400f0000030307145040b8800300b2040e081c00030030000104007004c1708980c0998040c10025600003400021420801038420041000e030415841d015003800c441c2034074900d9040c00c01d21656030100014100409061085151340c18080802d4071005682c001410220007514042e202e8455946451003c210004035811035400c040d01860854542c0c03018000540405000c03210313035041128002c100340d128000d091200c00c0d5080d100115191031804c0138040215a074020801300c151080c03c0101042c0312000300c9400840358030b14618541c0d00f010200007886d882d0b5160325480b0b030421411900746104558140c40c4180242c00c420a552500d800c0f059660304005060300300d00355401c00402c62519000e8406e80d001845000355403014280d0b0b030000e021201c40c2c05d402c4021490986019410341030903c1550448520001c6007040c0414038120b4078089694601030944043e060440c104c0161148050b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 231929532 1250 231928282 231928309
    0x220f110904050a0212012d031506240c1109040302030304060e0604030e2205091509010b031c02070e010e010608161e050702151215150307030207150501050315090d050702 75
    0x24041c140079140d281240820f64010303000302e082d034104400800c0104a00d2008001544100d8bc0601d418601c043d0030345035082c070840c05403545120011520300303e4a80c1c003050351141d4440d038041c66483c6414604281222425403008805900c200d00308400282c0140c402064000300b210a00801c10101805d400f070003240b8603000d030300c1908240a005c5894400103070f20105200d5003840803140d90311280024220307070303680c0d207019410790041c050742c840185040c035580c1c2040381510644030501d48610400514880a80c00840111b036540010050300380c1c40020240c20510030340c8040c540b8205001c0080400300c3e030701218003071000c0701d01501039a00d00800448109a41c050070390a00c03c2c0035081c00c00c920307270001100d00c0e040c03000800026103445098100e80c903603404000c110125a030146d04011503141c10042c860400c0c9036080116001242c10050031240740387c6c1e02c4101103425070400040c1410940300c1020b141040003010140840040c01007281c3c074803018035280a68032482d01e400000e829845120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 231930782 1250 231929532 231929609
    0x40e090c0409060608121e0309070803130306060611070312030b27011205030f07020418231b04050405010b0a0e010501080f06220f110904050a021201 66
    0xb0b050020400a50004000c0311910002d840e039070007010315056040d110b5045d4148280c50b2020a05181c0381e01c0d403010719040007001040355800c1c0d03103894903585983e0045100554161400000b081000924010320010340210700d401485203610300e090581d2150a0f00000b005103024090281d80280b10f41d02620100c84000c1141e5201d244000d41206c42c4051040201115040c2c00c001041c049101d054500405901000540c07a10016103450040c07504101c008070307881a00c0c1d06e504070390201490b222140f201e001c1c44c0040901c10810451190485044a11042c1500700b140204848101792010580003503040d1000300f0b03195581d02d010742c01000100300d200c0e44064144004a4824400e030300b00d9050324020f0300c2c0d00f0200c8c0c82c0c5500464119504803112507101c2c42ca54090110045141003000c050030032000045803000700b0501a4090342c3c04614240c0070760741c01054802842c0f80070f010385900507000f507608620f404803000c000310803200e0500030788144c492440c801154545000321110785c1480b4030b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 231932032 1250 231930782 231930791
    0x809120a05031608010506040b0706060302060309010c090603050618060a030203070602100e0a02060904021612110613050a030516051b1815040b033310060203040e090c04 75
    0x219001c0c00c1d94005480c1c42540b1010800341c5950385008521050588800800c4c0a0805160051548060340440c004444c0b072502d80c0000001622400042c40c000d100540022564002c81c02009150005590003001014100014040300d51280c0491000200252000c140746070358003000f14074909101d40c402501481940c0c00081c0b5a613003c2000b01c6070208241d01442313084100010b16550f080021400ba61044040103101490b150a9004041400070360b80300d202e07000d80710303100d074650781248584000101c0c80d941079482c1390b001d0a0003076035841204a032040c01d15500d1a150f2310780c1c8024096009092100c005541e407100c05c907240e030401031540d1200c121100000c1c01442d00900c0340c0c220005a00400695210312880c402c3c080219205001c1c030200411034240c2d403010480604051480c0325014003601c8080b64400d900d0240920000c505960030362805541414000e90f07450f00106400b20240400c0b1007031140329408030480d000c603400401d205503591921050071342444600c0581aa00134980b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 231933282 1250 231932032 231932047
    0xb041805030a11030a080f060118060801150503010e040602310608061f030b0a0e1f080307080301030b07030e0d020c1212070213020f030a140a020f0901080912 70
    0x10051030b81e4959035a4245100344203900441d540c3c01241e444001040708240003e0714880c000c4107103a0300040524240b48045a20245c605194409800c1040001c0f04c1000501038000000e8001070343d00c689240c078919561514150500707807940508010b08494001540307a4806189045143c014448265000701ea1136062841d0720505070b00d80b0801011030b0050740010180c0c600790492400c080c042c00c80518000070340c090304400800b5070b90501548540440710204015251400c440c0c8030341105c0741800e00c00102c1088400c019600741d0300c07610b1203030f100f0400b110010327003100709490460360b000d144040e40e900e8421040c0d000c0c114000c4a00c038184034552072003401943c0001da000c190740b0181d40a100c0b2550b4881c841d5114142c661245200c1e40c0b0030400d14005090440d07141c0360703019515400504142070303203000011560054908100d5186c03103d58501c4400018203080d80c101c1d1041c2c030704510b0241c4040504909020382001c05040c40f44140002c0c83e000700030701010288079980603c1942e40c1e00c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 231934532 1250 231933282 231933293
    0x1050405120307050702120708030a020313140a14010306090c0c02010e0621090a0804060206010906080d080a050603070b031f08060705160302030c06070306030203060609190b0418 79
    0x1046400303680c18071a020510041c0110349080b82d000c0d48050741c90510b010300075002d200c5040c95a02003030314240318001d0001842c00d01840608003002c902d0340515503036803000615105c02c0754260041c5440292400b624101943c031034001c48101c41c441081c041846105038016401081d00c4da120000003824100d5514002e0741c001c0415203c28400d0301c84490701160002402894051030550708202d414a01068050b0401101c2d0070741d1081000341201c00d8000302e030b90b44000c150401d03404440503a0100c80140240036a50040002408030b07000103100342820030000505401000e8003c1c59015030b00c4010039a640c0b4140301e03482c042d21040340240d640c0e041850210403003030084001444407080c0c00c075011039101c40c08074949008128981d109401d0048681c564264032200036070803400c0d1312080200c3e03507100c0010b0241d02d00c00c0d50580c80000c2e00d41c0c1fa50040c107043c954002c180300e100b10205410405c20740d0481160b83e400381c55125001030071013004404a401090045441214000c9a042907804c108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 231935782 1250 231934532 231934541
    0x3020910171302030c0103090203120a08060102212b0908031504060b030c090604030609080301090e1c0f0c02060714160b090108040309120c150216140102070506040801 74
    0x1c00984403110903a11184806803040705050000d5254110350002070044d031094001041aa0000303041c0c0b12849070099001c6880e030b122400c49004100c009081007041d6070144840202d582c9034a0000c84a810101b10a4105100c0c400884840c07020070b984242c517580290748900d6a0604000c404c001d255540e0401d44c0c00d0780c2007200d40016034500c04449000509141c0202c1c4219151688084d086443d0004210081d03040031400b142c110000b808000b021a00e680a003000d50360103664030710356035414100000299002c0d6041442a0360219110705c03d001c0c0f54800c250008492490450340f41c41040000b00c0d00e162314804081e41c400c8001c504c007000d01402c4c0c541d8002682d03480017180d502e00302600c0340c2e5100f03005600c50452003103014031003103081e540611a61a48203119183c60901c194803030954800309803c5003000c0d04c403510b58010502c100c5503a10702c848072055103030000308901c0c66411108000f203c42406400417031100c2e030070014041d03402082400080d1100500442e203c3d91558201b900030b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 231937032 1250 231935782 231935807
    0xf170c0105040605060909030a020a0b150904200a05010f08060111070801151d13020609100206070f0801080a0201030e070e07050d0b0103020403080415020f01020d02040501080603151603020910 85
    0x4c81410007c140380041c00021503802c0711f1103401400700c940b0340d44c50314030b40004001c05141c0751508011b01005503644007141a4400c5114151080400324036803071031790348111141240c40c05410007040c00c5c09560781000c00c03102d07101c0551030040d00c02d59507000120b4002c0d00b550580449440380101c0403032544070641084804803508408281c0d12950b03502e00040340184070550054140340c081c08541c0d1111625035040031a400680003074584841c62010860904012914100681048080c0581c0a91043d022503280383c052508100e01d504003554651034200c00040241416592465541c00e000140503d000401240c03250444600d000400a40140c1c454100d00d200507141103010b0170290b02034400e40b002e40b50040c0c482c0f407c142c1840741c02074545104180c0c205c01e500c1607a0349400540000d00040081d035915a9000d0f03115450000094540f81005d084e29100c0d4000e054464820300041012641c8007040145039070341d450980304141d00070302c104495140c003c907240010340c2d40c807900088991441d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 231938282 1250 231937032 231937039
    0x130204020c0a110402121909081201031b0302031c09120305041502030316050a0507020904210201020906070f0201090f0807030c05060307021c18030605010302120a0f170c010504060506 81
    0x43c0007010342040102d00c106003966005003c09400b246c6411811100394646c010355000c000340c0000d0948400c00242c02aa41e83e50204100d00014000c1109a049245074487d102403851200c0781945c0c0001d480b4011134845004074107544842810461040b01e0000003010030400ba44088281818010a59400381c000d807180d20000c0c20031030343c0c010300c00404c40c1e1150002c281c8501540e11780301c1046a480d40050011410050b0502401004d80c1d00c00001a000d503110700c10140c030000d00c03801210188690703c1160340540e4818440d90410307403a2807003114291903108014500d124501d10040c1d07070301486034001c4001e41c4141d20004ca00300b00002202c0e4282c030700400c0d802e0702c1159604104003051000311041c0c80182c0200301c0801c281c110542207141c082a45082075410001411088861040250b20584020307403a98010800c0d810b100381088d01010b0759201400803064075849100000f600013800410384001400c42001030401c3d1010f0790b440c166008000e0100d402c180c14550090081540d50520 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 231939532 1250 231938282 231938303
    0x4020d1b0206070c1a060d0b100302030d170105131d0309091b0720030118060b0a1a030408040302060a02010f0c0504050a061202070219080c011d0405130204020c0a 72
    0x7900580c1c031034203401c5d40305442c09040030119140b03582003100030f020342e03030000320401c1c0c0c13103001500070340101d4490b82072201038100451450041615250b26944d0345802e0061a60441e070145805085e81810748005a03104a01c0100d981c403420001c020782c0603240407103030a84e613000580c460040300910020500702d4078290107403516012840c0c201c2d100c00320324000c0c0400b0403c0e0780c000b40b180b40f80c0d10402d002c04844580014000b8012a003540d041031b080300000c0c0404180082003102da8426003101031010f0f54121113050034660285000e20820003400801c5c00c000c0000750800c101141120055580580704a88030108260041d000e03040d54124100024105209891224890404e03102281c1005000c0c40000349001d0303065a01c44040b03060212440d8003000700c4405a15886854a85038132a00d031115440f900c0d200c02c80d402c00704294142ca0400011240c01702090394004c5802c9840d210032600002e8a8407458000415800e0f0038074001d42240c0045002116070341c001c0382004480b80203540ca4030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 231940782 1250 231939532 231939541
    0xf03120103150606050d0905010e0105090a03030e07060e010507080c0109030305090609120d091b0303020a05070b0a020a020f030a020a0801051501051903050915010806010f2403020904020d1b0206 86
    0x800d41d0b006000b0100068418040391b8085c4a141d007154000601a00001810300c0110b20400d00f0b4480c11a254030441d400044d8801c20103030f05d40315001403407644901400c09141010801044041d0703800c502c50401030040344a1062101c0c0d4400c540c4201d0024000308681c060a150190140104583c0d032411400781030f0000301082c802145d56003c0120004407189450410050b15005021202007030f03c0d241945e01d182c000010f041615440910300039001081c0f51402031800500c1c3c05a180c108a51060050144837002900091a0307105142e0442d20320482106160210386440443c80f0013075803000e803000700000c1c5100107500444c042d50010340000b8269120350b0055510b44a410a114100303403c0d126049815442a8032150f00b005081703081d5036021f101900c0082c5d10700b2080e00a6903840c0c02c40c1c0010030902c140000381900034144140e8031303012481503003950b071808140c402d01c010605030005118601d075550b581c115489048140c404000781620700761815034007000f1044481c050300c030307040108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 231942032 1250 231940782 231940823
    0x2100c0c060b220218060d021305011d0103020a03020d15210f12090812030718051e0301020c071701140609151804030c05210d0902030f03120103 64
    0x82e10f411180903982d880440400c10301c0402980420314041e0040940c46041c03145070349410081c200700c10b42d0403015846502e003005404e0807520300d600590511429046040303035800825400401084242070058442c02c1130f400030390107031144d4501c071080c3c9854000e014001e030445044060640b008590390121220100314029008041d2030783c007a0001c3e0700213240c5c0700040d80545112004170750901e4094840e60351140158681212101c524076510303404010000c2840d0301c00e071004074160792513001c4010030f8502000b180c951014140030b0248406421406c11860302c0940442d800040004101c61300303241d0700d900011002c40c200340058220b509110396501d40c803040e058003074040c6c40c000707040100c40e854600c242801039a14050a0703030402e60380703066910208075502800d840740c0d0080e250061005283d00d05541007001300b81e115600018170070320002107a0700340b0b01901c480303c46580700007a0180803800003134a05000c0d0100c0d08524440021034500c1e00e0a41190b05041b24410401d04850880c0c00421 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 231943282 1250 231942032 231942049
    0xc0b060a0e0f0f07020d050702060f070501090b01081b010c060c03150825050303160c030c0e0109050f040809120a0503041e080106060212090d051c14031005010c0302100c0c060b 78
    0xc6c000010000d10210003d45442001440049403210304207240003901c0d40e400d401d60345180c0f000e40d04200031400400075801c00740603642c0d401311944d2140c80008000ba00207044101d00c0003020701910359400380e0f034141d41e0195201d40c00c1100030490300c4034003036502c050455661070320810300b04080c1c0a005101c0b4030600d0700716483e010345800502850600c03629401c0750200f0b107600310046c1c030030203c1c41c403001000c55529019500504002446990158145003104056070b40180241005000880811020503a2807040c0c940c500d004035030307400380380b54038092003450f04407800320280607400001000948e51340754040604105103640001d020041d03a07070910608890740c500c100307009604030381c1c40c4040c0889800b00810710035500400b9049105000c1d107030ba40ca000c2420840130001405094103022403500090301c803e030007064480040c03a52905184952007142030b481260b05100c019001c0304100340c02480035035281c10030380b0020002c0c804d10010017025401000300655006142044015140c18103100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 231944532 1250 231943282 231943303
    0x16020c0306040b010611070e0a090b070806010c1b0b0c0a0203070611060106120912030b04050a11040b0d020702031c0f030e0d1404051008010504050f070c0b060a0e0f0f0702 76
    0x100f840182c0c40d00c5d8080d541c80250f81104200c901498001180c94540303a0b6480703000b007035140c0c0005a20301c01484c048070001d001070410410712041300b08000c926a03001c10007170340040d4020483e402c19148406a100352448613009903402c85170109a00108007030016107040700d0342c02101124111541e404041e5210600d40082184a030003410041c00224000c0007c17440c889104080011400d6143c0c035810307510082040d803000060b4459149142c42d00c4e2a0066a0704111140010010b40304c2d5401410703a1442a4481c18000d000f020442c1011803d0642c180c42d00700d9005400d5603440c100c406608800a411070705943c01150158400001180c400c0c411500d01c032030745034000c02e0300b00c11520341070b03c005c00e40204850a2003000c001c00f148907216451122009600c540720001d182d410407041000b9243c00500040884c041401008402a48107415130032041e001040e600250715500049a0b20400982120b103050185105100906001042c80f51060aa0403860b500d55280c01d8003c03030300c3e10080302 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 231945782 1250 231944532 231944543
    0x13090519020a0c0218040303050106020c0319110a080307060e011505120c040c0f030f090b01060c08070b0f0103290c090a0f14010909150b03040f02030616020c030604 73
    0x4040040e49400c1d80107005030011420501004032566000903901844592801e528103051002d0008040d003501415000d810940041e207003800c101c1010070350310003501400c1003420780c40220074014059500b9042c00c201001800b04140d003034a8012180c3e43c0c2d8810b041c00c0b190303e85440c1c0d40d01c0b98080103202e4103062082041408804503d000e007040201c0340440d40c0321109005448034004940d07544d01c9906488a1705841e83d11644030030540240840d04100f00003121369040007603420000b400240481c0c156086410b19502a420034102031081c0d024410300100900004010f02000303240c110b0b50307107049902c2003100c09410000c08401e020b805103045a480d21007042030307010401d03110800015080c494400b5100004465440101c2e10b85400242d10500f0548816010700e10903503404441e20019100042007481104600c051034540ca0100f80f2a04c0d03450000400450308002205405040040d0000c1c00c035041d40c1854841e070361030743d24512a100007601c113100c0c0c445510308000c0340e810b1140d43c012 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 231947032 1250 231945782 231945811
    0x22502010507020f030312040606050f030c0607030f02031605160611060c0f0d050a0902031c020303070e01110a062c03030105060c071502031908090a150609060902130905 75
    0x10350a0010006900d02e130320307a03d8003050015880d00310000031040d01c2540190000306d00d042c540402d00100c1d49600b03440764080d4201c0222202140c0b0fa14045422072036042c60100500121840c08078290b00800c210261280d0207407118a050003000101c3c40703008030000701c0d580e80c890354400b401c1d1451000c0509088135604410700049002000c83e000d4010410341032800c900c1c0803d45e6018000312607084800c00e203803139517800d080001d40c01c017007004000c456591a100400c6070300030300d0003a6990100038130700710130085894080d0100d81d11590560b440c0403441c9045400d000c1d058503001c0058072618901c0701103481500700f4000c05070081c0c1d0714001040625000b662071642844148071803a40038140700d54231403050f140c000801003825a42e4003020016540610740b2181c250b5031032190420192500402c0243c454103102c200e800100705400b001e070b400030884400500e4020400041c004991140748698a40305002a000d15550010420803401102003062643c40c2c0c007402049031415200a461038101c0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 231948282 1250 231947032 231947047
    0x6040c021504021c0606090e010203040503030109090f020604030b0601111609050a0b1009030501050c07020f0906130204120c050307120213020702040c17060306070f05070809090702010225020105 86
    0x119101d15400900141c4881c142031468101c844800d440090100c0e0070f5981d03440200551400d9108800c18642010003c0d440c60070143c0b01d641d500c2c0018020ba4450070359030040035080041400780e41d020a503001d481c113a266a6281000d4144400c12119140860f4051101002c054408101c401060710703040e901104040c14240828000c0c400144003040b1203907254840040f9030390b034094103168103025550b052080344c158030307040342903a43c041c100e8000540d0500c0b4034401651000700720f20940005482e00c4009a072441d0009102c405401c140c4001c00c2e200081c042150040308001406107409a007515800c0c1d96550141940c0e02d4042c402d800302c00141e401c01e1001441d0802c80e010056400d400094209903d40d000202100c000e20f40101c0454004640b00507141080f80d03030703981e10401c210082c0081e441c00b40f5026081c04840342c030607003c110b80005c1c10760400c000138054a603002e001501070382c81440e0400001c0d00070340c0000c0d06a0340346054075810744a0003414206210500e40d041c2d40d074504207881c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 231949532 1250 231948282 231948313
    0x20a0b0c09060409060b03041a09100207030201020d15151106060103090f0b010801050f13030e152505012405040c0c05100b0a06021b06070512190806040c02 69
    0x10454180d8070010401c00058165005c0c0580c0000d002581d1486640f030800e0700d4041300000d480900c480c8029410406c20040d0103001c2107409214044240150b0380e5222454124028407507044c0105800e807411060101c3d84851506903070554081120740c0072078888180041d900c503100748000c80c01d6a400b0b078000510702d52013600025101c0f03220320389c0e05144c64450342c1c40917103460098011a0507a9074641c01c021030b5514038201581c000140d03020400d882c09060728020030304072420015601424681440c549a03410501c04c403915400404044044208844941a101c0700d8028003075030702e17600f8500001010380e0b041200740d03000d0b0f468401380d4058030b1900c030610000e806003250071000e104242c02070704040707402403041d1000d68003640b02c0080c1d01c0c00c0c0c00042020341c1340c1940011003190b2090981303134402e840c150307030760b895000003250b500351a0b07211494010301d82141802000c054540c013284007441880d00f070500c00011003c64465943c241d860030140070881d0b0003002c425006030b0103504501d10820 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 231950782 1250 231949532 231949537
    0x10e0601181e050d140d0903020102030a080415060305061801020c0a1103100c02060907090608120c030d140a060e0c1204260901180e0103140a020301050a0902010f020a0b0c 76
    0x850b0702c2c0811801594070000070b405041d8103d419078084180030541071044c030f002c2c0000300c1e042d010703418007004260031500000d6590091400070014411020082400d0101340d0042c0c4192041c401803d0007a69128541f0304c1c2c6924054614080d0050f205403c45e102e0303007060080e41c1103054040003c1034451003503124142c01c48103040b5056014024080056a1842c0c0c0780146940f280554004240b2800d0114034030f0300d444c4190f44803144581c5040030601044c140440d000381c0c000d8034203d095031641c402d010301c10f0a500c201905441e10a16100902c2804a10b07268220312031440b4283c1000309965075009002626012600340c10041002c100e20300041680600042c0c10034081c0c10111000c10092492000c3d9a02d00d0f000c000b40d41201089103400c640e44220315222500d032404e9503203200791500070040307015a01030000910980149405240f5010204004070013540c00a00034802824000c5a500040c03080060983c0003443c21110402c11f06d000162030b800c00b0340e00c80103840c2c2e956100c0f0409103007038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 231952032 1250 231950782 231950819
    0x81207050f030703140601080106050a200610230a0501201209030f011e0207032a0b010e040f0b070314090609010b100504091806020c0105010e060118 66
    0xe05008140408103108055032050007142c80000e030100c510282c07548414402021141000442801403021682c0403003a00c0c441c981904101c80942c0c201610740200001d0300091140c00e1007250b081003510340c2c85041c29821681c1c0d41400c00c0c080a145400f6041110105c043c054001031a0401040194441e0f100041400414401c1a0000482c61a0b90b42443e41d50a14426181008258810189020b1058502d2039070401c000f001b9907070b004404882c10112450b5640c1e01c280e03010841100385802000e0128400c80700502c0f2070404a651040c203c12229001015201d80e10620300108500b400000720342d0099030046081c000c08541a590f0341804900104404100340e02d69845c0075800d80d02500d914040d451030805002c142c0b6201851900310b44c1240800ca00c00d20054540f84c101641142c200d40a0350f594403030200d83c41801c120301902104d80900006d250900c00100200d5840c019403169040c1c407084003480040d0b44a80340115495541002800d1004c3c0b00f2000401040442081c140d110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 231953282 1250 231952032 231952037
    0xf0a150b03190f020c01050702010c020307021e061207020f0706030b01081801060902071a09120f0c031e0711060a0909020d0b1f09050a03030801031112030c010902090f04081207 78
    0x41c03000f4503120380c16600300280d4003640d0703912079052110a279028060092101c50302c1c401942040015000140c5030741d01913040500c400302c00c0514181c00d40700e204c120f0766500c2031740040e84030a08290a00a59844440c0c140c09203602482201169403442030203402a5148141c1d030b18503184e229000d81001d0403050120f1286190340c0d5a4000031031051300e0014000301400784a11280500b4443c004800310301009200380000d810a00d298242d100150003074031020701d014003d00784c55070441034001d440c40c85469108a0107483c11204ad032416032681c002001c903d44141d101d502c450042000b4801140118800c1c3c001048420b1018850900142c6c081d1681c0303524071a004c100200c3c04004242c6404000c00c0401244101300d1400226503080840d843c010002501c4014503d455520010300d4440103000c0103001c0c1607402e20342451a07450a00316240383d034030401569642d00803000c40d24020314246504902404c500740009480b91100c840d801e02c280e801c02070a5107094510040c9040500d8014811000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 231954532 1250 231953282 231953291
    0x2404080a1b060c0302070309241b020d0f0501140c0315030a060507170705071109060415060216050d020a0b0c10140a0f0b1e030c090f0a150b0319 64
    0x4242e1500422544a241d920016680d0002c0d007001003031404e041e080300d44003500051001030080c01c0c82c070025200b40d0013490f000080c604204045204480d500401079800a81c0203c5e060a2252103400a88000d12030402044648484400c3d2042000c0c11a80c19500e0f0606200003014079029141c075a0082d00d009059552110060340d1740d80403160140c0f031450009000c076244005801c581c410554000300309090441c1400c2099444458001d103c100150007240c100002ca5801d03111a000035a40440a51703145603140d0b2a1900250342c7d8003100c1140c50402c10300b0100054604024607816811178018008200071402c0102100311a48920803401c903a1140c2c03900840303000350380d100d074a50318100c0c008414007e0500c404101e003903e07019010315410304d103010301c2007190741d07280c0c90a1002c0202c2000111142e9640100180c2014104080766400803409403c0003115540354403414881e50f4015401c00000a803030b001d16403c0744076070142100e0301e035040001c200c00140288003541542c03045100404c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 231955782 1250 231954532 231954587
    0x61207030b07030204170705030706020303040c1e03021c030f09080307080a1b050c090c18100908030a0519050906071103010209060c0c040b0f0a0608060d0c03052404080a 75
    0x4121154286c40c80303c03600328020a010a00d814000e42004200c507100071030940c103049d11142d2411800d0f1051145421a41c0c9211002e643d00110704030040d44c0007041d0806c2c130002c0d400d00c400760030800039044002542d09415158154021071502e003e41d88200000d606140c00c43d9113040c490351000507101c050050614038102107024803a4400e8550384544090901c20f1003c4090004588016048800200040c000c80781c5aa0f4584031481980d501164000b40c1c1a08080041da011407840d0001d60160000080386481190004000e04000400c0d919465002000e41d10894003401001c0729168410001c01588001c00e20540a00784051001000180f40840e000e0000340e895001c081101240e80208840050f10f00c2c06115030703001d804017030b51001030036200c1d1000180307142c05030300540050080c040c01181c407541360118a000443d502c0909002029180d041440e941d108203400030b54048404051881c09820010105020382d0740154094181095000291500c02c00b20400340c90b01c8034100e0f2106c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 231957032 1250 231955782 231955799
    0xf080706050414070902041a090114161401090809210a21080714070312020408030301170a1509140106090609180c0302040b19090c08061207030b07030204 68
    0x7030300907440b45105280c0c4081040341541042015031240c010349105000400c20b0000342c000c90045044417203c01c541d212840c40041e60403900314400c0d1464071002054100c80714110000d4086103d006690492400c0000d01046007642c0a100004065070000d1000d280903080131511207046044202e000d0f400b8044806d0054901409500190741071031030307400c46418150044603000301340e02c041d14100c8514a40844040c02d0850b40390110100040006070200524ac450700b480e400c3c4a0104400b55611659804400d950350002e000d2818030640051640c5000d540000e007556555610550160b562510900c200713005141ca00402e0740e03c85684030990320b03110028030980000d0505100002075182c03c050303208045550500f1410888400000f00101003007644101000306ca130b045501043c005a8980401c1c41c0c0703007059240102000d031605000c1a0350480d40c12031091580e181e55174400300e617031b1a410000c140f0121150004c240e0001d00040c80450104681e5503880021424050f1410303640d081c02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 231958282 1250 231957032 231957041
    0x2190518030f073609020a050906090105060d02040f080a060b091b0310150f0e01020d0c06050606091e010e040612170c070801090209090109050d03090c32060f04030f080706 76
    0x13202544c4203202401c514003000008007820060b00c0c940c64034500140030441c00007060090034850100400d07104000700c0b403601180c002d800e070340c0104205039035580500703655500c0c00364046410700c2c01c00344e450801e814070b102c0e1903210702c40840900803d010760f0500c2e06203940c80500451141801298041142e6042442c00400070070b0a940328001c20105000040c40c254071010887d0454020100c0c9004541d0b01406a5a41c03581203000021076440d500700240c028031480710b525400000c01c21450b0f01c140c41c84007c05982a40a80b0b40c1c1c45004165410801100c145024202960f026010304201080f813550413040340000e105501450144c44100503840c2100980c4190a00da4450001030708500741004800c0c3c100340d07440001d00001742d80b07a40d0b140c0c8850842d00c4003010195100004000c1c400e0140c03640004003214046015460303407800f4442222000910800000851a04290303a40c4c20504200c07801010710b120854100b90840d0364080c520206040251480c01003800b040d80455013a128 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 231959532 1250 231958282 231958379
    0x80c2502090c070b010e06130b03070302090408040617010f21060501080a051005160807020c1f02010507020a0305091e060a080708070810060c03020102190518030f07 73
    0x142ca854543d68544868540016000721206030f00346414005581c66161500703070810138082d000304078000300380080ba2400e2401d0f4806517200c030070070080c082070118034001401a0340984d540c102d00780c00d44144c5901100d40078402c0c50444a40c00d5010010007046001280b500e21001121901144040e2120400c0e21030a81215a02c1e03000328200200300710b0300f081076a000d084894001d1005150044404258505441240c028003000a00251240d442480580d034000f400422000000760040040180c4141d45244035000d5860030010070485400080d000384400d6065851b146407411a90078800401940306040e6840c91404124440f59602d40f40507000003c126a50803581e0300c0d00100c0201200802342c188018003068405003c8a030b212017201d002a5422403c01402604691030124024880e805c0c0d46158465030308190203070158003000600000c0e0304295804a50794800042644400c0242d00150007a480760324100056000c2d2214020306000904121503408200c8a80e91242c201c01c92 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 231960782 1250 231959532 231959551
    0xc15140405030405040c0c020a0509041a0c12071e050d09020301060803180613031707060903020703020a050a0f0905090c03030328091109090712051606080c250209 72
    0x401384a2810544900300b800e52061038040c80c80c200940105030041e000303014941c007030b1504200007028080003045a9243c4102800c0c006440c5c80d2441403810140c0090f0360400c07807103403418003040d45a8410f201411403103550460101110f0341c038001c2a1682c0e4410ad1410860311f40392001c0704050b0b40c0c284505001084648050341e692201016016a00c500c0100403512804051180303155800c007685910040d0b0307501c0b4200d5415003080c40c000034124010158000d00b954105a80303c01050f0340440c040003128800c1d214050103030b486404105041583e4010010456000e00f42040140020740003150091424019100e6011644003c00c0c06e5074411070705094080c0b55082c0440130514460405d008407014494204040400c0d40d550500040204032034503c01c40b6800c01091041d00103001070030092105000342c1c1055080351a2454540309414a800580c54904000146a5000b150b115100d0382001d210f01d854079031080c032840f081880c00004041242114003101c0016207401e900c080c05141d200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 231962032 1250 231960782 231960787
    0x106120f1805030d1d120c0a020d1401050f150d02120a140c010203160813080601060f080f010e130c0f12060c0e0604090b0607060c030504030207060c030c1514040503 73
    0x2203007200944102140304008000b52600e172819804001c2103171707441a03d500078015500c0001001c218540600490080e6001407a42c0041042000b8404542d14003651000207106a949054051009070300880f0801c01010908048041c00d10304901120710b207520082c02ca00d07801030030001c40c0c0d01c0d00994480403500041ea802c58070907601e40401074035210702000d100640c90003c40c8500f000203182c00d558010503103400030a616036600d0911300c1c00805405440100c5a8a60b501c0c0002007000030001c80d0840440c00b080c0208030001c8015650740d0580b45200d0b021680c58846c1d0075880c908642c0d50405641072004d0324000324659561844020007451000c2039060b0300140b9017021800c41e0301d840e0f040018010341d00108601a145d80e01554101c41d03c5030000200c11030f100010403214840c0100081510345030140c3c1d8032210350036500940c0118002da080340c4441b610340b401514800f2200c24080c02040032604108001101c50b0035240d1f113410010b50106400318019655501d080f410368040758a038101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 231963282 1250 231962032 231962047
    0x5091c1502030f010e010f140d05121c02090a050f0d05010f0b101d060c03040801050a06090b091b130312021c0e060d02070309030f030503060306060103050106120f180503 75
    0x3c64140b405800c1d511070446865251021402401c0000d00c603182d00c1e0800c4401c840415a40e0b131070b0240589400500b81c90016100d076118201a50080020504030040340181c190030690314800d40d02e1181002d4030000c1d8490501e0200403007640c0300d078400c035408401281c500f00060021700800c400da402d40000820600307040e42c100141c600c3c1d1071941008100800303a44d0360070380c0c02002c1100c054102c20b031102c0c0d42e102c580c0d02c801c0d8298856030300580c65660901c17040c0405515103510810440f84d03068403c02009407100d0400a8010080e601c03c80241180d200b40c81c0e00b842c41c00000e15050910000c80c07401c1d40e17502c1c3d0b13130a88514103214031540540c10801c085612414400d500105140162030695902501180020b0080c019071b4080352a0ba42d000c41c40038205401260f414015580040c9420712003182d03481c00821550085070321710b0290003034001064075540240655410390f40c4d9074444501c900208803040d00284104201d6504454817004d0310710707081243c0308400c00c54600502c0555500e164 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 231964532 1250 231963282 231963301
    0x16051209160b070c0e040305030f1008010207051c0f05030106030b0607060c0519030c09030b040516080a060608212206020c010201060503151303050d110405030c0a030305091c150203 80
    0xc50317904c03400c01659031804220010341e004c01100c0e40b14120240c984030940b200880b03191410f1440d00841ca181d840000c40ba8240f02c0c0c000f4401100602e004000b17000d00c1c0450004031241060030a2a001107503040c00180f29960003504031040d002e20260540307051080c81d881300b80039034018250703070004100c0010300ca1562203048600c541c088015130409010584469030010040d480d00d20000d400006108007243c01c10009000b50100340c08a02c2c803403c052a20340ca190b42d10358504940c11100949405800070312028040b550075030040d501220b03205640f8090074450100c2d030041030540d0800c00c00120b010b5503058240f032100c0c0602003035401080c2d850302035400a0308540f200e0b0040c3d813081c2d20440212051141c0440d00310340c0700000c0c01c42102010294a8107a0b0765000e050018881541000c034040f80044070a009407045074130850440384490401000e00000c0d18090001a00203001040311441c682440413501d0000107808803401403a030119207450240342e00400d02d8584458000041c80003204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 231965782 1250 231964532 231964553
    0x60f08010f061401030b060d1407080f01080d05070201020f0709050105040b0303030c0405010c140109030206040b0a14061009050406090207140f03030f060a050613030b16051209160b07 81
    0x314041010400d8900700305030f000401d00c2c8014568101610380d024180544c40700e006640e103240305984140a050070b049501c1c0c3d0901001c82d640e41c00140e290300007883d54104030380c00c60b0403940072a0280400340d2045408a484c0d0740103e0090341544622401d2884c19030f0101300803c003e145140340046d69504000c1000190340c00c1900e400c1c441d03402402030041c0340202004507021a03c003428060200441781c640502c920a1032484070003d0f51800c85110240342d000304080344942e104041d11680340d540d07101c0c0101141d0306200c03201c0388003540700d0009007241460105071740e04070184e003080c6541ca651280010203980907a0008542c0d182c000c0742580401c000030340c1d020030001d20780018005041c04820b02c03958901004142405078600100440d2554542600e1100501006001c4907a1040c00e80703c0c4042e48219840300312021a903400000d240421696000001c1010543c0c1e1540742042e02400a120940c0c040e00c01030150140060032840f20481c004c5e068014103101011680f19040c0303041406610 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 231967032 1250 231965782 231965801
    0x1c021810080109030e06031003020303030112031407051e0106180609060e041a15060304050309030c01080c040302040905010609020a090602010f1e090f080c07050301060510090315090204060f0801 86
    0x2a0b041000d03050010b9080095445c0341003050700c00740d45990381ea00e185d41d0b250520b544041d40500000002003490308441500700e80d440d00039182c0b81021401e4101000b04d5210b9002d01508a400906074071140c40701042c0320760b104503a8400007081d22501c942c0c514400109986000e505e076035440004005e8410782d801182d0041024019190701403505450307482c0a208812040c400d000c80710030000c2c80300b441c581844010844080c0001d5224606440d01c13513580d034010403c0d07511030710408070759070010740c0304401d20b51040d2841602e603400c0924507403c1c8409018010400c840654882c0c3c40401c40303142c039102a10f0380c0442356843d200b195140050181c01c44902c0b26000c2c040c0c0c0e060142c0303c001000c101411007414140071000152001142c24a604401c180050042202100140e20030480304c000500c44140c4104034002c002060b51034082101000703250301c20001080b0790342410004680100c510380b01c1404000c2c40402e0011082c2d0014040307602c3c582203506003900c01c282c24170901e0800d200c1c400c1c0c030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 231968282 1250 231967032 231967049
    0x9060d052508073503070b043020010209190e0705040501091a0c060117010609051323060109090605070219060f0b041107170f091c021810 61
    0x89100420000005201e055204940341c0011340200181da0720400448422540002e002506401c062410704002c903414411100890b100f5170201ca5616904441c180483d030103074596000a94200d0018040000c0081042400355428008a91951101d043c201c8044800303241807814907041c83c50710100790b40090301c440d003044000e00090189907003148075a03050364400c00800000101c9a101486070348552111007400e4001c10000007143c0c4c0a80c145440c103810b1080080c8103480d140d00400084036800c41c0c0c21a480d041000c8000003161080c0404a1039686403803241d16419010001240361900c2a404034070640d544c2e5400105006a601c121a00400e031440600516105d429540c1c0440a61480143c11266240000c0750203030038590003841e0b81c0c18050b009004080a450b400409a0420442950b503c0151500442080b04043c1116502a0840318803810500e400c0140001d55240d003105840481003a0100340142e5929a007004014a0a2000d030580349060128010200006d5008460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 231969532 1250 231968282 231968309
    0x160e090d09031b150309150b0607150204050907020f010b090f040303270f02041b0503180705040f050601020106060f14130f0b030f0c040509060d05250807 68
    0x32080d501915140850750090451000ea03008000350103d11010341c0c1c044910109810103c82000d50107402c850140c900421540001852944c180b1013525011688140e0210040000000041076200100000c4002c9940117003815150000726250035003d65540d005644042c2c242004003409010340c0c10698000d0302e518205040040080e50300c031b000644020305154603612541c882003609031480d00d0701030002004203100c2505003003048201d00310072416070203982481c0480b01c211a0102d092000105141e46591556440ba503205085a001ca58280c0c01030044040c00222079495000f40c3d138800c2840100041c050408a001a0071101d403640010144510a980d120703d058000c0310700c41c129880320700d140d951015800e020f500c050242d60807644000c2042c80011840411400c003942c4142c034008100c80e011340341d803410483c0740d0050388103581c0d100d0103403800514581001c00d0b40081c0f10340f060302258100f031500c40d800d030845074180e001c10420a886103070400102e0383c00c000d210010021a800e0380d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 231970782 1250 231969532 231969553
    0x230109020609100e03010c0f0311030106020d270b091002070b03061309051204150503041e02010329030c06090604120206130807050114090a060e040e160e09 69
    0x1d01c58024141c035188a24044400709206134000c1103241c40405004008100107004e000015000000c100c01503000a407034072403400d4040c07071a401281e040c1d0b02d032600140b108584c0000d0840c0d801c6000c45400c0c060188400314070f450482c007421400082c062100d24903450b820182d00b8020701c0280714814038110b500c410010001d203d190411a500084159044266024044151005400c0c80355005080d8440c600c0c0c4a103610824402038001d030341a05902d5090103280040480310341c081541d01610026605005c501650650780101c101d035071040c100460303001c2d081e809804649009180c81301c121007516000c5145480c041c0488458158200c40d41030074030421001090f20b038016400b030000084905071007030b015541c8401c26980c6c11203482401a00183d1614030503900c4004501c0b07144c0c00f00d608400c1c1e024458241000392107040364064148014607107002c00c00c42c0d40440040859402541d6010a607114410a02c8001c004402e88545129410316103a04600c50304d5000309003640c2ea4001c0040c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 231972032 1250 231970782 231970789
    0x40e090c0f19060e1c080a0906020a0b01092003100611011112042102070305070e0103120e040609060f330807021204080a02030601080105011a1809010323010902 71
    0x30020f442d000d1609052040c40381022650f80103070741c80c007007081c0c08200e42c81e1801c020f06003000b408414030507512001d0940c0d0f500010f0341d540d41c1c951002003851444500500854140707501c0080030980f1000082c1c40d1811982080c107556000b91102203a214804500b8009550028840e9a68000400080020182a0400c45503a01030003030307200c0076002031102050510503a401c1c000d40541105010b598408c0003100c01941c1c030640c9200031100d0f406031000004501d03d101040c13504803a04440304c43c08000c800130048401c4c2a529100c0f42d8001d42e500404070710a10284503060150a4401c038a844050402d40680181918034070b609030131202800c54800a006070030003d512703559290601411907203558405070708003a244902c548920b80085000034030703044000f074007002541c02a415101142d0326501c8a0382601c3c02400303800e440c03500881200c0403000081c00146000b04416070201503007200c450000302d80349420390043d1440c030403002c1c220204e19255103d44d10300f0038103840200070f04040ca6010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 231973282 1250 231972032 231972079
    0xb070e090736091109180f090c18040f0b0705040e0108070b0f0c12030a064118040303140a14010501031a04110c0f06090a08030606040e090c0f 63
    0x1002c1d999038032030140100c4e01c20181c0580c1c0325000028400c050300900e0040030709409400310b0784900300c040240040b50a40e100411060f40c2c40c4000750044c131600306c00804001403404050000c0b1200c1402030022004282c1c1030b0750050042080b03035581c40d07403180391400c4a4100380f01070f040800039400c94038040154001e5001103410380114405000e07204c5007010690741c14034408c10035001c03107904004100321104400c1d50110b0b0544081c402c1c20806000e016188400044689007401c0242200c0c8284000c520002524015501001040e22003545c50340b1003200041042900c00b03c6c08280c50f81c2d002c00e001e03c0f0714011682d00194014040107000c400c82d4807151161720600c00c0605060b41c0c2e0140202c00601c4a81114006001901c244001c9d00c20184240300d96004014a03400d9000f203141d45280d00c9404180c050144490323000500d50480c040c2c0f612107803684003804543d8814000c1000080c42c00c0300c0101c0a111384010310141030030ba5480401c1c4544540c0242c6428400c1e006241e8501c00d8540c030001c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 231974532 1250 231973282 231973289
    0x120c040f0e0c15041511010903020106060f0201140105041e090b040b06011b150906021903050c0c060103080901020a05070f061202030405150424151a070b070e090736 73
    0x22105c4028507600d020380782d91720129040e010550800d0fa8010515405400440840d60b035a0740d0051060b507080700880c220b40d840404100c014449000400c01450282c0003504580c4564500e00c00151080c0300300008c5450700d080446d40c2d010503100b0070007406004140c0a5120601b0b08140350803844050141010b28803a6600a010407901d0038250382111803a4010f06441754072410441d80c4281c030070944440040182c51160000b810a40040d19400d006002e8840c0c41d11914007c2010ba401c0d42c1d515100c90b0400c8964504500c01e442c02d2001081c0200004c078000d0903061020045c01c3e00b001e03001001d11802107040000180100b003400700107540040d000440071a0042c00d0f06e542d4a540c038043d24017001040103840843c07000c0610240e0b010007503020308140170400e08070901580d600e01c4c1000d1802000c5d00c4010f1042000d02040000c1400d00030210b501c00c50501e400c44500e0050343c00070f125242e041d81e220000441450300406000e400384a013882240c11030f40c110b03191104081f080c4a48115501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 231975782 1250 231974532 231974549
    0xb190e0708040309050a0603091403040f14060f120906060d030807030507020a12020c091f05060304030908061003050d0804110f030a051027020a0302120c040f0e0c1504 74
    0x2402c0c14401c000d1040039045c001c01d036040343c6903103e4004010b024800c8080d20b000d000a00c2503c02202e00000b29002c4403d251082107a0a18000d0002014000306040c20342003181007003906620f01e0b400005180d009000c180340441800c09421552070920010000c500410044071500d011a801142c0154041d40c03511300820f0690304d0740701c00ca050076002d600040c808071000e05d80030440e5070081400700e48864299180701642c2ea484452000c84204503090340300b50103809074107101c24288500115400340c080d040c00360b10182d8801050f1714005044a90300302000e40168184200103007030100c81e000070150318082c0301504090b110395000525155465118140b0b070160101991070600030089041d4200c0e082d030f8041d105a540c03441c080d040104980e0043c8641c1c0000e403083d0941d20303641a2800742c01410b0303040498255030a0042284100a05940c0d602c104c2c03200c01341d1640d03907026825091078440d2000c03a817040c0850071945400e407420f00320f511804002500b03a40190f00041036404842844 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 231977032 1250 231975782 231975797
    0x909010306090816080c010e0606130c090308040f03030305010b120f0601110105011202010206010e1005090712090302011a060a17150a0803040f091a04091707060b190e07 75
    0xd1820410500c00c40303201c140442d4204e80c0f014140b00b80c21015180380e01e2180d00034060011a400d100d034984608482c101c3c0c1c860310b15404160005402c0d406898010250b0a211503d84e441ea10303840050742007940280b42051441105208140d403500a850042000c0d4800c6810407250303c0c00782d10380060040004010400190010354203a12900c01661140341d0240204415610b60001d0340d95500400410382c09445000000100c5040e100c1156200301241c0320466001801e102c10001c50b503601038110400c200c4000c010060640280c03060018252082e000040c41c0c41c123240c0f403841d00302460700d4194440c020501407003424503046220340c980c0204031550a00c040e40c440f503d07188084503003444503401121510380452000800402030080d10751400c2c440c0101d55582c1e2094060340c100b07803400a00100f848030030f4005420b041e000201c002d44180510b001d4400d060fa01c5c01c0c11030300a00320944010742c48500d00c0c0e240c0d050504040450142040728400807904210603080e50010140c46402084840d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 231978282 1250 231977032 231977051
    0x5100c2039010c05012003090705010e01021506150307050307031d03040b032d09100204050114130801020313140c0603040f0f0203010c030c0e031b0111070e0a020a0210020909010306 80
    0x2944110b101350402000c006d0706400b00c00a14403190800c0354403400074031829802203410341c052907070f03000443c10580c000e03c1e0400c03801070440040c82c0003400b915003080300c0048132101039143c0f4024510450003562a69140c0c03918030001401d5648020b094528680d00340c170341002c0f020012086034159114000000e80d26110150700c03980e840400c4d81c0424000ba1441050f01c249110951800e004080304403c840c200c5080a100300700306e1043c0e21030380780803036261109040c01c941040060200c91594410b00c5010507943c03900c41f401c0e82e10495000c208801c0100c610000c1010780311400214251000092070b00e42c4c12600410ba207403001400141c001610341204504020709101140b802c41c1c1c3c050001e00c2440200900500a011724084081c00710700c0c04c024620709401c000404421707880c001440500701110803801034510080c4005202c520f03000c3c0e0340011500200c5030701c509000e140300c61001070341c52000341d50013420010758800c00c0070340ca401002000c04a0355030401c40d0341901d030021000511181c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 231979532 1250 231978282 231978293
    0x1b130b03030c070f05100912020405061f0807020d02010e121e0408030409060503010c090311040603060e0609150c040506130306051e07050705100c2039010c 69
    0x5002e040b00d40303510452401042a40010440100f1980280c0303250908100008050307031301c20098000c01810990407440c41c1c001d07140c0758211355002400031780072014200d40b0000c0d0140140080d504000072039100400c0c030140d04d90401c0707400c50301400d0348002c00072405811001c1c0d484205c20030304902c80c00b40100b10014a112020300351002c40d052004060b50b90b5603145801c0d0348075046482030101e5280341c11000285801e040c069501e0214240d80c40031010342c110358030050804403601b8196009030307403100b010000901d50b00c82c84019811104c01402c0ca8988000703414508804012880f112810700c1d000c0c00200034450741907406072941207445a13260041d40c000000d0421550784050616030510301031007080002c0c0c01c075031042404032072003100c0306540d041d000340d4070780c443c500c80107081d5807046480752a030300c0701a8802c1c4070080840ca409103115202424450041e041c0c80c1f554582a0010842e42140489210070710036030202c1042441031075000b615400c44100700076001107040c880c150001404104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 231980782 1250 231979532 231979537
    0x705090d0c09050601050702100c0809030106140324010308031e01060309051b0109061d060a110106080a0201120c0216060509010801051816050c030f0901021b130b0303 74
    0x405400d4040c629254149a000040c0d036220b441e1203245400045003e5500c40e50072101e8064001e41007100c910201c8404607014014207600b0303126080f081c4020040c43c1d83c00c0c041c146c000e004d20441c10684004100425081c40e202c00341c0f581868202e000344017110300047e480a411650000d12060b00c0e40d0340c2a032019174501c3d842c000d8082206d000300000c40e1050301741d880030403514000c800300c1d208d89071100c3c000c8001c2905103406034003141160008204962241045601d40445072100a07180d00c81d580200344a42c04c08044600480d4545019140e400024412080104400c00081083c140250006003040c0e104143c680722440c0c9400c1040300d4a4001c000341d06501d00e40c0c2e0446100607070303214401405a04103210f10790009903810000160703881c00094a040445011040809a4a6400700d0920701c4030b0303070520a0306212080c894040400b00038405404062004c4001d035030340307401c241d000900340380c666141542c800351840d441c030a40b611103278a0360380044840c450000d030008007040024a0f60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 231982032 1250 231980782 231980797
    0xb091f050f0714060f090c06091c0303050601080f06150d0b150309101b030e1501030c050a08010504050616140309011b111002070c0e180709020c03030f0705 69
    0x400080540421100c0144892104000ca09585042c1c9881145e2500c0880c159400103066209607030030081c0c1d24110004041c04100104481013519034000e03003510f1000d4540055020968600400c090703941c100419a074869038110344d00e06503150220003d6594000c80905910a03440454050003070740c06940304000b0316500401c0701c0f00c1e84401c03070010701080d402210103070b115001f158401c141c0ba8030740e801902d1180e10384080c0c0b4100190000300c2100100181c0c4100c40561045843c020108050141d0141c0a14000d801c0c445116040030b09000b00050b2a0344580c4a6030f16010400000c206c0c0800c1040d003100320142da220260b00d006104075264050543d0300c15454800100340300100d8815442600901c101c0c149003581a4107882081d10b0f81e440a1406101680010040b481d040e9415401007980c24800c1005400268a07001c4a400b680c20858020321501c4609a00740c41490080003440f00a186202c400e40c900110400f010741c607800040d1083c0500c0d034045000c83ca00c6405101500c058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 231983282 1250 231982032 231982057
    0x9040f050f040203010f022703011e020904061203020a14031b0a12020703030f110111030c070303060b0a140f0c060408130518071803140c04060b091f05 67
    0x4604020289003074121081d102203110358607040ca0b13614900351038002e0701d4420b6855124108160380310405080001d01062985516540e250800188400c8100031854854440180140c43e02c03000300502c8210381307035604208500c03000480800c00007980050b40c80d42d015404032140c550117245003101c924602072403040e020a1102c0078036401d0f9a5200090b410b43c400e008078401d6801c4103490100b40d03141c2601c2e0101900003695811407205c00b0f805002020300960034100001110102c080403031a85400549442849500c001003810030b240e41402941e001c0c0180c11032503445c0c1060307250041c00d40b04401c03108040d150341c00304100c0c480f10440c0d025107d40444803801d680c014986417400d40c0300361380960420b40c802109400301040ea420030242681c042c0c180002482c00c680c6440e8802d0320820311640d110003101401080100008001409541041c14405c005060440b1010108004d48400c3c1e005407254400605c694042a554034880d221595100f0783c040d1003502da00f0300115040c0c070034414850513 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 231984532 1250 231983282 231983291
    0x3021b0712030905042714060c030402091521070306091407090501060f030e010e0a03030f06060507050c010809070e160906111b060c160e161409040f 66
    0x208044180520303001c15100340c1c1c41c032080b90380300c2080204642400340d2100c6625400841c0350441ca129100904141d401044030100c4400c50041d91481c1070b00c00c9494880c2900301006110841c18035080300d5800c91601c0040410f071800323801c007180e00c0002d40c1c00c051400000c22a4414440039050041001071900240c00f482012003a09110b101c0c80d1010800203410300c500b41000a050301c062003803c3c180d613882e03a00d5041c401d1070307001e0490142a2050280714295a18442d0102c0d0101c200404400207100391130110384803280c403005104a035409e80c04201441802c02c59400021400324400711401000d0034203001c2921914900307131414200340c02a03070008800005010346403c40d8501c01d80d03196620781c1c980e41c00c9501d810045603071045020440b1000e070700890380207924901c048047c100c1e00801074401c50a090b0420140752502800140c01c4046141000c0148101c0d00c0610308203a100c1d441e507403481c107250302c002c0c0e00410700e4051001002040030041600c0c1c1080c1d031150410190030103544010300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 231985782 1250 231984532 231984539
    0x280204080f030315091902030a0209030a030f0f0e03070b1b06090307052103160e10080103110105090102070918020d0809040515030d0e1c1a06041b03021b07 69
    0x5035a82c0c015071307144503036090070844031a803440c1c6120f10310310604040080320b14046200d42d024000e0741000c0c1c8444040c1e0713024401d120f00d0b91410801e5820ba10300a6860000c40c0c40031480140150152107160800c000c0c40303c0c080c1c4400e4400050402c00c071421003111a6448840c10280300740d0b06a42c80582d9a14003400007403080340340001028104150003102a110004081400c0e0110250405000e03100c0003014000940503440407405039030300081900f000c2481e82c00c0e240001e60a00c11246800b00811580c01c014814821182403402842e07074203003461440c00003000c001035035900b294450403241d40d8443c641c030030003c944042c044041d02d90103042c00c22a09080d2a00f111550444076483d8022490034001407200d107600c09092245000103402b4002c14110200c00f243c1c420109400e80307400003250084410320b4030000865a043c1c0740030f60580700c011003140f881c81e020040f001d08218416803c040200b40c8084c588040b0340c0400030141070060b07032024070120305020310074240d120807a180603040703000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 231987032 1250 231985782 231985813
    0x70203010608011d07060f0c140a0204051905060a0e160309020a0b0304120206010b0a0e0609090115020d0e06030a05041109091b0a0e01060e011101050408041d28020408 74
    0x1005013503d41078841441d100e400c2200d14048071074086d0002480040050081441c40c5102c05032180d0000c00c5d140000e00940100d800e40300207440c0250b084076044580300482c045446a5a000b280c103e41c60386c0b5140c60701440ca000c2e40d001404030703400c4401402c1c404041c180a94006030b03503154041c110300080c0d40e0341e10703604082e600102d9040d02c0312900803243c4041240301081050507620210300f114100340d00080111454403442c6082a042a01000a45026920045100c1c000c0c20f41c1d000e0b56107401c02982e0000d08244a50741104180640740204220340d036503040c11780340c0c080d0420800007904e503201d0074082c800c005200d071415081506101400b0b0100c0000c01e0a4441a070751583c02d0041c10301c0003042c4080103825100e504d004440240046c0038040c40303110041070304201498401d007860014403d00d4211035041d58100c0e0703041e00c000340804c150b00d420300402241c0004d282182c401440c01008611000310307c101d0084000d0155507040a44540ca9410341e000307004514103d40c0c1041c0c8d2030622 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 231988282 1250 231987032 231987071
    0x8030c13080f0c010e01030504020a090f0f0e0a060c090612090305090904030c0201091e0306050c040312030f15050303030a09031107091a0306040312021606020d0c030f020301081207020301060801 86
    0x41c0f500182039070124403819406030107414001c079809032145c458286401c94007402007028a00c0e000100351a09440c2e410300d500b50085140c1800231002411040c10303a840c01e08200d484400c981018403122901c200043c2da04801d810344551303288400811940f00c107260403280e521070b60f004150301000783c0c0c0a000c00d1580c0081400e00441c400c0c0c0b240c824031522107c9108226601070300700148403200c0f10045c80061042c2c1c02aa401401c61000242001d443c0c1d5207001d09556041c0540300041d5944001c00c490302d01c24020907a14244030508141004e06050200340c0700e00c0020490080305484d000c0e18010140f20700080c080003c0a541590301d4030341c98460385400750003000c1a12083d004038029911991802003000d0b8095071341078175141b6070b0700c40d0694180042d4000d0101500c60f0304d1000400c101240c138900040100c0007135080c0001c0d024140b0300c0c02804035920300906100441c030500050042030000500020b4031021090303c00d4507a0507610019024010075000a56039508100038010291507a400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 231989532 1250 231988282 231988303
    0x11040f0e040213110d0b0d02030a08071502072001140c0d09090b010203070b070e0402040303030506120706052b021303120c0506070804050115141302040308030c13080f 74
    0x9003294100000885041610b18000061007861420802c280c104d005d1a8841000031034064401c1c040e40c000d940004c0d0418200a03015522408001602d600708110103100c0b0b125000142011801c1031b070706032034070800d02181c2080c180d01c0300100409080681c1c020394818220f00e0b403164111341d64004492002d6121001d4400c03100c040b83c2c0e100004070340f4a43d00c0c0100650000c041cce004604211880e00d9003460740c00e000d404442400718034680b00c2844d442d03900041000e94000e0b24089013a080030014011060304480c1c01090f00d4202c5001800100d90110880d04c51002c130660140c00c005546c5003404411002090000d82284005044405107041c040c3c8070013103c1c0280b0b000072a4a00084042d030341d480e00d0190040964100340c000410050080e40070542240c0107600000d26014120001036445103190046071704407040c0509101c2600d40011a04410b01d48405d043d402c15165541d01d10303c0340009042c2e90f130001804113541002c43c15442d01d141c000c00d980003c07103503480307120419191203499428 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 231990782 1250 231989532 231989539
    0x9010e100b0f0f0d0227070203190c032f010e0c2b06050a0e030a03050f100810020306031606051c0203040b060409060209040c36030611040f0e0402 65
    0x601d24414605030b00349404070300001d400d5201d13034034a030307803c1007054000301c00b04e180d8a40800441010201c54880e0140c42100c02c0d400039959a200d50304004a460f0f00704503020100070b0b0881f0804002540b005461003403010205100203c070070811088012501c0502c101c4a00d50f11b008101481e054001503c01058441a91b181c00041401200581202d0300311800305030004103500b1100014104da0300c00e5602c500b0f40b007c0021080c426181c1e00c0d0450348190800e00002e07458600344070b0901e9880c52704030303007054040c0798004246242405458858020000d8021116408400500b15071000c1c4141c140c0100d00b8045c00d11007035242d10016000e03401c00307000c180024805406084103171490b4400c4a001d19004580c91400380d6038401004050109040308803000e41c0c0905c0000b0480d140d501032071014401644800d0001e480c1c24014a10742d5110040044074040d404880e4210351802403902e0042d070f500100c0220b0019084c010154151007260320069000d40d864400098000c001500640554400c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 231992032 1250 231990782 231990799
    0x2703160e0106050a171306020c03070c0b03090a1b0b040803030f060102071404090c0b03070306030204050906010e0c0f04030b0a021b0601061d040b12012708040e09010e100b 76
    0x3040300320740c503004050100011039601460b008170024044020f581c0200c0c160202c80c1083c280d40d0b924800e07a0483c00f030103486680013040010401030302c603c0b018081e00d101d504841c2145000444030313995580000001e0110603603058200440c075041d001174001703010311018090f03650b0750f1245901d5981e0700886010207280034040204510350701c08a400021180343c280004640301e003d408100042030102c0c4100c5021a00d02c00005035240c41002442c460011078900191252a42c014041504c038000c1601105402c4840180401d14880c01e41640100031540c00e6500c0d0a900c00c1081028811904094a03080b440c008009650f83d10360020980f13aa08080c3c0100b0681402c0361031030780c1d07440c01e0007440e0200e014000c0d1000340c00180b02e1001d9131000c0091020680c13a4013070001c6400b9502080103c1c20382d03511090300d0040707408110750324280b408540d03400508850040c1c42d1a1601e00460280000715001031001c40d040041c250071402d101c041c1c5100759016545000586401000b80000b10303070003010300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 231993282 1250 231992032 231992039
    0xd02060f010b0c030d2c030c03030a0f0f09060b030c0d02060a0e1503010f050a0b0705120c0a08030a0c0809071d060f030d0c030801060311040302060a03020f0310080705040c052703160e01 82
    0x8030944210002948c000c0d82103480361803084015080b81003642d200c090b51081000e080440714015030003130314010000040c1800d640001d0504009035082c103240500f80b413058034001031311030394102d65040301d151908414445008000407891480102c032401032040100001c920149000c216a04407801161010355069807401150054000d840014059400444090320508032090081180074926020758002c504141c1d03500720990030585141c82c00c00d5035105060300c496042040c05410038218402040b50a2502c2d9601071800c01e21403846212101d0300c3d002c244161034050800412040007420303981c01214240c1d0040c9003124014040d8000b074143c800003c1c01c40e00030312600d5400161b20310b00030f00e4181150203000340c5501c569124001c04da030030400d20002c00c1c241b2000e1401028101d05600d2403a242c244414500724090304401e100320f240c0500c4480e0590040100c3e60303000c00b075107007a01034180c5182c04028035074607610001d0340502510032a245804800c004a4043da149501c1c3c00c51180d8a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 231994532 1250 231993282 231993371
    0x509010c0f02060708070207051806040c020309130c2f0c060406020c0937060b04051e120102040801240e010605070503040f03140d02060f010b0c030d 66
    0x2030307441481d07000da0007a20106852610811040d58070210b540110381c8250b68890201e4a0308501e140b002065000000620000c9e1600b0700a40801000307510040d1708000000d000030380d400e00020141c6a0407551845100741103801540889804050b410203941041e02c0208507061003e0b403a015559039000f6002c0d840a103152071000d540545510340d005003058584041844210107000d0300100420005450003c00c641c5030600c0004503a00c0d07030784450f0900301200480400d40303480d038011070003c034030610050100b6192010301c10400941490601c0410a0941c00700301c04001c8038410101075400000c01007640c490540020400854070341c0e05803c8c5498030303100200f05c0240e0b40202988080e070310740100131813403084014081850242041d245455a50b03c49100c584050303610071215100514104030214200740200302140342d450024000900d404004449a1b54050050840311540840c450800000070410b990703000422520400201704003101110590300c0c000700c0411201e01e000400180c00c034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 231995782 1250 231994532 231994547
    0x6050f01410319060e19090507080a0507121502030a021315170114010c0201260103060c050307080610020f01140402040e0a080a121b03060812090604170712060509010c 74
    0x2c4052945d0b6441d9105d000c4d400d0a148500e0180000a584400a64004c1a801d00043c0000d114a4006009030125450461304100c2c0c1d56014288140c0a0240f00d030114058144051005555500040e90395079103c2525000b4012000c52400c1c0c100c24020100d1001740b45d0680701c0c03848841c0e4032881d810005074200c800700c1c0d2409002d00710140255105203000b42d4051244110704910504102441e14600ba1903100f07d1078071040e070703c00074070700c1403004000380f01440c4960701c5a0041841c046246262840340503100b100040c05c100c0c0101240c042d114007580c0300380a0000700304030b018020300101030405024075003400d0503541a44141c0c90134400d8003695900061540a10b503000140700d04004130020141e403004002075100191940310000b06a114030b2003940b40002082d29100051014144100f1728600880004004110f00301007011074003669070b030000d440031500300105080204c005410b0180c00d050259010b00d41c0c841c4400c92410801c00544c002d41c0c82540c0420081020540b016022203460 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 231997032 1250 231995782 231995789
    0x16031d060901170c04150f0305070c02010206190e191101020d021e0a0b040f05010510060e0607150203160807030902010e13090203031c06050f0141031906 68
    0x407043e0078143d045140300c02150f43d015540c841c0c0c4605103a80c4400440c05080c1d04a44e850004803101c1514240c40c0c1c041c4074640d007001c03640c80c18080c0f040780381c2d0010350b8422000c0c0004064440d0707c48110035010490300104181c1c482101503900019651090742088490004101d0b00001ca4500b40032803948001642d955107401e0394004d010711802544c01b00b0700c03032841d602c03042d04174001c154406011414880c038890150b84100c4140b04c01e00c2c0c05040075401c50300054008107405110440402c40c0e00ea000941000400d011189a90754000798a480c441105800d110074814600200410404400c034174025001001d413521000c1e0250745626084040718042000240410540c40c8031145a003081e10104004080d034050015040c07c81d03400003403440d001079282d00c5080c400948410341d403140c4c0b409004002d060603501000b0b000445000070701400721600c1e15006024040f156400f49800803a0341040b07202c400d025000304150410703803a0300c0960080300c0720380c01c4140200b48564400f51910810703007103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 231998282 1250 231997032 231997037
    0x109050301020c120c070509041223030a15121209090b031c2c10080103050a08030618010b0301060e091003082a01020405091b0304021516031d060901 66
    0x200642584620680c1002184242502c55007901040311b842310341ca0030307000f07034082c0e0100000f003c0356640041203891000c8040c598a102940d0041e0310021100a032500000c01100c0440e58130907900b00b107943c07201964002c403400418040700409000024064103883d05165843e00d146a440d5200042924102051280c155000b4214290265140141c0d614a401e07186006d483d41c40344954800769091b0020f0f82d401140400e0104100301703250148030f00c914405141002c0280c0c1d89961110b5452f581c0c00b0b070000e400007030008005141a50b40003c1400318094030301d207078441961030306034540c5a44c1007405000045489000d90903080c2c5000e0607901c0c82000280d4580d8500c504540e90340109401c240515601182240c0e009880c102c2c044900d0007072540c10000040e1a580b42404100344008050410802d00201d0080068183d05c240102da074059016a446040190b89190032401c510a04407400b044c44500b50307074a420154805240361454107004003c0d0043e20b0001e0401084d4410416003030701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 231999532 1250 231998282 231998293
    0x10c05070308031801020a0801150f05030c070614150906040603080a1413030f020a0509060d080a020705060307030f1116060b0a0b0a05130b0f0306040203060f041a0109050301020c 79
    0x8403598000c40c1e0000c101c3c005640300b1240404c1160030781e044103035820302254491005100c000907040c032801b40d207102c070710b080403c4009520b0003074020b10014242c0032814800140c203006218054202884070401d44e0149801131804040242c3e40101000c00345100c3c1c55942c1c04140d05103020702856058170740001c641c0f46428901d01c42941e001c840c655900c6d542d0407041c40768141014060b01020020b5010300c0e603100c04003d141c41041000070641d00440e1103080c122090003100e441d1000750824048e40402d280383d0302c1c0350501040e450400b503a80883c2e0701100c000700308455654540c001c2c8002d28094801880039000541034815240510f01c840b030649810b110401d400700345079422105001401030031003200c031a181d40524003180e001c4400c4201013800069013000c0544840317403610041c00c48200c0d4074109030f007104004055103c054a80c601c02c540101c0840c62603900c2c504200c50743c200052007041007007040d0101202041c00e20b035000b400300700303503a00c009542d0a041c0200c4038141c82401c007409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 232000782 1250 231999532 231999539
    0x601030c0605030405070302040501140918071205010f0f0b09090a08181c03050406080a0509030901050f13031103010b0613062006040b10140904150902031c020c010c0507 75
    0x182c66803c018416145031207a041c0c0000580c5640c42040d000c0d203291203035400040700c0e030802d00102840140c01c01885504044d82c8091640000c2001020b0740c04444001664084a0800501428060924114452400411501004850307204c04d02d00642a182c58060743d444a02d865200c892010016000d41300030000d00d0312800c0304a0310941d130081c2c010030004000320342401c000001051400110041440014180070030f40d04000c1e0580c3c081c1003c4000c2c0503e2400035613841c0c07a0700405c00c03120f040c0000800c1400480340c4007405d0b81c004070100c41c100c880590356404c22403030500d0b407600883d000b940b91102188860900700201c0c0c0d031180e020303a10752004500d40070045640c20881c1004039080c0e1041c444c10740c8c081000340403160156004207250303502ca0a00810b4010f002d00264081401c4901052128601c1d8683d0700c0c50aa01a82000140801041074035100002d000a00002907043c003d0b5528207050001d03ca00c0180c07603d12690842c1c0c00345c400d00c001075602e0682c1107400f0b04981d110113800c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 232002032 1250 232000782 232000787
    0xf080c03070804080a031106010b07061508030705010b01080106030221060604180203040204140618061f030609060b03010e0109020f09130b12030a090504090609081306030e0601030c06 81
    0x200000144042100e01d4004562a203114980240d000b0b4000c50b00716501010074542e1262508a030f90200070050003895141c401c4483d070301e21425800a00c00c42d140e07404c4202c2c51aa9030041c42c0204140e2080c1c950310406450a00d0090034440e140074003040d03808001040c0e551080c0300b95103414945044400c205200c210030312078000c0c4010040384c0d10040400020450300c4003218031342904010624096100d04091040000755108e03804081d950500040070032001d69a071460313012060b103515920240f075446041c0400c9080c9083c0030004061503041101d1081203034190700600c2211280102042a5030f01c40c64401400d1100b84a00c03c000f2040c0c1300140300600540e070041042141d030b4042680b401c8001c0c0c01141c1c8004c44c545840203030329138031400d0b0b049905182d100030100541c00b201861030050282e03000341c00c54049018560191303565008135000c00c03d040c0d11a140740c94000b60360540301c0c00c84a442124030000340c001c400000342010103a034203030440024014140c980c0b0002840d2000e0030000c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 232003282 1250 232002032 232002037
    0x4060212092b0e120703060216050114070e0904030c05030a020708010b0d023105040b0402010305060103050403120b010507050102030108032205010504090906020702040501090e0d1106010620010c0c060c05070f08 93
    0x130480390302500f00000005840c0b840100020184101d40080140242c1011030845004812608010f0424010424240e0384503481d0140d2010465400d2020b031142d085c12510480d4000d001411131000048410741290000b900004460010000b40301c06605281032025400303003944003e422002c0b40401000c0418404ca00540c2d004d0240701c84082031007070740040420b40340150f4081d2001c458410620080d545e040c040c0541c091400e081c207000f07d003040c0c6e400400e0301c0b03000c2c180f000e4010343d10240c0c52066031042d001c0f228255000002551a561500e01c1d25861340c3c0701c0032007018001d03021a074640c500c5100302811030456038140c4a0b14103041ca081c00c1000034088882c41200c0c0c580d820440d600050756140302d20f601800c0f99410000382c00c0d84c0400002c2c50601115070440900c001081601e4042c0c000040b141d05541c041d240918081840382d80540400703202000710101035090110710a51540e101c910942101c0c040c500901032260340d05001d4501c0d1050f803101900c19021001044c1c0800c0b1000d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 232004532 1250 232003282 232003309
    0x10b0307080c1804150c0e0f0303031506090d0f1101020f160315110a020d0909111e0c0303012c010b2d07030503040b010905010e040b04060212092b0e 66
    0x1049481d1780741c1e645c039a00720b50304200404003080c1e80156840700da00b40104081c01d1b43c1000d4000b0340c41e40c00c0800c4038001551a01800074801c42c000204c81c0c0a540f210410500c1440c3d00c008004203201e007600e490f142100c8100b410351f00600c00da02d078005200100080c0c501e03a1040552520a00b00d056840d040f01c0041805c400480c0143c07603a0f02d50008180300da00901d0300401c181d02801c1681c40f4000010320030f0a003640603501c05800c01c50780a04041d1003d013217a820105405590501e050b803500c0980b01c0d07001d8184048030071300020000284003451500b100d580c6642e0400000442c4005c002d005103049000c1c054510b5164092240301490b42100340c07248552049501100300c540403152441d10140c0c014901200024000b100344001c020045012a0240246003410303c461343c1003540d940320416004102400444003100400d0500145504541e11081004a641a1850b025056030f0b03a0b003000980076003000c03000e182c1c04012168103031002c10703002c99559210300c85641c154040119030004841d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 232005782 1250 232004532 232004543
    0x1103150f10031a0a050f06100e13020f0d060e1006030e0705030f070f0b0c0c0d0c0519060e010206092508010c09030302070f05030606060d1d010b0307080c1804 70
    0x190088049035550305a241c03c254941800300c02480c0520b41c2c882a1400a001450b95100d8101400b410f50780d0740c0785580e00f10446140514030246000000342d0304648c408040d4110300d200203007107946400b03210300401119006080c207000305960364481d4081450b04503000440810030080c00e20490344250000680e019003801100c00c03403501c034000070f4103107000c804139555107621811042060f2031000300500c0040c80c50842580c02d08040500882d1100961040d035445600300310748100400c00261400070103010701508d085008105100300c140d004996002d2840842c0c030302c11103910170390710011380d403803103000314a014054082c1002d40060550850420f16001d8101e0608040303403d040034030030100074400139030360040324a145040c041c0c01d1100d01c0e00440d0a00e04400302c140040c2d02c001030301c60340120b03040e12802c1e80d41c7c00000540c0e0060265405011201c4041c0c0801e580300001508000c101d610300320b0603110696582d80c42c581e070301c01c6004085a00400c5101c800c2d5051a107299a443d80a405070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 232007032 1250 232005782 232005811
    0x2060706091b0510091a03070216062f0703170d02160c0f141302092808030c120d0b090f040b0703060b072301020f03041103150f 57
    0xd0b074440c010a5529000785a64900055040000d4a807042844a0508031350a01603c00c5061404007454003240001c0048000400801300708014402c100030340640c40f10190b5541e01c141ca8035001070001820500d40b034458020b40c4040c0e05441c40c1550f840101042840050001c01d00d0b543c0c0785881d09800c4500000c0041c0d05002d20040c64002d80001e1000d81e80e1106c810300c14000368503002c160140300da000407600d8100c0038070a010158081762800300c01030303003280c134070309100c0c0c50042d000080d105144540c1c0d08403030311041002c1c1c0d0a48081c080304003448902c040c45080d81d102c1349919502d0054828105155000c211648228958000109102100c500001c01c0303c81142c8041144035030183c2c1d00045800682040009000070704c142d040c0c02c51080e00c2e0500646e0710f41144490180560000035018002505404510b400c5420300010700c403007240c00035511000c2e084079150541d0011501646c0c44181c0b004424000d28011481c00c0500c02902481e0189803107000ca04039155800500d81786115512 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 232008282 1250 232007032 232007051
    0x50903090406090603020a0e0f0a0b030c10030e010b1207140607020306071e0305160809480d15020c1c0f1e0c0c0b0c0c0a060f05030402060706 63
    0x2240640c00180c20f4000d000b01c0c00500c1c62061040361641d80d804250701c802c05e0420300424049a41c0d46540141c2603040100d04c04082c080000e0030708448480302948901c0640c049107110b60160010542110548000c0207851091420b02c143c800c5180c81c41d14464101074414014000c0219841c140f1000c0034107843d051850360381c0428517103002a604100807030701042c0b9040c8004550020601e444080b8a030921040c148844001000381c00e0442e01002c4c01040720000d0a81d000c03c0009200300c1202d00403030030441001d18610344290404d041d0864890a640c03412101c8074052014100f22582c0180c000f407580c88481e19991002c094030440c011029400300f103662083c1d54100811440f0203025000c1c1c80101d1100e81300030300ba034503d910183c1c0c1402100c43c0d042456110042e03211560321101c0c03c110045032500d180c000c121001c0b60700000d8040001090035140c1007800940320308228070544603000c503952504000d9402d5007040280c2c03400a002040007030010706050001d492103c1c03040340d012542018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 232009532 1250 232008282 232008289
    0x10e010c24061802031914070c020f040911030f030304080a0c030912030203040f05031614010507050a0b0a2306060a030e061504061725050a0b070c062105090309 71
    0x40c00e85610f607a190017001380040e40c82203140080d602c048a03141000b0044a4810b00d080c0b03c20003c11120901000d41c81d441c1c25511036070300058903000024000c114828007481c002d12210940100240a40309000680790b641c40c00204482c0660340240307400e03080c030741042d0044490700c5090004030200a269480010802c00c102411070040340b00e0b401071500d0350308019001d004802d403a030049100307600012031149039a41002d5444195000504048022010b600058440d8460140c0041c0303207100301d140c660240a02e05100c1400b54101d2001403191070800303a50400d040d103103e56500343d104010f201040d40f41c603041c1c0040c0803c100c0c60070007013540d00d403a801c19400c00d4012160300c1005243e4500b40b418034a0144604005010001814446500c034100d0403940e0b5034680c1c01c0c600440246104a94613a1200b40071a0010710723006100554450700c030346070300307240390070840c0d080302c45200d02e45000c02c00034094454142c0140c2048a5100c401c03060b070946101034440503002c080a401b0400c40c151480e103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 232010782 1250 232009532 232009559
    0x3030405010e0c0a180f0e0a080d0c02071a090a030b010909021003021e03190518010b010f08070804031404080a0b09010209010e0d030e041505010e010c2406 69
    0x24011000020b1400140079500d04000260000d58450000a00c0a1101200c9090080c803000d00c240800680c10010f00b540340000c1030020450300c5540f081107030307010030050101e004101000504509000724a602d2101340d80d02c505500841c1d2001103010340018402c84140c0c0584030080c0c0081c6020315030b81d030382d03103864100141c01e0708045a4140c460f1901da00790b0030400c1e40800c2840c0039107000c42c641605c0050340c0e141071068103101e40170030034000041500300034940606035010070340040400840c1015203040c0032000c41d00001d28155401c14680c00301943c01055040c21450b413a0312510020346d0f50100c11110140c0060048062142c00480341c00702c2c00c17802001d88003805541c002001e081c0c550342000480500c0007440041260f00400000005990040c14144111800d80c0e040821042d103180c140c810102e000d2150750800e19203030083c80d104400b1090a4200c640030f8803942c010084a000440d81544c4c00c41c00a4441c0000a200e04d5034076508886c0c4c802c8015001c500096942c1e11240e1100c0c0e0344 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 232012032 1250 232010782 232010791
    0x501142703060907150c0807140d0908060c09010c0503310f08190302070e070801211703100b030109051006020a0c03031b0b25030905030904110c0303 66
    0x24a148400e04610341402c201c2c940c1c1111680c40100395080c40c0040000180880603060743c1040380c00c0d86144204004402501c81c0294001048950f100c0000d101c0c0783d807200562030b800c001400c550000590b06002180150007001ca02080f90700d06070301d5200545d403600145000312400e2104108419031034600c042080400a200c031034800c1031100c1640c41c0c441d092490780214800c42d102c0007040003100000508102c40c0d80614400131841c514030f041c02d07410401c0990113200c4c8031043c401040400b40e40611124184d40c003e004c000610400d03d1604064400c0c000802000090151031200c22444200c1c00386d03034041620b64007402c0807905c07001d031b10020b50020303400700303403d140c072942031090008a40ca004405410a4801018401415192070700c1c610f500344000b4043c00104c2201c00350000d202408a030125070084800f84903070508482d9000e00862a110040020340c0400c1007081c036511a0169110980c0c009e0001c5080c0707001441048003c20801c1001441c54000300f281012104003440650300c42c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 232013282 1250 232012032 232012087
    0x50f090a030218190209030c12011e0504170a05090f060d14060909060c0714070504020c030d05060a05150d0b0306130501050f040c09151e0f0e10050114 67
    0x1802e10b41e60503d03040350f00f080354600307003801448098047d80b0005403020311406e007102e0a244540c480b851203401040c2e00ca80e2109844656850790070f600005d03400003400f0324882c110131095602c101c010300312580a6202403200003001040300c0c0500d481c000e80180d114100c0203100a14000e1141d00030000c0321b07000502c1032162228001044031034940325a94a0b80301e00d0a80c05810300385082401001c3c280f04004005000c501105800f40da40c3c942004903c2c00f901018000310f503910301c0445480d980f90811452503130f2041c20a00055001d08102c40c4610840350040e28104541140d04c0d44040260441d20402d0600360341c4048100080d6010001a40240d03108401c42480c012142001800d548009042c08105290002480001104600f030001201c0542000007100ca5498002c0701c403404141d44070404108840b0801c0340384180300d07114035003116490307003070030644a5a8102d8203100400895940c003507041c03840e40030051035028a003402c106503944090f16141507414050808801e84410b150440c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 232014388 1106 232013282 232013329
    0x50102120307170103030806130b030d120e030d0e0601060305010e1602010e06090322030c0302060a090b070507180e060129071a16050f090a0302 64
    0x5031040607443c1046594a08004010510580e10726109626410782410140c9951040400d80000500035106a10804005980140044030501005c5448042100c8014010300050108e14002c0324001403180c0c20302c0700c0030b01e000816004102410b160000501101c8201001c0350ba00010ba040d04598429019030120b000d410404200d040c148144000c0c008020b0001c0060420003200e034034140071940400b4000200c254807480054066941210140054103040c002020354000c54284100d800b9507400585106622070001590203800c801c42c02e1043c610701c1030b0302110717081c040707041030061101d05984151600d0042c0b08034002c602d41d0b450181501e02c00d01c80e2008141c41c520228a44800309410244038982a503505154a40b0040f030000c0d800040c807040720074640d01141c0c1c0b05400d1000d0441c2a6030560b1020740f41c203512041211002006a0b2070f50626005240340032400c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 231834532 232014388 := by
  have h0 := BRFrame.cov_init 231834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 231834532 ≤ n) (h2 : n < 232014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
